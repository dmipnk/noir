use noirc_errors::Location;

use crate::{
    DataType, Type,
    ast::{
        AssignStatement, Expression, ForLoopStatement, ForRange, Ident, ItemVisibility, LValue,
        LetStatement, Path, Statement, StatementKind, WhileStatement,
    },
    hir::{
        resolution::{
            errors::ResolverError, import::PathResolutionError,
            visibility::struct_member_is_visible,
        },
        type_check::{Source, TypeCheckError},
    },
    hir_def::{
        expr::HirIdent,
        stmt::{HirAssignStatement, HirForStatement, HirLValue, HirLetStatement, HirStatement},
    },
    node_interner::{DefinitionId, DefinitionKind, GlobalId, StmtId},
};

use super::{Elaborator, Loop, lints};

impl Elaborator<'_> {
    fn elaborate_statement_value(&mut self, statement: Statement) -> (HirStatement, Type) {
        self.elaborate_statement_value_with_target_type(statement, None)
    }

    fn elaborate_statement_value_with_target_type(
        &mut self,
        statement: Statement,
        target_type: Option<&Type>,
    ) -> (HirStatement, Type) {
        match statement.kind {
            StatementKind::Let(let_stmt) => self.elaborate_local_let(let_stmt),
            StatementKind::Assign(assign) => self.elaborate_assign(assign),
            StatementKind::For(for_stmt) => self.elaborate_for(for_stmt),
            StatementKind::Loop(block, location) => self.elaborate_loop(block, location),
            StatementKind::While(while_) => self.elaborate_while(while_),
            StatementKind::Break => self.elaborate_jump(true, statement.location),
            StatementKind::Continue => self.elaborate_jump(false, statement.location),
            StatementKind::Comptime(statement) => self.elaborate_comptime_statement(*statement),
            StatementKind::Expression(expr) => {
                let (expr, typ) = self.elaborate_expression_with_target_type(expr, target_type);
                (HirStatement::Expression(expr), typ)
            }
            StatementKind::Semi(expr) => {
                let (expr, _typ) = self.elaborate_expression(expr);
                (HirStatement::Semi(expr), Type::Unit)
            }
            StatementKind::Interned(id) => {
                let kind = self.interner.get_statement_kind(id);
                let statement = Statement { kind: kind.clone(), location: statement.location };
                self.elaborate_statement_value_with_target_type(statement, target_type)
            }
            StatementKind::Error => (HirStatement::Error, Type::Error),
        }
    }

    pub(crate) fn elaborate_statement(&mut self, statement: Statement) -> (StmtId, Type) {
        self.elaborate_statement_with_target_type(statement, None)
    }

    pub(crate) fn elaborate_statement_with_target_type(
        &mut self,
        statement: Statement,
        target_type: Option<&Type>,
    ) -> (StmtId, Type) {
        let location = statement.location;
        let (hir_statement, typ) =
            self.elaborate_statement_value_with_target_type(statement, target_type);
        let id = self.interner.push_stmt(hir_statement);
        self.interner.push_stmt_location(id, location);
        (id, typ)
    }

    pub(super) fn elaborate_local_let(&mut self, let_stmt: LetStatement) -> (HirStatement, Type) {
        self.elaborate_let(let_stmt, None)
    }

    /// Elaborate a local or global let statement.
    /// If this is a global let, the DefinitionId of the global is specified so that
    /// elaborate_pattern can create a Global definition kind with the correct ID
    /// instead of a local one with a fresh ID.
    pub(super) fn elaborate_let(
        &mut self,
        let_stmt: LetStatement,
        global_id: Option<GlobalId>,
    ) -> (HirStatement, Type) {
        let type_contains_unspecified = let_stmt.r#type.contains_unspecified();
        let annotated_type = self.resolve_inferred_type(let_stmt.r#type);

        let expr_location = let_stmt.expression.location;
        let (expression, expr_type) =
            self.elaborate_expression_with_target_type(let_stmt.expression, Some(&annotated_type));

        // Require the top-level of a global's type to be fully-specified
        if type_contains_unspecified && global_id.is_some() {
            let expected_type = annotated_type.clone();
            let error =
                ResolverError::UnspecifiedGlobalType { location: expr_location, expected_type };
            self.push_err(error);
        }

        let definition = match global_id {
            None => DefinitionKind::Local(Some(expression)),
            Some(id) => DefinitionKind::Global(id),
        };

        // Now check if LHS is the same type as the RHS
        // Importantly, we do not coerce any types implicitly
        self.unify_with_coercions(&expr_type, &annotated_type, expression, expr_location, || {
            TypeCheckError::TypeMismatch {
                expected_typ: annotated_type.to_string(),
                expr_typ: expr_type.to_string(),
                expr_location,
            }
        });

        if annotated_type.is_integer() {
            let errors = lints::overflowing_int(self.interner, &expression, &annotated_type);
            for error in errors {
                self.push_err(error);
            }
        }

        let warn_if_unused =
            !let_stmt.attributes.iter().any(|attr| attr.is_allow_unused_variables());

        let r#type = annotated_type;
        let pattern = self.elaborate_pattern_and_store_ids(
            let_stmt.pattern,
            r#type.clone(),
            definition,
            &mut Vec::new(),
            warn_if_unused,
        );

        let attributes = let_stmt.attributes;
        let comptime = let_stmt.comptime;
        let is_global_let = let_stmt.is_global_let;
        let let_ =
            HirLetStatement::new(pattern, r#type, expression, attributes, comptime, is_global_let);
        (HirStatement::Let(let_), Type::Unit)
    }

    pub(super) fn elaborate_assign(&mut self, assign: AssignStatement) -> (HirStatement, Type) {
        let expr_location = assign.expression.location;
        let (expression, expr_type) = self.elaborate_expression(assign.expression);
        let (lvalue, lvalue_type, mutable) = self.elaborate_lvalue(assign.lvalue);

        if !mutable {
            let (name, location) = self.get_lvalue_name_and_location(&lvalue);
            self.push_err(TypeCheckError::VariableMustBeMutable { name, location });
        }

        self.unify_with_coercions(&expr_type, &lvalue_type, expression, expr_location, || {
            TypeCheckError::TypeMismatchWithSource {
                actual: expr_type.clone(),
                expected: lvalue_type.clone(),
                location: expr_location,
                source: Source::Assignment,
            }
        });

        let stmt = HirAssignStatement { lvalue, expression };
        (HirStatement::Assign(stmt), Type::Unit)
    }

    pub(super) fn elaborate_for(&mut self, for_loop: ForLoopStatement) -> (HirStatement, Type) {
        let (start, end) = match for_loop.range {
            ForRange::Range(bounds) => bounds.into_half_open(),
            ForRange::Array(_) => {
                let for_stmt =
                    for_loop.range.into_for(for_loop.identifier, for_loop.block, for_loop.location);

                return self.elaborate_statement_value(for_stmt);
            }
        };

        let start_location = start.location;
        let end_location = end.location;

        let (start_range, start_range_type) = self.elaborate_expression(start);
        let (end_range, end_range_type) = self.elaborate_expression(end);
        let (identifier, block) = (for_loop.identifier, for_loop.block);

        let old_loop = std::mem::take(&mut self.current_loop);

        self.current_loop = Some(Loop { is_for: true, has_break: false });
        self.push_scope();

        // TODO: For loop variables are currently mutable by default since we haven't
        //       yet implemented syntax for them to be optionally mutable.
        let kind = DefinitionKind::Local(None);
        let identifier = self.add_variable_decl(
            identifier, false, // mutable
            true,  // allow_shadowing
            true,  // warn_if_unused
            kind,
        );

        // Check that start range and end range have the same types
        let range_location = start_location.merge(end_location);
        self.unify(&start_range_type, &end_range_type, || TypeCheckError::TypeMismatch {
            expected_typ: start_range_type.to_string(),
            expr_typ: end_range_type.to_string(),
            expr_location: range_location,
        });

        let expected_type = self.polymorphic_integer();

        self.unify(&start_range_type, &expected_type, || TypeCheckError::TypeCannotBeUsed {
            typ: start_range_type.clone(),
            place: "for loop",
            location: range_location,
        });

        self.interner.push_definition_type(identifier.id, start_range_type);

        let block_location = block.type_location();
        let (block, block_type) = self.elaborate_expression(block);

        self.unify(&block_type, &Type::Unit, || TypeCheckError::TypeMismatch {
            expected_typ: Type::Unit.to_string(),
            expr_typ: block_type.to_string(),
            expr_location: block_location,
        });

        self.pop_scope();
        self.current_loop = old_loop;

        let statement =
            HirStatement::For(HirForStatement { start_range, end_range, block, identifier });

        (statement, Type::Unit)
    }

    pub(super) fn elaborate_loop(
        &mut self,
        block: Expression,
        location: Location,
    ) -> (HirStatement, Type) {
        let in_constrained_function = self.in_constrained_function();
        if in_constrained_function {
            self.push_err(ResolverError::LoopInConstrainedFn { location });
        }

        let old_loop = std::mem::take(&mut self.current_loop);
        self.current_loop = Some(Loop { is_for: false, has_break: false });
        self.push_scope();

        let block_location = block.type_location();
        let (block, block_type) = self.elaborate_expression(block);

        self.unify(&block_type, &Type::Unit, || TypeCheckError::TypeMismatch {
            expected_typ: Type::Unit.to_string(),
            expr_typ: block_type.to_string(),
            expr_location: block_location,
        });

        self.pop_scope();

        let last_loop =
            std::mem::replace(&mut self.current_loop, old_loop).expect("Expected a loop");
        if !last_loop.has_break {
            self.push_err(ResolverError::LoopWithoutBreak { location });
        }

        let statement = HirStatement::Loop(block);

        (statement, Type::Unit)
    }

    pub(super) fn elaborate_while(&mut self, while_: WhileStatement) -> (HirStatement, Type) {
        let in_constrained_function = self.in_constrained_function();
        if in_constrained_function {
            self.push_err(ResolverError::WhileInConstrainedFn {
                location: while_.while_keyword_location,
            });
        }

        let old_loop = std::mem::take(&mut self.current_loop);
        self.current_loop = Some(Loop { is_for: false, has_break: false });
        self.push_scope();

        let location = while_.condition.type_location();
        let (condition, cond_type) = self.elaborate_expression(while_.condition);

        self.unify(&cond_type, &Type::Bool, || TypeCheckError::TypeMismatch {
            expected_typ: Type::Bool.to_string(),
            expr_typ: cond_type.to_string(),
            expr_location: location,
        });

        let block_location = while_.body.type_location();
        let (block, block_type) = self.elaborate_expression(while_.body);

        self.unify(&block_type, &Type::Unit, || TypeCheckError::TypeMismatch {
            expected_typ: Type::Unit.to_string(),
            expr_typ: block_type.to_string(),
            expr_location: block_location,
        });

        self.pop_scope();

        std::mem::replace(&mut self.current_loop, old_loop).expect("Expected a loop");

        let statement = HirStatement::While(condition, block);

        (statement, Type::Unit)
    }

    fn elaborate_jump(&mut self, is_break: bool, location: Location) -> (HirStatement, Type) {
        let in_constrained_function = self.in_constrained_function();

        if in_constrained_function {
            self.push_err(ResolverError::JumpInConstrainedFn { is_break, location });
        }

        if let Some(current_loop) = &mut self.current_loop {
            if is_break {
                current_loop.has_break = true;
            }
        } else {
            self.push_err(ResolverError::JumpOutsideLoop { is_break, location });
        }

        let expr = if is_break { HirStatement::Break } else { HirStatement::Continue };
        (expr, self.interner.next_type_variable())
    }

    fn get_lvalue_name_and_location(&self, lvalue: &HirLValue) -> (String, Location) {
        match lvalue {
            HirLValue::Ident(name, _) => {
                let location = name.location;

                if let Some(definition) = self.interner.try_definition(name.id) {
                    (definition.name.clone(), location)
                } else {
                    ("(undeclared variable)".into(), location)
                }
            }
            HirLValue::MemberAccess { object, .. } => self.get_lvalue_name_and_location(object),
            HirLValue::Index { array, .. } => self.get_lvalue_name_and_location(array),
            HirLValue::Dereference { lvalue, .. } => self.get_lvalue_name_and_location(lvalue),
        }
    }

    fn elaborate_lvalue(&mut self, lvalue: LValue) -> (HirLValue, Type, bool) {
        match lvalue {
            LValue::Ident(ident) => {
                let mut mutable = true;
                let location = ident.location();
                let path = Path::from_single(ident.0.contents, location);
                let ((ident, scope_index), _) = self.get_ident_from_path(path);

                self.resolve_local_variable(ident.clone(), scope_index);

                let typ = if ident.id == DefinitionId::dummy_id() {
                    Type::Error
                } else {
                    if let Some(definition) = self.interner.try_definition(ident.id) {
                        mutable = definition.mutable;

                        if definition.comptime && !self.in_comptime_context() {
                            self.push_err(ResolverError::MutatingComptimeInNonComptimeContext {
                                name: definition.name.clone(),
                                location: ident.location,
                            });
                        }
                    }

                    let typ = self.interner.definition_type(ident.id).instantiate(self.interner).0;
                    typ.follow_bindings()
                };

                self.interner.add_local_reference(ident.id, location);

                (HirLValue::Ident(ident.clone(), typ.clone()), typ, mutable)
            }
            LValue::MemberAccess { object, field_name, location } => {
                let (object, lhs_type, mut mutable) = self.elaborate_lvalue(*object);
                let mut object = Box::new(object);
                let field_name = field_name.clone();

                let object_ref = &mut object;
                let mutable_ref = &mut mutable;

                let dereference_lhs = move |_: &mut Self, _, element_type| {
                    // We must create a temporary value first to move out of object_ref before
                    // we eventually reassign to it.
                    let id = DefinitionId::dummy_id();
                    let ident = HirIdent::non_trait_method(id, location);
                    let tmp_value = HirLValue::Ident(ident, Type::Error);

                    let lvalue = std::mem::replace(object_ref, Box::new(tmp_value));
                    *object_ref =
                        Box::new(HirLValue::Dereference { lvalue, element_type, location });
                    *mutable_ref = true;
                };

                let name = &field_name.0.contents;
                let (object_type, field_index) = self
                    .check_field_access(
                        &lhs_type,
                        name,
                        field_name.location(),
                        Some(dereference_lhs),
                    )
                    .unwrap_or((Type::Error, 0));

                let field_index = Some(field_index);
                let typ = object_type.clone();
                let lvalue =
                    HirLValue::MemberAccess { object, field_name, field_index, typ, location };
                (lvalue, object_type, mutable)
            }
            LValue::Index { array, index, location } => {
                let expr_location = index.location;
                let (index, index_type) = self.elaborate_expression(index);

                let expected = self.polymorphic_integer_or_field();
                self.unify(&index_type, &expected, || TypeCheckError::TypeMismatch {
                    expected_typ: "an integer".to_owned(),
                    expr_typ: index_type.to_string(),
                    expr_location,
                });

                let (mut lvalue, mut lvalue_type, mut mutable) = self.elaborate_lvalue(*array);

                // Before we check that the lvalue is an array, try to dereference it as many times
                // as needed to unwrap any &mut wrappers.
                while let Type::MutableReference(element) = lvalue_type.follow_bindings() {
                    let element_type = element.as_ref().clone();
                    lvalue =
                        HirLValue::Dereference { lvalue: Box::new(lvalue), element_type, location };
                    lvalue_type = *element;
                    // We know this value to be mutable now since we found an `&mut`
                    mutable = true;
                }

                let typ = match lvalue_type.follow_bindings() {
                    Type::Array(_, elem_type) => *elem_type,
                    Type::Slice(elem_type) => *elem_type,
                    Type::Error => Type::Error,
                    Type::String(_) => {
                        let (_lvalue_name, lvalue_location) =
                            self.get_lvalue_name_and_location(&lvalue);
                        self.push_err(TypeCheckError::StringIndexAssign {
                            location: lvalue_location,
                        });
                        Type::Error
                    }
                    Type::TypeVariable(_) => {
                        self.push_err(TypeCheckError::TypeAnnotationsNeededForIndex { location });
                        Type::Error
                    }
                    other => {
                        self.push_err(TypeCheckError::TypeMismatch {
                            expected_typ: "array".to_string(),
                            expr_typ: other.to_string(),
                            expr_location: location,
                        });
                        Type::Error
                    }
                };

                let array = Box::new(lvalue);
                let array_type = typ.clone();
                (HirLValue::Index { array, index, typ, location }, array_type, mutable)
            }
            LValue::Dereference(lvalue, location) => {
                let (lvalue, reference_type, _) = self.elaborate_lvalue(*lvalue);
                let lvalue = Box::new(lvalue);

                let element_type = Type::type_variable(self.interner.next_type_variable_id());
                let expected_type = Type::MutableReference(Box::new(element_type.clone()));

                self.unify(&reference_type, &expected_type, || TypeCheckError::TypeMismatch {
                    expected_typ: expected_type.to_string(),
                    expr_typ: reference_type.to_string(),
                    expr_location: location,
                });

                // Dereferences are always mutable since we already type checked against a &mut T
                let typ = element_type.clone();
                let lvalue = HirLValue::Dereference { lvalue, element_type, location };
                (lvalue, typ, true)
            }
            LValue::Interned(id, location) => {
                let lvalue = self.interner.get_lvalue(id, location).clone();
                self.elaborate_lvalue(lvalue)
            }
        }
    }

    /// Type checks a field access, adding dereference operators as necessary
    pub(super) fn check_field_access(
        &mut self,
        lhs_type: &Type,
        field_name: &str,
        location: Location,
        dereference_lhs: Option<impl FnMut(&mut Self, Type, Type)>,
    ) -> Option<(Type, usize)> {
        let lhs_type = lhs_type.follow_bindings();

        match &lhs_type {
            Type::DataType(s, args) => {
                let s = s.borrow();
                if let Some((field, visibility, index)) = s.get_field(field_name, args) {
                    self.interner.add_struct_member_reference(s.id, index, location);

                    self.check_struct_field_visibility(&s, field_name, visibility, location);

                    return Some((field, index));
                }
            }
            Type::Tuple(elements) => {
                if let Ok(index) = field_name.parse::<usize>() {
                    let length = elements.len();
                    if index < length {
                        return Some((elements[index].clone(), index));
                    } else {
                        self.push_err(TypeCheckError::TupleIndexOutOfBounds {
                            index,
                            lhs_type,
                            length,
                            location,
                        });
                        return None;
                    }
                }
            }
            // If the lhs is a mutable reference we automatically transform
            // lhs.field into (*lhs).field
            Type::MutableReference(element) => {
                if let Some(mut dereference_lhs) = dereference_lhs {
                    dereference_lhs(self, lhs_type.clone(), element.as_ref().clone());
                    return self.check_field_access(
                        element,
                        field_name,
                        location,
                        Some(dereference_lhs),
                    );
                } else {
                    let (element, index) =
                        self.check_field_access(element, field_name, location, dereference_lhs)?;
                    return Some((Type::MutableReference(Box::new(element)), index));
                }
            }
            _ => (),
        }

        // If we get here the type has no field named 'access.rhs'.
        // Now we specialize the error message based on whether we know the object type in question yet.
        if let Type::TypeVariable(..) = &lhs_type {
            self.push_err(TypeCheckError::TypeAnnotationsNeededForFieldAccess { location });
        } else if lhs_type != Type::Error {
            self.push_err(TypeCheckError::AccessUnknownMember {
                lhs_type,
                field_name: field_name.to_string(),
                location,
            });
        }

        None
    }

    pub(super) fn check_struct_field_visibility(
        &mut self,
        struct_type: &DataType,
        field_name: &str,
        visibility: ItemVisibility,
        location: Location,
    ) {
        if self.silence_field_visibility_errors > 0 {
            return;
        }

        if !struct_member_is_visible(struct_type.id, visibility, self.module_id(), self.def_maps) {
            self.push_err(ResolverError::PathResolutionError(PathResolutionError::Private(
                Ident::new(field_name.to_string(), location),
            )));
        }
    }

    fn elaborate_comptime_statement(&mut self, statement: Statement) -> (HirStatement, Type) {
        let location = statement.location;
        let (hir_statement, _typ) =
            self.elaborate_in_comptime_context(|this| this.elaborate_statement(statement));
        let mut interpreter = self.setup_interpreter();
        let value = interpreter.evaluate_statement(hir_statement);
        let (expr, typ) = self.inline_comptime_value(value, location);

        let location = self.interner.id_location(hir_statement);
        self.debug_comptime(location, |interner| expr.to_display_ast(interner).kind);

        (HirStatement::Expression(expr), typ)
    }
}
