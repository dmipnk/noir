use crate::{
    Type,
    ast::{Ident, NoirFunction, Signedness, UnaryOp, Visibility},
    graph::CrateId,
    hir::{
        resolution::errors::{PubPosition, ResolverError},
        type_check::TypeCheckError,
    },
    hir_def::{
        expr::{HirBlockExpression, HirExpression, HirIdent, HirLiteral, HirMatch},
        function::FuncMeta,
        stmt::HirStatement,
    },
    node_interner::{
        DefinitionId, DefinitionKind, ExprId, FuncId, FunctionModifiers, NodeInterner,
    },
};

use noirc_errors::{Located, Location};

pub(super) fn deprecated_function(interner: &NodeInterner, expr: ExprId) -> Option<TypeCheckError> {
    let HirExpression::Ident(HirIdent { location, id, impl_kind: _ }, _) =
        interner.expression(&expr)
    else {
        return None;
    };

    let Some(DefinitionKind::Function(func_id)) = interner.try_definition(id).map(|def| &def.kind)
    else {
        return None;
    };

    let attributes = interner.function_attributes(func_id);
    attributes.get_deprecated_note().map(|note| TypeCheckError::CallDeprecated {
        name: interner.definition_name(id).to_string(),
        note,
        location,
    })
}

/// Inline attributes are only relevant for constrained functions
/// as all unconstrained functions are not inlined and so
/// associated attributes are disallowed.
pub(super) fn inlining_attributes(
    func: &FuncMeta,
    modifiers: &FunctionModifiers,
) -> Option<ResolverError> {
    if modifiers.is_unconstrained {
        if modifiers.attributes.is_no_predicates() {
            let ident = func_meta_name_ident(func, modifiers);
            Some(ResolverError::NoPredicatesAttributeOnUnconstrained { ident })
        } else if modifiers.attributes.is_foldable() {
            let ident = func_meta_name_ident(func, modifiers);
            Some(ResolverError::FoldAttributeOnUnconstrained { ident })
        } else {
            None
        }
    } else {
        None
    }
}

/// Attempting to define new low level (`#[builtin]` or `#[foreign]`) functions outside of the stdlib is disallowed.
pub(super) fn low_level_function_outside_stdlib(
    func: &FuncMeta,
    modifiers: &FunctionModifiers,
    crate_id: CrateId,
) -> Option<ResolverError> {
    let is_low_level_function =
        modifiers.attributes.function().is_some_and(|func| func.is_low_level());
    if !crate_id.is_stdlib() && is_low_level_function {
        let ident = func_meta_name_ident(func, modifiers);
        Some(ResolverError::LowLevelFunctionOutsideOfStdlib { ident })
    } else {
        None
    }
}

/// Oracle definitions (functions with the `#[oracle]` attribute) must be marked as unconstrained.
pub(super) fn oracle_not_marked_unconstrained(
    func: &FuncMeta,
    modifiers: &FunctionModifiers,
) -> Option<ResolverError> {
    let is_oracle_function = modifiers.attributes.function().is_some_and(|func| func.is_oracle());
    if is_oracle_function && !modifiers.is_unconstrained {
        let ident = func_meta_name_ident(func, modifiers);
        Some(ResolverError::OracleMarkedAsConstrained { ident })
    } else {
        None
    }
}

/// Oracle functions may not be called by constrained functions directly.
///
/// In order for a constrained function to call an oracle it must first call through an unconstrained function.
pub(super) fn oracle_called_from_constrained_function(
    interner: &NodeInterner,
    called_func: &FuncId,
    calling_from_constrained_runtime: bool,
    location: Location,
) -> Option<ResolverError> {
    if !calling_from_constrained_runtime {
        return None;
    }

    let function_attributes = interner.function_attributes(called_func);
    let is_oracle_call = function_attributes.function().is_some_and(|func| func.is_oracle());
    if is_oracle_call {
        Some(ResolverError::UnconstrainedOracleReturnToConstrained { location })
    } else {
        None
    }
}

/// `pub` is required on return types for entry point functions
pub(super) fn missing_pub(func: &FuncMeta, modifiers: &FunctionModifiers) -> Option<ResolverError> {
    if func.is_entry_point
        && func.return_type() != &Type::Unit
        && func.return_visibility == Visibility::Private
    {
        let ident = func_meta_name_ident(func, modifiers);
        Some(ResolverError::NecessaryPub { ident })
    } else {
        None
    }
}

/// Check that we are not passing a mutable reference from a constrained runtime to an unconstrained runtime.
pub(super) fn unconstrained_function_args(
    function_args: &[(Type, ExprId, Location)],
) -> Vec<TypeCheckError> {
    function_args
        .iter()
        .filter_map(|(typ, _, location)| {
            if !typ.is_valid_for_unconstrained_boundary() {
                Some(TypeCheckError::ConstrainedReferenceToUnconstrained { location: *location })
            } else {
                None
            }
        })
        .collect()
}

/// Check that we are not passing a slice from an unconstrained runtime to a constrained runtime.
pub(super) fn unconstrained_function_return(
    return_type: &Type,
    location: Location,
) -> Option<TypeCheckError> {
    if return_type.contains_slice() {
        Some(TypeCheckError::UnconstrainedSliceReturnToConstrained { location })
    } else if !return_type.is_valid_for_unconstrained_boundary() {
        Some(TypeCheckError::UnconstrainedReferenceToConstrained { location })
    } else {
        None
    }
}

/// Only entrypoint functions require a `pub` visibility modifier applied to their return types.
///
/// Application of `pub` to other functions is not meaningful and is a mistake.
pub(super) fn unnecessary_pub_return(
    func: &FuncMeta,
    modifiers: &FunctionModifiers,
    is_entry_point: bool,
) -> Option<ResolverError> {
    if !is_entry_point && func.return_visibility == Visibility::Public {
        let ident = func_meta_name_ident(func, modifiers);
        Some(ResolverError::UnnecessaryPub { ident, position: PubPosition::ReturnType })
    } else {
        None
    }
}

/// Only arguments to entrypoint functions may have a non-private visibility modifier applied to them.
///
/// Other functions are disallowed from declaring the visibility of their arguments.
pub(super) fn unnecessary_pub_argument(
    func: &NoirFunction,
    arg_visibility: Visibility,
    is_entry_point: bool,
) -> Option<ResolverError> {
    if arg_visibility == Visibility::Public && !is_entry_point {
        Some(ResolverError::UnnecessaryPub {
            ident: func.name_ident().clone(),
            position: PubPosition::Parameter,
        })
    } else {
        None
    }
}

/// Check if an assignment is overflowing with respect to `annotated_type`
/// in a declaration statement where `annotated_type` is a signed or unsigned integer
pub(crate) fn overflowing_int(
    interner: &NodeInterner,
    rhs_expr: &ExprId,
    annotated_type: &Type,
) -> Vec<TypeCheckError> {
    let expr = interner.expression(rhs_expr);
    let location = interner.expr_location(rhs_expr);

    let mut errors = Vec::with_capacity(2);
    match expr {
        HirExpression::Literal(HirLiteral::Integer(value)) => match annotated_type {
            Type::Integer(Signedness::Unsigned, bit_size) => {
                let bit_size: u32 = (*bit_size).into();
                let max = if bit_size == 128 { u128::MAX } else { 2u128.pow(bit_size) - 1 };
                if value.field > max.into() || value.is_negative {
                    errors.push(TypeCheckError::OverflowingAssignment {
                        expr: value,
                        ty: annotated_type.clone(),
                        range: format!("0..={}", max),
                        location,
                    });
                }
            }
            Type::Integer(Signedness::Signed, bit_count) => {
                let bit_count: u32 = (*bit_count).into();
                let min = 2u128.pow(bit_count - 1);
                let max = 2u128.pow(bit_count - 1) - 1;
                if (value.is_negative && value.field > min.into())
                    || (!value.is_negative && value.field > max.into())
                {
                    errors.push(TypeCheckError::OverflowingAssignment {
                        expr: value,
                        ty: annotated_type.clone(),
                        range: format!("-{}..={}", min, max),
                        location,
                    });
                }
            }
            _ => (),
        },
        HirExpression::Prefix(expr) => {
            overflowing_int(interner, &expr.rhs, annotated_type);
            if expr.operator == UnaryOp::Minus && annotated_type.is_unsigned() {
                errors.push(TypeCheckError::InvalidUnaryOp {
                    kind: annotated_type.to_string(),
                    location,
                });
            }
        }
        HirExpression::Infix(expr) => {
            errors.extend(overflowing_int(interner, &expr.lhs, annotated_type));
            errors.extend(overflowing_int(interner, &expr.rhs, annotated_type));
        }
        _ => {}
    }

    errors
}

fn func_meta_name_ident(func: &FuncMeta, modifiers: &FunctionModifiers) -> Ident {
    Ident(Located::from(func.name.location, modifiers.name.clone()))
}

/// Check that a recursive function *can* return without endlessly calling itself.
pub(crate) fn unbounded_recursion<'a>(
    interner: &'a NodeInterner,
    func_id: FuncId,
    func_name: impl FnOnce() -> &'a str,
    func_location: Location,
    body_id: ExprId,
) -> Option<ResolverError> {
    if !can_return_without_recursing(interner, func_id, body_id) {
        Some(ResolverError::UnconditionalRecursion {
            name: func_name().to_string(),
            location: func_location,
        })
    } else {
        None
    }
}

/// Check if an expression will end up calling a specific function.
fn can_return_without_recursing(interner: &NodeInterner, func_id: FuncId, expr_id: ExprId) -> bool {
    let check = |e| can_return_without_recursing(interner, func_id, e);

    let check_block = |block: HirBlockExpression| {
        block.statements.iter().all(|stmt_id| match interner.statement(stmt_id) {
            HirStatement::Let(s) => check(s.expression),
            HirStatement::Assign(s) => check(s.expression),
            HirStatement::Expression(e) => check(e),
            HirStatement::Semi(e) => check(e),
            // Rust doesn't seem to check the for loop body (it's bounds might mean it's never called).
            HirStatement::For(e) => check(e.start_range) && check(e.end_range),
            HirStatement::Loop(e) => check(e),
            HirStatement::While(condition, block) => check(condition) && check(block),
            HirStatement::Comptime(_)
            | HirStatement::Break
            | HirStatement::Continue
            | HirStatement::Error => true,
        })
    };

    match interner.expression(&expr_id) {
        HirExpression::Ident(ident, _) => {
            if ident.id == DefinitionId::dummy_id() {
                return true;
            }
            let definition = interner.definition(ident.id);
            if let DefinitionKind::Function(id) = definition.kind { func_id != id } else { true }
        }
        HirExpression::Block(b) => check_block(b),
        HirExpression::Prefix(e) => check(e.rhs),
        HirExpression::Infix(e) => check(e.lhs) && check(e.rhs),
        HirExpression::Index(e) => check(e.collection) && check(e.index),
        HirExpression::MemberAccess(e) => check(e.lhs),
        HirExpression::Call(e) => check(e.func) && e.arguments.iter().cloned().all(check),
        HirExpression::MethodCall(e) => check(e.object) && e.arguments.iter().cloned().all(check),
        HirExpression::Constrain(e) => check(e.0) && e.2.map(check).unwrap_or(true),
        HirExpression::Cast(e) => check(e.lhs),
        HirExpression::If(e) => {
            check(e.condition) && (check(e.consequence) || e.alternative.map(check).unwrap_or(true))
        }
        HirExpression::Match(e) => can_return_without_recursing_match(interner, func_id, &e),
        HirExpression::Tuple(e) => e.iter().cloned().all(check),
        HirExpression::Unsafe(b) => check_block(b),
        // Rust doesn't check the lambda body (it might not be called).
        HirExpression::Lambda(_)
        | HirExpression::Literal(_)
        | HirExpression::Constructor(_)
        | HirExpression::EnumConstructor(_)
        | HirExpression::Quote(_)
        | HirExpression::Unquote(_)
        | HirExpression::Comptime(_)
        | HirExpression::Error => true,
    }
}

fn can_return_without_recursing_match(
    interner: &NodeInterner,
    func_id: FuncId,
    match_expr: &HirMatch,
) -> bool {
    let check_match = |e| can_return_without_recursing_match(interner, func_id, e);
    let check = |e| can_return_without_recursing(interner, func_id, e);

    match match_expr {
        HirMatch::Success(expr) => check(*expr),
        HirMatch::Failure => true,
        HirMatch::Guard { cond: _, body, otherwise } => check(*body) && check_match(otherwise),
        HirMatch::Switch(_, cases, otherwise) => {
            cases.iter().all(|case| check_match(&case.body))
                && otherwise.as_ref().is_none_or(|case| check_match(case))
        }
    }
}
