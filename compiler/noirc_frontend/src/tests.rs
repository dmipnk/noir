#![cfg(test)]

mod aliases;
mod arithmetic_generics;
mod bound_checks;
mod enums;
mod imports;
mod metaprogramming;
mod name_shadowing;
mod references;
mod traits;
mod turbofish;
mod unused_items;
mod visibility;

// XXX: These tests repeat a lot of code
// what we should do is have test cases which are passed to a test harness
// A test harness will allow for more expressive and readable tests
use std::collections::{BTreeMap, HashMap};

use crate::elaborator::{FrontendOptions, UnstableFeature};
use fm::FileId;

use iter_extended::vecmap;
use noirc_errors::{CustomDiagnostic, Location, Span};

use crate::hir::Context;
use crate::hir::def_collector::dc_crate::CompilationError;
use crate::hir::def_map::ModuleData;
use crate::node_interner::{NodeInterner, StmtId};

use crate::hir::def_collector::dc_crate::DefCollector;
use crate::hir::def_map::{CrateDefMap, LocalModuleId};
use crate::hir_def::expr::HirExpression;
use crate::hir_def::stmt::HirStatement;
use crate::monomorphization::ast::Program;
use crate::monomorphization::errors::MonomorphizationError;
use crate::monomorphization::monomorphize;
use crate::parser::{ItemKind, ParserErrorReason};
use crate::token::SecondaryAttribute;
use crate::{ParsedModule, parse_program};
use fm::FileManager;
use noirc_arena::Arena;

pub(crate) fn has_parser_error(errors: &[CompilationError]) -> bool {
    errors.iter().any(|e| matches!(e, CompilationError::ParseError(_)))
}

pub(crate) fn remove_experimental_warnings(errors: &mut Vec<CompilationError>) {
    errors.retain(|error| match error {
        CompilationError::ParseError(error) => {
            !matches!(error.reason(), Some(ParserErrorReason::ExperimentalFeature(..)))
        }
        _ => true,
    });
}

pub(crate) fn get_program(src: &str) -> (ParsedModule, Context, Vec<CompilationError>) {
    let allow_parser_errors = false;
    get_program_with_options(src, allow_parser_errors, FrontendOptions::test_default())
}

pub(crate) fn get_program_using_features(
    src: &str,
    features: &[UnstableFeature],
) -> (ParsedModule, Context<'static, 'static>, Vec<CompilationError>) {
    let allow_parser_errors = false;
    let mut options = FrontendOptions::test_default();
    options.enabled_unstable_features = features;
    get_program_with_options(src, allow_parser_errors, options)
}

/// Compile a program.
///
/// The stdlib is not available for these snippets.
pub(crate) fn get_program_with_options(
    src: &str,
    allow_parser_errors: bool,
    options: FrontendOptions,
) -> (ParsedModule, Context<'static, 'static>, Vec<CompilationError>) {
    let root = std::path::Path::new("/");
    let fm = FileManager::new(root);

    let mut context = Context::new(fm, Default::default());
    context.def_interner.populate_dummy_operator_traits();
    let root_file_id = FileId::dummy();
    let root_crate_id = context.crate_graph.add_crate_root(root_file_id);

    let (program, parser_errors) = parse_program(src, root_file_id);
    let mut errors = vecmap(parser_errors, |e| e.into());
    remove_experimental_warnings(&mut errors);

    if allow_parser_errors || !has_parser_error(&errors) {
        let inner_attributes: Vec<SecondaryAttribute> = program
            .items
            .iter()
            .filter_map(|item| {
                if let ItemKind::InnerAttribute(attribute) = &item.kind {
                    Some(attribute.clone())
                } else {
                    None
                }
            })
            .collect();

        // Allocate a default Module for the root, giving it a ModuleId
        let mut modules: Arena<ModuleData> = Arena::default();
        let location = Location::new(Default::default(), root_file_id);
        let root = modules.insert(ModuleData::new(
            None,
            location,
            Vec::new(),
            inner_attributes.clone(),
            false, // is contract
            false, // is struct
        ));

        let def_map = CrateDefMap {
            root: LocalModuleId(root),
            modules,
            krate: root_crate_id,
            extern_prelude: BTreeMap::new(),
        };

        // Now we want to populate the CrateDefMap using the DefCollector
        errors.extend(DefCollector::collect_crate_and_dependencies(
            def_map,
            &mut context,
            program.clone().into_sorted(),
            root_file_id,
            options,
        ));
    }
    (program, context, errors)
}

pub(crate) fn get_program_errors(src: &str) -> Vec<CompilationError> {
    get_program(src).2
}

fn assert_no_errors(src: &str) {
    let errors = get_program_errors(src);
    if !errors.is_empty() {
        panic!("Expected no errors, got: {:?}; src = {src}", errors);
    }
}

/// Given a source file with annotated errors, like this
///
/// fn main() -> pub i32 {
///                  ^^^ expected i32 because of return type
///     true        
///     ~~~~ bool returned here
/// }
///
/// where:
/// - lines with "^^^" are primary errors
/// - lines with "~~~" are secondary errors
///
/// this method will check that compiling the program without those error markers
/// will produce errors at those locations and with/ those messages.
fn check_errors(src: &str) {
    let allow_parser_errors = false;
    check_errors_with_options(src, allow_parser_errors, FrontendOptions::test_default());
}

fn check_errors_using_features(src: &str, features: &[UnstableFeature]) {
    let allow_parser_errors = false;
    let mut options = FrontendOptions::test_default();
    options.enabled_unstable_features = features;
    check_errors_with_options(src, allow_parser_errors, options);
}

fn check_errors_with_options(src: &str, allow_parser_errors: bool, options: FrontendOptions) {
    let lines = src.lines().collect::<Vec<_>>();

    // Here we'll hold just the lines that are code
    let mut code_lines = Vec::new();
    // Here we'll capture lines that are primary error spans, like:
    //
    //   ^^^ error message
    let mut primary_spans_with_errors: Vec<(Span, String)> = Vec::new();
    // Here we'll capture lines that are secondary error spans, like:
    //
    //   ~~~ error message
    let mut secondary_spans_with_errors: Vec<(Span, String)> = Vec::new();
    // The byte at the start of this line
    let mut byte = 0;
    // The length of the last line, needed to go back to the byte at the beginning of the last line
    let mut last_line_length = 0;
    for line in lines {
        if let Some((span, message)) =
            get_error_line_span_and_message(line, '^', byte, last_line_length)
        {
            primary_spans_with_errors.push((span, message));
            continue;
        }

        if let Some((span, message)) =
            get_error_line_span_and_message(line, '~', byte, last_line_length)
        {
            secondary_spans_with_errors.push((span, message));
            continue;
        }

        code_lines.push(line);

        byte += line.len() + 1; // For '\n'
        last_line_length = line.len();
    }

    let mut primary_spans_with_errors: HashMap<Span, String> =
        primary_spans_with_errors.into_iter().collect();

    let mut secondary_spans_with_errors: HashMap<Span, String> =
        secondary_spans_with_errors.into_iter().collect();

    let src = code_lines.join("\n");
    let (_, _, errors) = get_program_with_options(&src, allow_parser_errors, options);
    if errors.is_empty() && !primary_spans_with_errors.is_empty() {
        panic!("Expected some errors but got none");
    }

    let errors = errors.iter().map(CustomDiagnostic::from).collect::<Vec<_>>();
    for error in &errors {
        let secondary = error
            .secondaries
            .first()
            .unwrap_or_else(|| panic!("Expected {:?} to have a secondary label", error));
        let span = secondary.location.span;
        let message = &error.message;

        let Some(expected_message) = primary_spans_with_errors.remove(&span) else {
            if let Some(message) = secondary_spans_with_errors.get(&span) {
                panic!(
                    "Error at {span:?} with message {message:?} is annotated as secondary but should be primary"
                );
            } else {
                panic!(
                    "Couldn't find primary error at {span:?} with message {message:?}.\nAll errors: {errors:?}"
                );
            }
        };

        assert_eq!(message, &expected_message, "Primary error at {span:?} has unexpected message");

        for secondary in &error.secondaries {
            let message = &secondary.message;
            if message.is_empty() {
                continue;
            }

            let span = secondary.location.span;
            let Some(expected_message) = secondary_spans_with_errors.remove(&span) else {
                if let Some(message) = primary_spans_with_errors.get(&span) {
                    panic!(
                        "Error at {span:?} with message {message:?} is annotated as primary but should be secondary"
                    );
                } else {
                    panic!(
                        "Couldn't find secondary error at {span:?} with message {message:?}.\nAll errors: {errors:?}"
                    );
                };
            };

            assert_eq!(
                message, &expected_message,
                "Secondary error at {span:?} has unexpected message"
            );
        }
    }

    if !primary_spans_with_errors.is_empty() {
        panic!("These primary errors didn't happen: {primary_spans_with_errors:?}");
    }

    if !secondary_spans_with_errors.is_empty() {
        panic!("These secondary errors didn't happen: {secondary_spans_with_errors:?}");
    }
}

/// Helper function for `check_errors` that returns the span that
/// `^^^^` or `~~~~` occupy, together with the message that follows it.
fn get_error_line_span_and_message(
    line: &str,
    char: char,
    byte: usize,
    last_line_length: usize,
) -> Option<(Span, String)> {
    if !line.trim().starts_with(char) {
        return None;
    }

    let chars = line.chars().collect::<Vec<_>>();
    let first_caret = chars.iter().position(|c| *c == char).unwrap();
    let last_caret = chars.iter().rposition(|c| *c == char).unwrap();
    let start = byte - last_line_length;
    let span = Span::from((start + first_caret - 1) as u32..(start + last_caret) as u32);
    let error = line.trim().trim_start_matches(char).trim().to_string();
    Some((span, error))
}

#[test]
fn check_trait_implemented_for_all_t() {
    let src = "
    trait Default {
        fn default() -> Self;
    }

    trait Eq {
        fn eq(self, other: Self) -> bool;
    }

    trait IsDefault {
        fn is_default(self) -> bool;
    }

    impl<T> IsDefault for T where T: Default + Eq {
        fn is_default(self) -> bool {
            self.eq(T::default())
        }
    }

    struct Foo {
        a: u64,
    }

    impl Eq for Foo {
        fn eq(self, other: Foo) -> bool { self.a == other.a }
    }

    impl Default for u64 {
        fn default() -> Self {
            0
        }
    }

    impl Default for Foo {
        fn default() -> Self {
            Foo { a: Default::default() }
        }
    }

    fn main(a: Foo) -> pub bool {
        a.is_default()
    }";
    assert_no_errors(src);
}

#[test]
fn check_trait_implementation_duplicate_method() {
    let src = "
    trait Default {
        fn default(x: Field, y: Field) -> Field;
    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
        // Duplicate trait methods should not compile
        fn default(x: Field, y: Field) -> Field {
           ^^^^^^^ Duplicate definitions of trait associated function with name default found
           ~~~~~~~ First trait associated function found here
            y + 2 * x
        }
        // Duplicate trait methods should not compile
        fn default(x: Field, y: Field) -> Field {
           ~~~~~~~ Second trait associated function found here
            x + 2 * y
        }
    }

    fn main() {
        let _ = Foo { bar: 1, array: [2, 3] }; // silence Foo never constructed warning
    }";
    check_errors(src);
}

#[test]
fn check_trait_wrong_method_return_type() {
    // TODO: improve the error location
    let src = "
    trait Default {
        fn default() -> Self;
    }

    struct Foo {
    }

    impl Default for Foo {
        fn default() -> Field {
           ^^^^^^^ Expected type Foo, found type Field
            0
        }
    }

    fn main() {
        let _ = Foo {}; // silence Foo never constructed warning
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_wrong_method_return_type2() {
    // TODO: improve the error location
    let src = "
    trait Default {
        fn default(x: Field, y: Field) -> Self;
    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
        fn default(x: Field, _y: Field) -> Field {
           ^^^^^^^ Expected type Foo, found type Field
            x
        }
    }

    fn main() {
        let _ = Foo { bar: 1, array: [2, 3] }; // silence Foo never constructed warning
    }";
    check_errors(src);
}

#[test]
fn check_trait_missing_implementation() {
    let src = "
    trait Default {
        fn default(x: Field, y: Field) -> Self;

        fn method2(x: Field) -> Field;

    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
                     ^^^ Method `method2` from trait `Default` is not implemented
                     ~~~ Please implement method2 here
        fn default(x: Field, y: Field) -> Self {
            Self { bar: x, array: [x,y] }
        }
    }

    fn main() {
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_not_in_scope() {
    let src = "
    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
         ^^^^^^^ Trait Default not found
        fn default(x: Field, y: Field) -> Self {
            Self { bar: x, array: [x,y] }
        }
    }

    fn main() {
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_wrong_method_name() {
    let src = "
    trait Default {
    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
        fn does_not_exist(x: Field, y: Field) -> Self {
           ^^^^^^^^^^^^^^ Method with name `does_not_exist` is not part of trait `Default`, therefore it can't be implemented
            Self { bar: x, array: [x,y] }
        }
    }

    fn main() {
        let _ = Foo { bar: 1, array: [2, 3] }; // silence Foo never constructed warning
    }";
    check_errors(src);
}

#[test]
fn check_trait_wrong_parameter() {
    // TODO: improve the error location
    let src = "
    trait Default {
        fn default(x: Field) -> Self;
    }

    struct Foo {
        bar: u32,
    }

    impl Default for Foo {
        fn default(x: u32) -> Self {
                   ^ Parameter #1 of method `default` must be of type Field, not u32
            Foo {bar: x}
        }
    }

    fn main() {
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_wrong_parameter2() {
    let src = "
    trait Default {
        fn default(x: Field, y: Field) -> Self;
    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
        fn default(x: Field, y: Foo) -> Self {
                             ^ Parameter #2 of method `default` must be of type Field, not Foo
            Self { bar: x, array: [x, y.bar] }
        }
    }

    fn main() {
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_wrong_parameter_type() {
    let src = "
    pub trait Default {
        fn default(x: Field, y: NotAType) -> Field;
                                ^^^^^^^^ Could not resolve 'NotAType' in path
    }

    fn main(x: Field, y: Field) {
        assert(y == x);
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_wrong_parameters_count() {
    let src = "
    trait Default {
        fn default(x: Field, y: Field) -> Self;
    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
        fn default(x: Field) -> Self {
           ^^^^^^^ `Default::default` expects 2 parameters, but this method has 1
            Self { bar: x, array: [x, x] }
        }
    }

    fn main() {
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_impl_for_non_type() {
    let src = "
    trait Default {
        fn default(x: Field, y: Field) -> Field;
    }

    impl Default for main {
                     ^^^^ expected type got function
        fn default(x: Field, y: Field) -> Field {
            x + y
        }
    }

    fn main() {}
    ";
    check_errors(src);
}

#[test]
fn check_impl_struct_not_trait() {
    let src = "
    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    struct Default {
        x: Field,
        z: Field,
    }

    impl Default for Foo {
         ^^^^^^^ Default is not a trait, therefore it can't be implemented
        fn default(x: Field, y: Field) -> Self {
            Self { bar: x, array: [x,y] }
        }
    }

    fn main() {
        let _ = Default { x: 1, z: 1 }; // silence Default never constructed warning
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_duplicate_declaration() {
    let src = "
    trait Default {
          ^^^^^^^ Duplicate definitions of trait definition with name Default found
          ~~~~~~~ First trait definition found here
        fn default(x: Field, y: Field) -> Self;
    }

    struct Foo {
        bar: Field,
        array: [Field; 2],
    }

    impl Default for Foo {
        fn default(x: Field,y: Field) -> Self {
            Self { bar: x, array: [x,y] }
        }
    }

    trait Default {
          ~~~~~~~ Second trait definition found here
        fn default(x: Field) -> Self;
    }

    fn main() {
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_duplicate_implementation() {
    let src = "
    trait Default {
    }
    struct Foo {
        bar: Field,
    }

    impl Default for Foo {
         ~~~~~~~ Previous impl defined here
    }
    impl Default for Foo {
                     ^^^ Impl for type `Foo` overlaps with existing impl
                     ~~~ Overlapping impl
    }
    fn main() {
        let _ = Foo { bar: 1 }; // silence Foo never constructed warning
    }
    ";
    check_errors(src);
}

#[test]
fn check_trait_duplicate_implementation_with_alias() {
    let src = "
    trait Default {
    }

    struct MyStruct {
    }

    type MyType = MyStruct;

    impl Default for MyStruct {
         ~~~~~~~ Previous impl defined here
    }

    impl Default for MyType {
                     ^^^^^^ Impl for type `MyType` overlaps with existing impl
                     ~~~~~~ Overlapping impl
    }

    fn main() {
        let _ = MyStruct {}; // silence MyStruct never constructed warning
    }
    ";
    check_errors(src);
}

#[test]
fn test_impl_self_within_default_def() {
    let src = "
    trait Bar {
        fn ok(self) -> Self;

        fn ref_ok(self) -> Self {
            self.ok()
        }
    }

    impl<T> Bar for (T, T) where T: Bar {
        fn ok(self) -> Self {
            self
        }
    }
    ";
    assert_no_errors(src);
}

#[test]
fn check_trait_as_type_as_fn_parameter() {
    let src = "
    trait Eq {
        fn eq(self, other: Self) -> bool;
    }

    struct Foo {
        a: u64,
    }

    impl Eq for Foo {
        fn eq(self, other: Foo) -> bool { self.a == other.a }
    }

    fn test_eq(x: impl Eq) -> bool {
        x.eq(x)
    }

    fn main(a: Foo) -> pub bool {
        test_eq(a)
    }";
    assert_no_errors(src);
}

#[test]
fn check_trait_as_type_as_two_fn_parameters() {
    let src = "
    trait Eq {
        fn eq(self, other: Self) -> bool;
    }

    trait Test {
        fn test(self) -> bool;
    }

    struct Foo {
        a: u64,
    }

    impl Eq for Foo {
        fn eq(self, other: Foo) -> bool { self.a == other.a }
    }

    impl Test for u64 {
        fn test(self) -> bool { self == self }
    }

    fn test_eq(x: impl Eq, y: impl Test) -> bool {
        x.eq(x) == y.test()
    }

    fn main(a: Foo, b: u64) -> pub bool {
        test_eq(a, b)
    }";
    assert_no_errors(src);
}

fn get_program_captures(src: &str) -> Vec<Vec<String>> {
    let (program, context, _errors) = get_program(src);
    let interner = context.def_interner;
    let mut all_captures: Vec<Vec<String>> = Vec::new();
    for func in program.into_sorted().functions {
        let func_id = interner.find_function(func.item.name()).unwrap();
        let hir_func = interner.function(&func_id);
        // Iterate over function statements and apply filtering function
        find_lambda_captures(hir_func.block(&interner).statements(), &interner, &mut all_captures);
    }
    all_captures
}

fn find_lambda_captures(stmts: &[StmtId], interner: &NodeInterner, result: &mut Vec<Vec<String>>) {
    for stmt_id in stmts.iter() {
        let hir_stmt = interner.statement(stmt_id);
        let expr_id = match hir_stmt {
            HirStatement::Expression(expr_id) => expr_id,
            HirStatement::Let(let_stmt) => let_stmt.expression,
            HirStatement::Assign(assign_stmt) => assign_stmt.expression,
            HirStatement::Semi(semi_expr) => semi_expr,
            HirStatement::For(for_loop) => for_loop.block,
            HirStatement::Loop(block) => block,
            HirStatement::While(_, block) => block,
            HirStatement::Error => panic!("Invalid HirStatement!"),
            HirStatement::Break => panic!("Unexpected break"),
            HirStatement::Continue => panic!("Unexpected continue"),
            HirStatement::Comptime(_) => panic!("Unexpected comptime"),
        };
        let expr = interner.expression(&expr_id);

        get_lambda_captures(expr, interner, result); // TODO: dyn filter function as parameter
    }
}

fn get_lambda_captures(
    expr: HirExpression,
    interner: &NodeInterner,
    result: &mut Vec<Vec<String>>,
) {
    if let HirExpression::Lambda(lambda_expr) = expr {
        let mut cur_capture = Vec::new();

        for capture in lambda_expr.captures.iter() {
            cur_capture.push(interner.definition(capture.ident.id).name.clone());
        }
        result.push(cur_capture);

        // Check for other captures recursively within the lambda body
        let hir_body_expr = interner.expression(&lambda_expr.body);
        if let HirExpression::Block(block_expr) = hir_body_expr {
            find_lambda_captures(block_expr.statements(), interner, result);
        }
    }
}

#[test]
fn resolve_empty_function() {
    let src = "
        fn main() {

        }
    ";
    assert_no_errors(src);
}

#[test]
fn resolve_basic_function() {
    let src = r#"
        fn main(x : Field) {
            let y = x + x;
            assert(y == x);
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_unused_var() {
    let src = r#"
        fn main(x : Field) {
            let y = x + x;
                ^ unused variable y
                ~ unused variable
            assert(x == x);
        }
    "#;
    check_errors(src);
}

#[test]
fn resolve_unresolved_var() {
    let src = r#"
        fn main(x : Field) {
            let y = x + x;
            assert(y == z);
                        ^ cannot find `z` in this scope
                        ~ not found in this scope
        }
    "#;
    check_errors(src);
}

#[test]
fn unresolved_path() {
    let src = "
        fn main(x : Field) {
            let _z = some::path::to::a::func(x);
                     ^^^^ Could not resolve 'some' in path
        }
    ";
    check_errors(src);
}

#[test]
fn resolve_literal_expr() {
    let src = r#"
        fn main(x : Field) {
            let y = 5;
            assert(y == x);
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn multiple_resolution_errors() {
    let src = r#"
        fn main(x : Field) {
           let y = foo::bar(x);
                   ^^^ Could not resolve 'foo' in path
           let z = y + a;
                       ^ cannot find `a` in this scope
                       ~ not found in this scope
               ^ unused variable z
               ~ unused variable
                       
        }
    "#;
    check_errors(src);
}

#[test]
fn resolve_prefix_expr() {
    let src = r#"
        fn main(x : Field) {
            let _y = -x;
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_for_expr() {
    let src = r#"
        fn main(x : u64) {
            for i in 1..20 {
                let _z = x + i;
            };
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_for_expr_incl() {
    let src = r#"
        fn main(x : u64) {
            for i in 1..=20 {
                let _z = x + i;
            };
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_call_expr() {
    let src = r#"
        fn main(x : Field) {
            let _z = foo(x);
        }

        fn foo(x : Field) -> Field {
            x
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_shadowing() {
    let src = r#"
        fn main(x : Field) {
            let x = foo(x);
            let x = x;
            let (x, x) = (x, x);
            let _ = x;
        }

        fn foo(x : Field) -> Field {
            x
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_basic_closure() {
    let src = r#"
        fn main(x : Field) -> pub Field {
            let closure = |y| y + x;
            closure(x)
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn resolve_simplified_closure() {
    // based on bug https://github.com/noir-lang/noir/issues/1088
    let src = r#"
      fn do_closure(x: Field) -> Field {
        let y = x;
        let ret_capture = || {
          y
        };
        ret_capture()
      }

      fn main(x: Field) {
          assert(do_closure(x) == 100);
      }

      "#;
    let parsed_captures = get_program_captures(src);
    let expected_captures = vec![vec!["y".to_string()]];
    assert_eq!(expected_captures, parsed_captures);
}

#[test]
fn resolve_complex_closures() {
    let src = r#"
        fn main(x: Field) -> pub Field {
            let closure_without_captures = |x: Field| -> Field { x + x };
            let a = closure_without_captures(1);

            let closure_capturing_a_param = |y: Field| -> Field { y + x };
            let b = closure_capturing_a_param(2);

            let closure_capturing_a_local_var = |y: Field| -> Field { y + b };
            let c = closure_capturing_a_local_var(3);

            let closure_with_transitive_captures = |y: Field| -> Field {
                let d = 5;
                let nested_closure = |z: Field| -> Field {
                    let doubly_nested_closure = |w: Field| -> Field { w + x + b };
                    a + z + y + d + x + doubly_nested_closure(4) + x + y
                };
                let res = nested_closure(5);
                res
            };

            a + b + c + closure_with_transitive_captures(6)
        }
    "#;
    assert_no_errors(src);

    let expected_captures = vec![
        vec![],
        vec!["x".to_string()],
        vec!["b".to_string()],
        vec!["x".to_string(), "b".to_string(), "a".to_string()],
        vec!["x".to_string(), "b".to_string(), "a".to_string(), "y".to_string(), "d".to_string()],
        vec!["x".to_string(), "b".to_string()],
    ];

    let parsed_captures = get_program_captures(src);

    assert_eq!(expected_captures, parsed_captures);
}

#[test]
fn resolve_fmt_strings() {
    let src = r#"
        fn main() {
            let string = f"this is i: {i}";
                                       ^ cannot find `i` in this scope
                                       ~ not found in this scope
            println(string);
            ^^^^^^^^^^^^^^^ Unused expression result of type fmtstr<14, ()>

            let new_val = 10;
            println(f"random_string{new_val}{new_val}");
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Unused expression result of type fmtstr<31, (Field, Field)>
        }
        fn println<T>(x : T) -> T {
            x
        }
    "#;
    check_errors(src);
}

fn monomorphize_program(src: &str) -> Result<Program, MonomorphizationError> {
    let (_program, mut context, _errors) = get_program(src);
    let main_func_id = context.def_interner.find_function("main").unwrap();
    monomorphize(main_func_id, &mut context.def_interner, false)
}

fn get_monomorphization_error(src: &str) -> Option<MonomorphizationError> {
    monomorphize_program(src).err()
}

fn check_rewrite(src: &str, expected: &str) {
    let program = monomorphize_program(src).unwrap();
    assert!(format!("{}", program) == expected);
}

#[test]
fn simple_closure_with_no_captured_variables() {
    let src = r#"
    fn main() -> pub Field {
        let x = 1;
        let closure = || x;
        closure()
    }
    "#;

    let expected_rewrite = r#"fn main$f0() -> Field {
    let x$0 = 1;
    let closure$3 = {
        let closure_variable$2 = {
            let env$1 = (x$l0);
            (env$l1, lambda$f1)
        };
        closure_variable$l2
    };
    {
        let tmp$4 = closure$l3;
        tmp$l4.1(tmp$l4.0)
    }
}
fn lambda$f1(mut env$l1: (Field)) -> Field {
    env$l1.0
}
"#;
    check_rewrite(src, expected_rewrite);
}

#[test]
fn deny_cyclic_globals() {
    let src = r#"
        global A: u32 = B;
                        ^ This global recursively depends on itself
               ^ Dependency cycle found
               ~ 'A' recursively depends on itself: A -> B -> A
        global B: u32 = A;
                        ^ Variable not in scope
                        ~ Could not find variable

        fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn deny_cyclic_type_aliases() {
    let src = r#"
        type A = B;
        type B = A;
        ^^^^^^^^^^ Dependency cycle found
        ~~~~~~~~~~ 'B' recursively depends on itself: B -> A -> B
        fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn ensure_nested_type_aliases_type_check() {
    let src = r#"
        type A = B;
        type B = u8;
        fn main() {
            let _a: A = 0 as u16;
                        ^^^^^^^^ Expected type A, found type u16
        }
    "#;
    check_errors(src);
}

#[test]
fn type_aliases_in_entry_point() {
    let src = r#"
        type Foo = u8;
        fn main(_x: Foo) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn operators_in_global_used_in_type() {
    let src = r#"
        global ONE: u32 = 1;
        global COUNT: u32 = ONE + 2;
        fn main() {
            let _array: [Field; COUNT] = [1, 2, 3];
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn break_and_continue_in_constrained_fn() {
    let src = r#"
        fn main() {
            for i in 0 .. 10 {
                if i == 2 {
                    continue;
                    ^^^^^^^^^ continue is only allowed in unconstrained functions
                    ~~~~~~~~~ Constrained code must always have a known number of loop iterations
                }
                if i == 5 {
                    break;
                    ^^^^^^ break is only allowed in unconstrained functions
                    ~~~~~~ Constrained code must always have a known number of loop iterations
                }
            }
        }
    "#;
    check_errors(src);
}

#[test]
fn break_and_continue_outside_loop() {
    let src = r#"
        unconstrained fn main() {
            continue;
            ^^^^^^^^^ continue is only allowed within loops
            break;
            ^^^^^^ break is only allowed within loops
        }
    "#;
    check_errors(src);
}

// Regression for #2540
#[test]
fn for_loop_over_array() {
    let src = r#"
        fn hello<let N: u32>(_array: [u1; N]) {
            for _ in 0..N {}
        }

        fn main() {
            let array: [u1; 2] = [0, 1];
            hello(array);
        }
    "#;
    assert_no_errors(src);
}

// Regression for #4545
#[test]
fn type_aliases_in_main() {
    let src = r#"
        type Outer<let N: u32> = [u8; N];
        fn main(_arg: Outer<1>) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn ban_mutable_globals() {
    let src = r#"
        mut global FOO: Field = 0;
                   ^^^ Only `comptime` globals may be mutable
        fn main() {
            let _ = FOO; // silence FOO never used warning
        }
    "#;
    check_errors(src);
}

#[test]
fn deny_inline_attribute_on_unconstrained() {
    // TODO: improve the error location
    let src = r#"
        #[no_predicates]
        unconstrained pub fn foo(x: Field, y: Field) {
                             ^^^ misplaced #[no_predicates] attribute on unconstrained function foo. Only allowed on constrained functions
                             ~~~ misplaced #[no_predicates] attribute
            assert(x != y);
        }
    "#;
    check_errors(src);
}

#[test]
fn deny_fold_attribute_on_unconstrained() {
    // TODO: improve the error location
    let src = r#"
        #[fold]
        unconstrained pub fn foo(x: Field, y: Field) {
                             ^^^ misplaced #[fold] attribute on unconstrained function foo. Only allowed on constrained functions
                             ~~~ misplaced #[fold] attribute
            assert(x != y);
        }
    "#;
    check_errors(src);
}

#[test]
fn specify_function_types_with_turbofish() {
    let src = r#"
        trait Default {
            fn default() -> Self;
        }

        impl Default for Field {
            fn default() -> Self { 0 }
        }

        impl Default for u64 {
            fn default() -> Self { 0 }
        }

        // Need the above as we don't have access to the stdlib here.
        // We also need to construct a concrete value of `U` without giving away its type
        // as otherwise the unspecified type is ignored.

        fn generic_func<T, U>() -> (T, U) where T: Default, U: Default {
            (T::default(), U::default())
        }

        fn main() {
            let _ = generic_func::<u64, Field>();
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn specify_method_types_with_turbofish() {
    let src = r#"
        trait Default {
            fn default() -> Self;
        }

        impl Default for Field {
            fn default() -> Self { 0 }
        }

        // Need the above as we don't have access to the stdlib here.
        // We also need to construct a concrete value of `U` without giving away its type
        // as otherwise the unspecified type is ignored.

        struct Foo<T> {
            inner: T
        }

        impl<T> Foo<T> {
            fn generic_method<U>(_self: Self) -> U where U: Default {
                U::default()
            }
        }

        fn main() {
            let foo: Foo<Field> = Foo { inner: 1 };
            let _ = foo.generic_method::<Field>();
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn incorrect_turbofish_count_function_call() {
    let src = r#"
        trait Default {
            fn default() -> Self;
        }

        impl Default for Field {
            fn default() -> Self { 0 }
        }

        impl Default for u64 {
            fn default() -> Self { 0 }
        }

        // Need the above as we don't have access to the stdlib here.
        // We also need to construct a concrete value of `U` without giving away its type
        // as otherwise the unspecified type is ignored.

        fn generic_func<T, U>() -> (T, U) where T: Default, U: Default {
            (T::default(), U::default())
        }

        fn main() {
            let _ = generic_func::<u64, Field, Field>();
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Expected 2 generics from this function, but 3 were provided
        }
    "#;
    check_errors(src);
}

#[test]
fn incorrect_turbofish_count_method_call() {
    let src = r#"
        trait Default {
            fn default() -> Self;
        }

        impl Default for Field {
            fn default() -> Self { 0 }
        }

        // Need the above as we don't have access to the stdlib here.
        // We also need to construct a concrete value of `U` without giving away its type
        // as otherwise the unspecified type is ignored.

        struct Foo<T> {
            inner: T
        }

        impl<T> Foo<T> {
            fn generic_method<U>(_self: Self) -> U where U: Default {
                U::default()
            }
        }

        fn main() {
            let foo: Foo<Field> = Foo { inner: 1 };
            let _ = foo.generic_method::<Field, u32>();
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Expected 1 generic from this function, but 2 were provided
        }
    "#;
    check_errors(src);
}

#[test]
fn struct_numeric_generic_in_function() {
    let src = r#"
    struct Foo {
        inner: u64
    }

    pub fn bar<let N: Foo>() {
                   ^ N has a type of Foo. The only supported numeric generic types are `u1`, `u8`, `u16`, and `u32`.
                   ~ Unsupported numeric generic type
        let _ = Foo { inner: 1 }; // silence Foo never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn struct_numeric_generic_in_struct() {
    let src = r#"
    pub struct Foo {
        inner: u64
    }

    pub struct Bar<let N: Foo> { }
                       ^ N has a type of Foo. The only supported numeric generic types are `u1`, `u8`, `u16`, and `u32`.
                       ~ Unsupported numeric generic type
    "#;
    check_errors(src);
}

#[test]
fn bool_numeric_generic() {
    let src = r#"
    pub fn read<let N: bool>() -> Field {
                    ^ N has a type of bool. The only supported numeric generic types are `u1`, `u8`, `u16`, and `u32`.
                    ~ Unsupported numeric generic type
        if N {
            0
        } else {
            1
        }
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_binary_operation_type_mismatch() {
    let src = r#"
    pub fn foo<let N: Field>() -> bool {
        let mut check: bool = true;
        check = N;
                ^ Cannot assign an expression of type Field to a value of type bool
        check
    }
    "#;
    check_errors(src);
}

#[test]
fn bool_generic_as_loop_bound() {
    // TODO: improve the error location of the last error (should be just on N)
    let src = r#"
    pub fn read<let N: bool>() {
                    ^ N has a type of bool. The only supported numeric generic types are `u1`, `u8`, `u16`, and `u32`.
                    ~ Unsupported numeric generic type
        let mut fields = [0; N];
                             ^ Expected kind numeric u32, found kind numeric bool
        for i in 0..N { 
                 ^^^^ Expected type Field, found type bool
            fields[i] = i + 1;
        }
        assert(fields[0] == 1);
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_in_function_signature() {
    let src = r#"
    pub fn foo<let N: u32>(arr: [Field; N]) -> [Field; N] { arr }
    "#;
    assert_no_errors(src);
}

#[test]
fn numeric_generic_as_struct_field_type_fails() {
    // TODO: improve error message, in Rust it says "expected type, found const parameter `N`"
    // which might be more understandable
    let src = r#"
    pub struct Foo<let N: u32> {
        a: Field,
        b: N,
           ^ Expected kind normal, found kind numeric u32
    }
    "#;
    check_errors(src);
}

#[test]
fn normal_generic_as_array_length() {
    // TODO: improve error location, should be just on N
    let src = r#"
    pub struct Foo<N> {
        a: Field,
        b: [Field; N],
           ^^^^^^^^^^ Expected kind numeric u32, found kind normal
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_as_param_type() {
    // TODO: improve the error message, see what Rust does
    let src = r#"
    pub fn foo<let I: u32>(x: I) -> I {
                              ^ Expected kind normal, found kind numeric u32
                                    ^ Expected kind normal, found kind numeric u32
        let _q: I = 5;
                ^ Expected kind normal, found kind numeric u32
        x
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_as_unused_param_type() {
    // TODO: improve the error message
    let src = r#"
    pub fn foo<let I: u32>(_x: I) { }
                               ^ Expected kind normal, found kind numeric u32
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_as_unused_trait_fn_param_type() {
    // TODO: improve the error message
    let src = r#"
    trait Foo {
          ^^^ unused trait Foo
          ~~~ unused trait
        fn foo<let I: u32>(_x: I) { }
                               ^ Expected kind normal, found kind numeric u32
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_as_return_type() {
    // TODO: improve the error message
    let src = r#"
    // std::mem::zeroed() without stdlib
    trait Zeroed {
        fn zeroed<T>(self) -> T;
    }

    fn foo<T, let I: Field>(x: T) -> I where T: Zeroed {
                                     ^ Expected kind normal, found kind numeric Field
       ^^^ unused function foo
       ~~~ unused function
        x.zeroed()
    }

    fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_used_in_nested_type_fails() {
    // TODO: improve the error message
    let src = r#"
    pub struct Foo<let N: u32> {
        a: Field,
        b: Bar<N>,
    }
    pub struct Bar<let N: u32> {
        inner: N
               ^ Expected kind normal, found kind numeric u32
    }
    "#;
    check_errors(src);
}

#[test]
fn normal_generic_used_in_nested_array_length_fail() {
    // TODO: improve the error message
    let src = r#"
    pub struct Foo<N> {
        a: Field,
        b: Bar<N>,
               ^ Expected kind numeric u32, found kind normal
    }
    pub struct Bar<let N: u32> {
        inner: [Field; N]
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_used_in_nested_type_pass() {
    // The order of these structs should not be changed to make sure
    // that we are accurately resolving all struct generics before struct fields
    let src = r#"
    pub struct NestedNumeric<let N: u32> {
        a: Field,
        b: InnerNumeric<N>
    }
    pub struct InnerNumeric<let N: u32> {
        inner: [u64; N],
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn numeric_generic_used_in_trait() {
    // We want to make sure that `N` in `impl<let N: u32, T> Deserialize<N, T>` does
    // not trigger `expected type, found numeric generic parameter N` as the trait
    // does in fact expect a numeric generic.
    let src = r#"
    struct MyType<T> {
        a: Field,
        b: Field,
        c: Field,
        d: T,
    }

    impl<let N: u32, T> Deserialize<N, T> for MyType<T> {
        fn deserialize(fields: [Field; N], other: T) -> Self {
            MyType { a: fields[0], b: fields[1], c: fields[2], d: other }
        }
    }

    trait Deserialize<let N: u32, T> {
        fn deserialize(fields: [Field; N], other: T) -> Self;
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn numeric_generic_in_trait_impl_with_extra_impl_generics() {
    let src = r#"
    trait Default {
        fn default() -> Self;
    }

    struct MyType<T> {
        a: Field,
        b: Field,
        c: Field,
        d: T,
    }

    // Make sure that `T` is placed before `N` as we want to test that the order of the generics is correctly maintained.
    // `N` is used first in the trait impl generics (`Deserialize<N> for MyType<T>`).
    // We want to make sure that the compiler correctly accounts for that `N` has a numeric kind
    // while `T` has a normal kind.
    impl<T, let N: u32> Deserialize<N> for MyType<T> where T: Default {
        fn deserialize(fields: [Field; N]) -> Self {
            MyType { a: fields[0], b: fields[1], c: fields[2], d: T::default() }
        }
    }

    trait Deserialize<let N: u32> {
        fn deserialize(fields: [Field; N]) -> Self;
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn numeric_generic_used_in_where_clause() {
    let src = r#"
    trait Deserialize<let N: u32> {
        fn deserialize(fields: [Field; N]) -> Self;
    }

    pub fn read<T, let N: u32>() -> T where T: Deserialize<N> {
        let mut fields: [Field; N] = [0; N];
        for i in 0..N {
            fields[i] = i as Field + 1;
        }
        T::deserialize(fields)
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn numeric_generic_used_in_turbofish() {
    let src = r#"
    pub fn double<let N: u32>() -> u32 {
        // Used as an expression
        N * 2
    }

    pub fn double_numeric_generics_test() {
        // Example usage of a numeric generic arguments.
        assert(double::<9>() == 18);
        assert(double::<7 + 8>() == 30);
    }
    "#;
    assert_no_errors(src);
}

// TODO(https://github.com/noir-lang/noir/issues/6245):
// allow u16 to be used as an array size
#[test]
fn numeric_generic_u16_array_size() {
    // TODO: improve the error location (and maybe the message)
    let src = r#"
    fn len<let N: u32>(_arr: [Field; N]) -> u32 {
        N
    }

    pub fn foo<let N: u16>() -> u32 {
        let fields: [Field; N] = [0; N];
                    ^^^^^^^^^^ Expected kind numeric u32, found kind numeric u16
                                     ^ Expected kind numeric u32, found kind numeric u16
        len(fields)
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generic_field_larger_than_u32() {
    let src = r#"
        global A: Field = 4294967297;

        fn foo<let A: Field>() { }

        fn main() {
            let _ = foo::<A>();
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn numeric_generic_field_arithmetic_larger_than_u32() {
    let src = r#"
        struct Foo<let F: Field> {}

        fn size<let F: Field>(_x: Foo<F>) -> Field {
            F
        }

        // 2^32 - 1
        global A: Field = 4294967295;

        fn foo<let A: Field>() -> Foo<A + A> {
            Foo {}
        }

        fn main() {
            let _ = size(foo::<A>());
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn cast_256_to_u8_size_checks() {
    let src = r#"
        fn main() {
            assert(256 as u8 == 0);
                   ^^^^^^^^^ Casting value of type Field to a smaller type (u8)
                   ~~~~~~~~~ casting untyped value (256) to a type with a maximum size (255) that's smaller than it
        }
    "#;
    check_errors(src);
}

// TODO(https://github.com/noir-lang/noir/issues/6247):
// add negative integer literal checks
#[test]
fn cast_negative_one_to_u8_size_checks() {
    let src = r#"
        fn main() {
            assert((-1) as u8 != 0);
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn constant_used_with_numeric_generic() {
    let src = r#"
    struct ValueNote {
        value: Field,
    }

    trait Serialize<let N: u32> {
        fn serialize(self) -> [Field; N];
    }

    impl Serialize<1> for ValueNote {
        fn serialize(self) -> [Field; 1] {
            [self.value]
        }
    }

    fn main() {
        let _ = ValueNote { value: 1 }; // silence ValueNote never constructed warning
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn normal_generic_used_when_numeric_expected_in_where_clause() {
    let src = r#"
    trait Deserialize<let N: u32> {
        fn deserialize(fields: [Field; N]) -> Self;
    }

    pub fn read<T, N>() -> T where T: Deserialize<N> {
                                                  ^ Expected kind numeric u32, found kind normal
        T::deserialize([0, 1])
    }
    "#;
    check_errors(src);

    // TODO: improve the error location for the array (should be on N)
    let src = r#"
    trait Deserialize<let N: u32> {
        fn deserialize(fields: [Field; N]) -> Self;
    }

    pub fn read<T, N>() -> T where T: Deserialize<N> {
                                                  ^ Expected kind numeric u32, found kind normal
        let mut fields: [Field; N] = [0; N];
                                         ^ Expected kind numeric u32, found kind normal
                        ^^^^^^^^^^ Expected kind numeric u32, found kind normal
        for i in 0..N {
                    ^ cannot find `N` in this scope
                    ~ not found in this scope
            fields[i] = i as Field + 1;
        }
        T::deserialize(fields)
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generics_type_kind_mismatch() {
    let src = r#"
    fn foo<let N: u32>() -> u16 {
        N as u16
    }

    global J: u16 = 10;

    fn bar<let N: u16>() -> u16 {
        foo::<J>()
              ^ Expected kind numeric u32, found kind numeric u16
    }

    global M: u16 = 3;

    fn main() {
        let _ = bar::<M>();
    }
    "#;
    check_errors(src);
}

#[test]
fn numeric_generics_value_kind_mismatch_u32_u64() {
    let src = r#"
    struct BoundedVec<T, let MaxLen: u32> {
        storage: [T; MaxLen],
        // can't be compared to MaxLen: u32
        // can't be used to index self.storage
        len: u64,
    }

    impl<T, let MaxLen: u32> BoundedVec<T, MaxLen> {
        pub fn extend_from_bounded_vec<let Len: u32>(&mut self, _vec: BoundedVec<T, Len>) {
            // We do this to avoid an unused variable warning on `self`
            let _ = self.len;
            for _ in 0..Len { }
        }

        pub fn push(&mut self, elem: T) {
            assert(self.len < MaxLen, "push out of bounds");
                   ^^^^^^^^^^^^^^^^^ Integers must have the same bit width LHS is 64, RHS is 32
            self.storage[self.len] = elem;
            self.len += 1;
        }
    }

    fn main() {
        let _ = BoundedVec { storage: [1], len: 1 }; // silence never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn quote_code_fragments() {
    // TODO: have the error also point to `contact!` as a secondary
    // This test ensures we can quote (and unquote/splice) code fragments
    // which by themselves are not valid code. They only need to be valid
    // by the time they are unquoted into the macro's call site.
    let src = r#"
        fn main() {
            comptime {
                concat!(quote { assert( }, quote { false); });
                                                   ^^^^^ Assertion failed
            }
        }

        comptime fn concat(a: Quoted, b: Quoted) -> Quoted {
            quote { $a $b }
        }
    "#;
    check_errors(src);
}

#[test]
fn impl_stricter_than_trait_no_trait_method_constraints() {
    // This test ensures that the error we get from the where clause on the trait impl method
    // is a `DefCollectorErrorKind::ImplIsStricterThanTrait` error.
    let src = r#"
    trait Serialize<let N: u32> {
        // We want to make sure we trigger the error when override a trait method
        // which itself has no trait constraints.
        fn serialize(self) -> [Field; N];
           ~~~~~~~~~ definition of `serialize` from trait
    }

    trait ToField {
        fn to_field(self) -> Field;
    }

    fn process_array<let N: u32>(array: [Field; N]) -> Field {
        array[0]
    }

    fn serialize_thing<A, let N: u32>(thing: A) -> [Field; N] where A: Serialize<N> {
        thing.serialize()
    }

    struct MyType<T> {
        a: T,
        b: T,
    }

    impl<T> Serialize<2> for MyType<T> {
        fn serialize(self) -> [Field; 2] where T: ToField {
                                                  ^^^^^^^ impl has stricter requirements than trait
                                                  ~~~~~~~ impl has extra requirement `T: ToField`
            [ self.a.to_field(), self.b.to_field() ]
        }
    }

    impl<T> MyType<T> {
        fn do_thing_with_serialization_with_extra_steps(self) -> Field {
            process_array(serialize_thing(self))
        }
    }

    fn main() {
        let _ = MyType { a: 1, b: 1 }; // silence MyType never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn impl_stricter_than_trait_different_generics() {
    let src = r#"
    trait Default { }

    // Object type of the trait constraint differs
    trait Foo<T> {
        fn foo_good<U>() where T: Default;

        fn foo_bad<U>() where T: Default;
           ~~~~~~~ definition of `foo_bad` from trait
    }

    impl<A> Foo<A> for () {
        fn foo_good<B>() where A: Default {}

        fn foo_bad<B>() where B: Default {}
                                 ^^^^^^^ impl has stricter requirements than trait
                                 ~~~~~~~ impl has extra requirement `B: Default`
    }
    "#;
    check_errors(src);
}

#[test]
fn impl_stricter_than_trait_different_object_generics() {
    let src = r#"
    trait MyTrait { }

    trait OtherTrait {}

    struct Option<T> {
        inner: T
    }

    struct OtherOption<T> {
        inner: Option<T>,
    }

    trait Bar<T> {
        fn bar_good<U>() where Option<T>: MyTrait, OtherOption<Option<T>>: OtherTrait;

        fn bar_bad<U>() where Option<T>: MyTrait, OtherOption<Option<T>>: OtherTrait;
           ~~~~~~~ definition of `bar_bad` from trait

        fn array_good<U>() where [T; 8]: MyTrait;

        fn array_bad<U>() where [T; 8]: MyTrait;
           ~~~~~~~~~ definition of `array_bad` from trait

        fn tuple_good<U>() where (Option<T>, Option<U>): MyTrait;

        fn tuple_bad<U>() where (Option<T>, Option<U>): MyTrait;
           ~~~~~~~~~ definition of `tuple_bad` from trait
    }

    impl<A> Bar<A> for () {
        fn bar_good<B>()
        where
            OtherOption<Option<A>>: OtherTrait,
            Option<A>: MyTrait { }

        fn bar_bad<B>()
        where
            OtherOption<Option<A>>: OtherTrait,
            Option<B>: MyTrait { }
                       ^^^^^^^ impl has stricter requirements than trait
                       ~~~~~~~ impl has extra requirement `Option<B>: MyTrait`

        fn array_good<B>() where [A; 8]: MyTrait { }

        fn array_bad<B>() where [B; 8]: MyTrait { }
                                        ^^^^^^^ impl has stricter requirements than trait
                                        ~~~~~~~ impl has extra requirement `[B; 8]: MyTrait`

        fn tuple_good<B>() where (Option<A>, Option<B>): MyTrait { }

        fn tuple_bad<B>() where (Option<B>, Option<A>): MyTrait { }
                                                        ^^^^^^^ impl has stricter requirements than trait
                                                        ~~~~~~~ impl has extra requirement `(Option<B>, Option<A>): MyTrait`
    }

    fn main() {
        let _ = OtherOption { inner: Option { inner: 1 } }; // silence unused warnings
    }
    "#;
    check_errors(src);
}

#[test]
fn impl_stricter_than_trait_different_trait() {
    let src = r#"
    trait Default { }

    trait OtherDefault { }

    struct Option<T> {
        inner: T
    }

    trait Bar<T> {
        fn bar<U>() where Option<T>: Default;
           ~~~ definition of `bar` from trait
    }

    impl<A> Bar<A> for () {
        // Trait constraint differs due to the trait even though the constraint
        // types are the same.
        fn bar<B>() where Option<A>: OtherDefault {}
                                     ^^^^^^^^^^^^ impl has stricter requirements than trait
                                     ~~~~~~~~~~~~ impl has extra requirement `Option<A>: OtherDefault`
    }

    fn main() {
        let _ = Option { inner: 1 }; // silence Option never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn trait_impl_where_clause_stricter_pass() {
    let src = r#"
    trait MyTrait {
        fn good_foo<T, H>() where H: OtherTrait;

        fn bad_foo<T, H>() where H: OtherTrait;
           ~~~~~~~ definition of `bad_foo` from trait
    }

    trait OtherTrait {}

    struct Option<T> {
        inner: T
    }

    impl<T> MyTrait for [T] where Option<T>: MyTrait {
        fn good_foo<A, B>() where B: OtherTrait { }

        fn bad_foo<A, B>() where A: OtherTrait { }
                                    ^^^^^^^^^^ impl has stricter requirements than trait
                                    ~~~~~~~~~~ impl has extra requirement `A: OtherTrait`
    }

    fn main() {
        let _ = Option { inner: 1 }; // silence Option never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn impl_stricter_than_trait_different_trait_generics() {
    let src = r#"
    trait Foo<T> {
        fn foo<U>() where T: T2<T>;
           ~~~ definition of `foo` from trait
    }

    impl<A> Foo<A> for () {
        // Should be A: T2<A>
        fn foo<B>() where A: T2<B> {}
                             ^^ impl has stricter requirements than trait
                             ~~ impl has extra requirement `A: T2<B>`
    }

    trait T2<C> {}
    "#;
    check_errors(src);
}

#[test]
fn impl_not_found_for_inner_impl() {
    // We want to guarantee that we get a no impl found error
    let src = r#"
    trait Serialize<let N: u32> {
        fn serialize(self) -> [Field; N];
    }

    trait ToField {
        fn to_field(self) -> Field;
    }

    fn process_array<let N: u32>(array: [Field; N]) -> Field {
        array[0]
    }

    fn serialize_thing<A, let N: u32>(thing: A) -> [Field; N] where A: Serialize<N> {
        thing.serialize()
    }

    struct MyType<T> {
        a: T,
        b: T,
    }

    impl<T> Serialize<2> for MyType<T> where T: ToField {
        fn serialize(self) -> [Field; 2] {
            [ self.a.to_field(), self.b.to_field() ]
        }
    }

    impl<T> MyType<T> {
        fn do_thing_with_serialization_with_extra_steps(self) -> Field {
            process_array(serialize_thing(self))
                          ^^^^^^^^^^^^^^^ No matching impl found for `T: ToField`
                          ~~~~~~~~~~~~~~~ No impl for `T: ToField`
        }
    }

    fn main() {
        let _ = MyType { a: 1, b: 1 }; // silence MyType never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn cannot_call_unconstrained_function_outside_of_unsafe() {
    let src = r#"
    fn main() {
        foo();
        ^^^^^ Call to unconstrained function is unsafe and must be in an unconstrained function or unsafe block
    }

    unconstrained fn foo() {}
    "#;
    check_errors(src);
}

#[test]
fn cannot_call_unconstrained_first_class_function_outside_of_unsafe() {
    let src = r#"
    fn main() {
        let func = foo;
        func();
        ^^^^^^ Call to unconstrained function is unsafe and must be in an unconstrained function or unsafe block
        inner(func);
    }

    fn inner(x: unconstrained fn() -> ()) {
        x();
        ^^^ Call to unconstrained function is unsafe and must be in an unconstrained function or unsafe block
    }

    unconstrained fn foo() {}
    "#;
    check_errors(src);
}

#[test]
fn missing_unsafe_block_when_needing_type_annotations() {
    // This test is a regression check that even when an unsafe block is missing
    // that we still appropriately continue type checking and infer type annotations.
    let src = r#"
    fn main() {
        let z = BigNum { limbs: [2, 0, 0] };
        assert(z.__is_zero() == false);
    }

    struct BigNum<let N: u32> {
        limbs: [u64; N],
    }

    impl<let N: u32> BigNum<N> {
        unconstrained fn __is_zero_impl(self) -> bool {
            let mut result: bool = true;
            for i in 0..N {
                result = result & (self.limbs[i] == 0);
            }
            result
        }
    }

    trait BigNumTrait {
        fn __is_zero(self) -> bool;
    }

    impl<let N: u32> BigNumTrait for BigNum<N> {
        fn __is_zero(self) -> bool {
            self.__is_zero_impl()
            ^^^^^^^^^^^^^^^^^^^ Call to unconstrained function is unsafe and must be in an unconstrained function or unsafe block
        }
    }
    "#;
    check_errors(src);
}

#[test]
fn cannot_pass_unconstrained_function_to_regular_function() {
    let src = r#"
    fn main() {
        let func = foo;
        expect_regular(func);
                       ^^^^ Converting an unconstrained fn to a non-unconstrained fn is unsafe
    }

    unconstrained fn foo() {}

    fn expect_regular(_func: fn() -> ()) {
    }
    "#;
    check_errors(src);
}

#[test]
fn cannot_assign_unconstrained_and_regular_fn_to_variable() {
    let src = r#"
    fn main() {
        let _func = if true { foo } else { bar };
                                           ^^^ Expected type fn() -> (), found type unconstrained fn() -> ()
    }

    fn foo() {}
    unconstrained fn bar() {}
    "#;
    check_errors(src);
}

#[test]
fn can_pass_regular_function_to_unconstrained_function() {
    let src = r#"
    fn main() {
        let func = foo;
        expect_unconstrained(func);
    }

    fn foo() {}

    fn expect_unconstrained(_func: unconstrained fn() -> ()) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn cannot_pass_unconstrained_function_to_constrained_function() {
    let src = r#"
    fn main() {
        let func = foo;
        expect_regular(func);
                       ^^^^ Converting an unconstrained fn to a non-unconstrained fn is unsafe
    }

    unconstrained fn foo() {}

    fn expect_regular(_func: fn() -> ()) {}
    "#;
    check_errors(src);
}

#[test]
fn can_assign_regular_function_to_unconstrained_function_in_explicitly_typed_var() {
    let src = r#"
    fn main() {
        let _func: unconstrained fn() -> () = foo;
    }

    fn foo() {}
    "#;
    assert_no_errors(src);
}

#[test]
fn can_assign_regular_function_to_unconstrained_function_in_struct_member() {
    let src = r#"
    fn main() {
        let _ = Foo { func: foo };
    }

    fn foo() {}

    struct Foo {
        func: unconstrained fn() -> (),
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn trait_impl_generics_count_mismatch() {
    let src = r#"
    trait Foo {}

    impl Foo<()> for Field {}
         ^^^ Foo expects 0 generics but 1 was given

    fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn bit_not_on_untyped_integer() {
    let src = r#"
    fn main() {
        let _: u32 = 3 & !1;
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn duplicate_struct_field() {
    // TODO: the primary error location should be on the second field
    let src = r#"
    pub struct Foo {
        x: i32,
        ^ Duplicate definitions of struct field with name x found
        ~ First struct field found here
        x: i32,
        ~ Second struct field found here
    }

    fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn trait_constraint_on_tuple_type() {
    let src = r#"
        trait Foo<A> {
            fn foo(self, x: A) -> bool;
        }

        pub fn bar<T, U, V>(x: (T, U), y: V) -> bool where (T, U): Foo<V> {
            x.foo(y)
        }

        fn main() {}"#;
    assert_no_errors(src);
}

#[test]
fn trait_constraint_on_tuple_type_pub_crate() {
    let src = r#"
        pub(crate) trait Foo<A> {
            fn foo(self, x: A) -> bool;
        }

        pub fn bar<T, U, V>(x: (T, U), y: V) -> bool where (T, U): Foo<V> {
            x.foo(y)
        }

        fn main() {}"#;
    assert_no_errors(src);
}

#[test]
fn incorrect_generic_count_on_struct_impl() {
    let src = r#"
    struct Foo {}
    impl <T> Foo<T> {}
             ^^^ Foo expects 0 generics but 1 was given
    fn main() {
        let _ = Foo {}; // silence Foo never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn incorrect_generic_count_on_type_alias() {
    let src = r#"
    pub struct Foo {}
    pub type Bar = Foo<i32>;
                   ^^^ Foo expects 0 generics but 1 was given
    fn main() {
        let _ = Foo {}; // silence Foo never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn uses_self_type_for_struct_function_call() {
    let src = r#"
    struct S { }

    impl S {
        fn one() -> Field {
            1
        }

        fn two() -> Field {
            Self::one() + Self::one()
        }
    }

    fn main() {
        let _ = S {}; // silence S never constructed warning
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn uses_self_type_inside_trait() {
    let src = r#"
    trait Foo {
        fn foo() -> Self {
            Self::bar()
        }

        fn bar() -> Self;
    }

    impl Foo for Field {
        fn bar() -> Self {
            1
        }
    }

    fn main() {
        let _: Field = Foo::foo();
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn uses_self_type_in_trait_where_clause() {
    let src = r#"
    pub trait Trait {
        fn trait_func(self) -> bool;
    }

    pub trait Foo where Self: Trait {
                              ~~~~~ required by this bound in `Foo
        fn foo(self) -> bool {
            self.trait_func()
            ^^^^^^^^^^^^^^^^^ No method named 'trait_func' found for type 'Bar'
        }
    }

    struct Bar {}

    impl Foo for Bar {
                 ^^^ The trait bound `_: Trait` is not satisfied
                 ~~~ The trait `Trait` is not implemented for `_

    }

    fn main() {
        let _ = Bar {}; // silence Bar never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn do_not_eagerly_error_on_cast_on_type_variable() {
    let src = r#"
    pub fn foo<T, U>(x: T, f: fn(T) -> U) -> U {
        f(x)
    }

    fn main() {
        let x: u8 = 1;
        let _: Field = foo(x, |x| x as Field);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn error_on_cast_over_type_variable() {
    let src = r#"
    pub fn foo<T, U>(f: fn(T) -> U, x: T, ) -> U {
        f(x)
    }

    fn main() {
        let x = "a";
        let _: Field = foo(|x| x as Field, x);
                                           ^ Expected type Field, found type str<1>
    }
    "#;
    check_errors(src);
}

#[test]
fn trait_impl_for_a_type_that_implements_another_trait() {
    let src = r#"
    trait One {
        fn one(self) -> i32;
    }

    impl One for i32 {
        fn one(self) -> i32 {
            self
        }
    }

    trait Two {
        fn two(self) -> i32;
    }

    impl<T> Two for T where T: One {
        fn two(self) -> i32 {
            self.one() + 1
        }
    }

    pub fn use_it<T>(t: T) -> i32 where T: Two {
        Two::two(t)
    }

    fn main() {}
    "#;
    assert_no_errors(src);
}

#[test]
fn trait_impl_for_a_type_that_implements_another_trait_with_another_impl_used() {
    let src = r#"
    trait One {
        fn one(self) -> i32;
    }

    impl One for i32 {
        fn one(self) -> i32 {
            let _ = self;
            1
        }
    }

    trait Two {
        fn two(self) -> i32;
    }

    impl<T> Two for T where T: One {
        fn two(self) -> i32 {
            self.one() + 1
        }
    }

    impl Two for u32 {
        fn two(self) -> i32 {
            let _ = self;
            0
        }
    }

    pub fn use_it(t: u32) -> i32 {
        Two::two(t)
    }

    fn main() {}
    "#;
    assert_no_errors(src);
}

#[test]
fn impl_missing_associated_type() {
    let src = r#"
    trait Foo {
        type Assoc;
    }

    impl Foo for () {}
         ^^^ `Foo` is missing the associated type `Assoc`
    "#;
    check_errors(src);
}

#[test]
fn as_trait_path_syntax_resolves_outside_impl() {
    let src = r#"
    trait Foo {
        type Assoc;
    }

    struct Bar {}

    impl Foo for Bar {
        type Assoc = i32;
    }

    fn main() {
        // AsTraitPath syntax is a bit silly when associated types
        // are explicitly specified
        let _: i64 = 1 as <Bar as Foo<Assoc = i32>>::Assoc;
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Expected type i64, found type i32

        let _ = Bar {}; // silence Bar never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn as_trait_path_syntax_no_impl() {
    let src = r#"
    trait Foo {
        type Assoc;
    }

    struct Bar {}

    impl Foo for Bar {
        type Assoc = i32;
    }

    fn main() {
        let _: i64 = 1 as <Bar as Foo<Assoc = i8>>::Assoc;
                                  ^^^ No matching impl found for `Bar: Foo<Assoc = i8>`
                                  ~~~ No impl for `Bar: Foo<Assoc = i8>`

        let _ = Bar {}; // silence Bar never constructed warning
    }
    "#;
    check_errors(src);
}

#[test]
fn do_not_infer_globals_to_u32_from_type_use() {
    // TODO: improve the error location (maybe it should be on the global name)
    let src = r#"
        global ARRAY_LEN = 3;
                           ^ Globals must have a specified type
                           ~ Inferred type is `Field`
        global STR_LEN: _ = 2;
                            ^ Globals must have a specified type
                            ~ Inferred type is `Field`
        global FMT_STR_LEN = 2;
                             ^ Globals must have a specified type
                             ~ Inferred type is `Field`

        fn main() {
            let _a: [u32; ARRAY_LEN] = [1, 2, 3];
                    ^^^^^^^^^^^^^^^^ Expected kind numeric u32, found kind numeric Field
            let _b: str<STR_LEN> = "hi";
                    ^^^^^^^^^^^^ Expected kind numeric u32, found kind numeric Field
            let _c: fmtstr<FMT_STR_LEN, _> = f"hi";
                    ^^^^^^^^^^^^^^^^^^^^^^ Expected kind numeric u32, found kind numeric Field
        }
    "#;
    check_errors(src);
}

#[test]
fn do_not_infer_partial_global_types() {
    let src = r#"
        pub global ARRAY: [Field; _] = [0; 3];
                                       ^^^^^^ Globals must have a specified type
                                       ~~~~~~ Inferred type is `[Field; 3]`
        pub global NESTED_ARRAY: [[Field; _]; 3] = [[]; 3];
                                                   ^^^^^^^ Globals must have a specified type
                                                   ~~~~~~~ Inferred type is `[[Field; 0]; 3]`
        pub global STR: str<_> = "hi";
                                 ^^^^ Globals must have a specified type
                                 ~~~~ Inferred type is `str<2>`
                 
        pub global NESTED_STR: [str<_>] = &["hi"];
                                          ^^^^^^^ Globals must have a specified type
                                          ~~~~~~~ Inferred type is `[str<2>]`
        pub global FORMATTED_VALUE: str<5> = "there";
        pub global FMT_STR: fmtstr<_, _> = f"hi {FORMATTED_VALUE}";
                                           ^^^^^^^^^^^^^^^^^^^^^^^ Globals must have a specified type
                                           ~~~~~~~~~~~~~~~~~~~~~~~ Inferred type is `fmtstr<20, (str<5>)>`
        pub global TUPLE_WITH_MULTIPLE: ([str<_>], [[Field; _]; 3]) = 
            (&["hi"], [[]; 3]);
            ^^^^^^^^^^^^^^^^^^ Globals must have a specified type
            ~~~~~~~~~~~~~~~~~~ Inferred type is `([str<2>], [[Field; 0]; 3])`

        fn main() { }
    "#;
    check_errors(src);
}

#[test]
fn u32_globals_as_sizes_in_types() {
    let src = r#"
        global ARRAY_LEN: u32 = 3;
        global STR_LEN: u32 = 2;
        global FMT_STR_LEN: u32 = 2;

        fn main() {
            let _a: [u32; ARRAY_LEN] = [1, 2, 3];
            let _b: str<STR_LEN> = "hi";
            let _c: fmtstr<FMT_STR_LEN, _> = f"hi";
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn struct_array_len() {
    let src = r#"
        struct Array<T, let N: u32> {
            inner: [T; N],
        }

        impl<T, let N: u32> Array<T, N> {
            pub fn len(self) -> u32 {
                       ^^^^ unused variable self
                       ~~~~ unused variable
                N as u32
            }
        }

        fn main(xs: [Field; 2]) {
            let ys = Array {
                inner: xs,
            };
            assert(ys.len() == 2);
        }
    "#;
    check_errors(src);
}

// TODO(https://github.com/noir-lang/noir/issues/6245):
// support u8 as an array size
#[test]
fn non_u32_as_array_length() {
    let src = r#"
        global ARRAY_LEN: u8 = 3;

        fn main() {
            let _a: [u32; ARRAY_LEN] = [1, 2, 3];
                    ^^^^^^^^^^^^^^^^ Expected kind numeric u32, found kind numeric u8
        }
    "#;
    check_errors(src);
}

#[test]
fn use_non_u32_generic_in_struct() {
    let src = r#"
        struct S<let N: u8> {}

        fn main() {
            let _: S<3> = S {};
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn use_numeric_generic_in_trait_method() {
    let src = r#"
        trait Foo  {
            fn foo<let N: u32>(self, x: [u8; N]) -> Self;
        }

        struct Bar;

        impl Foo for Bar {
            fn foo<let N: u32>(self, _x: [u8; N]) -> Self {
                self
            }
        }

        fn main() {
            let bytes: [u8; 3] = [1,2,3];
            let _ = Bar{}.foo(bytes);
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn trait_unconstrained_methods_typechecked_correctly() {
    // This test checks that we properly track whether a method has been declared as unconstrained on the trait definition
    // and preserves that through typechecking.
    let src = r#"
        trait Foo {
            unconstrained fn identity(self) -> Self {
                self
            }

            unconstrained fn foo(self) -> Field;
        }

        impl Foo for u64 {
            unconstrained fn foo(self) -> Field {
                self as Field
            }
        }

        unconstrained fn main() {
            assert_eq(2.foo(), 2.identity() as Field);
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn error_if_attribute_not_in_scope() {
    let src = r#"
        #[not_in_scope]
        ^^^^^^^^^^^^^^^ Attribute function `not_in_scope` is not in scope
        fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn arithmetic_generics_rounding_pass() {
    let src = r#"
        fn main() {
            // 3/2*2 = 2
            round::<3, 2>([1, 2]);
        }

        fn round<let N: u32, let M: u32>(_x: [Field; N / M * M]) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn arithmetic_generics_rounding_fail() {
    let src = r#"
        fn main() {
            // Do not simplify N/M*M to just N
            // This should be 3/2*2 = 2, not 3
            round::<3, 2>([1, 2, 3]);
                          ^^^^^^^^^ Expected type [Field; 2], found type [Field; 3]
        }

        fn round<let N: u32, let M: u32>(_x: [Field; N / M * M]) {}
    "#;
    check_errors(src);
}

#[test]
fn arithmetic_generics_rounding_fail_on_struct() {
    let src = r#"
        struct W<let N: u32> {}

        fn foo<let N: u32, let M: u32>(_x: W<N>, _y: W<M>) -> W<N / M * M> {
            W {}
        }

        fn main() {
            let w_2: W<2> = W {};
            let w_3: W<3> = W {};
            // Do not simplify N/M*M to just N
            // This should be 3/2*2 = 2, not 3
            let _: W<3> = foo(w_3, w_2);
                          ^^^^^^^^^^^^^ Expected type W<3>, found type W<2>
        }
    "#;
    check_errors(src);
}

#[test]
fn unconditional_recursion_fail() {
    // These examples are self recursive top level functions, which would actually
    // not be inlined in the SSA (there is nothing to inline into but self), so it
    // wouldn't panic due to infinite recursion, but the errors asserted here
    // come from the compilation checks, which does static analysis to catch the
    // problem before it even has a chance to cause a panic.
    let srcs = vec![
        r#"
        fn main() {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            main()
        }
        "#,
        r#"
        fn main() -> pub bool {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            if main() { true } else { false }
        }
        "#,
        r#"
        fn main() -> pub bool {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            if true { main() } else { main() }
        }
        "#,
        r#"
        fn main() -> pub u64 {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            main() + main()
        }
        "#,
        r#"
        fn main() -> pub u64 {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            1 + main()
        }
        "#,
        r#"
        fn main() -> pub bool {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            let _ = main();
            true
        }
        "#,
        r#"
        fn main(a: u64, b: u64) -> pub u64 {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            main(a + b, main(a, b))
        }
        "#,
        r#"
        fn main() -> pub u64 {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            foo(1, main())
        }
        fn foo(a: u64, b: u64) -> u64 {
            a + b
        }
        "#,
        r#"
        fn main() -> pub u64 {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            let (a, b) = (main(), main());
            a + b
        }
        "#,
        r#"
        fn main() -> pub u64 {
           ^^^^ function `main` cannot return without recursing
           ~~~~ function cannot return without recursing
            let mut sum = 0;
            for i in 0 .. main() {
                sum += i;
            }
            sum
        }
        "#,
    ];

    for src in srcs {
        check_errors(src);
    }
}

#[test]
fn unconditional_recursion_pass() {
    let srcs = vec![
        r#"
        fn main() {
            if false { main(); }
        }
        "#,
        r#"
        fn main(i: u64) -> pub u64 {
            if i == 0 { 0 } else { i + main(i-1) }
        }
        "#,
        // Only immediate self-recursion is detected.
        r#"
        fn main() {
            foo();
        }
        fn foo() {
            bar();
        }
        fn bar() {
            foo();
        }
        "#,
        // For loop bodies are not checked.
        r#"
        fn main() -> pub u64 {
            let mut sum = 0;
            for _ in 0 .. 10 {
                sum += main();
            }
            sum
        }
        "#,
        // Lambda bodies are not checked.
        r#"
        fn main() {
            let foo = || main();
            foo();
        }
        "#,
    ];

    for src in srcs {
        assert_no_errors(src);
    }
}

#[test]
fn uses_self_in_import() {
    let src = r#"
    mod moo {
        pub mod bar {
            pub fn foo() -> i32 {
                1
            }
        }
    }

    use moo::bar::{self};

    pub fn baz() -> i32 {
        bar::foo()
    }

    fn main() {}
    "#;
    assert_no_errors(src);
}

#[test]
fn does_not_error_on_return_values_after_block_expression() {
    // Regression test for https://github.com/noir-lang/noir/issues/4372
    let src = r#"
    fn case1() -> [Field] {
        if true {
        }
        &[1]
    }

    fn case2() -> [u8] {
        let mut var: u8 = 1;
        {
            var += 1;
        }
        &[var]
    }

    fn main() {
        let _ = case1();
        let _ = case2();
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn use_type_alias_in_method_call() {
    let src = r#"
        pub struct Foo {
        }

        impl Foo {
            fn new() -> Self {
                Foo {}
            }
        }

        type Bar = Foo;

        fn foo() -> Foo {
            Bar::new()
        }

        fn main() {
            let _ = foo();
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn use_type_alias_to_generic_concrete_type_in_method_call() {
    let src = r#"
        pub struct Foo<T> {
            x: T,
        }

        impl<T> Foo<T> {
            fn new(x: T) -> Self {
                Foo { x }
            }
        }

        type Bar = Foo<i32>;

        fn foo() -> Bar {
            Bar::new(1)
        }

        fn main() {
            let _ = foo();
        }
    "#;
    assert_no_errors(src);
}

#[test]
fn allows_struct_with_generic_infix_type_as_main_input_1() {
    let src = r#"
        struct Foo<let N: u32> {
            x: [u64; N * 2],
        }

        fn main(_x: Foo<18>) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn allows_struct_with_generic_infix_type_as_main_input_2() {
    let src = r#"
        struct Foo<let N: u32> {
            x: [u64; N * 2],
        }

        fn main(_x: Foo<2 * 9>) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn allows_struct_with_generic_infix_type_as_main_input_3() {
    let src = r#"
        struct Foo<let N: u32> {
            x: [u64; N * 2],
        }

        global N: u32 = 9;

        fn main(_x: Foo<N * 2>) {}
    "#;
    assert_no_errors(src);
}

#[test]
fn errors_with_better_message_when_trying_to_invoke_struct_field_that_is_a_function() {
    let src = r#"
        pub struct Foo {
            wrapped: fn(Field) -> bool,
        }

        impl Foo {
            fn call(self) -> bool {
                self.wrapped(1)
                ^^^^^^^^^^^^^^^ Cannot invoke function field 'wrapped' on type 'Foo' as a method
                ~~~~~~~~~~~~~~~ to call the function stored in 'wrapped', surround the field access with parentheses: '(', ')'
            }
        }

        fn main() {}
    "#;
    check_errors(src);
}

#[test]
fn disallows_test_attribute_on_impl_method() {
    // TODO: improve the error location
    let src = "
        pub struct Foo { }

        impl Foo {
            #[test]
            fn foo() { }
               ^^^ The `#[test]` attribute is disallowed on `impl` methods
        }

        fn main() { }
    ";
    check_errors(src);
}

#[test]
fn disallows_test_attribute_on_trait_impl_method() {
    let src = "
        pub trait Trait {
            fn foo() { }
        }

        pub struct Foo { }

        impl Trait for Foo {
            #[test]
            fn foo() { }
               ^^^ The `#[test]` attribute is disallowed on `impl` methods
        }

        fn main() { }
    ";
    check_errors(src);
}

#[test]
fn disallows_export_attribute_on_impl_method() {
    // TODO: improve the error location
    let src = "
        pub struct Foo { }

        impl Foo {
            #[export]
            fn foo() { }
               ^^^ The `#[export]` attribute is disallowed on `impl` methods
        }

        fn main() { }
    ";
    check_errors(src);
}

#[test]
fn disallows_export_attribute_on_trait_impl_method() {
    // TODO: improve the error location
    let src = "
        pub trait Trait {
            fn foo() { }
        }

        pub struct Foo { }

        impl Trait for Foo {
            #[export]
            fn foo() { }
               ^^^ The `#[export]` attribute is disallowed on `impl` methods
        }

        fn main() { }
    ";
    check_errors(src);
}

#[test]
fn allows_multiple_underscore_parameters() {
    let src = r#"
        pub fn foo(_: i32, _: i64) {}

        fn main() {}
    "#;
    assert_no_errors(src);
}

#[test]
fn disallows_underscore_on_right_hand_side() {
    let src = r#"
        fn main() {
            let _ = 1;
            let _x = _;
                     ^ in expressions, `_` can only be used on the left-hand side of an assignment
                     ~ `_` not allowed here
        }
    "#;
    check_errors(src);
}

#[test]
fn errors_on_cyclic_globals() {
    let src = r#"
    pub comptime global A: u32 = B;
                                 ^ This global recursively depends on itself
                        ^ Dependency cycle found
                        ~ 'A' recursively depends on itself: A -> B -> A
    pub comptime global B: u32 = A;
                                 ^ Variable not in scope
                                 ~ Could not find variable

    fn main() { }
    "#;
    check_errors(src);
}

#[test]
fn warns_on_unneeded_unsafe() {
    let src = r#"
    fn main() {
        // Safety: test
        unsafe {
        ^^^^^^ Unnecessary `unsafe` block
            foo()
        }
    }

    fn foo() {}
    "#;
    check_errors(src);
}

#[test]
fn warns_on_nested_unsafe() {
    let src = r#"
    fn main() {
        // Safety: test
        unsafe {
            // Safety: test
            unsafe {
            ^^^^^^ Unnecessary `unsafe` block
            ~~~~~~ Because it's nested inside another `unsafe` block
                foo()
            }
        }
    }

    unconstrained fn foo() {}
    "#;
    check_errors(src);
}

#[test]
fn mutable_self_call() {
    let src = r#"
    fn main() {
        let mut bar = Bar {};
        let _ = bar.bar();
    }

    struct Bar {}

    impl Bar {
        fn bar(&mut self) {
            let _ = self;
        }
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn checks_visibility_of_trait_related_to_trait_impl_on_method_call() {
    let src = r#"
    mod moo {
        pub struct Bar {}
    }

    trait Foo {
        fn foo(self);
    }

    impl Foo for moo::Bar {
        fn foo(self) {}
    }

    fn main() {
        let bar = moo::Bar {};
        bar.foo();
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_method_call_function_type() {
    let src = r#"
    struct Foo {
        value: Field,
    }

    impl Foo {
        fn foo(self) -> Field {
            self.value
        }
    }

    struct Box<T> {
        value: T,
    }

    impl<T> Box<T> {
        fn map<U>(self, f: fn(T) -> U) -> Box<U> {
            Box { value: f(self.value) }
        }
    }

    fn main() {
        let box = Box { value: Foo { value: 1 } };
        let _ = box.map(|foo| foo.foo());
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_call_function_type() {
    let src = r#"
    struct Foo {
        value: Field,
    }

    fn call(f: fn(Foo) -> Field) -> Field {
        f(Foo { value: 1 })
    }

    fn main() {
        let _ = call(|foo| foo.value);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_call_function_type_in_generic_call() {
    let src = r#"
    struct Foo {
        value: Field,
    }

    fn call<T>(t: T, f: fn(T) -> Field) -> Field {
        f(t)
    }

    fn main() {
        let _ = call(Foo { value: 1 }, |foo| foo.value);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_call_function_type_as_alias() {
    let src = r#"
    struct Foo {
        value: Field,
    }

    type MyFn = fn(Foo) -> Field;

    fn call(f: MyFn) -> Field {
        f(Foo { value: 1 })
    }

    fn main() {
        let _ = call(|foo| foo.value);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_function_return_type() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    pub fn func() -> fn(Foo) -> Field {
        |foo| foo.value
    }

    fn main() {
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_function_return_type_multiple_statements() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    pub fn func() -> fn(Foo) -> Field {
        let _ = 1;
        |foo| foo.value
    }

    fn main() {
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_function_return_type_when_inside_if() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    pub fn func() -> fn(Foo) -> Field {
        if true {
            |foo| foo.value
        } else {
            |foo| foo.value
        }
    }

    fn main() {
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_variable_type() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    fn main() {
      let _: fn(Foo) -> Field = |foo| foo.value;
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_variable_alias_type() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    type FooFn = fn(Foo) -> Field;

    fn main() {
      let _: FooFn = |foo| foo.value;
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_variable_double_alias_type() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    type FooFn = fn(Foo) -> Field;
    type FooFn2 = FooFn;

    fn main() {
      let _: FooFn2 = |foo| foo.value;
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_variable_tuple_type() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    fn main() {
      let _: (fn(Foo) -> Field, _) = (|foo| foo.value, 1);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn infers_lambda_argument_from_variable_tuple_type_aliased() {
    let src = r#"
    pub struct Foo {
        value: Field,
    }

    type Alias = (fn(Foo) -> Field, Field);

    fn main() {
      let _: Alias = (|foo| foo.value, 1);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn regression_7088() {
    // A test for code that initially broke when implementing inferring
    // lambda parameter types from the function type related to the call
    // the lambda is in (PR #7088).
    let src = r#"
    struct U60Repr<let N: u32, let NumSegments: u32> {}

    impl<let N: u32, let NumSegments: u32> U60Repr<N, NumSegments> {
        fn new<let NumFieldSegments: u32>(_: [Field; N * NumFieldSegments]) -> Self {
            U60Repr {}
        }
    }

    fn main() {
        let input: [Field; 6] = [0; 6];
        let _: U60Repr<3, 6> = U60Repr::new(input);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn errors_on_empty_loop_no_break() {
    let src = r#"
    fn main() {
        // Safety: test
        unsafe {
            foo()
        }
    }

    unconstrained fn foo() {
        loop {}
        ^^^^ `loop` must have at least one `break` in it
        ~~~~ Infinite loops are disallowed
    }
    "#;
    check_errors(src);
}

#[test]
fn errors_on_loop_without_break() {
    let src = r#"
    fn main() {
        // Safety: test
        unsafe {
            foo()
        }
    }

    unconstrained fn foo() {
        let mut x = 1;
        loop {
        ^^^^ `loop` must have at least one `break` in it
        ~~~~ Infinite loops are disallowed
            x += 1;
            bar(x);
        }
    }

    fn bar(_: Field) {}
    "#;
    check_errors(src);
}

#[test]
fn errors_on_loop_without_break_with_nested_loop() {
    let src = r#"
    fn main() {
        // Safety: test
        unsafe {
            foo()
        }
    }

    unconstrained fn foo() {
        let mut x = 1;
        loop {
        ^^^^ `loop` must have at least one `break` in it
        ~~~~ Infinite loops are disallowed
            x += 1;
            bar(x);
            loop {
                x += 2;
                break;
            }
        }
    }

    fn bar(_: Field) {}
    "#;
    check_errors(src);
}

#[test]
fn call_function_alias_type() {
    let src = r#"
    type Alias<Env> = fn[Env](Field) -> Field;

    fn main() {
        call_fn(|x| x + 1);
    }

    fn call_fn<Env>(f: Alias<Env>) {
        assert_eq(f(0), 1);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn errors_on_if_without_else_type_mismatch() {
    let src = r#"
    fn main() {
        if true {
            1
            ^ Expected type Field, found type ()
        }
    }
    "#;
    check_errors(src);
}

#[test]
fn does_not_stack_overflow_on_many_comments_in_a_row() {
    let src = "//\n".repeat(10_000);
    assert_no_errors(&src);
}

#[test]
fn errors_if_for_body_type_is_not_unit() {
    let src = r#"
    fn main() {
        for _ in 0..1 {
            1
            ^ Expected type (), found type Field
        }
    }
    "#;
    check_errors(src);
}

#[test]
fn errors_if_loop_body_type_is_not_unit() {
    let src = r#"
    unconstrained fn main() {
        loop {
            if false { break; }

            1
            ^ Expected type (), found type Field
        }
    }
    "#;
    check_errors(src);
}

#[test]
fn errors_if_while_body_type_is_not_unit() {
    let src = r#"
    unconstrained fn main() {
        while 1 == 1 {
            1
            ^ Expected type (), found type Field
        }
    }
    "#;
    check_errors(src);
}

#[test]
fn check_impl_duplicate_method_without_self() {
    // TODO: the primary error location should be n the second `foo`
    let src = "
    pub struct Foo {}

    impl Foo {
        fn foo() {}
           ^^^ duplicate definitions of foo found
           ~~~ first definition found here
        fn foo() {}
           ~~~ second definition found here
    }

    fn main() {}
    ";
    check_errors(src);
}

#[test]
fn int_min_global() {
    let src = r#"
        global MIN: i8 = -128;
        fn main() {
            let _x = MIN;
        }
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 0);
}

#[test]
fn subtract_to_int_min() {
    // This would cause an integer underflow panic before
    let src = r#"
        fn main() {
            let _x: i8 = comptime {
                let y: i8 = -127;
                let z = y - 1;
                z
            };
        }
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 0);
}
