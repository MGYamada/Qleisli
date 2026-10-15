//! Small source-association checks; no IR, simulation or native quantum case.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::resolve::locals::OccurrencesForest;

const FIRST: &str = "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
unitary fn hold[const U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Applicable(U){U(q)}
unitary fn direct(q:Q<Unit>)->Q<Unit>{hold[identity](q)}
unitary fn zero(q:Q<Unit>)->Q<Unit>{hold[power(identity,0)](q)}
unitary fn nested(q:Q<Unit>)->Q<Unit>{hold[power(power(identity,0),0)](q)}";

fn fixture(text: &str, run: impl FnOnce(&Module, &mut check::CheckedProgram, &Forest<'_>)) {
    let ast = crate::frontend::parser::parse_module(text).unwrap();
    let (mut program, occurrences) = check::program_with(
        BTreeMap::from([("main", &ast)]),
        SourceLimits::finite(),
        |resolution, _, _, _, _, indices, budget| {
            let mut occurrences = OccurrencesForest::default();
            for (id, index) in indices {
                let declaration = resolution.declaration(*id);
                occurrences.insert_budgeted(
                    index.take_occurrences(),
                    ast.decls[declaration.ast_index].span,
                    &mut |span, cells| budget.charge(span, cells),
                )?;
            }
            Ok(occurrences)
        },
    )
    .unwrap();
    let forest = Forest::from_occurrences(occurrences);
    run(&ast, &mut program, &forest);
}

fn call<'ast>(
    program: &check::CheckedProgram,
    ast: &'ast Module,
    name: &str,
) -> OriginalCall<'ast> {
    let owner = program
        .resolution
        .qualified(&format!("main::{name}"))
        .unwrap();
    let declaration = program.resolution.declaration(owner);
    let FnBody::Quantum(body) = &ast.decls[declaration.ast_index].body else {
        panic!("runtime body")
    };
    let expression = body.result.as_ref();
    let (callee, static_arguments, runtime_arguments) = match &expression.kind {
        ExprKind::Call {
            callee,
            static_args,
            args,
        } => (
            callee,
            static_args.as_slice(),
            RuntimeArguments::Values(args),
        ),
        ExprKind::AccessCall {
            callee,
            static_args,
            args,
        } => (
            callee,
            static_args.as_slice(),
            RuntimeArguments::Accesses(args),
        ),
        _ => panic!("direct runtime call"),
    };
    OriginalCall {
        owner,
        module: declaration.module,
        expression,
        callee,
        static_arguments,
        runtime_arguments,
    }
}

fn error(span: Span, code: ErrorCode, message: &'static str) -> CompileError {
    CompileError {
        code,
        path: PathBuf::from("main.qli"),
        span,
        line: 1,
        column: 1,
        message: message.into(),
    }
}

fn validate<'checked>(
    program: &'checked check::CheckedProgram,
    forest: &Forest<'_>,
    call: OriginalCall<'_>,
) -> Result<CheckedCall<'checked>, CompileError> {
    CheckedCall::original(
        program,
        &forest.lookup(&program.lexical),
        call,
        &mut |_, _| Ok(()),
        &error,
    )
}

fn rejection(result: Result<CheckedCall<'_>, CompileError>) -> CompileError {
    match result {
        Ok(_) => panic!("foreign or altered call passed"),
        Err(error) => error,
    }
}

#[test]
fn direct_zero_and_nested_calls_borrow_the_exact_original_plan_and_arcs() {
    fixture(FIRST, |ast, program, forest| {
        for name in ["direct", "zero", "nested"] {
            let original = call(program, ast, name);
            let site = forest
                .lookup(&program.lexical)
                .try_reference_site(original.callee)
                .unwrap();
            let checked = validate(program, forest, original).unwrap();
            assert!(std::ptr::eq(checked.plan(), &program.static_calls[&site]));
            assert!(Arc::ptr_eq(
                &checked.plan().arguments[0].value,
                &program.static_calls[&site].arguments[0].value
            ));
        }
    });
}

#[test]
fn same_span_cloned_expression_callee_and_operand_slices_are_refused_without_panics() {
    fixture(FIRST, |ast, program, forest| {
        let mut original = call(program, ast, "direct");
        let cloned = original.expression.clone();
        original.expression = &cloned;
        assert!(
            rejection(validate(program, forest, original))
                .message
                .contains("original expression")
        );

        let mut original = call(program, ast, "direct");
        let cloned = original.callee.clone();
        original.callee = &cloned;
        assert!(
            rejection(validate(program, forest, original))
                .message
                .contains("original reference")
        );

        let mut original = call(program, ast, "direct");
        let cloned = original.static_arguments.to_vec();
        original.static_arguments = &cloned;
        assert!(
            rejection(validate(program, forest, original))
                .message
                .contains("AST slices")
        );

        let mut original = call(program, ast, "direct");
        let cloned: Vec<_> = original.runtime_arguments.iter().cloned().collect();
        original.runtime_arguments = RuntimeArguments::Values(&cloned);
        assert!(
            rejection(validate(program, forest, original))
                .message
                .contains("AST slices")
        );
    });
}

#[test]
fn another_judgment_with_the_same_ast_and_numeric_ids_is_not_the_checked_collection() {
    fixture(FIRST, |ast, program, forest| {
        let foreign = check::program_with(
            BTreeMap::from([("main", ast)]),
            SourceLimits::finite(),
            |_, _, _, _, _, _, _| Ok(()),
        )
        .unwrap()
        .0;
        let original = call(&foreign, ast, "direct");
        assert!(
            rejection(CheckedCall::original(
                &foreign,
                &forest.lookup(&program.lexical),
                original,
                &mut |_, _| Ok(()),
                &error,
            ))
            .message
            .contains("different checked collections")
        );
        assert!(
            forest
                .lookup(&foreign.lexical)
                .try_node_id_expr(call(program, ast, "direct").expression)
                .is_none()
        );
        assert!(
            forest
                .lookup(&foreign.lexical)
                .try_reference_site(call(program, ast, "direct").callee)
                .is_none()
        );
    });
}

#[test]
fn original_basis_nat_and_operation_categories_are_retained_without_generic_admission() {
    fixture(
        "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
         unitary fn mixed[const A:Basis,const n:Nat,const U:Op<Unit>](q:Q<Unit>)->Q<Unit>
         requires Applicable(U){U(q)}
         unitary fn caller(q:Q<Unit>)->Q<Unit>{mixed[type(Unit),0,identity](q)}",
        |ast, program, forest| {
            let checked = validate(program, forest, call(program, ast, "caller")).unwrap();
            assert_eq!(
                checked
                    .plan()
                    .arguments
                    .iter()
                    .map(|a| a.category)
                    .collect::<Vec<_>>(),
                [
                    StaticCategory::Basis,
                    StaticCategory::Natural,
                    StaticCategory::Operation
                ]
            );
        },
    );
}

#[test]
fn owner_module_effect_cardinality_category_and_ordered_actual_roots_are_checked() {
    for change in 0..11 {
        fixture(FIRST, |ast, program, forest| {
            let original = call(program, ast, "direct");
            let site = forest
                .lookup(&program.lexical)
                .try_reference_site(original.callee)
                .unwrap();
            let other = call(program, ast, "zero");
            let other_site = forest
                .lookup(&program.lexical)
                .try_reference_site(other.callee)
                .unwrap();
            let replacement = Arc::clone(&program.static_calls[&other_site].arguments[0].value);
            let foreign_owner = other.owner;
            let ExprKind::Name(name) = &original.runtime_arguments.first().unwrap().kind else {
                panic!("runtime parameter")
            };
            let wrong_formal = forest
                .lookup(&program.lexical)
                .local_key(name)
                .unwrap()
                .clone();
            let plan = program.static_calls.get_mut(&site).unwrap();
            match change {
                0 => plan.owner = foreign_owner,
                1 => Arc::make_mut(&mut plan.environment).owner = foreign_owner,
                2 => plan.source_effect = Some(crate::ir::Effect::Observe),
                3 => plan.parameters.clear(),
                4 => plan.arguments[0].category = StaticCategory::Natural,
                5 => plan.arguments[0].value = replacement,
                6 => plan.arguments[0].formal = wrong_formal,
                7 => plan.target = foreign_owner,
                8 => plan.arguments.clear(),
                9 => plan.source_effect = None,
                10 => Arc::make_mut(&mut plan.arguments[0].value).node = None,
                _ => unreachable!(),
            }
            assert_eq!(
                rejection(validate(program, forest, original)).code,
                ErrorCode::TypeMismatch
            );
        });
    }
}

#[test]
fn same_owner_actual_roots_cannot_be_reordered_even_after_copying_the_original_span() {
    fixture(
        "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
         unitary fn pair[const U:Op<Unit>,const V:Op<Unit>](q:Q<Unit>)->Q<Unit>
         requires Applicable(U),Applicable(V){U(q)}
         unitary fn caller(q:Q<Unit>)->Q<Unit>{pair[identity,power(identity,0)](q)}",
        |ast, program, forest| {
            let original = call(program, ast, "caller");
            let site = forest
                .lookup(&program.lexical)
                .try_reference_site(original.callee)
                .unwrap();
            let plan = program.static_calls.get_mut(&site).unwrap();
            let mut wrong_root = (*plan.arguments[1].value).clone();
            wrong_root.span = plan.arguments[0].value.span;
            plan.arguments[0].value = Arc::new(wrong_root);
            assert!(
                rejection(validate(program, forest, original))
                    .message
                    .contains("ordered original root")
            );
        },
    );
}

#[test]
fn access_calls_keep_the_original_access_argument_slice() {
    fixture(
        "unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
         unitary fn caller(q:Q<Unit>)->Q<Unit>{identity(excl q);q}",
        |ast, program, forest| {
            let owner = program.resolution.qualified("main::caller").unwrap();
            let record = program.resolution.declaration(owner);
            let FnBody::Quantum(body) = &ast.decls[record.ast_index].body else {
                panic!("quantum body")
            };
            let StmtKind::Expr(expression) = &body.statements[0].kind else {
                panic!("access statement")
            };
            let ExprKind::AccessCall {
                callee,
                static_args,
                args,
            } = &expression.kind
            else {
                panic!("access call")
            };
            let original = || OriginalCall {
                owner,
                module: record.module,
                expression,
                callee,
                static_arguments: static_args,
                runtime_arguments: RuntimeArguments::Accesses(args),
            };
            validate(program, forest, original()).unwrap();
            let cloned = args.clone();
            let mut foreign = original();
            foreign.runtime_arguments = RuntimeArguments::Accesses(&cloned);
            assert!(
                rejection(validate(program, forest, foreign))
                    .message
                    .contains("AST slices")
            );
        },
    );
}

#[test]
fn declaring_module_and_public_source_effect_cannot_be_sharpened_by_the_adapter() {
    let main = crate::frontend::parser::parse_module(
        "use library::exported;isometry fn caller(q:Q<Unit>)->Q<Unit>{exported(q)}",
    )
    .unwrap();
    let library =
        crate::frontend::parser::parse_module("pub isometry fn exported(q:Q<Unit>)->Q<Unit>{q}")
            .unwrap();
    let (program, occurrences) = check::program_with(
        BTreeMap::from([("main", &main), ("library", &library)]),
        SourceLimits::finite(),
        |_, _, _, _, _, indices, budget| {
            let mut occurrences = OccurrencesForest::default();
            for index in indices.values_mut() {
                occurrences.insert_budgeted(
                    index.take_occurrences(),
                    Span::default(),
                    &mut |span, cells| budget.charge(span, cells),
                )?;
            }
            Ok(occurrences)
        },
    )
    .unwrap();
    let forest = Forest::from_occurrences(occurrences);
    let checked = validate(&program, &forest, call(&program, &main, "caller")).unwrap();
    assert_eq!(
        checked.plan().source_effect,
        Some(crate::ir::Effect::Isometry)
    );
    let mut original = call(&program, &main, "caller");
    original.module = program.resolution.module("library").unwrap();
    assert!(
        rejection(validate(&program, &forest, original))
            .message
            .contains("original identity")
    );
}

#[test]
fn every_association_visit_is_charged_even_when_the_same_plan_was_borrowed_before() {
    fixture(FIRST, |ast, program, forest| {
        let mut total = 0;
        CheckedCall::original(
            program,
            &forest.lookup(&program.lexical),
            call(program, ast, "direct"),
            &mut |_, cells| {
                total += cells;
                Ok(())
            },
            &error,
        )
        .unwrap();
        assert!(total > 20);
        for allowance in [0, 6, total - 1] {
            let mut used = 0usize;
            let failure = rejection(CheckedCall::original(
                program,
                &forest.lookup(&program.lexical),
                call(program, ast, "direct"),
                &mut |span, cells| {
                    if cells > allowance.saturating_sub(used) {
                        return Err(error(span, ErrorCode::Limit, "test finite work exhausted"));
                    }
                    used += cells;
                    Ok(())
                },
                &error,
            ));
            assert_eq!(failure.code, ErrorCode::Limit);
            assert!(used <= allowance);
        }
    });
}
