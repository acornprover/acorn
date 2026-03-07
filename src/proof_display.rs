use std::collections::BTreeMap;

use crate::certificate::CertificateLine;
use crate::code_generator::CodeGenerator;
use crate::elaborator::acorn_value::{AcornValue, FunctionApplication, MatchCase, TypeApplication};
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::atom::AtomId;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DisplayedProofLine {
    pub statement: String,
    pub reason: String,
    pub source_index: Option<usize>,
}

#[derive(Debug, Clone)]
struct ChooseAlias {
    choose: AcornValue,
    name: String,
    first_source_index: usize,
}

fn collect_choose_terms(value: &AcornValue, output: &mut Vec<AcornValue>) {
    match value {
        AcornValue::Variable(..) | AcornValue::Constant(..) | AcornValue::Bool(..) => {}
        AcornValue::Application(app) => {
            collect_choose_terms(&app.function, output);
            for arg in &app.args {
                collect_choose_terms(arg, output);
            }
        }
        AcornValue::TypeApplication(app) => {
            collect_choose_terms(&app.function, output);
        }
        AcornValue::Lambda(_, body)
        | AcornValue::Not(body)
        | AcornValue::Try(body, _)
        | AcornValue::ForAll(_, body)
        | AcornValue::Exists(_, body) => {
            collect_choose_terms(body, output);
        }
        AcornValue::Choose(_, body) => {
            collect_choose_terms(body, output);
            output.push(value.clone());
        }
        AcornValue::Binary(_, left, right) => {
            collect_choose_terms(left, output);
            collect_choose_terms(right, output);
        }
        AcornValue::IfThenElse(cond, if_value, else_value) => {
            collect_choose_terms(cond, output);
            collect_choose_terms(if_value, output);
            collect_choose_terms(else_value, output);
        }
        AcornValue::Match(scrutinee, cases) => {
            collect_choose_terms(scrutinee, output);
            for case in cases {
                collect_choose_terms(&case.pattern, output);
                collect_choose_terms(&case.result, output);
            }
        }
    }
}

fn build_choose_aliases(lines: &[CertificateLine]) -> Vec<ChooseAlias> {
    let mut counts: BTreeMap<AcornValue, usize> = BTreeMap::new();
    let mut first_occurrence: BTreeMap<AcornValue, (usize, usize)> = BTreeMap::new();
    let mut global_order = 0;

    for (step_index, line) in lines.iter().enumerate() {
        let mut choose_terms = Vec::new();
        collect_choose_terms(&line.value, &mut choose_terms);
        for choose in choose_terms {
            *counts.entry(choose.clone()).or_default() += 1;
            first_occurrence.entry(choose).or_insert_with(|| {
                let answer = (step_index, global_order);
                global_order += 1;
                answer
            });
        }
    }

    let mut repeated: Vec<_> = counts
        .into_iter()
        .filter_map(|(choose, count)| (count >= 2).then_some(choose))
        .collect();
    repeated.sort_by_key(|choose| {
        first_occurrence
            .get(choose)
            .copied()
            .expect("first occurrence recorded for every counted choose")
    });

    repeated
        .into_iter()
        .enumerate()
        .map(|(i, choose)| ChooseAlias {
            first_source_index: first_occurrence
                .get(&choose)
                .expect("first occurrence recorded for repeated choose")
                .0,
            choose,
            name: format!("e{}", i + 1),
        })
        .collect()
}

fn aliasify_value(
    value: &AcornValue,
    alias_indices: &BTreeMap<AcornValue, usize>,
    visible_alias_count: usize,
) -> AcornValue {
    if let Some(&alias_index) = alias_indices.get(value) {
        if alias_index < visible_alias_count {
            return AcornValue::Variable(alias_index as AtomId, value.get_type());
        }
    }

    match value {
        AcornValue::Variable(i, var_type) => {
            AcornValue::Variable(i + visible_alias_count as AtomId, var_type.clone())
        }
        AcornValue::Constant(constant) => AcornValue::Constant(constant.clone()),
        AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
            function: Box::new(aliasify_value(
                &app.function,
                alias_indices,
                visible_alias_count,
            )),
            args: app
                .args
                .iter()
                .map(|arg| aliasify_value(arg, alias_indices, visible_alias_count))
                .collect(),
        }),
        AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
            function: Box::new(aliasify_value(
                &app.function,
                alias_indices,
                visible_alias_count,
            )),
            type_param_names: app.type_param_names.clone(),
            type_param_constraints: app.type_param_constraints.clone(),
            type_args: app.type_args.clone(),
        }),
        AcornValue::Lambda(args, body) => AcornValue::Lambda(
            args.clone(),
            Box::new(aliasify_value(body, alias_indices, visible_alias_count)),
        ),
        AcornValue::Binary(op, left, right) => AcornValue::Binary(
            *op,
            Box::new(aliasify_value(left, alias_indices, visible_alias_count)),
            Box::new(aliasify_value(right, alias_indices, visible_alias_count)),
        ),
        AcornValue::Not(body) => AcornValue::Not(Box::new(aliasify_value(
            body,
            alias_indices,
            visible_alias_count,
        ))),
        AcornValue::Try(body, acorn_type) => AcornValue::Try(
            Box::new(aliasify_value(body, alias_indices, visible_alias_count)),
            acorn_type.clone(),
        ),
        AcornValue::ForAll(args, body) => AcornValue::ForAll(
            args.clone(),
            Box::new(aliasify_value(body, alias_indices, visible_alias_count)),
        ),
        AcornValue::Exists(args, body) => AcornValue::Exists(
            args.clone(),
            Box::new(aliasify_value(body, alias_indices, visible_alias_count)),
        ),
        AcornValue::Choose(choice_type, body) => AcornValue::Choose(
            choice_type.clone(),
            Box::new(aliasify_value(body, alias_indices, visible_alias_count)),
        ),
        AcornValue::Bool(value) => AcornValue::Bool(*value),
        AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
            Box::new(aliasify_value(cond, alias_indices, visible_alias_count)),
            Box::new(aliasify_value(if_value, alias_indices, visible_alias_count)),
            Box::new(aliasify_value(
                else_value,
                alias_indices,
                visible_alias_count,
            )),
        ),
        AcornValue::Match(scrutinee, cases) => AcornValue::Match(
            Box::new(aliasify_value(
                scrutinee,
                alias_indices,
                visible_alias_count,
            )),
            cases
                .iter()
                .map(|case| MatchCase {
                    new_vars: case.new_vars.clone(),
                    pattern: aliasify_value(&case.pattern, alias_indices, visible_alias_count),
                    result: aliasify_value(&case.result, alias_indices, visible_alias_count),
                    constructor_index: case.constructor_index,
                    constructor_total: case.constructor_total,
                })
                .collect(),
        ),
    }
}

fn render_value_with_aliases(
    bindings: &BindingMap,
    value: &AcornValue,
    raw_statement: &str,
    alias_indices: &BTreeMap<AcornValue, usize>,
    alias_names: &[String],
) -> String {
    let aliasified = aliasify_value(value, alias_indices, alias_names.len());
    let mut code_gen = CodeGenerator::new(bindings);
    match code_gen.value_to_code_with_initial_vars(&aliasified, alias_names) {
        Ok(code) => code,
        Err(_) => raw_statement.to_string(),
    }
}

fn render_alias_declaration(
    bindings: &BindingMap,
    alias: &ChooseAlias,
    alias_index: usize,
    alias_indices: &BTreeMap<AcornValue, usize>,
    alias_names: &[String],
) -> String {
    let AcornValue::Choose(choice_type, body) = &alias.choose else {
        panic!("choose aliases must be Choose terms");
    };

    let rendered_body = aliasify_value(body, alias_indices, alias_index);
    let mut initial_var_names: Vec<String> = alias_names[..alias_index].to_vec();
    initial_var_names.push(alias.name.clone());

    let mut code_gen = CodeGenerator::new(bindings);
    let type_code = code_gen
        .type_to_code_for_display(choice_type)
        .unwrap_or_else(|_| choice_type.to_string());
    let body_code = code_gen
        .value_to_code_with_initial_vars(&rendered_body, &initial_var_names)
        .unwrap_or_else(|_| rendered_body.to_string());
    format!(
        "let {}: {} satisfy {{ {} }}",
        alias.name, type_code, body_code
    )
}

pub fn display_certificate_lines(
    bindings: &BindingMap,
    lines: &[CertificateLine],
) -> Vec<DisplayedProofLine> {
    let aliases = build_choose_aliases(lines);
    if aliases.is_empty() {
        return lines
            .iter()
            .enumerate()
            .map(|(i, line)| DisplayedProofLine {
                statement: line.statement.clone(),
                reason: line.reason.description(),
                source_index: Some(i),
            })
            .collect();
    }

    let alias_indices: BTreeMap<AcornValue, usize> = aliases
        .iter()
        .enumerate()
        .map(|(i, alias)| (alias.choose.clone(), i))
        .collect();
    let alias_names: Vec<String> = aliases.iter().map(|alias| alias.name.clone()).collect();

    let mut displayed = Vec::new();
    let mut visible_alias_count = 0;
    for (source_index, line) in lines.iter().enumerate() {
        while visible_alias_count < aliases.len()
            && aliases[visible_alias_count].first_source_index == source_index
        {
            displayed.push(DisplayedProofLine {
                statement: render_alias_declaration(
                    bindings,
                    &aliases[visible_alias_count],
                    visible_alias_count,
                    &alias_indices,
                    &alias_names,
                ),
                reason: "display alias".to_string(),
                source_index: None,
            });
            visible_alias_count += 1;
        }

        displayed.push(DisplayedProofLine {
            statement: render_value_with_aliases(
                bindings,
                &line.value,
                &line.statement,
                &alias_indices,
                &alias_names[..visible_alias_count],
            ),
            reason: line.reason.description(),
            source_index: Some(source_index),
        });
    }

    displayed
}

#[cfg(test)]
mod tests {
    use super::display_certificate_lines;
    use crate::certificate::CertificateLine;
    use crate::elaborator::acorn_type::AcornType;
    use crate::elaborator::acorn_value::AcornValue;
    use crate::kernel::checker::StepReason;
    use crate::project::Project;

    #[test]
    fn test_display_certificate_lines_aliases_repeated_choose_terms() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem goal { true }\n");
        let module_id = project.expect_ok("main");
        let env = project.get_env_by_id(module_id).unwrap();

        let choose = AcornValue::choose(AcornType::Bool, AcornValue::Variable(0, AcornType::Bool));
        let lines = vec![
            CertificateLine {
                statement: format!("{} = true", choose),
                reason: StepReason::PreviousClaim,
                value: AcornValue::equals(choose.clone(), AcornValue::Bool(true)),
            },
            CertificateLine {
                statement: format!("not {}", choose),
                reason: StepReason::BooleanReduction(0),
                value: AcornValue::Not(Box::new(choose.clone())),
            },
        ];

        let displayed = display_certificate_lines(&env.bindings, &lines);

        assert_eq!(displayed.len(), 3);
        assert_eq!(displayed[0].statement, "let e1: Bool satisfy { e1 }");
        assert_eq!(displayed[0].reason, "display alias");
        assert_eq!(displayed[1].statement, "e1 = true");
        assert_eq!(displayed[1].reason, "previous claim");
        assert_eq!(displayed[2].statement, "not e1");
        assert_eq!(displayed[2].reason, "boolean reduction");
    }
}
