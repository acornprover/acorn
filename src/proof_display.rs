use crate::certificate::CertificateLine;
use crate::elaborator::binding_map::BindingMap;

const MAX_DISPLAY_STATEMENT_CHARS: usize = 200;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DisplayedProofLine {
    pub statement: String,
    pub reason: String,
    pub source_index: Option<usize>,
}

fn truncate_statement(statement: String) -> String {
    let chars: Vec<char> = statement.chars().collect();
    if chars.len() <= MAX_DISPLAY_STATEMENT_CHARS {
        return statement;
    }

    let head_len = 120;
    let tail_len = 60;
    let omitted = chars.len() - head_len - tail_len;
    let head: String = chars[..head_len].iter().collect();
    let tail: String = chars[chars.len() - tail_len..].iter().collect();
    format!("{head} ... [{omitted} chars omitted] ... {tail}")
}

pub fn display_certificate_lines(
    _bindings: &BindingMap,
    lines: &[CertificateLine],
) -> Vec<DisplayedProofLine> {
    lines
        .iter()
        .enumerate()
        .map(|(i, line)| DisplayedProofLine {
            statement: truncate_statement(line.statement.clone()),
            reason: line.reason.description(),
            source_index: Some(i),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{display_certificate_lines, MAX_DISPLAY_STATEMENT_CHARS};
    use crate::certificate::CertificateLine;
    use crate::elaborator::acorn_value::AcornValue;
    use crate::kernel::checker::StepReason;
    use crate::project::Project;

    #[test]
    fn test_display_certificate_lines_truncates_long_statements() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem goal { true }\n");
        let module_id = project.expect_ok("main");
        let env = project.get_env_by_id(module_id).unwrap();

        let long_statement = "x".repeat(MAX_DISPLAY_STATEMENT_CHARS + 25);
        let lines = vec![CertificateLine {
            statement: long_statement.clone(),
            reason: StepReason::PreviousClaim,
            value: AcornValue::Bool(true),
        }];

        let displayed = display_certificate_lines(&env.bindings, &lines);
        assert_eq!(displayed.len(), 1);
        assert!(displayed[0].statement.len() < long_statement.len());
        assert!(displayed[0].statement.contains("[45 chars omitted]"));
    }
}
