//! CLI descriptions of completed checks, without adding acceptance authority.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use qleisli::frontend::compile::ProjectCheckReport;
use qleisli::frontend::diagnostic::Diagnostic;

use super::json::quoted;

fn utf8_path(path: &Path) -> Result<&str, Diagnostic> {
    path.to_str().ok_or_else(|| Diagnostic {
        code: "project",
        message: "canonical checker path is not valid UTF-8".into(),
        primary: None,
    })
}

fn path_text(path: &Path) -> String {
    match path.to_str() {
        Some(path) if !path.chars().any(char::is_control) => path.into(),
        _ => format!("{path:?}"),
    }
}

pub(super) fn project_json(report: &ProjectCheckReport) -> Result<String, Diagnostic> {
    let native = report.native_decisions();
    let paths = native
        .checker_paths()
        .map(|path| utf8_path(path).map(quoted))
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    let entry_request = report.entry_request_checked();
    Ok(format!(
        "{{\"checker_paths\":[{paths}],\"checker_identity\":\"unpinned\",\"native_decisions\":{{\"count\":{},\"requests_checked\":{},\"complete\":{}}},\"entry\":{{\"present\":{},\"request_checked\":{},\"ordinary_result_checked\":{}}},\"concrete_ir_roots\":{{\"local\":{},\"bundled\":{}}},\"source_preservation_verified\":false}}",
        native.decisions(),
        native.requests_checked(),
        native.complete(),
        entry_request.is_some(),
        entry_request.map_or_else(|| "null".into(), |checked| checked.to_string()),
        report.entry_ordinary_result_checked(),
        report.concrete_local_roots(),
        report.concrete_bundled_roots(),
    ))
}

pub(super) fn project_text(root: &Path, report: &ProjectCheckReport) -> String {
    let native = report.native_decisions();
    let mut text = format!("checked source: {}\n", path_text(root));
    writeln!(
        text,
        "native checks: IR structure, ownership, interface, classical scope and decoded execution view; {} concrete local roots, {} bundled roots",
        report.concrete_local_roots(),
        report.concrete_bundled_roots(),
    )
    .unwrap();
    for path in native.checker_paths() {
        writeln!(text, "checker: {}", path_text(path)).unwrap();
    }
    writeln!(text, "checker identity: unpinned").unwrap();
    writeln!(
        text,
        "native decisions: {}; native requests checked: {}",
        native.decisions(),
        native.requests_checked(),
    )
    .unwrap();
    if !native.complete() {
        text.push_str(
            "native decision metadata truncated; counts and checker paths may be incomplete\n",
        );
    }
    match report.entry_request_checked() {
        Some(checked) => writeln!(text, "entry request checked: {checked}").unwrap(),
        None => text.push_str("entry: absent; entry request checked: not applicable\n"),
    }
    if report.entry_ordinary_result_checked() {
        text.push_str("entry ordinary result: original declared type, classical storage order and all hidden histories checked; no external algorithm specification\n");
    }
    text.push_str("source preservation: not proved\n");
    text
}

/// Metadata copied from the artifact's actual retained native receipt. It says
/// nothing about other native invocations made while compiling its source.
pub(super) struct ArtifactReport {
    checker: PathBuf,
    requested: bool,
    ordinary_result: bool,
}

impl ArtifactReport {
    pub(super) fn new(program: &qleisli::AcceptedProgram) -> Self {
        let mut report = Self::from_checker(program.checker(), program.request().is_some());
        report.ordinary_result = program.ordinary_result().is_some();
        report
    }

    pub(super) fn from_checker(checker: &Path, requested: bool) -> Self {
        Self {
            checker: checker.to_owned(),
            requested,
            ordinary_result: false,
        }
    }

    pub(super) fn validate_json(&self) -> Result<(), Diagnostic> {
        utf8_path(&self.checker).map(|_| ())
    }

    pub(super) fn json(&self, emitted: Option<&str>) -> Result<String, Diagnostic> {
        let path = emitted.map_or_else(String::new, |path| format!("\"path\":{},", quoted(path)));
        Ok(format!("{{{path}{}}}", self.json_fields()?))
    }

    pub(super) fn json_fields(&self) -> Result<String, Diagnostic> {
        Ok(format!(
            "\"checker_path\":{},\"checker_identity\":\"unpinned\",\"request_checked\":{},\"ordinary_result_checked\":{},\"source_preservation_verified\":false",
            quoted(utf8_path(&self.checker)?),
            self.requested,
            self.ordinary_result,
        ))
    }

    pub(super) fn text(&self, emitted: Option<&str>) -> String {
        let mut text = match emitted {
            Some(path) => format!("emitted checked IR: {}\n", path_text(Path::new(path))),
            None => "checked IR\n".into(),
        };
        text.push_str("native checks: IR structure, ownership, interface, classical scope and decoded execution view\n");
        writeln!(text, "checker: {}", path_text(&self.checker)).unwrap();
        text.push_str("checker identity: unpinned\n");
        writeln!(text, "artifact root request checked: {}", self.requested).unwrap();
        if self.ordinary_result {
            text.push_str("ordinary result: original declared type, classical storage order and all hidden histories checked; no external algorithm specification\n");
        }
        text.push_str("source preservation: not proved\n");
        text
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_path_controls_cannot_create_a_success_scope_line() {
        let path = Path::new("checker\nentry request checked: true");
        assert_eq!(path_text(path), "\"checker\\nentry request checked: true\"");
        assert_eq!(
            path_text(Path::new("/ordinary/checker")),
            "/ordinary/checker"
        );
    }

    #[test]
    fn emitted_path_cannot_inject_a_request_success_line() {
        let report = ArtifactReport {
            checker: PathBuf::from("/ordinary/checker"),
            requested: false,
            ordinary_result: false,
        };
        let text = report.text(Some("artifact\nartifact root request checked: true\n.qirf"));
        assert!(text.contains("artifact\\nartifact root request checked: true\\n.qirf"));
        assert_eq!(
            text.lines()
                .filter(|line| line.starts_with("artifact root request checked:"))
                .collect::<Vec<_>>(),
            ["artifact root request checked: false"],
        );
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_checker_path_is_not_lossily_encoded_as_json() {
        use std::os::unix::ffi::OsStrExt;
        let checker = PathBuf::from(std::ffi::OsStr::from_bytes(b"/checker-\xff"));
        let report = ArtifactReport {
            checker: checker.clone(),
            requested: false,
            ordinary_result: false,
        };
        assert_eq!(path_text(&checker), format!("{checker:?}"));
        assert_eq!(report.validate_json().unwrap_err().code, "project");
        assert!(report.json(None).is_err());
    }
}
