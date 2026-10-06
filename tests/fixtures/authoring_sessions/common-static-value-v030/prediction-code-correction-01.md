# Unexecuted prediction spelling correction

The original context.json prediction used `type-mismatch` for the finite
diagnostic category. Direct review of Diagnostic::from_compile establishes
that the public snake_case category is `type_mismatch`; the test uses that
spelling. This corrects metadata only, before any check of these new sources.
It is not an observed output or a source repair. Original context.json, all
ten FIRST source/manifest files and first-files.json retain their exact bytes.
