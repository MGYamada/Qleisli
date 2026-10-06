# Authored Clippy repair: four saturating additions

The actual latest-attempt-08 Clippy stderr identified manual saturating arithmetic at original locals.rs lines 324, 330, 339 and 370. Its exact raw identity is retained in both maps. This packet preserves the complete original and repaired source, plus the exact patch.

Each replacement is mathematically identical for every usize value: checked_add(addend).unwrap_or(usize::MAX) returns the exact sum when representable and usize::MAX on overflow, exactly as saturating_add(addend). The statement child count still calls charge(statement.span, 1) before visitation/addition; all children, spans, task variants, limit checks and source order are unchanged. The separate chained runtime-call expression is untouched, as are all other files.

This is an author equivalence review, not independent review or a new Clippy/test result. No build, test, CLI, native, format, inventory, Git or source-fixture command was executed. Parent owns formatting and validation; original failed stage remains failed in its immutable logs.
