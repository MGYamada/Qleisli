# Remaining ordinary-library test observations

[Session](session.json), [source index](source-index.json), [terminal bindings](reports/terminal-bindings.json), [actual BEFORE projection](observations-before/remaining-normal.json), and [separate environment retry](observations-after/process-tree-environment.json) retain the actual source and diagnostic histories. See [scope](context.md).

The complete BEFORE [stdout](reports/remaining-normal.stdout.txt.gz), [stderr](reports/remaining-normal.stderr.txt.gz), [final driver](reports/remaining-normal.driver.json.gz), [started driver](reports/remaining-normal.started.json.gz), [exec-wrapper source](reports/remaining-normal.invocation.py.txt.gz), and [observer source](reports/root-observer.py.txt.gz) are lossless inert gzip files. Expanded hashes, lengths and complete per-failure byte ranges are recorded in the linked JSON; existing readers do not execute or decode them.

Semantic AFTER and latest CI are pending. Any later summary must be a separate actual-observation file rooted through this session, with command/compiler/kernel/input identity and the actual validation epoch. This record includes no reserved nonexistent file or invented result.
