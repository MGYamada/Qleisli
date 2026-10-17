#!/usr/bin/env python3
"""Regressions for explicit historical/current source fixture selection.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import copy
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import current_source_fixtures as fixtures
from primitive_source_migration import OLD, migrate_qli, migrate_qli_current


class PrimitiveSourceMigration(unittest.TestCase):
    def translated(self, before, after):
        result = migrate_qli(before)
        self.assertEqual(result['issues'], [])
        self.assertEqual(result['source'], after)
        self.assertEqual(migrate_qli(after)['source'], after)

    def unchanged_refusal(self, source, message):
        result = migrate_qli(source)
        self.assertEqual(result['source'], source)
        self.assertEqual(result['edits'], [])
        self.assertTrue(any(message in issue for issue in result['issues']), result)

    def test_mixed_group_splits_only_actual_imports_and_renames_eighth(self):
        self.translated('use std::{quantum::{h,s,phase_eighth},observe::{reset,measure_z}};\nfn f(q:Q<Bit>)->Q<Bit>{phase_eighth(s(h(q)))}',
                        'use std::gate::s;\nuse std::state::reset;\nfn f(q:Q<Bit>)->Q<Bit>{global_phase_eighth(s(h(q)))}')

    def test_comment_quoted_text_and_crlf_are_not_spelling_rewrites(self):
        self.translated('// std::quantum::h\r\nuse std::quantum::h;\r\n/* phase_eighth /* nested */ */\r\n"std::quantum::h"\r\nfn f(q:Q<Bit>)->Q<Bit>{h(q)}',
                        '// std::quantum::h\r\n\r\n/* phase_eighth /* nested */ */\r\n"std::quantum::h"\r\nfn f(q:Q<Bit>)->Q<Bit>{h(q)}')

    def test_import_line_comment_cannot_swallow_following_function(self):
        self.translated('use std::quantum::{h // keep this\n};fn f(q:Q<Bit>)->Q<Bit>{h(q)}',
                        '// keep this\nfn f(q:Q<Bit>)->Q<Bit>{h(q)}')

    def test_empty_register_and_classical_paths_have_distinct_destinations(self):
        self.translated('use std::registers::{empty,consume_empty,take_bit,put_bit};use std::classical::{empty_bits,prepend_bit};',
                        'use std::structure::empty;\nuse std::structure::consume_empty;')

    def test_explicit_bit_and_product_basis_arguments_remain_exact(self):
        self.translated('use std::quantum::id;fn f(q:Q<(Unit,Bits<0>)>)->Q<(Unit,Bits<0>)>{id[type((Unit,Bits<0>))](q)}',
                        'use std::gate::id;fn f(q:Q<(Unit,Bits<0>)>)->Q<(Unit,Bits<0>)>{id[type((Unit,Bits<0>))](q)}')

    def test_id_cannot_gain_inferred_argument_or_provider_type(self):
        for source in ('use std::quantum::id;fn f(q:Q<Bit>)->Q<Bit>{id(q)}',
                       'use std::{gate::{id,t}};fn f(q:Q<Bit>)->Q<Bit>{power(id,0)(q)}'):
            self.unchanged_refusal(source, 'explicit Basis')

    def test_shadowed_renaming_and_import_conflicts_require_manual_review(self):
        for source in ('use std::quantum::phase_eighth;fn f(phase_eighth:Bit)->Bit{phase_eighth}',
                       'use std::quantum::phase_eighth;fn f(global_phase_eighth:Bit)->Bit{global_phase_eighth}',
                       'use std::quantum::phase_eighth;fn f((phase_eighth,x):(Bit,Bit))->Bit{x}',
                       'use std::quantum::phase_eighth;fn f(q:Q<Bit>)->Q<Bit>{with_computed(q,p){|global_phase_eighth| phase_eighth(global_phase_eighth)}}',
                       'use std::quantum::phase_eighth;fn f(q:Q<Bit>)->Q<Bit>{with_computed(q,p){|(x,phase_eighth)| x}}',
                       'use std::quantum::phase_eighth;fn f(q:Q<Bit>)->Q<Bit>{basis q as (phase_eighth,x) {x}}',
                       'use std::quantum::h;unitary fn h(q:Q<Bit>)->Q<Bit>{q}',
                       'use std::quantum::h;use other::h;'):
            result=migrate_qli(source)
            self.assertTrue(result['issues'])
            self.assertEqual(result['source'], source)

    def test_deliberate_alias_glob_qualified_and_unknown_negatives_are_not_repaired(self):
        for source, diagnostic in (
                ('use std::quantum::h as local;', 'alias'),
                ('use std::quantum::*;', 'glob'),
                ('fn f(q:Q<Bit>)->Q<Bit>{std::quantum::h(q)}', 'qualified'),
                ('use std::quantum::missing;', 'unknown retired'),
                ('use std::quantum::swap;', 'unknown retired')):
            self.unchanged_refusal(source, diagnostic)

    def test_catalog_is_the_exact_27_old_entries(self):
        self.assertEqual(len(OLD), 27)
        self.translated('use std::gate::swap;', 'use std::gate::swap;')

    def test_local_function_named_use_is_not_treated_as_an_import(self):
        self.translated('use std::quantum::h;fn use(q:Q<Bit>)->Q<Bit>{h(q)}',
                        'fn use(q:Q<Bit>)->Q<Bit>{h(q)}')



class CurrentPrimitiveLayout(unittest.TestCase):
    def test_only_erased_import_separators_at_line_end_are_removed(self):
        before = 'use std::quantum::init0; use std::observe::measure_z;\nfn f(){()}\n'
        lexical = migrate_qli(before)
        result = migrate_qli_current(before)
        self.assertEqual(lexical['source'], 'use std::state::init0; \nfn f(){()}\n')
        self.assertEqual(result['source'], 'use std::state::init0;\nfn f(){()}\n')
        self.assertEqual(result['edits'], lexical['edits'])
        self.assertEqual(result['layout_edits'], [(22, 23, '', 'removed-import separator')])
        self.assertEqual(migrate_qli_current(result['source'])['source'], result['source'])

    def test_comments_quoted_text_and_all_line_endings_are_preserved(self):
        before = ('// retained padding \r\nuse std::quantum::h; \r\n'
                  '"quoted trailing \t\ntext"\r'
                  '/* retained block \t\ncomment */\nfn f(){()} \n')
        result = migrate_qli_current(before)
        self.assertEqual(result['source'], before.replace('use std::quantum::h; ', ''))
        self.assertEqual(result['source'].count('\r'), before.count('\r'))
        self.assertEqual(result['source'].count('\n'), before.count('\n'))

    def test_adjacent_removals_clean_only_their_own_empty_line(self):
        before = '  use std::quantum::h; \tuse std::quantum::unit; \t\nfn f(){()}  \n\n'
        result = migrate_qli_current(before)
        self.assertEqual(result['source'], '\nfn f(){()}  \n\n')
        self.assertEqual(len(result['layout_edits']), 1)

    def test_import_adjacent_comments_and_nonterminal_gaps_stay_exact(self):
        for before in ('use std::quantum::h; \t// retained trailing \nfn f(){()}\n',
                       'use std::quantum::h; \tfn f(){()}\n'):
            self.assertEqual(migrate_qli_current(before)['source'], migrate_qli(before)['source'])

    def test_refused_source_has_no_layout_fallback(self):
        before = 'use std::quantum::unknown; \nfn f(){()}\n'
        result = migrate_qli_current(before)
        self.assertTrue(result['issues'])
        self.assertEqual(result['source'], before)
        self.assertEqual(result['layout_edits'], [])


class SourceFixtureIdentity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="qleisli-fixture-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.original = self.root / "historical"
        self.current = self.root / "current"
        self.manifest = self.root / "source-map.json"
        self.namespace_manifest = self.root / "namespace-source-map.json"
        self.coherent_manifest = self.root / "coherent-source-map.json"
        self.checked_manifest = self.root / "checked-source-map.json"
        self.classical_manifest = self.root / "classical-source-map.json"
        self.qfor_manifest = self.root / "qfor-source-map.json"
        self.client_const_manifest = self.root / "const-client-source-map.json"
        self.naming_manifest = self.root / "capability-naming-source-map.json"
        self.naming_manifest.write_text(json.dumps(dict(format="qleisli.capability-naming-source-map", version=1, files=[], projects=[])))
        self.isometry_manifest = self.root / "isometry-vocabulary-source-map.json"
        self.isometry_manifest.write_text(json.dumps(dict(format="qleisli.isometry-vocabulary-source-map", version=1, files=[], projects=[])))
        self.primitive_manifest = self.root / "language-primitive-source-map.json"
        self.primitive_manifest.write_text(json.dumps(dict(format="qleisli.language-primitive-source-map", version=1, files=[], projects=[])))
        self.public_effects_manifest = self.root / "public-effect-source-map.json"
        self.public_effects_manifest.write_text(json.dumps(dict(format="qleisli.public-effect-source-map", version=1, files=[], projects=[])))
        self.retired_manifest = self.root / "retired-operation-source-map.json"
        self.retired_manifest.write_text(json.dumps(dict(format="qleisli.retired-operation-source-map", version=1, files=[], projects=[])))
        self.client_const_manifest.write_text(json.dumps(dict(format="qleisli.const-client-source-map", version=1, files=[], projects=[])))
        self.application_manifest = self.root / "application-source-map.json"
        self.application_manifest.write_text(json.dumps(dict(format="qleisli.operation-application-source-map", version=1, files=[], projects=[])))
        self.const_manifest = self.root / "const-source-map.json"
        self.const_manifest.write_text(json.dumps(dict(format="qleisli.const-parameter-source-map", version=1, files=[], projects=[])))
        self.qfor_manifest.write_text(json.dumps(dict(format="qleisli.qfor-source-map", version=1, files=[], projects=[])))
        self.classical_manifest.write_text(json.dumps(dict(format="qleisli.classical-function-source-map", version=1, files=[], projects=[])))
        files = []
        for directory in (self.original, self.current):
            directory.mkdir()
            (directory / "Qargo.toml").write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')
            (directory / "main.qli").write_text(
                "observe fn main() -> " + ("CBit { false }" if directory == self.original else "Bit { 0 }"))
        for name in ("Qargo.toml", "main.qli"):
            files.append(dict(path=name, historical_sha256=self.sha(self.original / name),
                              current_sha256=self.sha(self.current / name)))
        self.entry = dict(historical_path="historical", current_path="current", files=files)
        self.write_map([self.entry])
        self.write_namespaces([])
        self.coherent_manifest.write_text(json.dumps(dict(
            format="qleisli.coherent-basis-source-map", version=1, files=[], projects=[])))
        self.write_checked_projects([])
        for name, value in (("ROOT", self.root), ("MAP", self.manifest),
                            ("NAMESPACE_MAP", self.namespace_manifest.name),
                            ("COHERENT_MAP", self.coherent_manifest.name),
                            ("CHECKED_MAP", self.checked_manifest.name),
                            ("CLASSICAL_MAP", self.classical_manifest.name),
                            ("QFOR_MAP", self.qfor_manifest.name),
                            ("CONST_MAP", self.const_manifest.name),
                            ("APPLICATION_MAP", self.application_manifest.name),
                            ("CLIENT_CONST_MAP", self.client_const_manifest.name),
                            ("RETIRED_OPERATION_MAP", self.retired_manifest.name),
                            ("CAPABILITY_NAMING_MAP", self.naming_manifest.name),
                            ("ISOMETRY_MAP", self.isometry_manifest.name),
                            ("PUBLIC_EFFECTS_MAP", self.public_effects_manifest.name),
                            ("PRIMITIVE_MAP", self.primitive_manifest.name)):
            patched = patch.object(fixtures, name, value)
            patched.start()
            self.addCleanup(patched.stop)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def write_map(self, entries):
        self.manifest.write_text(json.dumps(dict(projects=entries)))

    def write_namespaces(self, entries):
        self.namespace_manifest.write_text(json.dumps(dict(
            format="qleisli.semantic-namespace-source-map", version=1, files=[], projects=entries)))

    def write_checked_projects(self, entries):
        self.checked_manifest.write_text(json.dumps(dict(
            format="qleisli.checked-operation-source-map", version=1, files=[], projects=entries)))

    def namespace_entry(self):
        self.selected = self.root / "namespace-current"
        shutil.copytree(self.current, self.selected)
        (self.selected / "main.qli").write_text(
            "use std::transform::qft2; observe fn main() -> Bit { 0 }")
        entry = dict(before_path="current", current_path="namespace-current", files=[
            dict(path=name, before_sha256=self.sha(self.current / name),
                 current_sha256=self.sha(self.selected / name))
            for name in ("Qargo.toml", "main.qli")])
        self.write_namespaces([entry])
        return entry

    def checked_project_entry(self):
        self.namespace_entry()
        self.coherent = self.root / "coherent-current"
        shutil.copytree(self.selected, self.coherent)
        (self.coherent / "main.qli").write_text(
            "fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](basis q as x { not x }) }")
        coherent_entry = dict(before_path="namespace-current", current_path="coherent-current", files=[
            dict(path=name, before_sha256=self.sha(self.selected / name),
                 current_sha256=self.sha(self.coherent / name))
            for name in ("Qargo.toml", "main.qli")])
        self.coherent_manifest.write_text(json.dumps(dict(
            format="qleisli.coherent-basis-source-map", version=1,
            files=[], projects=[coherent_entry])))
        self.checked = self.root / "checked-current"
        shutil.copytree(self.coherent, self.checked)
        source = self.checked / "main.qli"
        source.write_text(source.read_text().replace("bind_op", "checked_op"))
        entry = dict(before_path="coherent-current", current_path="checked-current", files=[
            dict(path=name, before_sha256=self.sha(self.coherent / name),
                 current_sha256=self.sha(self.checked / name))
            for name in ("Qargo.toml", "main.qli")])
        self.write_checked_projects([entry])
        return entry

    def test_selects_only_recorded_current_source_and_keeps_original(self):
        before = (self.original / "main.qli").read_bytes()
        self.assertEqual(fixtures.current_source_fixture(self.original), self.current)
        self.assertEqual((self.original / "main.qli").read_bytes(), before)
        self.assertEqual(fixtures.source_hashes(self.current), {
            file["path"]: file["current_sha256"] for file in self.entry["files"]})

    def public_effect_project(self):
        for directory in (self.original, self.current):
            (directory / "main.qli").write_text("pub fn f(q:Q<Bit>)->Q<Bit>{q}\n")
        for file in self.entry["files"]:
            file["historical_sha256"] = self.sha(self.original / file["path"])
            file["current_sha256"] = self.sha(self.current / file["path"])
        self.write_map([self.entry])
        selected = self.root / "public-effect-current"
        shutil.copytree(self.current, selected)
        source = selected / "main.qli"
        source.write_bytes(source.read_bytes().replace(b"pub fn f", b"pub unitary fn f"))
        entry = dict(before_path="current", current_path=selected.name, files=[
            dict(path=name, before_sha256=self.sha(self.current / name),
                 current_sha256=self.sha(selected / name))
            for name in ("Qargo.toml", "main.qli")])
        self.public_effects_manifest.write_text(json.dumps(dict(
            format="qleisli.public-effect-source-map", version=1,
            projects=[entry], files=[])))
        return selected

    def test_public_effect_project_preserves_original_and_complete_final_inputs(self):
        selected = self.public_effect_project()
        original = (self.original / "main.qli").read_bytes()
        self.assertEqual(fixtures.current_source_fixture(self.original), selected)
        self.assertEqual((self.original / "main.qli").read_bytes(), original)
        for directory in (self.original, self.current, selected):
            for name in ("main.qli", "Qargo.toml"):
                with self.subTest(directory=directory.name, file=name):
                    path = directory / name
                    before = path.read_bytes()
                    path.write_bytes(before + b"\nchanged")
                    try:
                        with self.assertRaisesRegex(ValueError, "identity changed"):
                            fixtures.current_source_fixture(self.original)
                    finally:
                        path.write_bytes(before)
        for directory in (self.current, selected):
            extra = directory / "unexpected.qli"
            extra.write_text("pub unitary fn unexpected()->Unit{()}")
            try:
                with self.assertRaisesRegex(ValueError, "identity changed"):
                    fixtures.current_source_fixture(self.original)
            finally:
                extra.unlink()

    def test_missing_public_effect_project_stage_has_no_previous_project_fallback(self):
        self.public_effect_project()
        self.public_effects_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing public effect source map"):
            fixtures.current_source_fixture(self.original)

    def test_stale_original_rejects(self):
        (self.original / "main.qli").write_text("changed historical source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_stale_derivative_rejects(self):
        (self.current / "main.qli").write_text("changed current source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_extra_source_or_manifest_rejects_in_either_snapshot(self):
        for directory in (self.original, self.current):
            for name in ("unused.qli", "nested/Qargo.toml"):
                with self.subTest(directory=directory.name, file=name):
                    extra = directory / name
                    extra.parent.mkdir(exist_ok=True)
                    extra.write_text("unexpected project input")
                    try:
                        with self.assertRaisesRegex(ValueError, "identity changed"):
                            fixtures.current_source_fixture(self.original)
                    finally:
                        extra.unlink()

    def test_missing_source_or_manifest_rejects_in_either_snapshot(self):
        for directory in (self.original, self.current):
            for name in ("main.qli", "Qargo.toml"):
                with self.subTest(directory=directory.name, file=name):
                    missing = directory / name
                    original = missing.read_bytes()
                    missing.unlink()
                    try:
                        with self.assertRaisesRegex(ValueError, "identity changed"):
                            fixtures.current_source_fixture(self.original)
                    finally:
                        missing.write_bytes(original)

    def test_missing_or_duplicate_project_mapping_rejects(self):
        for entries in ([], [self.entry, self.entry]):
            with self.subTest(entries=len(entries)):
                self.write_map(entries)
                with self.assertRaisesRegex(ValueError, "missing or duplicate"):
                    fixtures.current_source_fixture(self.original)

    def test_namespace_selection_checks_both_links_and_preserves_predecessors(self):
        entry = self.namespace_entry()
        original = (self.original / "main.qli").read_bytes()
        current = (self.current / "main.qli").read_bytes()
        self.assertEqual(fixtures.current_source_fixture(self.original), self.selected)
        self.assertEqual((self.original / "main.qli").read_bytes(), original)
        self.assertEqual((self.current / "main.qli").read_bytes(), current)
        self.assertEqual(fixtures.source_hashes(self.selected), {
            file["path"]: file["current_sha256"] for file in entry["files"]})

    def test_missing_namespace_map_rejects_without_previous_source_fallback(self):
        self.namespace_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing semantic namespace source map"):
            fixtures.current_source_fixture(self.original)

    def test_missing_coherent_map_rejects_without_previous_project_fallback(self):
        self.coherent_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing coherent basis source map"):
            fixtures.current_source_fixture(self.original)

    def test_missing_checked_map_rejects_without_previous_project_fallback(self):
        self.checked_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing checked operation source map"):
            fixtures.current_source_fixture(self.original)

    def test_checked_project_chain_preserves_every_predecessor_and_complete_inventory(self):
        entry = self.checked_project_entry()
        before = {path: fixtures.source_hashes(path)
                  for path in (self.original, self.current, self.selected, self.coherent)}
        self.assertEqual(fixtures.current_source_fixture(self.original), self.checked)
        self.assertEqual({path: fixtures.source_hashes(path) for path in before}, before)
        self.assertEqual(fixtures.source_hashes(self.checked), {
            file["path"]: file["current_sha256"] for file in entry["files"]})

    def test_checked_map_cannot_hide_changed_coherent_project_predecessor(self):
        entry = self.checked_project_entry()
        source = self.coherent / "main.qli"
        source.write_text("changed predecessor")
        entry["files"][1]["before_sha256"] = self.sha(source)
        self.write_checked_projects([entry])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_checked_project_rejects_missing_extra_and_stale_final_inputs(self):
        self.checked_project_entry()
        source = self.checked / "main.qli"
        original = source.read_bytes()
        for change in ("missing", "stale", "extra"):
            with self.subTest(change=change):
                if change == "missing":
                    source.unlink()
                elif change == "stale":
                    source.write_text("stale final source")
                else:
                    (self.checked / "unexpected.qli").write_text("extra input")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    source.write_bytes(original)
                    (self.checked / "unexpected.qli").unlink(missing_ok=True)

    def test_checked_project_symlink_cannot_escape_snapshot(self):
        self.checked_project_entry()
        source = self.checked / "main.qli"
        source.unlink()
        source.symlink_to(self.coherent / "main.qli")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_fixture(self.original)

    def test_unmapped_current_project_keeps_previous_selection(self):
        entry = self.namespace_entry()
        shutil.copytree(self.current, self.root / "other-current")
        entry["before_path"] = "other-current"
        self.write_namespaces([entry])
        self.assertEqual(fixtures.current_source_fixture(self.original), self.current)

    def test_namespace_cannot_hide_changed_original_or_prior_current(self):
        entry = self.namespace_entry()
        for directory in (self.original, self.current):
            with self.subTest(directory=directory.name):
                source = directory / "main.qli"
                before = source.read_bytes()
                source.write_text("changed previous source")
                if directory == self.current:
                    entry["files"][1]["before_sha256"] = self.sha(source)
                    self.write_namespaces([entry])
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    source.write_bytes(before)

    def test_namespace_stale_before_hash_or_final_source_rejects(self):
        entry = self.namespace_entry()
        stale = copy.deepcopy(entry)
        stale["files"][1]["before_sha256"] = "0" * 64
        self.write_namespaces([stale])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)
        self.write_namespaces([entry])
        (self.selected / "main.qli").write_text("changed final source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_namespace_extra_source_or_manifest_rejects(self):
        self.namespace_entry()
        for name in ("unused.qli", "nested/Qargo.toml"):
            with self.subTest(file=name):
                extra = self.selected / name
                extra.parent.mkdir(exist_ok=True)
                extra.write_text("unrecorded selected input")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    extra.unlink()

    def test_namespace_missing_source_or_manifest_rejects(self):
        self.namespace_entry()
        for name in ("main.qli", "Qargo.toml"):
            with self.subTest(file=name):
                missing = self.selected / name
                before = missing.read_bytes()
                missing.unlink()
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    missing.write_bytes(before)

    def test_namespace_partial_recorded_inventory_rejects(self):
        entry = self.namespace_entry()
        entry["files"].pop()
        self.write_namespaces([entry])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_namespace_duplicate_predecessor_or_destination_rejects(self):
        entry = self.namespace_entry()
        for other_before in ("current", "other-current"):
            with self.subTest(before=other_before):
                other = dict(entry, before_path=other_before)
                self.write_namespaces([entry, other])
                with self.assertRaisesRegex(ValueError, "duplicate namespace"):
                    fixtures.current_source_fixture(self.original)

    def test_duplicate_inventory_paths_reject_at_either_link(self):
        entry = self.namespace_entry()
        for prior in (True, False):
            with self.subTest(prior=prior):
                changed = copy.deepcopy(self.entry if prior else entry)
                changed["files"].append(changed["files"][0])
                self.write_map([changed if prior else self.entry])
                self.write_namespaces([entry if prior else changed])
                with self.assertRaisesRegex(ValueError, "duplicate source fixture file"):
                    fixtures.current_source_fixture(self.original)

    def test_unmapped_namespace_metadata_cannot_hide_duplicate_or_escaping_files(self):
        entry = self.namespace_entry()
        entry["before_path"] = "unselected-current"
        for escaping in (False, True):
            with self.subTest(escaping=escaping):
                changed = copy.deepcopy(entry)
                if escaping:
                    changed["files"][0]["path"] = "../outside.qli"
                else:
                    changed["files"].append(changed["files"][0])
                self.write_namespaces([changed])
                with self.assertRaises(ValueError):
                    fixtures.current_source_fixture(self.original)

    def test_escaping_project_paths_reject_at_either_link(self):
        entry = self.namespace_entry()
        for prior, field in ((True, "historical_path"), (True, "current_path"),
                             (False, "before_path"), (False, "current_path")):
            for escaping in ("../outside", str(self.root.parent / "outside")):
                with self.subTest(prior=prior, field=field, path=escaping):
                    changed = copy.deepcopy(self.entry if prior else entry)
                    changed[field] = escaping
                    self.write_map([changed if prior else self.entry])
                    self.write_namespaces([entry if prior else changed])
                    with self.assertRaisesRegex(ValueError, "escaping"):
                        fixtures.current_source_fixture(self.original)

    def test_escaping_file_paths_reject_at_either_link(self):
        entry = self.namespace_entry()
        for prior in (True, False):
            changed = copy.deepcopy(self.entry if prior else entry)
            changed["files"][0]["path"] = "../escape.qli"
            self.write_map([changed if prior else self.entry])
            self.write_namespaces([entry if prior else changed])
            with self.subTest(prior=prior), self.assertRaisesRegex(ValueError, "escaping"):
                fixtures.current_source_fixture(self.original)

    def test_project_or_source_symlink_cannot_escape_its_snapshot(self):
        entry = self.namespace_entry()
        external = tempfile.TemporaryDirectory(prefix="qleisli-fixture-outside-")
        self.addCleanup(external.cleanup)
        (self.root / "escaped-project").symlink_to(external.name, target_is_directory=True)
        self.write_namespaces([dict(entry, current_path="escaped-project")])
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_fixture(self.original)
        self.write_namespaces([entry])
        source = self.selected / "main.qli"
        source.unlink()
        source.symlink_to(self.current / "main.qli")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_fixture(self.original)

    def test_duplicate_json_fields_and_wrong_namespace_schema_reject(self):
        self.namespace_entry()
        self.namespace_manifest.write_text('{"projects": [], "projects": []}')
        with self.assertRaisesRegex(ValueError, "duplicate source migration JSON field"):
            fixtures.current_source_fixture(self.original)
        self.namespace_manifest.write_text(json.dumps(dict(
            format="other-source-map", version=1, projects=[])))
        with self.assertRaisesRegex(ValueError, "invalid semantic namespace"):
            fixtures.current_source_fixture(self.original)


    def test_project_selector_checks_all_links_from_any_registered_root(self):
        self.checked_project_entry()
        for path in (self.original, self.current, self.selected, self.coherent, self.checked):
            self.assertEqual(fixtures.current_source_project(path), self.checked)
            self.assertEqual(fixtures.current_source_project(path.relative_to(self.root)), self.checked)
        old = (self.original / "main.qli").read_bytes()
        (self.original / "main.qli").write_bytes(old + b"\nchanged")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_project(self.checked)

    def test_project_selector_checks_complete_source_inventory_at_each_link(self):
        self.checked_project_entry()
        for project in (self.original, self.current, self.selected, self.coherent, self.checked):
            added = project / "unused.qli"
            added.write_text("unitary fn unused()->Unit{()}")
            try:
                with self.assertRaisesRegex(ValueError, "identity changed"):
                    fixtures.current_source_project(self.checked)
            finally:
                added.unlink()

    def test_project_selector_requires_registered_roots_not_arbitrary_directories(self):
        unknown = self.root / "unregistered"
        unknown.mkdir()
        (unknown / "main.qli").write_text("unitary fn f()->Unit{()}")
        with self.assertRaisesRegex(ValueError, "unregistered source project"):
            fixtures.current_source_project(unknown)
        with self.assertRaisesRegex(ValueError, "unregistered source project"):
            fixtures.current_source_project(self.current / "main.qli")

    def test_project_selector_follows_a_new_final_stage_from_a_registered_current_root(self):
        selected = self.public_effect_project()
        final = self.root / "primitive-current"
        shutil.copytree(selected, final)
        entry = dict(before_path=selected.name, current_path=final.name, files=[
            dict(path=name, before_sha256=self.sha(selected / name),
                 current_sha256=self.sha(final / name)) for name in ("main.qli", "Qargo.toml")])
        self.primitive_manifest.write_text(json.dumps(dict(
            format="qleisli.language-primitive-source-map", version=1, files=[], projects=[entry])))
        self.assertEqual(fixtures.current_source_project(final), final)
        self.assertEqual(fixtures.current_source_fixture(self.original), final)
        original = (selected / "main.qli").read_bytes()
        (selected / "main.qli").write_bytes(original + b"\nchanged")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_project(final)

    def test_project_selector_rejects_duplicate_and_backwards_chain_links(self):
        entry = self.namespace_entry()
        for before, current in (("current", "different"), (entry["current_path"], "historical")):
            changed = dict(entry, before_path=before, current_path=current)
            self.primitive_manifest.write_text(json.dumps(dict(
                format="qleisli.language-primitive-source-map", version=1,
                files=[], projects=[changed])))
            with self.assertRaisesRegex(ValueError, "ambiguous|unordered|cyclic"):
                fixtures.current_source_project(self.selected)


class SourceFileIdentity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="qleisli-file-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.original = self.root / "original.qli"
        self.namespace = self.root / "namespace.qli"
        self.coherent = self.root / "coherent.qli"
        self.current = self.root / "checked.qli"
        self.original.write_text("use std::routines::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](do x <- q; pure not x) }")
        self.namespace.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](do x <- q; pure not x) }")
        self.coherent.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](basis q as x { not x }) }")
        self.current.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[checked_op(u,m)](basis q as x { not x }) }")
        self.namespace_manifest = self.root / "namespace-map.json"
        self.coherent_manifest = self.root / "coherent-map.json"
        self.checked_manifest = self.root / "checked-map.json"
        self.classical_manifest = self.root / "classical-map.json"
        self.qfor_manifest = self.root / "qfor-map.json"
        self.client_const_manifest = self.root / "const-client-source-map.json"
        self.naming_manifest = self.root / "capability-naming-source-map.json"
        self.naming_manifest.write_text(json.dumps(dict(format="qleisli.capability-naming-source-map", version=1, files=[], projects=[])))
        self.isometry_manifest = self.root / "isometry-vocabulary-source-map.json"
        self.isometry_manifest.write_text(json.dumps(dict(format="qleisli.isometry-vocabulary-source-map", version=1, files=[], projects=[])))
        self.primitive_manifest = self.root / "language-primitive-source-map.json"
        self.primitive_manifest.write_text(json.dumps(dict(format="qleisli.language-primitive-source-map", version=1, files=[], projects=[])))
        self.public_effects_manifest = self.root / "public-effect-source-map.json"
        self.public_effects_manifest.write_text(json.dumps(dict(format="qleisli.public-effect-source-map", version=1, files=[], projects=[])))
        self.retired_manifest = self.root / "retired-operation-source-map.json"
        self.retired_manifest.write_text(json.dumps(dict(format="qleisli.retired-operation-source-map", version=1, files=[], projects=[])))
        self.client_const_manifest.write_text(json.dumps(dict(format="qleisli.const-client-source-map", version=1, files=[], projects=[])))
        self.application_manifest = self.root / "application-source-map.json"
        self.application_manifest.write_text(json.dumps(dict(format="qleisli.operation-application-source-map", version=1, files=[], projects=[])))
        self.const_manifest = self.root / "const-source-map.json"
        self.const_manifest.write_text(json.dumps(dict(format="qleisli.const-parameter-source-map", version=1, files=[], projects=[])))
        self.qfor_manifest.write_text(json.dumps(dict(format="qleisli.qfor-source-map", version=1, files=[], projects=[])))
        self.classical_manifest.write_text(json.dumps(dict(format="qleisli.classical-function-source-map", version=1, files=[], projects=[])))
        self.namespace_entry = self.entry(self.original, self.namespace)
        self.coherent_entry = self.entry(self.namespace, self.coherent)
        self.checked_entry = self.entry(self.coherent, self.current)
        self.write_maps()
        for name, value in (("ROOT", self.root),
                            ("NAMESPACE_MAP", self.namespace_manifest.name),
                            ("COHERENT_MAP", self.coherent_manifest.name),
                            ("CHECKED_MAP", self.checked_manifest.name),
                            ("CLASSICAL_MAP", self.classical_manifest.name),
                            ("QFOR_MAP", self.qfor_manifest.name),
                            ("CONST_MAP", self.const_manifest.name),
                            ("APPLICATION_MAP", self.application_manifest.name),
                            ("CLIENT_CONST_MAP", self.client_const_manifest.name),
                            ("RETIRED_OPERATION_MAP", self.retired_manifest.name),
                            ("CAPABILITY_NAMING_MAP", self.naming_manifest.name),
                            ("ISOMETRY_MAP", self.isometry_manifest.name),
                            ("PUBLIC_EFFECTS_MAP", self.public_effects_manifest.name),
                            ("PRIMITIVE_MAP", self.primitive_manifest.name)):
            patched = patch.object(fixtures, name, value)
            patched.start()
            self.addCleanup(patched.stop)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def entry(self, before, current):
        return dict(before_path=before.relative_to(self.root).as_posix(),
                    current_path=current.relative_to(self.root).as_posix(),
                    before_sha256=self.sha(before), current_sha256=self.sha(current))

    def write_maps(self, namespace=None, coherent=None, checked=None):
        for path, format_name, entries in (
                (self.namespace_manifest, "qleisli.semantic-namespace-source-map",
                 [self.namespace_entry] if namespace is None else namespace),
                (self.coherent_manifest, "qleisli.coherent-basis-source-map",
                 [self.coherent_entry] if coherent is None else coherent),
                (self.checked_manifest, "qleisli.checked-operation-source-map",
                 [self.checked_entry] if checked is None else checked)):
            path.write_text(json.dumps(dict(format=format_name, version=1,
                                           files=entries, projects=[])))

    def public_effect_file(self):
        for path in (self.original, self.namespace, self.coherent, self.current):
            path.write_bytes(path.read_bytes().replace(b"fn f(", b"pub fn f("))
        self.namespace_entry = self.entry(self.original, self.namespace)
        self.coherent_entry = self.entry(self.namespace, self.coherent)
        self.checked_entry = self.entry(self.coherent, self.current)
        self.write_maps()
        selected = self.root / "public-effect.qli"
        selected.write_bytes(self.current.read_bytes().replace(
            b"pub fn f", b"pub unitary fn f"))
        entry = self.entry(self.current, selected)
        self.public_effects_manifest.write_text(json.dumps(dict(
            format="qleisli.public-effect-source-map", version=1,
            files=[entry], projects=[])))
        return selected, entry

    def test_public_effect_file_checks_every_predecessor_and_final_identity(self):
        selected, _ = self.public_effect_file()
        paths = (self.original, self.namespace, self.coherent, self.current, selected)
        originals = {path: path.read_bytes() for path in paths}
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        for path in paths:
            with self.subTest(source=path.name):
                path.write_bytes(originals[path] + b"\nchanged")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_file(self.original)
                finally:
                    path.write_bytes(originals[path])
        self.assertEqual({path: path.read_bytes() for path in paths}, originals)

    def test_missing_public_effect_file_stage_has_no_unannotated_fallback(self):
        self.public_effect_file()
        self.public_effects_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing public effect source map"):
            fixtures.current_source_file(self.original)

    def test_public_effect_stage_rejects_duplicate_hash_and_escaping_records(self):
        _, entry = self.public_effect_file()
        for mutation in ("duplicate", "before_sha256", "current_sha256", "before_path", "current_path"):
            with self.subTest(mutation=mutation):
                changed = dict(entry)
                if mutation.endswith("_sha256"):
                    changed[mutation] = "not-a-sha256"
                elif mutation.endswith("_path"):
                    changed[mutation] = "../escape.qli"
                entries = [entry, changed] if mutation == "duplicate" else [changed]
                self.public_effects_manifest.write_text(json.dumps(dict(
                    format="qleisli.public-effect-source-map", version=1,
                    files=entries, projects=[])))
                with self.assertRaises(ValueError):
                    fixtures.current_source_file(self.original)

    def test_complete_file_chain_keeps_all_predecessors(self):
        originals = {path: path.read_bytes() for path in (self.original, self.namespace, self.coherent)}
        self.assertEqual(fixtures.current_source_file(self.original), self.current)
        self.assertEqual(fixtures.current_source_file(self.original.name), self.current)
        self.assertEqual(fixtures.current_source_file(self.namespace), self.current)
        self.assertEqual(fixtures.current_source_file(self.coherent), self.current)
        self.assertEqual({path: path.read_bytes() for path in originals}, originals)

    def test_missing_const_client_stage_has_no_previous_source_fallback(self):
        self.client_const_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing const client source map"):
            fixtures.current_source_file(self.original)

    def test_isometry_stage_preserves_history_and_rejects_stale_sources(self):
        predecessors = {path: path.read_bytes() for path in
                        (self.original, self.namespace, self.coherent, self.current)}
        selected = self.root / "isometry-current.qli"
        selected.write_text("isometry fn prepare()->Q<Bit>{init0()}")
        self.isometry_manifest.write_text(json.dumps(dict(
            format="qleisli.isometry-vocabulary-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual({path: path.read_bytes() for path in predecessors}, predecessors)
        for source in (self.current, selected):
            with self.subTest(source=source.name):
                original = source.read_bytes()
                source.write_text("changed isometry migration input")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_file(self.original)
                finally:
                    source.write_bytes(original)

    def test_missing_isometry_stage_has_no_legacy_source_fallback(self):
        self.isometry_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing isometry vocabulary source map"):
            fixtures.current_source_file(self.original)

    def test_unmapped_file_is_returned_unchanged(self):
        source = self.root / "unmapped.qli"
        source.write_text("fn identity(q: Q<Bit>) -> Q<Bit> { q }")
        original = source.read_bytes()
        self.assertEqual(fixtures.current_source_file(source), source)
        self.assertEqual(source.read_bytes(), original)

    def test_classical_file_stage_preserves_every_previous_source(self):
        before = {path: path.read_bytes() for path in
                  (self.original, self.namespace, self.coherent, self.current)}
        selected = self.root / "classical-current.qli"
        selected.write_text("classical fn flip(b: Bit) -> Bit { not b }")
        entry = self.entry(self.current, selected)
        self.classical_manifest.write_text(json.dumps(dict(
            format="qleisli.classical-function-source-map", version=1,
            files=[entry], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual({path: path.read_bytes() for path in before}, before)
        selected.write_text("changed classical function")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_classical_stage_has_no_old_spelling_fallback(self):
        self.classical_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing classical function source map"):
            fixtures.current_source_file(self.original)

    def test_quantum_fold_stage_preserves_history_and_rejects_stale_final_source(self):
        before = {path: path.read_bytes() for path in
                  (self.original, self.namespace, self.coherent, self.current)}
        selected = self.root / "qfor-current.qli"
        selected.write_text("fn f(q: Q<Bit>) -> Q<Bit> { qfor static i in 0..0 carry a=q { yield a; } }")
        self.qfor_manifest.write_text(json.dumps(dict(
            format="qleisli.qfor-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual({path: path.read_bytes() for path in before}, before)
        selected.write_text("stale quantum fold source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_quantum_fold_stage_has_no_previous_source_fallback(self):
        self.qfor_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing quantum fold source map"):
            fixtures.current_source_file(self.original)

    def test_const_stage_retains_history_and_rejects_stale_sources(self):
        before = self.current.read_bytes()
        selected = self.root / "const-current.qli"
        selected.write_text("fn identity[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { q }")
        self.const_manifest.write_text(json.dumps(dict(
            format="qleisli.const-parameter-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual(self.current.read_bytes(), before)
        selected.write_text("stale const source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_const_stage_has_no_previous_source_fallback(self):
        self.const_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing const parameter source map"):
            fixtures.current_source_file(self.original)

    def test_application_stage_rejects_stale_final_source(self):
        original = self.current.read_bytes()
        selected = self.root / "application-current.qli"
        selected.write_text("unitary fn f(q: Q<Bit>) -> Q<Bit> { inverse(f)(q) }")
        self.application_manifest.write_text(json.dumps(dict(
            format="qleisli.operation-application-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual(self.current.read_bytes(), original)
        selected.write_text("stale application source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_application_stage_has_no_previous_source_fallback(self):
        self.application_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing operation application source map"):
            fixtures.current_source_file(self.original)

    def test_classical_stage_cannot_hide_stale_checked_predecessor(self):
        selected = self.root / "classical-current.qli"
        selected.write_text("classical fn flip(b: Bit) -> Bit { not b }")
        self.current.write_text("changed checked predecessor")
        self.classical_manifest.write_text(json.dumps(dict(
            format="qleisli.classical-function-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_all_file_maps_are_required_even_for_unmapped_input(self):
        for path, label in ((self.namespace_manifest, "semantic namespace"),
                            (self.coherent_manifest, "coherent basis"),
                            (self.checked_manifest, "checked operation")):
            with self.subTest(map=label):
                data = path.read_bytes()
                path.unlink()
                try:
                    with self.assertRaisesRegex(ValueError, f"missing {label} source map"):
                        fixtures.current_source_file(self.current)
                finally:
                    path.write_bytes(data)

    def test_stale_bytes_reject_at_every_selected_link(self):
        for path in (self.original, self.namespace, self.coherent, self.current):
            with self.subTest(source=path.name):
                original = path.read_bytes()
                path.write_text("changed source")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_file(self.original)
                finally:
                    path.write_bytes(original)

    def test_later_map_cannot_hide_changed_namespace_predecessor(self):
        self.namespace.write_text("changed predecessor")
        changed = dict(self.coherent_entry, before_sha256=self.sha(self.namespace))
        self.write_maps(coherent=[changed])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_checked_map_cannot_hide_changed_coherent_predecessor(self):
        self.coherent.write_text("changed predecessor")
        changed = dict(self.checked_entry, before_sha256=self.sha(self.coherent))
        self.write_maps(checked=[changed])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_selected_source_rejects(self):
        self.current.unlink()
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_duplicate_before_or_destination_rejects_in_every_map(self):
        for label, entry in (("namespace", self.namespace_entry),
                             ("coherent", self.coherent_entry), ("checked", self.checked_entry)):
            for field in ("before_path", "current_path"):
                with self.subTest(map=label, duplicate=field):
                    other = dict(entry)
                    other["current_path" if field == "before_path" else "before_path"] = "other.qli"
                    kwargs = {label: [entry, other]}
                    self.write_maps(**kwargs)
                    with self.assertRaisesRegex(ValueError, "duplicate.*source file migration"):
                        fixtures.current_source_file(self.original)
                    self.write_maps()

    def test_file_entries_require_exact_fields_hashes_and_source_extensions(self):
        changes = [dict(self.coherent_entry, unknown=True)]
        for field in ("before_sha256", "current_sha256"):
            changes.extend(dict(self.coherent_entry, **{field: value})
                           for value in (None, "0" * 63, "A" * 64))
        for field in ("before_path", "current_path"):
            changes.append(dict(self.coherent_entry, **{field: "source.txt"}))
        for changed in changes:
            with self.subTest(entry=changed):
                self.write_maps(coherent=[changed])
                with self.assertRaises(ValueError):
                    fixtures.current_source_file(self.original)

    def test_escaping_and_noncanonical_file_paths_reject_even_if_unmapped(self):
        for field in ("before_path", "current_path"):
            for path in ("../outside.qli", str(self.root / "absolute.qli"),
                         "nested//source.qli", "./source.qli", "nested/../source.qli"):
                with self.subTest(field=field, path=path):
                    changed = dict(self.coherent_entry, before_path="unmapped.qli")
                    changed[field] = path
                    self.write_maps(coherent=[changed])
                    with self.assertRaisesRegex(ValueError, "escaping|noncanonical"):
                        fixtures.current_source_file(self.original)

    def test_file_or_map_symlink_cannot_escape_root(self):
        external = tempfile.TemporaryDirectory(prefix="qleisli-file-outside-")
        self.addCleanup(external.cleanup)
        outside = Path(external.name)
        (outside / "source.qli").write_text("outside source")
        self.current.unlink()
        self.current.symlink_to(outside / "source.qli")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)
        self.current.unlink()
        self.current.write_text("current source")
        self.checked_manifest.unlink()
        self.checked_manifest.symlink_to(outside / "map.json")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)

    def test_map_identity_and_duplicate_json_fields_reject(self):
        for path in (self.namespace_manifest, self.coherent_manifest, self.checked_manifest):
            original = path.read_text()
            for invalid in (original.replace('"version": 1', '"version": true'),
                            original.replace('"version": 1', '"version": 2'),
                            original.replace('"format": "qleisli.', '"format": "wrong.'),
                            original.replace('"before_sha256":', '"current_sha256":', 1)):
                with self.subTest(map=path.name, data=invalid):
                    path.write_text(invalid)
                    with self.assertRaises(ValueError):
                        fixtures.current_source_file(self.original)
            path.write_text(original)

    def test_malformed_json_or_missing_map_inventories_reject(self):
        for path in (self.namespace_manifest, self.coherent_manifest, self.checked_manifest):
            original = path.read_text()
            for invalid in ("not JSON", "[]", "{}", original.replace('"files": [', '"omitted": [')):
                with self.subTest(map=path.name, data=invalid):
                    path.write_text(invalid)
                    with self.assertRaises(ValueError):
                        fixtures.current_source_file(self.original)
            path.write_text(original)

    def test_unselected_project_metadata_is_not_ignored_by_file_selection(self):
        data = json.loads(self.checked_manifest.read_text())
        data["projects"] = [dict(before_path="unselected", current_path="../outside", files=[])]
        self.checked_manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)


    def test_language_primitive_map_is_required_even_for_unmapped_source(self):
        self.primitive_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing language primitive source map"):
            fixtures.current_source_file(self.current)


class RepositoryMigrationTests(unittest.TestCase):
    def test_primitive_derivatives_replay_only_recorded_lexical_and_explicit_type_edits(self):
        from primitive_source_migration import migrate_qli, migrate_qli_current
        directory = fixtures.ROOT / "tests/fixtures/frontend_v030/language-primitives"
        mapping = fixtures._read_map(directory / "source-map.json")
        entries = fixtures._file_entries(mapping, "language primitive")
        review = json.loads((directory / "translation-review.json").read_text())
        self.assertEqual(review["status"], "generated-unvalidated")
        self.assertEqual(review["layout_revision"], 5)
        self.assertEqual(review["layout_helper"]["sha256"], hashlib.sha256(
            (fixtures.ROOT / review["layout_helper"]["path"]).read_bytes()).hexdigest())
        self.assertEqual({r["before_path"] for r in review["files"]}, set(entries))
        expected = set()
        for row in review["files"]:
            before, current = (fixtures.ROOT / row[key] for key in ("before_path", "current_path"))
            self.assertEqual(row["before_sha256"], hashlib.sha256(before.read_bytes()).hexdigest())
            self.assertEqual(row["current_sha256"], hashlib.sha256(current.read_bytes()).hexdigest())
            text = before.read_bytes().decode("utf-8")
            for edit in row["manual_edits"]:
                self.assertEqual(edit["before"], "id(q)")
                self.assertEqual(edit["after"], "id[type(Bit)](q)")
                self.assertEqual(text.count(edit["before"]), 1)
                text = text.replace(edit["before"], edit["after"])
            lexical = migrate_qli(text)
            self.assertEqual(row["lexical_sha256"], hashlib.sha256(
                lexical["source"].encode("utf-8")).hexdigest())
            translated = migrate_qli_current(text)
            self.assertEqual(translated["issues"], [])
            self.assertEqual(row["lexical_edits"], [dict(start=a, end=b, replacement=c, kind=k)
                             for a, b, c, k in translated["edits"]])
            self.assertEqual(row["layout_edits"], [dict(start=a, end=b, replacement=c, kind=k)
                             for a, b, c, k in translated["layout_edits"]])
            self.assertEqual(translated["source"].encode("utf-8"), current.read_bytes())
            expected.add(current)
        for entry in mapping["projects"]:
            before, current = (fixtures.ROOT / entry[key] for key in ("before_path", "current_path"))
            fixtures._verify_pair(before, current, entry, "before_sha256")
            for row in entry["files"]:
                if row["path"].endswith("Qargo.toml"):
                    self.assertEqual((before / row["path"]).read_bytes(), (current / row["path"]).read_bytes())
                else:
                    selected = fixtures.current_source_file(before / row["path"])
                    self.assertEqual(selected.read_bytes(), (current / row["path"]).read_bytes())
                expected.add(current / row["path"])
        # Full byte inventories above cover every record. The selector's
        # graph/order checks run once here; synthetic tests exercise each
        # mutation. Avoid reparsing the complete map for every fixture row.
        for row in (review["files"][0], review["files"][-1]):
            self.assertEqual(fixtures.current_source_file(fixtures.ROOT / row["before_path"]),
                             fixtures.ROOT / row["current_path"])
        for row in (mapping["projects"][0], mapping["projects"][-1]):
            current = fixtures.ROOT / row["current_path"]
            self.assertEqual(fixtures.current_source_project(current), current)
        self.assertEqual({p for p in (directory / "current").rglob("*") if p.is_file()}, expected)
        for row in review["exclusions"]:
            original = fixtures.ROOT / row["path"]
            self.assertEqual(hashlib.sha256(original.read_bytes()).hexdigest(), row["sha256"])
            self.assertNotIn(row["path"], entries)


    def test_public_effect_map_changes_only_recorded_named_annotation_prefixes(self):
        import re
        root = fixtures.ROOT
        directory = root / "tests/fixtures/frontend_v030/public-effects"
        review = fixtures._read_map(directory / "source-map.json")
        entries = fixtures._file_entries(review, "public effect")
        projects = fixtures._projects(review, "before_path", "public effect")
        translations = json.loads((directory / "translation-review.json").read_text())
        self.assertEqual(translations["format"], "qleisli.public-effect-source-translations")
        self.assertEqual(translations["version"], 1)
        self.assertEqual(translations["status"], "generated-unvalidated")
        self.assertEqual(len(entries), 62)
        self.assertEqual(len(projects), 11)
        self.assertEqual(len(translations["files"]), len(entries))
        recorded = set()
        prior = fixtures._migration_maps(stop_before=fixtures.PUBLIC_EFFECTS_MAP)
        expected_inputs = set()
        for item in translations["files"]:
            logical = root / item["logical_path"]
            self.assertEqual(hashlib.sha256(logical.read_bytes()).hexdigest(),
                             item["logical_sha256"])
            selected = item["logical_path"]
            for stage, _ in prior:
                if selected in stage:
                    selected = stage[selected]["current_path"]
            self.assertEqual(selected, item["before_path"])
            self.assertNotIn(selected, recorded)
            recorded.add(selected)
            entry = entries[selected]
            self.assertEqual(entry["current_path"], item["current_path"])
            before, current = root / selected, root / item["current_path"]
            # This edit allowlist grants no authority to the prefixes: source
            # consumers must still independently check them against the bodies.
            transformed = before.read_bytes()
            for name, effect in item["inserted_public_prefixes"].items():
                self.assertIn(effect, ("unitary", "isometry", "observe"))
                self.assertRegex(name, r"^[A-Za-z_][A-Za-z_0-9]*$")
                transformed, count = re.subn(
                    rb"\bpub(?P<gap>\s+)fn(?=\s+" + name.encode() + rb"\b)",
                    lambda match: b"pub" + match["gap"] + effect.encode() + b" fn",
                    transformed,
                )
                self.assertEqual(count, 1)
            self.assertEqual(current.read_bytes(), transformed)
            self.assertNotEqual(current.read_bytes(), before.read_bytes())
            self.assertEqual(fixtures.current_source_file(logical),
                             fixtures.current_source_file(current))
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))
            expected_inputs.add(current)
        self.assertEqual(recorded, set(entries))
        for entry in projects.values():
            before, current = root / entry["before_path"], root / entry["current_path"]
            fixtures._verify_pair(before, current, entry, "before_sha256")
            self.assertEqual((before / "Qargo.toml").read_bytes(),
                             (current / "Qargo.toml").read_bytes())
            expected_inputs.add(current / "Qargo.toml")
        self.assertEqual({p for p in (directory / "current").rglob("*") if p.is_file()},
                         expected_inputs)
        broad = root / "tests/fixtures/authoring_sessions/isometry-preparation-v030/attempt-01/empty-classical/main.qli"
        self.assertNotIn(broad.relative_to(root).as_posix(), entries)
        self.assertIn(b"pub observe fn entry", broad.read_bytes())

    def test_isometry_map_covers_selected_clients_and_changes_only_effect_prefixes(self):
        import re
        prior = fixtures._migration_maps(stop_before=fixtures.ISOMETRY_MAP)
        candidates = {name for files, _ in prior for name in files}
        candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                          (fixtures.ROOT / 'tests/fixtures/frontend_v030/ordinary-type-cutover/current').rglob('*.qli'))
        marker = re.compile(rb'\biso(?=\s+fn\b)')
        expected = set()
        for candidate in candidates:
            selected = candidate
            for files, _ in prior:
                if selected in files:
                    selected = files[selected]['current_path']
            if marker.search((fixtures.ROOT / selected).read_bytes()):
                expected.add(selected)
        data = fixtures._read_map(fixtures.ROOT / fixtures.ISOMETRY_MAP)
        entries = fixtures._file_entries(data, 'isometry vocabulary')
        self.assertEqual(set(entries), expected)
        self.assertEqual(data['projects'], [])
        for entry in entries.values():
            before, current = (fixtures.ROOT / entry[key] for key in ('before_path', 'current_path'))
            transformed, count = marker.subn(b'isometry', before.read_bytes())
            self.assertGreater(count, 0)
            self.assertEqual(current.read_bytes(), transformed)
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))

    def test_selected_current_file_inventory_has_no_unmapped_operation_names(self):
        from operation_naming import canonical_operation_names
        prior = fixtures._migration_maps(stop_before=fixtures.CAPABILITY_NAMING_MAP)
        candidates = {name for files, _ in prior for name in files}
        candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                          (fixtures.ROOT / 'tests/fixtures/frontend_v030/ordinary-type-cutover/current').rglob('*.qli'))
        current = fixtures._file_entries(fixtures._read_map(
            fixtures.ROOT / fixtures.CAPABILITY_NAMING_MAP), 'capability naming')
        expected = set()
        for candidate in candidates:
            selected = candidate
            for files, _ in prior:
                if selected in files:
                    selected = files[selected]['current_path']
            source = (fixtures.ROOT / selected).read_bytes()
            if canonical_operation_names(source) != source:
                expected.add(selected)
        self.assertEqual(set(current), expected)

    def test_capability_naming_preserves_non_name_tokens_comments_and_manifest_bytes(self):
        import re
        # Check allowed token changes independently of the migration helper.
        pattern = re.compile(rb'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[^\s]', re.S)
        renames = {b'Apply': b'Applicable', b'Adjoint': b'Adjointable',
                   b'Controlled': b'Controllable', b'inverse_op': b'adjoint',
                   b'controlled_op': b'controlled', b'inverse': b'adjoint'}
        def compare(before, after):
            old, new = list(pattern.finditer(before)), list(pattern.finditer(after))
            self.assertEqual(len(old), len(new))
            old_end = new_end = 0
            for index, (a, b) in enumerate(zip(old, new)):
                self.assertEqual(before[old_end:a.start()], after[new_end:b.start()])
                old_end, new_end = a.end(), b.end()
                if a[0] == b[0]:
                    continue
                self.assertEqual(renames.get(a[0]), b[0])
                self.assertEqual(old[index + 1][0], b'(')
                if a[0] == b'inverse':
                    depth = 0
                    for closing in range(index + 1, len(old)):
                        depth += (old[closing][0] == b'(') - (old[closing][0] == b')')
                        if depth == 0:
                            self.assertEqual(old[closing + 1][0], b'(')
                            break
                elif a[0] in (b'Apply', b'Adjoint', b'Controlled'):
                    prefix = [item[0] for item in old[:index]]
                    self.assertIn(b'requires', prefix)
                    self.assertNotIn(b'{', prefix[len(prefix) - 1 - prefix[::-1].index(b'requires'):])
            self.assertEqual(before[old_end:], after[new_end:])
        data = fixtures._read_map(fixtures.ROOT / fixtures.CAPABILITY_NAMING_MAP)
        files = fixtures._file_entries(data, 'capability naming')
        projects = fixtures._projects(data, 'before_path', 'capability naming')
        self.assertTrue(files and projects)
        for entry in files.values():
            before, current = (fixtures.ROOT / entry[key] for key in ('before_path', 'current_path'))
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))
            self.assertNotEqual(before.read_bytes(), current.read_bytes())
            compare(before.read_bytes(), current.read_bytes())
        for entry in projects.values():
            before, current = (fixtures.ROOT / entry[key] for key in ('before_path', 'current_path'))
            fixtures._verify_pair(before, current, entry, 'before_sha256')
            for item in entry['files']:
                old, new = before / item['path'], current / item['path']
                if old.suffix == '.qli': compare(old.read_bytes(), new.read_bytes())
                else: self.assertEqual(old.read_bytes(), new.read_bytes())

    def test_naming_migration_preserves_comments_strings_and_ordinary_calls(self):
        from operation_naming import canonical_operation_names
        source = (b'// inverse(U)(q), Apply(U)\r\n'
                  b'/* outer /* inverse_op(U) */ Controlled(U) */\n'
                  b'"inverse(U)(q) and Adjoint(U)"\n'
                  b'fn inverse(q:Q<Bit>)->Q<Bit>{inverse(q)}\n'
                  b'fn f[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> '
                  b'requires Apply(U),Adjoint(U),Controlled(U){inverse /* note */ (U)(q)}\n'
                  b'helper[controlled_op(inverse_op(U))](q)')
        expected = source.replace(b'requires Apply(U),Adjoint(U),Controlled(U)',
                                  b'requires Applicable(U),Adjointable(U),Controllable(U)').replace(
                                  b'inverse /* note */ (U)(q)', b'adjoint /* note */ (U)(q)').replace(
                                  b'helper[controlled_op(inverse_op(U))]', b'helper[controlled(adjoint(U))]')
        self.assertEqual(canonical_operation_names(source), expected)
        self.assertEqual(canonical_operation_names(expected), expected)

    def test_const_client_maps_retain_every_project_and_file_byte_except_markers(self):
        import re
        data = fixtures._read_map(fixtures.ROOT / fixtures.CLIENT_CONST_MAP)
        projects = fixtures._projects(data, "before_path", "const client")
        prior_maps = fixtures._migration_maps(stop_before=fixtures.CLIENT_CONST_MAP)
        marker = re.compile(rb'\bstatic(?= [A-Za-z_]\w*\s*:)')
        expected_projects = set()
        for entry in fixtures._read_map(fixtures.MAP)['projects']:
            selected = entry['current_path']
            for _, stage in prior_maps:
                if selected in stage:
                    selected = stage[selected]['current_path']
            if any(marker.search(path.read_bytes()) for path in
                   (fixtures.ROOT / selected).rglob('*.qli')):
                expected_projects.add(selected)
        self.assertEqual(set(projects), expected_projects)
        for entry in projects.values():
            before = fixtures.ROOT / entry["before_path"]
            current = fixtures.ROOT / entry["current_path"]
            fixtures._verify_pair(before, current, entry, "before_sha256")
            for path in before.rglob('*'):
                if path.is_file():
                    transformed = re.sub(rb'\bstatic(?= [A-Za-z_]\w*\s*:)',
                                         b'const', path.read_bytes()) if path.suffix == '.qli' else path.read_bytes()
                    self.assertEqual((current / path.relative_to(before)).read_bytes(), transformed)
        entries = fixtures._file_entries(data, "const client")
        candidates = {entry['before_path'] for stage, _ in prior_maps
                      for entry in stage.values()}
        for folder in ('sized_clients', 'measured_clients'):
            candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                (fixtures.ROOT / 'tests/fixtures/frontend_v030/ordinary-type-cutover/current' /
                 folder).glob('*.qli'))
        candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
            (fixtures.ROOT / 'tests/fixtures/authoring_sessions/common-provider-access-v030/attempt-01').glob('*/main.qli'))
        candidates.update([
            'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/lexical-resolution/additional-study/shadow-static-missing-argument/main.qli',
            'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/lexical-resolution/additional-study/shadow-static-valid-argument/main.qli',
            'tests/fixtures/frontend_v030/ordinary-type-cutover/current/review_v019/static_budget/main.qli',
        ])
        candidates.update([
            'tests/fixtures/authoring_sessions/body-effects-v030/attempt-01/generic-missing-access/main.qli',
            'tests/fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-hidden-observer/main.qli',
            'tests/fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-wide-pure/main.qli',
            'tests/fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/host-wrong-shape/main.qli',
            'tests/fixtures/authoring_sessions/body-effects-host-review-v030/attempt-02/finite-sealed-provider/main.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/bits-attempt-01/spaced.qli',
        ])
        candidates.update([
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/access-attempt-01/adjoint-bit.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/access-attempt-01/controlled-unit.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/bit.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/repeated-bit.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/unit.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/explicit-attempt-01/main.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/forward-helper-attempt-01/main.qli',
            'tests/fixtures/authoring_sessions/meaning-enforcement-v030/tuple-attempt-01/main.qli',
            'tests/fixtures/authoring_sessions/meaning-specialization-v030/attempt-01/correct-x/main.qli',
            'tests/fixtures/authoring_sessions/meaning-specialization-v030/attempt-01/scalar-minus/main.qli',
            'tests/fixtures/authoring_sessions/meaning-specialization-v030/attempt-01/wrong-x/main.qli',
        ])
        candidates.update([
            'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/common-parser/counted-control.qli',
            'tests/fixtures/frontend_v030/ordinary-type-cutover/current/sized_review/unguarded_take.qli',
        ])
        for folder in ['basis-polymorphism-v030/attempt-02', 'inference-law-v030/attempt-01', 'quantum-tuple-unitors-v030/attempt-01', 'mixed-boolean-v030']:
            candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                (fixtures.ROOT / "tests/fixtures/authoring_sessions" / folder).rglob("*.qli"))
        candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
            (fixtures.ROOT / "tests/fixtures/frontend_v030/quantum-tuple-unitors/independent-sources").glob("*.qli"))
        for folder in ['body-effects-v030/attempt-01', 'quantum-unit-v030/attempt-01', 'runtime-parameter-pattern-v030/validation-repairs', 'common-static-value-v030/attempt-01']:
            candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                (fixtures.ROOT / "tests/fixtures/authoring_sessions" / folder).rglob("*.qli"))
        for folder in ['tests/fixtures/frontend_v030/quantum-unit-source/current', 'tests/fixtures/frontend_v030/ordinary-type-cutover/current/iterative_qpe/faults']:
            candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                (fixtures.ROOT / folder).glob("*.qli"))
        candidates.update(['tests/fixtures/authoring_sessions/operation-application-v030/attempt-02/main.qli', 'tests/fixtures/authoring_sessions/operation-application-v030/attempt-03/main.qli', 'tests/fixtures/frontend_v030/ordinary-type-cutover/current/authoring_sessions/iterative-qpe/attempt-01/iterative.qli'])
        for folder in ['tests/fixtures/frontend_v030/ordinary-type-cutover/current/qli_authoring', 'tests/fixtures/frontend_v030/ordinary-type-cutover/current/quick_reference', 'tests/fixtures/frontend_v030/ordinary-type-cutover/current/repair_diagnostics', 'tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/sized-declarations-independent/sources']:
            candidates.update(path.relative_to(fixtures.ROOT).as_posix() for path in
                (fixtures.ROOT / folder).rglob("*.qli"))
        candidates.update(['tests/fixtures/frontend_v030/ordinary-types-independent/sources/symbolic-word/main.qli', 'tests/fixtures/authoring_sessions/canonical-control-migration-v030/attempt-01/estimation.qli'])
        expected_files = set()
        for selected in candidates:
            for stage, _ in prior_maps:
                if selected in stage:
                    selected = stage[selected]['current_path']
            path = fixtures.ROOT / selected
            if ('qualtran_qft' not in path.parts and path.name != 'delayed_fourier.qli'
                    and marker.search(path.read_bytes())):
                expected_files.add(selected)
        self.assertEqual(set(entries), expected_files)
        for entry in entries.values():
            before = fixtures.ROOT / entry["before_path"]
            current = fixtures.ROOT / entry["current_path"]
            transformed, count = re.subn(rb'\bstatic(?= [A-Za-z_]\w*\s*:)',
                                        b'const', before.read_bytes())
            self.assertGreater(count, 0)
            self.assertEqual(current.read_bytes(), transformed)
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))

    def test_retired_operation_map_preserves_all_other_source_tokens_and_manifests(self):
        import re
        # Independent token-level check of the permitted source edits. Hashes
        # alone cannot tell whether a selected derivative changed the algorithm.
        def tokens(text):
            return re.findall(r"//[^\n]*|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]", text)
        def canonical(items):
            result, index = [], 0
            while index < len(items):
                name = items[index]
                if name not in ("adjoint", "repeat_op", "repeat_static"):
                    result.append(name); index += 1; continue
                self.assertEqual(items[index + 1], "(")
                depth, args, argument = 0, [], []
                index += 2
                while True:
                    token = items[index]; index += 1
                    if token == ")" and depth == 0:
                        args.append(canonical(argument)); break
                    if token == "," and depth == 0:
                        args.append(canonical(argument)); argument = []; continue
                    argument.append(token)
                    if token in ("(", "[", "{"): depth += 1
                    elif token in (")", "]", "}"): depth -= 1
                self.assertEqual(len(args), 3 if name == "repeat_static" else 2)
                if name == "adjoint":
                    result += ["inverse", "(", *args[0], ")", "(", *args[1], ")"]
                else:
                    result += ["power", "(", *args[1], ",", *args[0], ")"]
                    if name == "repeat_static": result += ["(", *args[2], ")"]
            return result
        data = fixtures._read_map(fixtures.ROOT / fixtures.RETIRED_OPERATION_MAP)
        files = fixtures._file_entries(data, "retired operation")
        projects = fixtures._projects(data, "before_path", "retired operation")
        self.assertTrue(files and projects)
        for entry in files.values():
            before, current = (fixtures.ROOT / entry[key] for key in ("before_path", "current_path"))
            self.assertEqual(fixtures.current_source_file(before), fixtures.current_source_file(current))
            self.assertEqual(tokens(current.read_text()), canonical(tokens(before.read_text())))
            self.assertNotEqual(before.read_bytes(), current.read_bytes())
        for entry in projects.values():
            before, current = (fixtures.ROOT / entry[key] for key in ("before_path", "current_path"))
            fixtures._verify_pair(before, current, entry, "before_sha256")
            for item in entry["files"]:
                old, new = before / item["path"], current / item["path"]
                if old.suffix == ".qli":
                    self.assertEqual(tokens(new.read_text()), canonical(tokens(old.read_text())))
                else: self.assertEqual(old.read_bytes(), new.read_bytes())

    def test_qpe_application_map_changes_only_adopted_operator_forms(self):
        data = json.loads((fixtures.ROOT / fixtures.APPLICATION_MAP).read_text())
        entries = fixtures._file_entries(data, "operation application")
        self.assertEqual(len(entries), 1)
        entry = next(iter(entries.values()))
        before = fixtures.ROOT / entry["before_path"]
        current = fixtures.ROOT / entry["current_path"]
        transformed = before.read_bytes().replace(
            b'controlled(repeat_op(2^k,U))', b'controlled(power(U,2^k))').replace(
            b'adjoint(fourier[m],phase)', b'inverse(fourier[m])(phase)')
        self.assertNotEqual(transformed, before.read_bytes())
        self.assertEqual(current.read_bytes(), transformed)
        self.assertEqual(fixtures.current_source_file(
            "corpus/sized/qualtran_qpe/estimation.qli"), fixtures.current_source_file(current))

    def test_actual_quantum_fold_map_has_canonical_entries_and_matching_sources(self):
        # Synthetic maps alone did not catch explanatory metadata inserted in
        # real strict file records. Exercise the same entry point as Rust tests.
        data = json.loads((fixtures.ROOT / fixtures.QFOR_MAP).read_text())
        entries = fixtures._file_entries(data, "quantum fold")
        self.assertEqual(len(entries), 16)
        for entry in entries.values():
            before = fixtures.ROOT / entry["before_path"]
            current = fixtures.ROOT / entry["current_path"]
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))

    def test_const_map_changes_only_parameter_markers(self):
        import re
        data = json.loads((fixtures.ROOT / fixtures.CONST_MAP).read_text())
        entries = fixtures._file_entries(data, "const parameter")
        expected = {p.relative_to(fixtures.ROOT).as_posix() for p in
                    (fixtures.ROOT / "corpus/sized").rglob("*.qli")
                    if "qualtran_qft" not in p.parts}
        destinations = set()
        for entry in entries.values():
            before = fixtures.ROOT / entry["before_path"]
            current = fixtures.ROOT / entry["current_path"]
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))
            transformed, count = re.subn(rb"\bstatic(?= [A-Za-z_]\w*\s*:)",
                                        b"const", before.read_bytes())
            self.assertGreater(count, 0)
            self.assertEqual(current.read_bytes(), transformed)
            destinations.add(current.relative_to(
                fixtures.ROOT / "tests/fixtures/frontend_v030/const-parameters/current").as_posix())
        self.assertEqual(destinations, expected)


if __name__ == "__main__":
    unittest.main()
