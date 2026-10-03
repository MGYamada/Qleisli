#!/usr/bin/env python3
"""Check the reviewed VM29 migration inventory, not production soundness.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
from pathlib import Path
import sys
from check_verification_inventory import INVENTORY, test_names

ROOT = Path(__file__).resolve().parents[1]
COVERAGE = 'tests/fixtures/verification_v029/coverage.json'
GATES = {'S05-C1', 'S05-C2', 'S05-C3', 'S05-C4', 'S05-C5'}
CUTOVER = {'MIG-1', 'MIG-2', 'MIG-3', 'MIG-4', 'MIG-5'}
# Reviewed routes; source loading and simulation cannot mint accepted handles.
ROUTES = {'raw': ('native-execution', 'tests/native_paths.rs', 'raw_exports_conversions_and_native_reports_share_the_original_byte_gate'), 'contract': ('native-execution', 'tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'), 'function': ('native-execution', 'tests/function_evidence.rs', 'checks_two_raw_functions_and_retains_their_full_snapshots'), 'qirf': ('native-execution', 'tests/native_paths.rs', 'raw_exports_conversions_and_native_reports_share_the_original_byte_gate'), 'finite-leaf': ('native-execution', 'tests/finite_leaf.rs', 'reconstruct_hadamard_in_both_formats_and_bind_complete_bytes'), 'source': ('native-execution', 'scripts/test_source_kernel.py', 'test_unused_body_native_rejection_blocks_every_source_action'), 'foreign': ('native-execution', 'scripts/test_interop_native.py', 'test_all_actions_formats_use_real_native_checker'), 'native-components': ('lean-component', 'tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes'), 'hierarchy-inspect': ('native-execution', 'tests/hierarchical_host.rs', 'native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes'), 'execution': ('untrusted-host', 'tests/sampling.rs', 'stochastic_samples_match_independent_bell_and_reset_feedback_contracts'), 'readout-component': ('lean-component', 'scripts/test_hierarchical_readout.py', 'test_native_branches'), 'preparation-component': ('lean-component', 'scripts/test_hierarchical_preparation.py', 'test_zero_reference'), 'instrument-composition': ('native-execution', 'tests/hierarchical_host.rs', 'native_instrument_binds_all_stages_and_reconstructs_finite_obligations'), 'hierarchy-execution': ('native-execution', 'tests/hierarchical_execution.rs', 'small_source_clients_match_independent_complex_reference_branches'), 'sized-source-proposal': ('native-execution', 'tests/sized_source.rs', 'rust_source_proposals_check_natively_and_preserve_small_system_coefficients'), 'named-qpe-components': ('native-execution', 'tests/hierarchical_qpe_host.rs', 'native_qpe_instrument_binds_provider_phase_hadamards_and_all_boundaries'), 'source-edition-configuration': ('untrusted-host', 'tests/review_v021.rs', 'grouped_imports_expand_to_existing_leaves_with_docs_spans_and_resolution'), 'lean-finite-component-v024': ('lean-component', 'tests/semantic_contracts.rs', 'primitive_evidence_preserves_exact_phase'), 'qirf-native-v028': ('native-execution', 'tests/native_paths.rs', 'native_report_retains_the_exact_artifact_request_and_reconstructed_program'), 'qirf-native-v029': ('native-execution', 'tests/native_acceptance.rs', 'native_handles_execute_bell_and_feedback_without_legacy_receipts')}


def surface_identity(inventory):
    # Include full hashes where the bounded Rust signature scanner does not
    # describe public interfaces (CLI/Python/Lean). No changed path is inferred
    # covered just because another API uses the same implementation.
    value = {key: inventory[key] for key in ('enums', 'boundaries', 'capacities')}
    value['sources'] = [{key: row[key] for key in ('path', 'group', 'surface')} |
                        ({} if row['surface'] and row['surface']['functions'] else {'sha256': row['sha256']})
                        for row in inventory['sources']]
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def check(root, data=None, inventory=None):
    data = json.loads((root/COVERAGE).read_text()) if data is None else data
    inventory = json.loads((root/INVENTORY).read_text()) if inventory is None else inventory
    def require(value, message):
        if not value:
            raise ValueError(message)
    require(data['format'] == 'qleisli.vm29-coverage' and data['version'] == 1, 'unknown coverage format')
    require(data['authority'] == 'Lean' and data['external_schemas_enabled'] is False,
            'production acceptance is Lean-only; schemas remain disabled')
    require(data['migration'] == {
        'decision': 'https://github.com/MGYamada/Qleisli/issues/276',
        'target_version': '0.2.9', 'target_authority': 'Lean',
        'status': 'in-progress', 'soundness_target': '0.5.0',
        'cutover_criteria': sorted(CUTOVER),
    }, 'unreviewed migration decision or completion claim')
    require(data['surface_sha256'] == surface_identity(inventory), 'public surface changed; review VM29 coverage')
    groups = {g['id'] for g in inventory['groups']}
    rows = data['groups']
    require(len(rows) == len(groups) and {r['id'] for r in rows} == groups, 'missing, duplicate or extra coverage group')
    boundaries = {b['id']: b for b in inventory['boundaries']}
    entries = data['boundaries']
    require(len(entries) == len(boundaries) and {r['id'] for r in entries} == set(boundaries), 'missing, duplicate or extra public boundary')
    for row in rows + entries:
        require(row['status'] in {'untrusted-host', 'lean-component', 'native-execution'}, 'unknown migration status')
        require(isinstance(row['blocker'], str) and row['blocker'].strip(), 'missing explicit migration blocker')
        require(set(row['proof_gates']) == GATES, 'incomplete proof obligations')
        require(set(row['cutover_gates']) == CUTOVER, 'incomplete legacy-removal criteria')
        require(bool(row['evidence']), 'missing coverage evidence')
        for name in row['evidence']:
            path = (root/name).resolve()
            require(path.is_relative_to(root.resolve()) and path.is_file() and 'docs-old' not in path.parts,
                    'missing or retired coverage evidence: ' + name)
    for row in entries:
        require(row['entry_points'] == boundaries[row['id']]['entry_points'], 'unreviewed public entry point')
        route = ROUTES.get(row['id'])
        if route is not None:
            require(row['status'] == route[0], 'reviewed selected route was omitted')
        if route is not None:
            require(route is not None and row['status'] == route[0], 'unreviewed production selection')
            require(row.get('selection') and row.get('legacy') == 'removed; no Rust acceptance fallback', 'selection/removal scope must be explicit')
            require(row.get('route_test') == dict(path=route[1], test=route[2]), 'unreviewed selected-path regression')
            require(route[2] in test_names(root/route[1]), 'missing selected-path regression')
    require(not (root/'src/verify.rs').exists() and not (root/'src/interchange/dual.rs').exists(),
            'retired Rust acceptance implementation remains')
    require({g['id'] for g in data['gates']} == GATES and len(data['gates']) == len(GATES), 'missing transfer gate')
    require(all(g['status'] == 'open' and g['acceptance'].strip() for g in data['gates']),
            'gate closure needs proof/specification review, not a metadata edit')
    return dict(groups=len(rows), public_boundaries=len(entries),
                public_source_files=sum(bool(s['surface']) for s in inventory['sources']),
                constructor_variants=sum(len(e['members']) for e in inventory['enums']),
                authority='Lean', migration='in-progress', target_authority='Lean',
                open_gates=sorted(GATES))


def main():
    try:
        print(json.dumps(check(ROOT), indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
