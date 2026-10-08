#!/usr/bin/env python3
"""Bounded parser/producer-guard regressions; no graph generation or acceptance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import unittest
from unittest.mock import patch

from compile_sized_corpus import (Parser, Producer, SourceError, check_moves,
    compile_source, type_shape)
from compile_sized_instrument import InstrumentParser, InstrumentProducer, check_body


IDENTITY = 'pub unitary fn step[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { q }'


class LocalResolution(unittest.TestCase):
    def test_const_headers_preserve_ordered_natural_and_operation_parameters(self):
        source = ('pub unitary fn step[static n: Nat, static U: Op<Bits<n>>]'
                  '(c: Q<Bit>, q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) '
                  'requires Controlled(U) { controlled(U)(c,q) }')
        current = source.replace('static ', 'const ')
        for parser_class in (Parser, InstrumentParser):
            with self.subTest(parser=parser_class.__name__):
                old = parser_class(source, module='register_tools').parse()
                new = parser_class(current, module='register_tools').parse()
                self.assertEqual(old, new)
                self.assertEqual(new[8], ['n', 'U'])
                self.assertEqual(new[7], {'U': {'Controlled'}})

    def test_const_names_remain_contextual_and_preserve_small_proposals(self):
        for name in ('n', 'const'):
            legacy = IDENTITY.replace('n: Nat', name+': Nat').replace('Bits<n>', 'Bits<'+name+'>')
            current = legacy.replace('static ', 'const ')
            for width in (0, 1, 2):
                with self.subTest(name=name, width=width):
                    self.assertEqual(compile_source(legacy, 'step', {name: width}),
                                     compile_source(current, 'step', {name: width}))
        source = 'pub unitary fn const(const: Q<Bit>) -> Q<Bit> { const }'
        self.assertEqual(Parser(source, module='register_tools').parse()[0], 'const')
        # Initialization uses the same marker parser without changing its effect.
        source = 'use std::quantum::init0; pub iso fn fresh[const n: Nat]() -> Q<Bit> { init0() }'
        parser = InstrumentParser(source, module='initialization')
        parser.parse()
        self.assertEqual(parser.effect, 'iso')

    def test_parameter_header_requires_an_explicit_marker(self):
        source = IDENTITY.replace('static n: Nat', 'n: Nat')
        for parser_class in (Parser, InstrumentParser):
            with self.subTest(parser=parser_class.__name__), self.assertRaisesRegex(SourceError, "expected 'const'"):
                parser_class(source, module='register_tools').parse()

    def parse(self, body, *, module='register_tools', imports='', parameters=None):
        source = IDENTITY.replace('{ q }', '{ '+body+' }')
        if parameters is not None:
            source = source.replace('q: Q<Bits<n>>', parameters)
        parser = Parser(imports+source, {'relay', module}, module=module)
        return parser, parser.parse()

    def check_moves(self, declaration):
        signature = (len(declaration[8]), [type_shape(t) for _, t in declaration[2]],
                     type_shape(declaration[3]))
        return check_moves(declaration[4], {n: type_shape(t) for n, t in declaration[2]},
                           {'register_tools::step': signature}, declaration[8])

    def test_local_call_uses_module_identity_without_self_import(self):
        parser, declaration = self.parse('step[n](q)')
        self.assertEqual(declaration[4][1],
                         ('call', 'register_tools::step', [('name', 'n')], [('var', 'q')]))
        self.assertEqual(parser.imports, {})
        self.assertEqual(parser.local_functions, {'step': 'register_tools::step'})

    def test_local_adjoint_and_control_definition(self):
        _, declaration = self.parse('adjoint(step[n],q)')
        self.assertEqual(declaration[4][1][0:2], ('adjoint', 'register_tools::step'))
        _, declaration = self.parse('controlled(step[n])(c,q)',
                                    parameters='c: Q<Bit>, q: Q<Bits<n>>')
        self.assertEqual(declaration[4][1][1],
                         ('definition', 'register_tools::step', [('name', 'n')]))

    def test_local_definition_as_ordered_static_operation_argument(self):
        parser, declaration = self.parse('relay[n,step[n]](q)', imports='use relay::relay;')
        self.assertEqual(declaration[4][1][2],
                         [('name', 'n'), ('definition', 'register_tools::step', [('name', 'n')])])
        self.assertEqual(parser.imports, {'relay': 'relay::relay'})

    def test_operation_formal_shadows_same_named_declaration(self):
        source = ('pub unitary fn step[static n: Nat, static step: Op<Bits<n>>]'
                  '(c: Q<Bit>, q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) '
                  'requires Controlled(step) { controlled(step)(c,q) }')
        declaration = Parser(source, module='register_tools').parse()
        self.assertEqual(declaration[4][1][1], ('parameter', 'step'))

    def test_actual_local_corpus_declarations_parse_without_source_repair(self):
        root = Path(__file__).resolve().parent.parent/'corpus/sized'
        for relative, module, function, parser_class in [
            ('measured_qpe/initialization.qli', 'initialization', 'init_zero', InstrumentParser),
            ('measured_qpe/readout.qli', 'readout', 'measure_bits', InstrumentParser),
            ('qualtran_arithmetic/controls.qli', 'controls', 'all_ones', Parser),
            ('qualtran_arithmetic/increment.qli', 'increment', 'increment', Parser),
        ]:
            with self.subTest(module=module):
                parser = parser_class((root/relative).read_text(), {'controls', module}, module=module)
                declaration = parser.parse()
                self.assertEqual(declaration[0], function)
                self.assertNotIn(function, parser.imports)
                self.assertEqual(parser.local_functions[function], module+'::'+function)

    def test_unknown_definitions_do_not_fall_back_to_current_module(self):
        for body in ('unknown[n](q)', 'adjoint(unknown[n],q)',
                     'controlled(unknown[n])(q,q)'):
            with self.subTest(body=body), self.assertRaises(SourceError):
                self.parse(body)

    def test_self_and_foreign_import_collisions_reject(self):
        for imported in ('register_tools::step', 'relay::step'):
            with self.subTest(imported=imported), self.assertRaisesRegex(SourceError, 'collides'):
                self.parse('q', imports='use '+imported+';')

    def test_runtime_and_let_binding_shadowing_do_not_resolve_to_global(self):
        for body, parameters in [('step[n](step)', 'step: Q<Bits<n>>'),
                                 ('let step=q; step[n](step)', None)]:
            with self.subTest(body=body):
                _, declaration = self.parse(body, parameters=parameters)
                with self.assertRaisesRegex(SourceError, 'binding hides'):
                    self.check_moves(declaration)

    def test_static_natural_shadowing_does_not_resolve_to_global(self):
        source = IDENTITY.replace('static n: Nat', 'static step: Nat').replace(
            'Bits<n>', 'Bits<step>').replace('{ q }', '{ step[step](q) }')
        declaration = Parser(source, module='register_tools').parse()
        with self.assertRaisesRegex(SourceError, 'binding hides'):
            self.check_moves(declaration)

    def test_fold_index_shadowing_rejects_in_every_pure_body(self):
        for count in (0, 1):
            with self.subTest(count=count):
                body = f'qfor static step in 0..{count} carry q=q {{ yield step[n](q); }}'
                _, declaration = self.parse(body)
                with self.assertRaisesRegex(SourceError, 'binding hides'):
                    self.check_moves(declaration)
                _, unshadowed = self.parse(body.replace('static step in', 'static i in'))
                self.assertIsNone(self.check_moves(unshadowed))

    def test_fold_index_shadowing_rejects_in_every_instrument_body(self):
        for count in (0, 1):
            with self.subTest(count=count):
                body = f'qfor static step in 0..{count} carry q=q {{ yield step[n](q); }}'
                source = IDENTITY.replace('{ q }', '{ '+body+' }')
                producer = InstrumentProducer({'register_tools': source})
                declaration = producer.declarations['register_tools::step']
                with self.assertRaisesRegex(SourceError, 'binding hides'):
                    check_body(declaration[4], {'q': None}, producer.declarations,
                               producer.effects, 'unitary', declaration[8])
                unshadowed_source = source.replace('static step in', 'static i in')
                producer = InstrumentProducer({'register_tools': unshadowed_source})
                declaration = producer.declarations['register_tools::step']
                self.assertIsNone(check_body(declaration[4], {'q': None}, producer.declarations,
                                             producer.effects, 'unitary', declaration[8]))

    def test_entry_module_is_bound_before_compile_without_generating_graph(self):
        marker = object()
        for modules, explicit, expected in [({}, None, '__entry__'),
            ({'register_tools': IDENTITY}, None, 'register_tools'),
            ({'one': IDENTITY, 'two': IDENTITY}, 'two', 'two')]:
            with self.subTest(expected=expected), patch.object(Producer, 'compile', return_value=marker) as compiled:
                self.assertIs(compile_source(IDENTITY, 'step', {'n': 1}, modules=modules,
                                             module=explicit), marker)
                self.assertEqual(compiled.call_args.kwargs['module'], expected)

    def test_ambiguous_or_stale_entry_module_rejects(self):
        with self.assertRaisesRegex(SourceError, 'ambiguous'):
            compile_source(IDENTITY, 'step', {'n': 1}, modules={'one': IDENTITY, 'two': IDENTITY})
        with self.assertRaisesRegex(SourceError, 'does not match'):
            compile_source(IDENTITY+' ', 'step', {'n': 1}, modules={'one': IDENTITY}, module='one')
        with self.assertRaisesRegex(SourceError, 'does not match'):
            Producer({'one': IDENTITY}).compile(IDENTITY, 'step', {'n': 1}, module='two')
        with self.assertRaisesRegex(SourceError, 'does not match'):
            compile_source(IDENTITY, 'step', {'n': 1}, modules={'__entry__': IDENTITY+' '})

    def test_non_decreasing_recursion_rejects_at_pure_producer_boundary(self):
        source = IDENTITY.replace('{ q }', '{ step[n](q) }')
        key = ('register_tools::step', (1,), ())
        producer = Producer({'register_tools': source}, stack=(key,))
        with self.assertRaisesRegex(SourceError, 'cyclic or excessive'):
            producer.source_operation('register_tools::step', (1,), ('bits', 1))
        # A distinct smaller instantiation passes this guard; no body is executed.
        self.assertEqual(producer.source_operation('register_tools::step', (0,), ('bits', 0))[0],
                         ('register_tools::step', (0,), ()))
        producer.stack = (key,)*32
        with self.assertRaisesRegex(SourceError, 'cyclic or excessive'):
            producer.source_operation('register_tools::step', (2,), ('bits', 2))

    def test_non_decreasing_recursion_rejects_at_instrument_boundary(self):
        source = 'pub iso fn init[static n: Nat]() -> Unit { init[n]() }'
        producer = InstrumentProducer({'initialization': source})
        producer.stack = (('initialization::init', (1,), ()),)
        with self.assertRaisesRegex(SourceError, 'cyclic or excessive'):
            producer.invoke('initialization::init', [1], [], {})
        self.assertEqual(producer.definitions, [])

    def test_pure_compile_keeps_original_quantum_only_parser_subset(self):
        source = 'pub unitary fn copy(q: Bit) -> Bit { q }'
        instrument = InstrumentProducer({'classical_tools': source})
        pure = Producer(instrument.modules, work=instrument.work)
        with self.assertRaisesRegex(SourceError, "expected 'Q'"):
            pure.compile(source, 'copy', {}, module='classical_tools')
        self.assertEqual(pure.definitions, [])


if __name__ == '__main__':
    unittest.main()
