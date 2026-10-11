#!/usr/bin/env python3
"""Phase, sharing and zero-owner regressions for untrusted graph compaction.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy
import math
import unittest

from compact_sized_graph import artifact, compact
from compile_sized_corpus import SourceError, compile_source
from test_hierarchical_qft import Circuit, SharedGradientCircuit, port
from test_sized_corpus import circuit_action, difference


class CompactionTests(unittest.TestCase):
    def compare(self, graph):
        result = compact(graph)
        old = graph['definitions'][graph['entry']['implementation']]['interface']
        new = result['definitions'][result['entry']['implementation']]['interface']
        self.assertEqual(old,new)
        first,_ = circuit_action(graph)
        second,_ = circuit_action(result)
        width = sum(len(p['axes']) for p in old['inputs']['quantum'])
        for column in [{i:1} for i in range(1 << width)] + [
                {0:1/math.sqrt(3),(1 << width)-1:1j/math.sqrt(6)}]:
            self.assertLess(difference(first(column),second(column)),1e-12)
        return result

    def test_source_empty_classical_boundary_compacts_to_identity(self):
        for source in ('pub unitary fn f() -> Unit { () }',
                       'pub unitary fn f(q: Unit) -> Unit { q }',
                       'pub unitary fn f(q: (Unit, Unit)) -> (Unit, Unit) { q }'):
            with self.subTest(source=source):
                direct = compile_source(source, 'f', {}, compact=False)
                normalized = compile_source(source, 'f', {})
                first, _ = circuit_action(direct)
                second, _ = circuit_action(normalized)
                for column in ({0: 1}, {0: 2 + 3j}, {0: -1j}):
                    self.assertEqual(first(column), column)
                    self.assertEqual(second(column), column)
                self.compare(normalized)
                root = normalized['definitions'][normalized['entry']['implementation']]
                self.assertEqual(root['interface']['inputs']['quantum'], [])
                self.assertEqual(root['interface']['outputs']['quantum'], [])

    def test_empty_quantum_owner_is_retained_with_phase(self):
        # Q<Unit> and Q<Bits<0>> each retain a logical owner. Neither is the
        # owner-free classical () handled by an empty tensor above.
        for basis in ([dict(tag='unit')], [dict(tag='bits', width=0)]):
            with self.subTest(basis=basis):
                c = Circuit()
                empty = dict(owner=9, axes=[], basis=basis)
                bit = port(1, [0], True)
                phase = c.add([bit], [bit], dict(tag='dyadic_phase', target=1, j=1, k=2),
                              dict(tag='phase', j=1, k=2), 'phase')
                entry = c.tensor(c.identity([empty]), phase)
                result = self.compare(artifact(c, entry))
                root = result['definitions'][result['entry']['implementation']]
                self.assertEqual(root['interface']['inputs']['quantum'], [empty, bit])
                self.assertEqual(root['interface']['outputs']['quantum'], [empty, bit])
                action, _ = circuit_action(result)
                self.assertLess(difference(action({0: 1, 1: 1}), {0: 1, 1: 1j}), 1e-12)
        source = 'pub unitary fn f(q: Q<Bits<0>>) -> Q<Bits<0>> { q }'
        result = compile_source(source, 'f', {})
        root = result['definitions'][result['entry']['implementation']]
        self.assertEqual(len(root['interface']['outputs']['quantum']), 1)
        with self.assertRaisesRegex(SourceError, 'unreturned quantum owners'):
            compile_source('pub unitary fn f(q: Q<Bits<0>>) -> Unit { () }', 'f', {})

    def test_routes_keep_zero_owner_and_bit_order(self):
        c = Circuit()
        a,b,empty = port(1,[7],True),port(2,[3],True),port(3,[])
        first = c.rewire([a,b,empty],[b,empty,a],[1,2,0],[1,0])
        last = c.rewire([b,empty,a],[empty,a,b],[1,2,0],[1,0])
        result = self.compare(artifact(c,c.sequence([first,last])))
        self.assertEqual(len(result['definitions']),1)
        self.assertEqual(result['definitions'][0]['body']['permutation']['owners'],[2,0,1])
        self.assertEqual(len(result['definitions'][0]['interface']['outputs']['quantum']),3)

    def test_tensor_maps_use_input_offsets(self):
        c = Circuit()
        p = [port(i,[i],True) for i in range(4)]
        left = c.rewire(p[:2],list(reversed(p[:2])),[1,0],[1,0])
        right = c.rewire(p[2:],list(reversed(p[2:])),[1,0],[1,0])
        result = self.compare(artifact(c,c.tensor(left,right)))
        self.assertEqual(result['definitions'][0]['body']['permutation']['axes'],[1,0,3,2])

    def test_swapped_tensor_retains_changing_arity_and_empty_owners(self):
        c = Circuit()
        a, empty = port(1,[7],True), port(2,[])
        register, bit, tail = port(3,[9]), port(4,[9],True), port(5,[])
        left = c.tensor(c.h(a),c.identity([empty]))
        right = c.structural([register],[bit,tail],'take_bit',1,0)
        first = c.rewire([register,a,empty],[a,empty,register],[1,2,0],[1,0])
        last = c.rewire([a,empty,bit,tail],[bit,tail,a,empty],[2,3,0,1],[1,0])
        graph = artifact(c,c.sequence([first,c.tensor(left,right),last]))
        result = self.compare(graph)
        root = result['definitions'][result['entry']['implementation']]
        self.assertEqual(root['body']['tag'],'tensor')
        self.assertEqual(root['interface']['outputs']['quantum'],[bit,tail,a,empty])
        self.assertEqual(result['definitions'][root['body']['left']]['body']['tag'],'structural')

    def test_wrong_closing_permutation_is_not_a_tensor_swap(self):
        c = Circuit()
        a,b = port(1,[0],True),port(2,[1],True)
        phase = c.add([a],[a],dict(tag='dyadic_phase',target=1,j=1,k=3),
            dict(tag='phase',j=1,k=3),'phase')
        first = c.rewire([b,a],[a,b],[1,0],[1,0])
        # This is a valid wire relabelling, but not the inverse of first.
        last = c.rewire([a,b],[b,a],[0,1],[0,1])
        entry = c.sequence([first,c.tensor(phase,c.h(b)),last])
        result = self.compare(artifact(c,entry))
        self.assertEqual(result['definitions'][result['entry']['implementation']]['body']['tag'],'sequence')

    def test_common_identity_frame_keeps_phase_and_empty_owner(self):
        for frame_on_left in (False,True):
            c = Circuit()
            q,empty = port(1,[0],True),port(2,[])
            phase = c.add([q],[q],dict(tag='dyadic_phase',target=1,j=3,k=4),
                dict(tag='phase',j=3,k=4),'phase')
            frame = c.identity([empty])
            with_frame = lambda node: c.tensor(frame,node) if frame_on_left else c.tensor(node,frame)
            result = self.compare(artifact(c,c.sequence([with_frame(phase),with_frame(c.h(q))])))
            root = result['definitions'][result['entry']['implementation']]
            self.assertEqual(root['body']['tag'],'tensor')
            side = 'left' if frame_on_left else 'right'
            retained = result['definitions'][root['body'][side]]
            self.assertEqual(retained['interface']['inputs']['quantum'],[empty])
            self.assertEqual(retained['interface']['outputs']['quantum'],[empty])

    def test_nonidentity_frame_is_not_factored(self):
        c = Circuit()
        a,b = port(1,[0],True),port(2,[1],True)
        phase = c.add([a],[a],dict(tag='dyadic_phase',target=1,j=1,k=3),
            dict(tag='phase',j=1,k=3),'phase')
        root = c.sequence([c.tensor(phase,c.h(b)),c.tensor(c.h(a),c.h(b))])
        result = self.compare(artifact(c,root))
        self.assertEqual(result['definitions'][result['entry']['implementation']]['body']['tag'],'sequence')

    def test_empty_register_conversion_is_explicit(self):
        c = Circuit()
        bit,empty,register = port(1,[0],True),port(2,[]),port(3,[0])
        body = dict(tag='structural',operation=dict(tag='pack_empty_bits'))
        pack = c.add([], [empty], body,body,'structural')
        put = c.structural([bit,empty],[register],'put_bit',1,0)
        entry = c.sequence([c.tensor(c.identity([bit]),pack),put])
        result = self.compare(artifact(c,entry))
        self.assertEqual(result['definitions'][0]['body'],dict(tag='structural',operation=dict(tag='bit_to_bits')))
        # The caller's empty owner cannot disappear under that rewrite.
        retained = c.tensor(entry,c.identity([port(8,[])]))
        result = self.compare(artifact(c,retained))
        root = result['definitions'][result['entry']['implementation']]
        self.assertEqual(root['interface']['inputs']['quantum'][-1],port(8,[]))
        self.assertEqual(root['interface']['outputs']['quantum'][-1],port(8,[]))

    def test_phase_inverse_and_control_survive(self):
        c = Circuit()
        q,control = port(1,[0],True),port(2,[1],True)
        phase = c.add([q],[q],dict(tag='dyadic_phase',target=1,j=3,k=4),dict(tag='phase',j=3,k=4),'phase')
        child = c.sequence([c.identity([q]),c.h(q),phase,c.identity([q])])
        inverse = c.add([q],[q],dict(tag='inverse',definition=child),dict(tag='inverse',child=child),'inverse',[child])
        active = c.add([control,q],[control,q],dict(tag='control',definition=inverse,polarity=False),
            dict(tag='control',child=inverse,polarity=False),'control',[inverse])
        result = self.compare(artifact(c,active))
        self.assertTrue(any(d['body'].get('j') == 3 for d in result['definitions']))
        self.assertFalse(result['definitions'][result['entry']['implementation']]['body']['polarity'])

    def test_inverse_operand_keeps_inspectable_recursive_structure(self):
        def tree(graph, index):
            node = copy.deepcopy(graph['definitions'][index])
            body = node['body']
            if body['tag'] == 'sequence':
                body['children'] = [tree(graph,i) for i in body['children']]
            elif body['tag'] == 'tensor':
                body['left'],body['right'] = tree(graph,body['left']),tree(graph,body['right'])
            elif body['tag'] in ('inverse','control','repeat'):
                body['definition'] = tree(graph,body['definition'])
            return node
        for width in (1,2,3):
            c = SharedGradientCircuit()
            original = c.qft(width)
            child = original['entry']['implementation']
            before,after = c.ends(child)
            inverse = c.add(after,before,dict(tag='inverse',definition=child),
                dict(tag='inverse',child=child),'inverse',[child])
            graph = artifact(c,inverse)
            result = self.compare(graph)
            actual = result['definitions'][result['entry']['implementation']]['body']['definition']
            self.assertEqual(tree(original,child),tree(result,actual))

    def test_zero_repeat_retains_finite_child(self):
        c = Circuit()
        q = port(1,[0],True)
        child = c.h(q)
        repeated = c.add([q],[q],dict(tag='repeat',count=0,definition=child),
            dict(tag='power',count=0,child=child),'repeat',[child])
        graph = artifact(c,repeated)
        leaf = next(d for d in graph['definitions'] if d['body']['tag'] == 'leaf')
        leaf['body']['program'] = 'invalid finite bytes under zero repetition'
        result = self.compare(graph)
        self.assertEqual(result['definitions'][-1]['body']['count'],0)
        self.assertTrue(any(d['body'] == leaf['body'] for d in result['definitions']))

    def test_repetition_does_not_expand_shared_graph(self):
        c = Circuit()
        q = port(1,[0],True)
        child = c.h(q)
        repeated = c.add([q],[q],dict(tag='repeat',count=1,definition=child),
            dict(tag='power',count=1,child=child),'repeat',[child])
        one = compact(artifact(c,repeated))
        for count in (0,64,256):
            graph = copy.deepcopy(artifact(c,repeated))
            graph['definitions'][repeated]['body']['count'] = count
            graph['meanings'][repeated]['body']['count'] = count
            result = compact(graph)
            self.assertEqual(len(result['definitions']),len(one['definitions'])+1)
            self.assertEqual(result['definitions'][-1]['body']['count'],count)


if __name__ == '__main__':
    unittest.main()
