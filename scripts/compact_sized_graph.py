#!/usr/bin/env python3
"""Untrusted local normalization of source-produced pure graph proposals.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The output still requires fresh native and exact finite checking. This pass
does not consume external evidence or issue source-preservation evidence.
"""
import copy

from compile_sized_corpus import Producer, wires


def artifact(circuit, entry):
    return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
        definitions=circuit.definitions, meanings=circuit.meanings,
        encodings=circuit.encodings, proofs=circuit.proofs,
        entry=dict(implementation=entry, proof=entry))


class Compact(Producer):
    def __init__(self):
        super().__init__()
        self.routes = {}

    def coordinates(self, before, after, body):
        tag = body['tag']
        if tag == 'rewire':
            return tuple(body['permutation']['axes'])
        if tag == 'structural':
            axes = wires(before)
            return tuple(axes.index(axis) for axis in wires(after))
        if tag == 'sequence':
            result = tuple(range(len(wires(before))))
            for child in body['children']:
                route = self.routes.get(child)
                if route is None:
                    return None
                result = tuple(result[i] for i in route)
            return result
        if tag == 'tensor':
            left, right = self.routes.get(body['left']), self.routes.get(body['right'])
            if left is not None and right is not None:
                return left+tuple(len(left)+i for i in right)
        return None

    def permutation(self, index):
        body = self.definitions[index]['body']
        return body['permutation'] if body['tag'] == 'rewire' else None

    def is_identity(self, index):
        before, after = self.ends(index)
        return before == after and self.permutation(index) == dict(
            owners=list(range(len(before))), axes=list(range(len(wires(before)))), classical=[])

    def swapped_tensor(self, first, middle, last):
        """Move a complete tensor frame across two exact block swaps.

        Keep every port (including zero-width owners) and each child's exact
        endpoints. No gate is commuted across another gate: the surrounding
        rewires merely change the order in which the two factors are listed.
        """
        body = self.definitions[middle]['body']
        if (body['tag'] != 'tensor' or self.meanings[middle]['body'] != body or
                self.proofs[middle]['rule'] != dict(tag='tensor') or
                self.proofs[middle]['premises'] != [body['left'],body['right']]):
            return None
        left, right = body['left'], body['right']
        a, b = self.ends(left)
        c, d = self.ends(right)
        def swap(front, back):
            return dict(owners=list(range(len(back), len(back)+len(front)))+list(range(len(back))),
                axes=list(range(len(wires(back)), len(wires(back))+len(wires(front))))+
                    list(range(len(wires(back)))), classical=[])
        if (self.ends(first) != (c+a, a+c) or self.ends(last) != (b+d, d+b) or
                self.permutation(first) != swap(a,c) or
                self.permutation(last) != swap(d,b)):
            return None
        return self.tensor(right, left)

    def common_frame(self, first, second):
        """Factor consecutive operations with the same explicit identity frame."""
        one, two = (self.definitions[i]['body'] for i in (first, second))
        if any(body['tag'] != 'tensor' or self.meanings[index]['body'] != body or
                self.proofs[index]['rule'] != dict(tag='tensor') or
                self.proofs[index]['premises'] != [body['left'],body['right']]
                for index,body in [(first,one),(second,two)]):
            return None
        for frame, active in [('right','left'), ('left','right')]:
            a, b = one[frame], two[frame]
            if (self.is_identity(a) and self.is_identity(b) and
                    self.ends(a) == self.ends(b) and
                    self.ends(one[active])[1] == self.ends(two[active])[0]):
                joined = self.sequence([one[active], two[active]])
                return self.tensor(joined,a) if frame == 'right' else self.tensor(a,joined)
        return None

    def add(self, before, after, body, meaning, rule, premises=()):
        # Only the internal ordinary equations below are rewritten. Endpoints
        # are exact type trees and ordered owner/axis lists, including Bits<0>.
        coordinates = self.coordinates(before, after, body)
        if body == meaning and body['tag'] in ('sequence', 'tensor') and coordinates == (0,) and len(before) == len(after) == 1:
            source, target = before[0], after[0]
            conversion = {
                ('bit', 'bits'): 'bit_to_bits', ('bits', 'bit'): 'bits_to_bit',
            }.get((source['basis'][0]['tag'], target['basis'][0]['tag']))
            if (conversion and source['axes'] == target['axes'] and source['owner'] != target['owner'] and
                    len(source['basis']) == len(target['basis']) == 1 and
                    all(p['basis'] == [dict(tag='bit')] or p['basis'] == [dict(tag='bits', width=1)] for p in (source,target))):
                # Cancel only an internal, balanced empty-register lifecycle.
                # An input/output empty owner prevents this one-port match.
                replacement = dict(tag='structural', operation=dict(tag=conversion))
                return self.add(before, after, replacement, replacement, 'structural')
        if rule == 'sequence' and body == meaning and body['tag'] == 'sequence' and list(premises) == body['children']:
            children = []
            for child in body['children']:
                if self.is_identity(child):
                    continue
                right = self.permutation(child)
                left = self.permutation(children[-1]) if children else None
                if left is not None and right is not None:
                    first = children.pop()
                    assert self.ends(first)[1] == self.ends(child)[0]
                    child = self.rewire(self.ends(first)[0], self.ends(child)[1],
                        [left['owners'][i] for i in right['owners']],
                        [left['axes'][i] for i in right['axes']])
                    if self.is_identity(child):
                        continue
                children.append(child)
                if len(children) >= 3:
                    replacement = self.swapped_tensor(*children[-3:])
                    if replacement is not None:
                        children[-3:] = [replacement]
                if len(children) >= 2:
                    replacement = self.common_frame(*children[-2:])
                    if replacement is not None:
                        children[-2:] = [replacement]
            if not children:
                assert before == after
                return self.identity(before)
            if len(children) == 1:
                assert self.ends(children[0]) == (before, after)
                return children[0]
            body = meaning = dict(tag='sequence', children=children)
            premises = children
        elif rule == 'tensor' and body == meaning and body['tag'] == 'tensor' and list(premises) == [body['left'], body['right']]:
            first, second = body['left'], body['right']
            left, right = self.permutation(first), self.permutation(second)
            if left is not None and right is not None:
                inputs, _ = self.ends(first)
                return self.rewire(before, after,
                    left['owners']+[len(inputs)+i for i in right['owners']],
                    left['axes']+[len(wires(inputs))+i for i in right['axes']])
        elif (rule == 'repeat' and body.get('tag') == 'repeat' and body.get('count') == 1 and
              meaning == dict(tag='power', child=body['definition'], count=1) and
              list(premises) == [body['definition']]):
            child = body['definition']
            if before == after and self.ends(child) == (before, after):
                return child
        result = super().add(before, after, body, meaning, rule, premises)
        self.routes[result] = coordinates
        return result


def remap(body, indices):
    body = copy.deepcopy(body)
    tag = body['tag']
    if tag == 'sequence':
        body['children'] = [indices[i] for i in body['children']]
    elif tag == 'tensor':
        body['left'], body['right'] = indices[body['left']], indices[body['right']]
    elif tag in ('inverse', 'control', 'repeat', 'power'):
        field = 'child' if 'child' in body else 'definition'
        body[field] = indices[body[field]]
    return body


def compact(proposal):
    proposal = copy.deepcopy(proposal)
    # An inverse refers to a shared operation, whose internal decomposition may
    # be inspected by an independent meaning checker (for example Fourier).
    # Preserve its whole subgraph, without recognizing names or trusting an
    # algorithm annotation. Parent routing remains eligible for normalization.
    preserved, pending = set(), [d['body']['definition'] for d in proposal['definitions']
        if d['body']['tag'] == 'inverse']
    while pending:
        index = pending.pop()
        if index not in preserved:
            preserved.add(index)
            pending.extend(proposal['proofs'][index]['premises'])
    uses = [0]*len(proposal['proofs'])
    uses[proposal['entry']['proof']] += 1
    for proof in proposal['proofs']:
        for index in proof['premises']:
            uses[index] += 1
    for index, definition in enumerate(proposal['definitions']):
        body, proof = definition['body'], proposal['proofs'][index]
        if (index in preserved or body['tag'] != 'sequence' or body != proposal['meanings'][index]['body'] or
                proof['rule'] != dict(tag='sequence') or proof['premises'] != body['children']):
            continue
        children = []
        for child in body['children']:
            nested = proposal['definitions'][child]['body']
            # Inline only single-use composition wrappers. Shared functions,
            # inverse/control/repeat nodes and zero-count children stay shared.
            children.extend(nested['children'] if child not in preserved and uses[child] == 1 and
                nested['tag'] == 'sequence' else [child])
        body['children'] = children
        proposal['meanings'][index]['body'] = copy.deepcopy(body)
        proof['premises'] = list(children)
    normalized = Compact()
    entry = normalized.import_artifact(proposal, preserve=preserved)
    # Remove only nodes made unreachable by the local rewrites. Zero repeats
    # keep their body edge; all reachable finite payloads remain byte-for-byte.
    live, pending = set(), [entry]
    while pending:
        index = pending.pop()
        if index not in live:
            live.add(index)
            pending.extend(normalized.proofs[index]['premises'])
    result, indices = Producer(), {}
    for index in sorted(live):
        definition, proof = normalized.definitions[index], normalized.proofs[index]
        before, after = normalized.ends(index)
        indices[index] = result.add(before, after, remap(definition['body'], indices),
            remap(normalized.meanings[index]['body'], indices), proof['rule']['tag'],
            [indices[i] for i in proof['premises']])
    return artifact(result, indices[entry])
