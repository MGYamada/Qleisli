#!/usr/bin/env python3
"""Untrusted initializing/observing source proposal, sharing the sized pure core.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No result here is verification evidence.
"""
import copy
from dataclasses import dataclass
import hashlib

from compile_sized_corpus import (IMPORTS, Parser, Producer, Quantum, Operation,
    SourceError, argument_group, check_static_names, instantiate, natural,
    predicate_holds, validate_provider, value_type, wires)


EFFECTS = {'unitary': 0, 'iso': 1, 'observe': 2}
ADAPTERS = IMPORTS | {
    'std::quantum::init0': 'init0', 'std::observe::measure_z': 'measure_z',
    'std::registers::empty': 'empty', 'std::registers::consume_empty': 'consume_empty',
    'std::classical::empty_bits': 'empty_bits', 'std::classical::prepend_bit': 'prepend_bit',
}


class InstrumentParser(Parser):
    primitive_imports = ADAPTERS

    def function_effect(self):
        spelling = self.peek()
        # This untrusted comparison reader also reads frozen pre-0.3.0 input.
        # Canonical source vocabulary maps to the unchanged transport tag; the
        # production Rust parser owns legacy-source migration diagnostics.
        self.effect = 'iso' if spelling == 'isometry' else spelling
        if self.effect not in EFFECTS:
            raise SourceError('expected unitary, isometry or observe function effect')
        self.index += 1

    def ty(self):
        if self.eat('Bit'):
            return ('cbit',)
        if self.eat('Bits'):
            self.need('<')
            width = self.nat()
            self.need('>')
            return ('cbits', width)
        return super().ty()


def concrete(ty, sizes):
    if ty[0] == 'tuple':
        return ('tuple', tuple(concrete(child, sizes) for child in ty[1]))
    if ty[0] == 'cbits':
        return ('cbits', instantiate(('bits', ty[1]), sizes)[1])
    return instantiate(ty, sizes)


def shape(ty):
    if ty[0] == 'tuple':
        return tuple(shape(child) for child in ty[1])
    return ty[0] if ty[0] in ('cbit', 'cbits') else None


@dataclass(frozen=True)
class Classical:
    ty: tuple
    values: tuple


def quantum(value):
    if isinstance(value, tuple):
        return any(quantum(child) for child in value)
    return value is None or isinstance(value, Quantum)


def flattened(value):
    if isinstance(value, tuple):
        return [leaf for child in value for leaf in flattened(child)]
    return [value]


def bind(pattern, value, env):
    if isinstance(pattern, tuple):
        names = flattened(pattern)
        if len(names) != len(set(names)):
            raise SourceError('duplicate binding in one pattern')
        if not isinstance(value, tuple) or len(pattern) != len(value):
            raise SourceError('tuple pattern has the wrong shape')
        for p, child in zip(pattern, value):
            bind(p, child, env)
    else:
        if pattern in env and quantum(env[pattern]):
            raise SourceError('binding would discard live owner '+pattern)
        env[pattern] = value


def move(name, env):
    if name not in env:
        raise SourceError('unknown, captured or already moved value '+name)
    return env.pop(name) if quantum(env[name]) else env[name]


def check_body(body, env, declarations, effects, effect, hidden=()):
    """Source effects and copy/move shape checks, including all static branches."""
    hidden = set(hidden) | set(env)

    def static_names(values):
        for value in values:
            if value[0] == 'definition':
                name = value[1]
                if name.rsplit('::', 1)[-1] in hidden:
                    raise SourceError('binding hides imported operation '+name)
                if effects[name] != 'unitary':
                    raise SourceError('operation provider must be unitary')
                static_names(value[2])
            elif value[0] == 'repeat':
                static_names([value[2]])

    def operation(name, args, static, transform=False):
        static_names(static)
        if name.rsplit('::', 1)[-1] in hidden:
            raise SourceError('binding hides imported operation '+name)
        if '::' in name:
            declaration = declarations[name]
            expected = [shape(t) for _, t in declaration[2]]
            output = shape(declaration[3])
            if len(static) != len(declaration[8]) or (argument_group(expected) != args if transform else expected != args):
                raise SourceError('ordinary argument shape/arity mismatch')
            actual_effect = effects[name]
            if transform and (actual_effect != 'unitary' or output != argument_group(expected)):
                raise SourceError('inverse/control requires a type-preserving unitary body')
        else:
            signatures = {
                'init0': ([], None, 0, 'iso'), 'empty': ([], None, 0, 'unitary'),
                'consume_empty': ([None], (), 0, 'unitary'),
                'measure_z': ([None], 'cbit', 0, 'observe'),
                'empty_bits': ([], 'cbits', 0, 'unitary'),
                'prepend_bit': (['cbit', 'cbits'], 'cbits', 1, 'unitary'),
                'h': ([None], None, 0, 'unitary'), 'x': ([None], None, 0, 'unitary'),
                'phase': ([None], None, 2, 'unitary'),
                'take_bit': ([None], (None, None), 2, 'unitary'),
                'put_bit': ([None, None], None, 2, 'unitary'),
                'cnot': ([None, None], (None, None), 0, 'unitary'),
                'controlled_phase': ([None, None], (None, None), 2, 'unitary'),
            }
            expected, output, count, actual_effect = signatures[name]
            if expected != args or count != len(static):
                raise SourceError('operation argument shape/arity mismatch')
        if EFFECTS[actual_effect] > EFFECTS[effect]:
            raise SourceError(f'{effect} body cannot perform {actual_effect} operation {name}')
        return output

    def expression(expr, scope):
        tag, *fields = expr
        if tag == 'var':
            return move(fields[0], scope)
        if tag == 'tuple':
            return tuple(expression(child, scope) for child in fields[0])
        if tag in ('call', 'adjoint'):
            name, static, args = fields
            args = [expression(child, scope) for child in args]
            return operation(name, args[0] if tag == 'adjoint' else args, static, tag == 'adjoint')
        if tag == 'controlled':
            op, args = fields
            args = [expression(child, scope) for child in args]
            if len(args) != 2 or args[0] is not None:
                raise SourceError('controlled application requires a quantum control')
            while op[0] == 'repeat':
                op = op[2]
            if op[0] == 'definition':
                operation(op[1], args[1], op[2], True)
            elif args[1] is not None:
                raise SourceError('operation parameter requires one quantum owner')
            return tuple(args)
        if tag == 'if':
            _, first, second = fields
            a, b = (check_body(branch, dict(scope), declarations, effects, effect, hidden)
                    for branch in (first, second))
            if a != b:
                raise SourceError('static branches have different tuple/classical shapes')
            for key in list(scope):
                if quantum(scope[key]):
                    del scope[key]
            return a
        index, _, _, carry, initial, inner = fields
        initial = expression(initial, scope)
        captures = {name: value for name, value in scope.items() if not quantum(value)}
        if check_body(inner, captures | {carry: initial}, declarations, effects, effect, hidden | {index}) != initial:
            raise SourceError('fold carry tuple/classical shape changed')
        return initial

    bindings, result = body
    for pattern, expr in bindings:
        bind(pattern, expression(expr, env), env)
        hidden.update(flattened(pattern))
    result = expression(result, env)
    if any(quantum(value) for value in env.values()):
        raise SourceError('unreturned quantum owners: '+', '.join(name for name, value in env.items() if quantum(value)))
    return result


class InstrumentProducer(Producer):
    def __init__(self, modules):
        work = {'iterations': 0, 'calls': 0, 'modules': {}}
        self.effects = {}
        for name, source in modules.items():
            parser = InstrumentParser(source, modules, module=name)
            declaration = parser.parse()
            if len({n for n, _ in declaration[2]}) != len(declaration[2]):
                raise SourceError('duplicate runtime parameter')
            work['modules'][name] = declaration, parser.imports
            self.effects[name+'::'+declaration[0]] = parser.effect
        super().__init__(modules, work=work)
        for _, imports in work['modules'].values():
            self.check_imports(imports)
        self.declarations = {name+'::'+d[0]: d for name, (d, _) in work['modules'].items()}
        self.initializations, self.allocated, self.measured = [], [], []
        self.classical_name, self.axis = 10000, 0

    def ordinary(self, name, sizes, args, inverse=False, operations=()):
        if self.effects[name] != 'unitary':
            if inverse:
                raise SourceError('adjoint requires a unitary operation')
            return self.invoke(name, sizes, args, dict(operations))
        return super().ordinary(name, sizes, args, inverse, operations)

    def apply(self, definition):
        # Retain local operations until all fresh owners are known. Framing
        # here and again in finish_graph would duplicate routes and tensors.
        # Source ownership is checked now; the complete frame is emitted once.
        before, after = self.ends(definition)
        owners = {port['owner'] for port in before}
        if len(owners) != len(before) or any(port not in self.state for port in before):
            raise SourceError('aliased or unavailable operation operands')
        rest = [port for port in self.state if port['owner'] not in owners]
        self.steps.append(definition)
        self.state = after+rest

    def call(self, name, sizes, args):
        if name == 'init0':
            if self.axis >= 16:
                raise SourceError('initialization exceeds the 16-wire profile')
            result = self.fresh(('bit',), [self.axis])
            self.axis += 1
            before = dict(quantum=copy.deepcopy(self.inputs+self.allocated), classical=[])
            after = dict(quantum=before['quantum']+[result.port], classical=[])
            self.initializations.append(dict(interface=dict(inputs=before, outputs=after),
                                             effect='iso', body=dict(tag='init0', output=result.port['owner'])))
            self.allocated.append(result.port)
            self.state.append(result.port)
            return result
        if name == 'empty':
            result = self.fresh(('bits', 0), [])
            body = dict(tag='structural', operation=dict(tag='pack_empty_bits'))
            self.apply(self.add([], [result.port], body, body, 'structural'))
            return result
        if name == 'consume_empty':
            if value_type(args[0]) != ('bits', 0):
                raise SourceError('consume_empty requires Q<Bits<0>>')
            body = dict(tag='structural', operation=dict(tag='unpack_empty_bits'))
            self.apply(self.add([args[0].port], [], body, body, 'structural'))
            return ()
        if name == 'measure_z':
            if value_type(args[0]) != ('bit',):
                raise SourceError('measure_z requires Q<Bit>; split registers explicitly')
            self.classical_name += 1
            self.measured.append((args[0].port, self.classical_name))
            return Classical(('cbit',), (self.classical_name,))
        if name == 'empty_bits':
            return Classical(('cbits', 0), ())
        if name == 'prepend_bit':
            width, = sizes
            if width >= 8 or [value_type(value) for value in args] != [('cbit',), ('cbits', width)]:
                raise SourceError('prepend_bit requires Bit and exactly Bits<n>, with n < 8')
            return Classical(('cbits', width+1), args[0].values+args[1].values)
        return super().call(name, sizes, args)

    def expr(self, expr, env, sizes):
        if expr[0] == 'var':
            return move(expr[1], env)
        if expr[0] == 'fold':
            _, variable, lo, hi, carry, initial, body = expr
            lo, hi = natural(lo, sizes), natural(hi, sizes)
            if hi < lo or self.work['iterations']+hi-lo > 1024:
                raise SourceError('invalid or excessive static fold range')
            self.work['iterations'] += hi-lo
            value = self.expr(initial, env, sizes)
            ty = value_type(value)
            captures = {name: v for name, v in env.items() if not quantum(v)}
            for i in range(lo, hi):
                value = self.block(body, captures | {carry: value}, sizes | {variable: i})
                if value_type(value) != ty:
                    raise SourceError('fold carry type/tuple shape changed')
            return value
        return super().expr(expr, env, sizes)

    def block(self, body, env, sizes):
        bindings, result = body
        for pattern, expr in bindings:
            bind(pattern, self.expr(expr, env, sizes), env)
        result = self.expr(result, env, sizes)
        if any(quantum(value) for value in env.values()):
            raise SourceError('unreturned quantum owners')
        return result

    def invoke(self, name, values, args, operations):
        self.charge_call()
        declaration = self.declarations[name]
        _, parameters, arguments, output, body, premises, operation_types, access, _ = declaration
        if len(values) != len(parameters) or len(args) != len(arguments):
            raise SourceError('ordinary argument arity mismatch')
        sizes = dict(zip(parameters, values))
        if any(type(n) is not int or not 0 <= n <= 65535 for n in values):
            raise SourceError('invalid concrete static natural')
        if not all(predicate_holds(p, sizes) for p in premises):
            raise SourceError('static entry premise is false')
        if [value_type(value) for value in args] != [concrete(t, sizes) for _, t in arguments]:
            raise SourceError('ordinary argument type mismatch')
        if set(operations) != set(operation_types):
            raise SourceError('static operation arguments do not match declaration')
        key = name, tuple(values), tuple(sorted(operations.items()))
        if key in self.stack or len(self.stack) >= 32:
            raise SourceError('cyclic or excessive source operation instantiation')
        old_stack, old_operations = self.stack, self.operations if hasattr(self, 'operations') else {}
        self.stack, self.operations = self.stack+(key,), {}
        step_start, allocated_start, measured_start = len(self.steps), len(self.allocated), len(self.measured)
        try:
            for parameter, provider in operations.items():
                validate_provider(provider)
                ty = concrete(operation_types[parameter], sizes)
                if self.effects.get(provider.name) != 'unitary':
                    raise SourceError('operation provider must be unitary')
                provider_key, source, function, substitutions = self.source_operation(
                    provider.name, provider.sizes, ty, operations=provider.operations)
                if provider_key not in self.providers:
                    self.providers[provider_key] = Producer(self.modules, self.stack+(provider_key,), self.work).compile(
                        source, function, substitutions, operations=dict(provider.operations),
                        module=provider.name.split('::')[0])
                self.operations[parameter] = provider, ty
            check_static_names(body, parameters, access, self.declarations)
            check_body(body, {n: shape(t) for n, t in arguments}, self.declarations,
                       self.effects, self.effects[name], set(parameters)|set(operation_types))
            env = dict(zip((n for n, _ in arguments), args))
            result = self.block(body, env, sizes)
            if value_type(result) != concrete(output, sizes):
                raise SourceError('return type/tuple shape mismatch')
            # Keep each ordinary helper's local frame. In recursive init/readout
            # the caller's target and previously measured bits need only one
            # outer tensor, not a new full frame at every inner operation.
            inputs = [leaf.port for leaf in flattened(tuple(args)) if isinstance(leaf, Quantum)]
            inputs += self.allocated[allocated_start:]
            outputs = [port for port, _ in self.measured[measured_start:]]
            outputs += [leaf.port for leaf in flattened(result) if isinstance(leaf, Quantum)]
            entry = self.frame(inputs, self.steps[step_start:], outputs)
            self.steps[step_start:] = [entry]
            return result
        finally:
            self.stack, self.operations = old_stack, old_operations

    def frame(self, inputs, children, desired):
        # Frame every recorded operation with every freshly allocated owner.
        # This is an untrusted hoisting proposal; native typing/derivations must
        # validate every resulting tensor, route and structural operation.
        current, steps = inputs, []
        for child in children:
            before, after = self.ends(child)
            if any(port not in current for port in before):
                raise SourceError('instrument framing lost an owner')
            rest = [p for p in current if p not in before]
            if current != before+rest:
                steps.append(self.route(current, before+rest))
            steps.append(self.tensor(child, self.identity(rest)) if rest else child)
            current = after+rest
        if current != desired:
            steps.append(self.route(current, desired))
        return self.sequence(steps) if steps else self.identity(desired)

    def finish_graph(self, returned):
        desired = [port for port, _ in self.measured]+[leaf.port for leaf in flattened(returned) if isinstance(leaf, Quantum)]
        entry = self.frame(self.inputs+self.allocated, self.steps, desired)
        return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
            definitions=self.definitions, meanings=self.meanings, encodings=self.encodings,
            proofs=self.proofs, entry=dict(implementation=entry, proof=entry))

    def compile_instrument(self, name, sizes, operations):
        declaration = self.declarations[name]
        if set(sizes) != set(declaration[1]):
            raise SourceError('entry static arguments do not match declaration')
        types = [concrete(t, sizes) for _, t in declaration[2]]
        if any(leaf[0] not in ('bit', 'bits') for t in types for leaf in type_leaves(t)):
            raise SourceError('this instrument entry requires quantum inputs')
        args = [self.input(ty) for ty in types]
        self.inputs = copy.deepcopy(self.state)
        self.axis = len(wires(self.state))
        result = self.invoke(name, [sizes[p] for p in declaration[1]], args, operations)
        graph = self.finish_graph(result)
        values = [leaf for leaf in flattened(result) if isinstance(leaf, Classical)]
        if len(values) > 1 or values and values[0].ty[0] != 'cbits':
            raise SourceError('this instrument profile returns at most one Bits value')
        if self.measured and not values:
            raise SourceError('this readout profile retains all measured results')
        readout = None
        if values:
            before = copy.deepcopy(self.definitions[graph['entry']['implementation']]['interface']['outputs'])
            readout_inputs, measurements = copy.deepcopy(before), []
            for port, value in self.measured:
                after = dict(quantum=[p for p in before['quantum'] if p['owner'] != port['owner']],
                             classical=before['classical']+[dict(value=value, basis=[dict(tag='bit')])])
                measurements.append(dict(interface=dict(inputs=before, outputs=after),
                                         effect='observe', body=dict(tag='observe_z', input=port['owner'], output=value)))
                before = after
            self.classical_name += 1
            outputs = dict(quantum=before['quantum'], classical=[dict(value=self.classical_name,
                               basis=[dict(tag='bits', width=values[0].ty[1])])])
            readout = dict(inputs=readout_inputs, owners=[p['owner'] for p, _ in self.measured],
                           result=self.classical_name, measurements=measurements,
                           pack=list(values[0].values), outputs=outputs)
        return dict(format='qleisli.sized-instrument-proposal', version=1,
            inputs=dict(quantum=self.inputs, classical=[]), initialized=self.allocated,
            initialization=self.initializations, graph=graph, readout=readout, result_type=value_type(result),
            source_sha256={m: hashlib.sha256(s.encode()).hexdigest() for m, s in self.modules.items()})


def type_leaves(ty):
    return [leaf for child in ty[1] for leaf in type_leaves(child)] if ty[0] == 'tuple' else [ty]


def compile_instrument(modules, entry, sizes, operations=None, *, compact_graph=True):
    proposal = InstrumentProducer(modules).compile_instrument(entry, sizes, {} if operations is None else operations)
    if compact_graph:
        from compact_sized_graph import compact
        proposal['graph'] = compact(proposal['graph'])
    return proposal
