#!/usr/bin/env python3
"""Untrusted sized-source corpus producer.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This tool emits proposals, never verification evidence or production programs.
"""
import argparse
import copy
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import re
import sys

from test_hierarchical_qft import Circuit, SharedGradientCircuit, hadamard_matrix, port, text, wires


class SourceError(ValueError):
    pass


IMPORTS = {
    'std::quantum::h': 'h', 'std::quantum::x': 'x',
    'std::quantum::cnot': 'cnot',
    'std::quantum::controlled_phase': 'controlled_phase',
    'std::quantum::phase': 'phase',
    'std::registers::take_bit': 'take_bit',
    'std::registers::put_bit': 'put_bit',
}
TOKEN = re.compile(r'\s+|//[^\n]*|::|->|\.\.|>=|<=|==|!=|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][(){}<>,:;=+\-^]')
RESERVED = {'pub', 'unitary', 'fn', 'static', 'let', 'for', 'in', 'carry', 'yield', 'use', 'requires', 'if', 'else', 'adjoint', 'controlled', 'repeat_op'}


class Parser:
    primitive_imports = IMPORTS

    def __init__(self, source, modules=()):
        if len(source.encode()) > 65536:
            raise SourceError('source exceeds 64 KiB')
        self.tokens = []
        offset, delimiters = 0, []
        while offset < len(source):
            match = TOKEN.match(source, offset)
            if match is None:
                raise SourceError(f'unexpected character at byte/character offset {offset}')
            token = match.group()
            offset = match.end()
            if token.isspace() or token.startswith('//'):
                continue
            self.tokens.append(token)
            # The type parser checks angle brackets; these tokens also denote
            # comparisons. Keep even contextual names such as `Q < n` out of
            # lexical delimiter accounting. Valid type angles have depth two;
            # recursive type structure uses the bounded tuple parentheses.
            if token in ('(', '[', '{'):
                delimiters.append(token)
            elif token in (')', ']', '}'):
                if not delimiters or delimiters.pop() != {')': '(', ']': '[', '}': '{'}[token]:
                    raise SourceError('unbalanced source delimiters')
            if len(delimiters) > 64 or len(self.tokens) > 10000:
                raise SourceError('unbalanced or excessive source nesting/tokens')
        if delimiters:
            raise SourceError('unbalanced source delimiters')
        self.tokens.append('<eof>')
        self.index = 0
        self.imports = {}
        self.modules = set(modules)
        self.operations = {}

    def peek(self):
        return self.tokens[self.index]

    def eat(self, token):
        if self.peek() == token:
            self.index += 1
            return True
        return False

    def need(self, token):
        if not self.eat(token):
            raise SourceError(f'expected {token!r}, found {self.peek()!r} at token {self.index}')

    def name(self):
        name = self.peek()
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) or name in RESERVED:
            raise SourceError(f'expected identifier, found {name!r}')
        self.index += 1
        return name

    def nat(self, atomic=False):
        def atom():
            if self.eat('('):
                value = self.nat()
                self.need(')')
                return value
            token = self.peek()
            if token.isdecimal():
                self.index += 1
                if len(token) > 10 or int(token) > 65535:
                    raise SourceError('static natural exceeds 65535')
                return ('number', int(token))
            return ('name', self.name())
        value = atom()
        operations = 0
        while not atomic and self.peek() in ('+', '-'):
            operations += 1
            if operations > 64:
                raise SourceError('size expression exceeds 64 operations')
            op = self.peek()
            self.index += 1
            value = (op, value, atom())
        return value

    def ty(self):
        if self.eat('('):
            if self.eat(')'):
                return ('tuple', ())
            children = [self.ty()]
            self.need(',')
            children.append(self.ty())
            while self.eat(','):
                children.append(self.ty())
            self.need(')')
            return ('tuple', tuple(children))
        self.need('Q')
        self.need('<')
        if self.eat('Bit'):
            result = ('bit',)
        else:
            self.need('Bits')
            self.need('<')
            result = ('bits', self.nat())
            self.need('>')
        self.need('>')
        return result

    def pattern(self):
        if self.eat('('):
            if self.eat(')'):
                return ()
            children = [self.pattern()]
            self.need(',')
            children.append(self.pattern())
            while self.eat(','):
                children.append(self.pattern())
            self.need(')')
            return tuple(children)
        return self.name()

    def static_argument(self):
        name = self.peek()
        if name in self.operations or (name in self.imports and '::' in self.imports[name]
                                      and self.tokens[self.index+1] == '['):
            return self.operation()
        return self.nat()

    def static_arguments(self):
        self.need('[')
        values = [self.static_argument()]
        while self.eat(','):
            values.append(self.static_argument())
        self.need(']')
        return values

    def expr(self):
        if self.eat('controlled'):
            self.need('(')
            operation = self.operation()
            self.need(')')
            self.need('(')
            control = self.expr()
            self.need(',')
            target = self.expr()
            self.need(')')
            return ('controlled', operation, [control, target])
        if self.eat('adjoint'):
            self.need('(')
            name = self.name()
            if name not in self.imports or '::' not in self.imports[name]:
                raise SourceError('adjoint requires an imported ordinary unitary definition')
            sizes = self.static_arguments()
            self.need(',')
            arg = self.expr()
            self.need(')')
            return ('adjoint', self.imports[name], sizes, [arg])
        if self.eat('if'):
            self.need('static')
            condition = self.predicate()
            first = self.block()
            self.need('else')
            return ('if', condition, first, self.block())
        if self.eat('for'):
            self.need('static')
            variable = self.name()
            self.need('in')
            lo = self.nat()
            self.need('..')
            hi = self.nat()
            self.need('carry')
            carry = self.name()
            self.need('=')
            initial = self.expr()
            return ('fold', variable, lo, hi, carry, initial, self.block(True))
        if self.eat('('):
            if self.eat(')'):
                return ('tuple', [])
            first = self.expr()
            if not self.eat(','):
                self.need(')')
                return first
            children = [first, self.expr()]
            while self.eat(','):
                children.append(self.expr())
            self.need(')')
            return ('tuple', children)
        name = self.name()
        sizes = []
        if self.peek() == '[':
            sizes = self.static_arguments()
        if self.eat('('):
            args = []
            if self.peek() != ')':
                args.append(self.expr())
                while self.eat(','):
                    args.append(self.expr())
            self.need(')')
            if name not in self.imports:
                raise SourceError(f'unknown or unimported operation {name}')
            return ('call', self.imports[name], sizes, args)
        if sizes:
            raise SourceError('static arguments require a call')
        return ('var', name)

    def operation(self):
        if self.eat('repeat_op'):
            self.need('(')
            # Exponentiation is a bounded operation count, never a size expression.
            count = self.nat()
            if self.eat('^'):
                if count != ('number', 2):
                    raise SourceError('power counts require literal base two')
                count = ('pow2', self.nat(atomic=True))
            self.need(',')
            child = self.operation()
            self.need(')')
            return ('repeat', count, child)
        name = self.name()
        if name in self.operations:
            return ('parameter', name)
        if name in self.imports and '::' in self.imports[name]:
            sizes = self.static_arguments()
            return ('definition', self.imports[name], sizes)
        raise SourceError(f'unknown static operation parameter or definition {name}')

    def predicate(self):
        left = self.nat()
        comparison = self.peek()
        if comparison not in ('>=', '<=', '==', '!=', '<', '>'):
            raise SourceError('expected a static comparison')
        self.index += 1
        return comparison, left, self.nat()

    def block(self, yielding=False):
        self.need('{')
        bindings = []
        while self.eat('let'):
            pattern = self.pattern()
            self.need('=')
            value = self.expr()
            self.need(';')
            bindings.append((pattern, value))
        if yielding:
            self.need('yield')
        result = self.expr()
        if yielding:
            self.need(';')
        self.need('}')
        return bindings, result

    def function_effect(self):
        self.need('unitary')

    def parse(self):
        while self.eat('use'):
            parts = [self.name()]
            while self.eat('::'):
                parts.append(self.name())
            self.need(';')
            path = '::'.join(parts)
            ordinary = len(parts) == 2 and parts[0] != 'std' and parts[0] in self.modules
            if (path not in self.primitive_imports and not ordinary) or parts[-1] in self.imports:
                raise SourceError(f'unsupported or duplicate import {path}')
            self.imports[parts[-1]] = self.primitive_imports.get(path, path)
        self.need('pub')
        self.function_effect()
        self.need('fn')
        name = self.name()
        sizes = []
        static_names = []
        has_static = self.eat('[')
        while has_static and self.peek() != ']':
            self.need('static')
            parameter = self.name()
            static_names.append(parameter)
            self.need(':')
            if self.eat('Nat'):
                sizes.append(parameter)
            else:
                self.need('Op')
                self.need('<')
                self.need('Bits')
                self.need('<')
                self.operations[parameter] = ('bits', self.nat())
                self.need('>')
                self.need('>')
            if not self.eat(','):
                break
        if has_static:
            self.need(']')
        if len(set(static_names)) != len(static_names):
            raise SourceError('duplicate static parameter')
        self.need('(')
        parameters = []
        while self.peek() != ')':
            parameter = self.name()
            if parameter in static_names:
                raise SourceError('quantum parameter shadows a static parameter')
            self.need(':')
            parameters.append((parameter, self.ty()))
            if not self.eat(','):
                break
        self.need(')')
        self.need('->')
        output = self.ty()
        premises, access = [], {name: set() for name in self.operations}
        if self.eat('requires'):
            while True:
                if self.peek() in ('Apply', 'Adjoint', 'Controlled'):
                    capability = self.peek()
                    self.index += 1
                    self.need('(')
                    parameter = self.name()
                    self.need(')')
                    if parameter not in access or capability in access[parameter]:
                        raise SourceError('unknown or duplicate operation access constraint')
                    access[parameter].add(capability)
                else:
                    premises.append(self.predicate())
                if not self.eat(','):
                    break
        body = self.block()
        self.need('<eof>')
        parsed = name, sizes, parameters, output, body, premises, self.operations, access, static_names
        pending = [(parsed, 0)]
        while pending:
            item, depth = pending.pop()
            if depth > 128:
                raise SourceError('source expression nesting exceeds 128 AST levels')
            if isinstance(item, (tuple, list)):
                pending.extend((child, depth+1) for child in item)
        return parsed


def natural(expr, sizes):
    tag, *fields = expr
    if tag == 'number':
        return fields[0]
    if tag == 'name':
        if fields[0] not in sizes:
            raise SourceError(f'unbound static natural {fields[0]}')
        return sizes[fields[0]]
    a, b = (natural(child, sizes) for child in fields)
    result = a+b if tag == '+' else a-b
    if not 0 <= result <= 65535:
        raise SourceError('static arithmetic underflow/overflow')
    return result


def instantiate(ty, sizes):
    if ty[0] == 'tuple':
        return ('tuple', tuple(instantiate(t, sizes) for t in ty[1]))
    if ty[0] == 'bits':
        width = natural(ty[1], sizes)
        if width > 8:
            raise SourceError('register width exceeds the eight-bit register profile')
        return ('bits', width)
    return ty


def predicate_holds(predicate, sizes):
    comparison, left, right = predicate
    left, right = natural(left, sizes), natural(right, sizes)
    return {'>=': left >= right, '<=': left <= right, '==': left == right,
            '!=': left != right, '<': left < right, '>': left > right}[comparison]


def check_static_names(body, names, access=None, declarations=None):
    """Resolve static names in every body, including unselected/empty paths."""
    access = {} if access is None else access
    declarations = {} if declarations is None else declarations
    def nat(expr, bound):
        if expr[0] not in ('number', 'name', '+', '-', 'pow2'):
            raise SourceError('natural argument expected, not an operation')
        if expr[0] == 'name' and expr[1] not in bound:
            raise SourceError(f'unbound static natural {expr[1]}')
        if expr[0] in ('+', '-'):
            nat(expr[1], bound)
            nat(expr[2], bound)
        if expr[0] == 'pow2':
            nat(expr[1], bound)

    def arguments(name, values, bound):
        if '::' not in name:
            for value in values:
                nat(value, bound)
            return
        if name not in declarations:
            raise SourceError('unknown imported operation '+name)
        declaration = declarations[name]
        operation_types, required, order = declaration[6:9]
        if len(values) != len(order):
            raise SourceError('ordinary operation static argument arity mismatch')
        for parameter, value in zip(order, values):
            if parameter in operation_types:
                operation(value, bound, required[parameter])
            else:
                nat(value, bound)

    def operation(expr, bound, required=frozenset({'Controlled'})):
        if expr[0] == 'parameter':
            if not required <= access.get(expr[1], set()):
                raise SourceError('operation use requires declared '+', '.join(sorted(required))+' access')
        elif expr[0] == 'definition':
            arguments(expr[1], expr[2], bound)
        elif expr[0] == 'repeat':
            nat(expr[1], bound)
            operation(expr[2], bound, required)
        else:
            raise SourceError('operation argument expected, not a natural')

    def pattern_names(pattern):
        if isinstance(pattern, tuple):
            return set().union(*(pattern_names(p) for p in pattern))
        return {pattern}

    def block(body, bound):
        bindings, result = body
        for pattern, expr in bindings:
            if pattern_names(pattern) & (set(bound) | set(access)):
                raise SourceError('quantum binding shadows a static parameter/index')
            expression(expr, bound)
        expression(result, bound)

    def expression(expr, bound):
        tag, *fields = expr
        if tag == 'tuple':
            for child in fields[0]:
                expression(child, bound)
        elif tag in ('call', 'adjoint'):
            name, static, args = fields
            arguments(name, static, bound)
            for child in args:
                expression(child, bound)
        elif tag == 'controlled':
            operation(fields[0], bound)
            for child in fields[1]:
                expression(child, bound)
        elif tag == 'if':
            condition, first, second = fields
            nat(condition[1], bound)
            nat(condition[2], bound)
            block(first, bound)
            block(second, bound)
        elif tag == 'fold':
            index, lo, hi, _, initial, inner = fields
            if index in bound or index in access:
                raise SourceError('fold index shadows a static parameter')
            if fields[3] in bound or fields[3] in access or fields[3] == index:
                raise SourceError('fold carry shadows a static parameter/index')
            nat(lo, bound)
            nat(hi, bound)
            expression(initial, bound)
            block(inner, bound | {index})
    block(body, set(names))


@dataclass
class Quantum:
    ty: tuple
    port: dict


@dataclass(frozen=True)
class Operation:
    """Explicit transparent source provider, never an opaque capability claim."""
    name: str
    sizes: tuple
    operations: tuple = ()


def validate_provider(provider, depth=0):
    if (depth >= 32 or not isinstance(provider, Operation) or
            not isinstance(provider.name, str) or provider.name.count('::') != 1 or
            not isinstance(provider.sizes, tuple) or not isinstance(provider.operations, tuple) or
            len(provider.operations) > 64 or
            any(type(n) is not int or not 0 <= n <= 65535 for n in provider.sizes)):
        raise SourceError('invalid or excessively nested transparent operation provider')
    names = set()
    for pair in provider.operations:
        if (not isinstance(pair, tuple) or len(pair) != 2 or not isinstance(pair[0], str)
                or pair[0] in names):
            raise SourceError('invalid or duplicate nested operation argument')
        names.add(pair[0])
        validate_provider(pair[1], depth+1)


def value_type(value):
    if isinstance(value, tuple):
        return ('tuple', tuple(value_type(v) for v in value))
    return value.ty


def type_shape(ty):
    return tuple(type_shape(t) for t in ty[1]) if ty[0] == 'tuple' else None


def argument_group(values):
    return values[0] if len(values) == 1 else tuple(values)


def leaves(value):
    if isinstance(value, tuple):
        return [p for child in value for p in leaves(child)]
    return [value.port]


def bind(pattern, value, env):
    if isinstance(pattern, tuple):
        if not isinstance(value, tuple) or len(pattern) != len(value):
            raise SourceError('tuple pattern has the wrong shape')
        for p, v in zip(pattern, value):
            bind(p, v, env)
    else:
        if pattern in env:
            raise SourceError(f'binding would discard live owner {pattern}')
        env[pattern] = value


def check_moves(body, env, signatures=None, hidden=()):
    """Check linear scope/arity even in an empty concretized fold body.

    Leaves are opaque quantum values; exact sizes are checked at each actual
    instantiation, without evaluating impossible indices in an empty range.
    """
    signatures = {} if signatures is None else signatures
    hidden = set(hidden) | set(env)

    def static_names(values):
        for value in values:
            if value[0] == 'definition':
                if value[1].rsplit('::', 1)[-1] in hidden:
                    raise SourceError('quantum/static binding hides imported operation '+value[1])
                static_names(value[2])

    def imported(name, static, values, grouped=False):
        static_names(static)
        if name.rsplit('::', 1)[-1] in hidden:
            raise SourceError('quantum/static binding hides imported operation '+name)
        if name not in signatures:
            raise SourceError('unknown imported operation signature '+name)
        _, parameters, output = signatures[name]
        if len(static) != signatures[name][0]:
            raise SourceError('ordinary operation static argument arity mismatch')
        if (argument_group(parameters) != values if grouped else parameters != values):
            raise SourceError('ordinary operation argument tuple shape/arity mismatch')
        if output != argument_group(parameters):
            raise SourceError('ordinary unitary operation must preserve the complete quantum type')
        return output

    def expression(expr, scope):
        tag, *fields = expr
        if tag == 'var':
            name = fields[0]
            if name not in scope:
                raise SourceError(f'unknown, captured or already moved quantum value {name}')
            return scope.pop(name)
        if tag == 'tuple':
            return tuple(expression(e, scope) for e in fields[0])
        if tag == 'if':
            _, first, second = fields
            a, b = (check_moves(branch, dict(scope), signatures, hidden) for branch in (first, second))
            if a != b:
                raise SourceError('static branches have different tuple shapes')
            scope.clear()
            return a
        if tag == 'controlled':
            values = [expression(a, scope) for a in fields[1]]
            if len(values) != 2 or values[0] is not None:
                raise SourceError('controlled application requires one control owner')
            op = fields[0]
            while op[0] == 'repeat':
                op = op[2]
            if op[0] == 'definition':
                imported(op[1], op[2], values[1], True)
            elif values[1] is not None:
                raise SourceError('operation parameter requires one quantum target owner')
            return None, values[1]
        if tag in ('call', 'adjoint'):
            name, static, args = fields
            values = [expression(a, scope) for a in args]
            if '::' in name:
                return imported(name, static, values[0] if tag == 'adjoint' else values,
                                tag == 'adjoint')
            if name in hidden:
                raise SourceError('quantum/static binding hides imported operation '+name)
            arity = 2 if name in ('cnot', 'put_bit', 'controlled_phase') else 1
            if len(values) != arity or any(v is not None for v in values) or len(static) != (
                    2 if name in ('take_bit', 'put_bit', 'controlled_phase', 'phase') else 0):
                raise SourceError('operation argument shape/arity mismatch')
            return (None, None) if name in ('take_bit', 'cnot', 'controlled_phase') else None
        _, _, _, carry, initial, inner = fields
        value = expression(initial, scope)
        if check_moves(inner, {carry: value}, signatures, hidden) != value:
            raise SourceError('fold carry tuple shape changed')
        return value

    bindings, result = body
    for pattern, expr in bindings:
        bind(pattern, expression(expr, env), env)
        def names(pattern):
            return set().union(*(names(p) for p in pattern)) if isinstance(pattern, tuple) else {pattern}
        hidden |= names(pattern)
    value = expression(result, env)
    if env:
        raise SourceError('unreturned quantum owners: '+', '.join(sorted(env)))
    return value


class Producer(Circuit):
    def __init__(self, modules=None, stack=(), work=None):
        super().__init__()
        self.owner = 100
        self.state, self.steps = [], []
        self.trace = []
        self.modules = {} if modules is None else dict(modules)
        if len(self.modules) > 64:
            raise SourceError('source directory exceeds 64 modules')
        self.work = {'iterations': 0, 'calls': 0, 'modules': {}} if work is None else work
        if work is None:
            for module, source in self.modules.items():
                parser = Parser(source, self.modules)
                declaration = parser.parse()
                self.work['modules'][module] = (declaration, parser.imports)
            for _, imports in self.work['modules'].values():
                self.check_imports(imports)
        self.stack = stack
        self.imported = {}
        self.providers = {}

    def check_imports(self, imports):
        for name in imports.values():
            if '::' in name:
                module, function = name.split('::')
                if self.work['modules'].get(module, ((None,),))[0][0] != function:
                    raise SourceError(f'unknown imported declaration {name}')

    def add(self, *args, **kwargs):
        if len(self.definitions) >= 10000:
            raise SourceError('generated definition limit')
        return super().add(*args, **kwargs)

    def fresh(self, ty, axes):
        self.owner += 1
        return Quantum(ty, port(self.owner, axes, ty == ('bit',)))

    def input(self, ty):
        if ty[0] == 'tuple':
            return tuple(self.input(t) for t in ty[1])
        first = len(wires(self.state))
        width = 1 if ty[0] == 'bit' else ty[1]
        if first + width > 16:
            raise SourceError('input exceeds the 16-wire profile')
        value = self.fresh(ty, range(first, first+width))
        self.state.append(value.port)
        return value

    def route(self, before, after):
        owners = [p['owner'] for p in before]
        if set(owners) != {p['owner'] for p in after} or len(before) != len(after):
            raise SourceError('routing must retain all distinct owners')
        axes = wires(before)
        return self.rewire(before, after, [owners.index(p['owner']) for p in after],
                           [axes.index(a) for a in wires(after)])

    def apply(self, definition):
        before, after = self.ends(definition)
        owners = {p['owner'] for p in before}
        if len(owners) != len(before) or any(p not in self.state for p in before):
            raise SourceError('aliased or unavailable operation operands')
        rest = [p for p in self.state if p['owner'] not in owners]
        if self.state != before+rest:
            self.steps.append(self.route(self.state, before+rest))
        self.steps.append(self.tensor(definition, self.identity(rest)) if rest else definition)
        self.state = after+rest

    def gate(self, gate, target):
        if not isinstance(target, Quantum) or target.ty != ('bit',):
            raise SourceError(f'{gate} requires Q<Bit>; conversions are explicit')
        output = self.fresh(('bit',), target.port['axes'])
        program = dict(format='qleisli.finite-ir', version=2, profile='finite-meaning-v1',
            sources=[], evidence=[], root=0,
            root_interface=dict(input=dict(tag='bit'), output=dict(tag='bit')),
            programs=[dict(quantum_inputs=[dict(token=target.port['owner'],
                wires=target.port['axes'], shape=dict(bits=1))],
                quantum_outputs=[output.port['owner']], classical_inputs=[], classical_outputs=[],
                declared_effect='unitary', operations=[dict(tag='gate', gate=gate,
                    input=target.port['owner'], output=output.port['owner'])])])
        if gate == 'h':
            matrix = hadamard_matrix()
        else:
            entries = [[dict(numerator=str(v if i == 0 else 0), denominator_bits=0)
                        for i in range(4)] for v in (0, 1, 1, 0)]
            matrix = text(dict(format='qleisli.finite-matrix', version=1,
                domain='zeta8-dyadic-v1', rows=2, cols=2, entries=entries))
        leaf = self.add([target.port], [output.port], dict(tag='leaf', program=text(program)),
                        dict(tag='finite', description=matrix), 'finite')
        # A closed target boundary is required by coherent control.
        return self.sequence([leaf, self.rewire([output.port], [target.port])])

    def import_artifact(self, artifact, *, preserve=()):
        """Merge exact source-produced graph entries with structural sharing.

        This internal producer format has aligned tables, identity encodings
        and a topological order. Rebuild those same equations through add(),
        deduplicating complete bodies/headers/bytes rather than function names.
        No externally supplied artifact or evidence receipt is accepted here.
        `preserve` keeps selected internal nodes out of subclass normalization;
        their bodies, endpoints and exact bytes are still imported and checked.
        """
        if not len(artifact['definitions']) == len(artifact['meanings']) == len(artifact['proofs']):
            raise SourceError('source artifact table alignment')
        translated = []
        def reference(index):
            if type(index) is not int or not 0 <= index < len(translated):
                raise SourceError('source artifact requires preceding graph references')
            return translated[index]
        def body(value, logical=False):
            value = copy.deepcopy(value)
            tag = value['tag']
            if tag == 'sequence':
                value['children'] = [reference(i) for i in value['children']]
            elif tag == 'tensor':
                value['left'] = reference(value['left'])
                value['right'] = reference(value['right'])
            elif tag in ('control', 'inverse', 'repeat', 'power'):
                field = 'child' if logical else 'definition'
                value[field] = reference(value[field])
            elif tag not in ('leaf', 'finite', 'rewire', 'structural', 'dyadic_phase', 'phase'):
                raise SourceError('unsupported source artifact operation')
            return value
        for index, (definition, meaning, proof) in enumerate(zip(
                artifact['definitions'], artifact['meanings'], artifact['proofs'])):
            header = definition['interface']
            if (definition['effect'] != 'unitary' or header != meaning['interface'] or
                    proof['implementation'] != index or proof['meaning'] != index or
                    proof['kind'] != 'equation' or proof['witness'] != dict(
                        template_version=1, parameters=[], references=[])):
                raise SourceError('unsupported internal source equation')
            for name, side in [('input_encoding', 'inputs'), ('output_encoding', 'outputs')]:
                encoding = artifact['encodings'][proof[name]]
                if encoding != dict(logical=header[side], physical=header[side], body=dict(tag='identity')):
                    raise SourceError('source equation requires complete identity encodings')
            if header['inputs']['classical'] or header['outputs']['classical']:
                raise SourceError('source import requires quantum-only endpoints')
            add = Producer.add.__get__(self) if index in preserve else self.add
            translated.append(add(copy.deepcopy(header['inputs']['quantum']),
                copy.deepcopy(header['outputs']['quantum']), body(definition['body']),
                body(meaning['body'], True), proof['rule']['tag'],
                [reference(i) for i in proof['premises']]))
        if artifact['entry']['implementation'] != artifact['entry']['proof']:
            raise SourceError('source entry table alignment')
        return reference(artifact['entry']['implementation'])

    def resolve_call(self, name, values, sizes):
        module, function = name.split('::')
        declaration = self.work['modules'][module][0]
        if declaration[0] != function or len(values) != len(declaration[8]):
            raise SourceError('ordinary operation static argument arity mismatch')
        naturals, operations = {}, []
        for parameter, value in zip(declaration[8], values):
            if parameter in declaration[6]:
                if value[0] == 'parameter':
                    provider, _ = self.operations[value[1]]
                elif value[0] == 'definition':
                    provider = self.resolve_call(value[1], value[2], sizes)
                else:
                    raise SourceError('static operation argument requires a parameter or transparent definition')
                operations.append((parameter, provider))
            else:
                naturals[parameter] = natural(value, sizes)
        return Operation(name, tuple(naturals[p] for p in declaration[1]), tuple(operations))

    def source_operation(self, name, sizes, ty, arguments=None, operations=()):
        if not isinstance(name, str) or name.count('::') != 1:
            raise SourceError('operation provider requires module::function')
        if any(type(n) is not int or not 0 <= n <= 65535 for n in sizes):
            raise SourceError('invalid operation static arguments')
        module, function = name.split('::')
        source = self.modules.get(module)
        if source is None:
            raise SourceError(f'unknown source module {module}')
        declared, static, parameters, result, _, _, operation_types, _, _ = self.work['modules'][module][0]
        if (declared != function or len(static) != len(sizes) or
                {p for p, _ in operations} != set(operation_types) or len(operations) != len(operation_types)):
            raise SourceError('ordinary operation signature/static arguments do not match')
        substitutions = dict(zip(static, sizes))
        inputs = [instantiate(t, substitutions) for _, t in parameters]
        if arguments is not None and inputs != arguments:
            raise SourceError('ordinary operation argument type/arity mismatch')
        input_type = inputs[0] if len(inputs) == 1 else ('tuple', tuple(inputs))
        if input_type != ty or instantiate(result, substitutions) != ty:
            raise SourceError('ordinary unitary operation must preserve the complete quantum type')
        key = name, tuple(sizes), tuple(sorted(operations))
        if key in self.stack or len(self.stack) >= 32:
            raise SourceError('cyclic or excessive source operation instantiation')
        return key, source, function, substitutions

    def shared_operation(self, name, sizes, ty, operations=()):
        key, source, function, substitutions = self.source_operation(name, sizes, ty, operations=operations)
        if key not in self.imported:
            artifact = self.providers.get(key)
            if artifact is None:
                artifact = Producer(self.modules, self.stack+(key,), self.work).compile(
                    source, function, substitutions, operations=dict(operations))
            if len(self.definitions)+len(artifact['definitions']) > 10000:
                raise SourceError('generated definition limit')
            self.imported[key] = self.import_artifact(artifact)
        return self.imported[key]

    def charge_call(self):
        self.work['calls'] += 1
        if self.work['calls'] > 1024:
            raise SourceError('source operation call limit')

    def ordinary(self, name, sizes, args, inverse=False, operations=()):
        self.charge_call()
        value = argument_group(args)
        ty = value_type(value)
        self.source_operation(name, sizes, ty, None if inverse else [value_type(a) for a in args], operations)
        child = self.shared_operation(name, sizes, ty, operations)
        before, after = self.ends(child)
        if inverse:
            child = self.add(after, before, dict(tag='inverse', definition=child),
                             dict(tag='inverse', child=child), 'inverse', [child])
            before, after = after, before
        def fresh_value(value):
            if isinstance(value, tuple):
                return tuple(fresh_value(v) for v in value)
            return self.fresh(value.ty, value.port['axes'])
        output = fresh_value(value)
        node = self.sequence([self.rewire(leaves(value), before), child,
                              self.rewire(after, leaves(output))])
        self.apply(node)
        self.trace.append(('call', name, tuple(sizes), inverse))
        return output

    def controlled(self, expression, sizes, args):
        self.charge_call()
        if len(args) != 2 or not isinstance(args[0], Quantum) or args[0].ty != ('bit',):
            raise SourceError('controlled application requires Q<Bit> and a quantum target')
        control, target = args
        counts = []
        while expression[0] == 'repeat':
            count = expression[1]
            if count[0] == 'pow2':
                exponent = natural(count[1], sizes)
                if exponent > 8:
                    raise SourceError('power exponent exceeds eight')
                count = 1 << exponent
            else:
                count = natural(count, sizes)
            if count > 256:
                raise SourceError('operation repetition exceeds 256')
            counts.append(count)
            expression = expression[2]
        product = 1
        for count in counts:
            product *= count
        if product > 256:
            raise SourceError('composed operation repetition exceeds 256')
        if expression[0] == 'parameter':
            provider, ty = self.operations[expression[1]]
            if value_type(target) != ty:
                raise SourceError('static operation target type mismatch')
        else:
            provider = self.resolve_call(expression[1], expression[2], sizes)
            ty = value_type(target)
        child = self.shared_operation(provider.name, provider.sizes, ty, provider.operations)
        before, after = self.ends(child)
        child = self.sequence([child, self.rewire(after, before)])
        for count in reversed(counts):
            child = self.add(before, before, dict(tag='repeat', count=count, definition=child),
                             dict(tag='power', count=count, child=child), 'repeat', [child])
        # Close the provider on the caller's actual owner/axis labels before control.
        child = self.sequence([self.rewire(leaves(target), before), child,
                               self.rewire(before, leaves(target))])
        ps = [control.port, *leaves(target)]
        node = self.add(ps, ps, dict(tag='control', definition=child, polarity=True),
                        dict(tag='control', child=child, polarity=True), 'control', [child])
        self.apply(node)
        self.trace.append(('call', provider.name, provider.sizes, 'controlled', tuple(counts)))
        return control, target

    def call(self, name, sizes, args):
        if '::' in name:
            return self.ordinary(name, sizes, args)
        if name == 'phase':
            if len(sizes) != 2 or len(args) != 1 or not isinstance(args[0], Quantum) or args[0].ty != ('bit',):
                raise SourceError('phase requires j,k and one Q<Bit> argument')
            j, k = sizes
            if k > 8 or j >= 1 << k:
                raise SourceError('dyadic angle is outside the normalized denominator-256 profile')
            p = args[0].port
            self.apply(self.add([p], [p], dict(tag='dyadic_phase', target=p['owner'], j=j, k=k),
                                dict(tag='phase', j=j, k=k), 'phase'))
            self.trace.append(('phase', p['axes'][0], j, k))
            return args[0]
        if name == 'controlled_phase':
            if len(sizes) != 2 or len(args) != 2 or any(
                    not isinstance(a, Quantum) or a.ty != ('bit',) for a in args):
                raise SourceError('controlled_phase requires j,k and two Q<Bit> arguments')
            j, k = sizes
            if k > 8 or j >= 1 << k:
                raise SourceError('dyadic angle is outside the normalized denominator-256 profile')
            control, target = args
            child = self.add([target.port], [target.port],
                dict(tag='dyadic_phase', target=target.port['owner'], j=j, k=k),
                dict(tag='phase', j=j, k=k), 'phase')
            ps = [control.port, target.port]
            node = self.add(ps, ps, dict(tag='control', definition=child, polarity=True),
                            dict(tag='control', child=child, polarity=True), 'control', [child])
            self.apply(node)
            self.trace.append((name, control.port['axes'][0], target.port['axes'][0], j, k))
            return tuple(args)
        if name in ('h', 'x'):
            if sizes or len(args) != 1:
                raise SourceError('one-bit gate arity')
            self.apply(self.gate(name, args[0]))
            self.trace.append((name, *args[0].port['axes']))
            return args[0]
        if name == 'cnot':
            if sizes or len(args) != 2 or any(not isinstance(a, Quantum) or a.ty != ('bit',) for a in args):
                raise SourceError('cnot requires two distinct Q<Bit> arguments')
            control, target = args
            child = self.gate('x', target)
            ps = [control.port, target.port]
            node = self.add(ps, ps, dict(tag='control', definition=child, polarity=True),
                            dict(tag='control', child=child, polarity=True), 'control', [child])
            self.apply(node)
            self.trace.append(('cnot', control.port['axes'][0], target.port['axes'][0]))
            return tuple(args)
        if len(sizes) != 2:
            raise SourceError('register operation requires width and position')
        width, position = sizes
        if not 1 <= width <= 8 or position >= width:
            raise SourceError('bit index outside register')
        if name == 'take_bit':
            if len(args) != 1 or not isinstance(args[0], Quantum) or args[0].ty != ('bits', width):
                raise SourceError('take_bit width/type mismatch')
            axes = args[0].port['axes']
            bit = self.fresh(('bit',), [axes[position]])
            rest = self.fresh(('bits', width-1), axes[:position]+axes[position+1:])
            result = (bit, rest)
        else:
            if len(args) != 2 or any(not isinstance(a, Quantum) for a in args) or (
                    args[0].ty, args[1].ty) != (('bit',), ('bits', width-1)):
                raise SourceError('put_bit width/type mismatch')
            axes = list(args[1].port['axes'])
            axes.insert(position, args[0].port['axes'][0])
            result = self.fresh(('bits', width), axes)
        self.apply(self.structural([p for a in args for p in leaves(a)], leaves(result),
                                   name, width, position))
        return result

    def expr(self, expr, env, sizes):
        tag, *fields = expr
        if tag == 'var':
            name = fields[0]
            if name not in env:
                raise SourceError(f'unknown, captured or already moved quantum value {name}')
            return env.pop(name)
        if tag == 'tuple':
            return tuple(self.expr(e, env, sizes) for e in fields[0])
        if tag == 'controlled':
            return self.controlled(fields[0], sizes, [self.expr(e, env, sizes) for e in fields[1]])
        if tag == 'if':
            condition, first, second = fields
            return self.block(first if predicate_holds(condition, sizes) else second, env, sizes)
        if tag in ('call', 'adjoint'):
            name, static, args = fields
            values = [self.expr(e, env, sizes) for e in args]
            if '::' in name:
                provider = self.resolve_call(name, static, sizes)
                return self.ordinary(name, provider.sizes, values, tag == 'adjoint', provider.operations)
            return self.call(name, [natural(s, sizes) for s in static], values)
        variable, lo, hi, carry, initial, body = fields
        if variable in sizes:
            raise SourceError('fold index shadows a static parameter')
        lo, hi = natural(lo, sizes), natural(hi, sizes)
        if hi < lo or self.work['iterations'] + hi-lo > 1024:
            raise SourceError('invalid or excessive static fold range')
        self.work['iterations'] += hi-lo
        value = self.expr(initial, env, sizes)
        ty = value_type(value)
        for i in range(lo, hi):
            value = self.block(body, {carry: value}, sizes | {variable: i})
            if value_type(value) != ty:
                raise SourceError('fold carry type/tuple shape changed')
        return value

    def block(self, body, env, sizes):
        bindings, expr = body
        for pattern, value in bindings:
            bind(pattern, self.expr(value, env, sizes), env)
        result = self.expr(expr, env, sizes)
        if env:
            raise SourceError('unreturned quantum owners: '+', '.join(sorted(env)))
        return result

    def compile(self, source, entry, sizes, compact=True, operations=None):
        parser = Parser(source, self.modules)
        name, static, parameters, output, body, premises, operation_types, access, _ = parser.parse()
        self.check_imports(parser.imports)
        if name != entry or set(sizes) != set(static) or any(type(n) is not int or not 0 <= n <= 65535 for n in sizes.values()):
            raise SourceError('entry/static arguments do not match the declaration')
        if any(not predicate_holds(p, sizes) for p in premises):
            raise SourceError('static entry premise is false')
        declarations = {module+'::'+declaration[0]: declaration
                        for module, (declaration, _) in self.work['modules'].items()}
        check_static_names(body, static, access, declarations)
        operations = {} if operations is None else operations
        if set(operations) != set(operation_types) or any(not isinstance(p, Operation) for p in operations.values()):
            raise SourceError('static operation arguments do not match the declaration')
        self.operations = {}
        for parameter, provider in operations.items():
            validate_provider(provider)
            ty = instantiate(operation_types[parameter], sizes)
            key, provider_source, function, substitutions = self.source_operation(
                provider.name, provider.sizes, ty, operations=provider.operations)
            # Validate transparent providers even if unused or repeated zero times.
            self.charge_call()
            self.providers[key] = Producer(self.modules, self.stack+(key,), self.work).compile(
                provider_source, function, substitutions, operations=dict(provider.operations))
            self.operations[parameter] = provider, ty
        env = {}
        shapes = {}
        for parameter, ty in parameters:
            bind(parameter, type_shape(ty), shapes)
        signatures = {module+'::'+declaration[0]: (len(declaration[8]),
            [type_shape(t) for _, t in declaration[2]], type_shape(declaration[3]))
            for module, (declaration, _) in self.work['modules'].items()}
        check_moves(body, shapes, signatures, set(static) | set(operation_types))
        for parameter, ty in parameters:
            bind(parameter, self.input(instantiate(ty, sizes)), env)
        inputs = list(self.state)
        result = self.block(body, env, sizes)
        if value_type(result) != instantiate(output, sizes):
            raise SourceError('return type/tuple shape mismatch')
        returned = leaves(result)
        if compact and not any(g[0] == 'call' for g in self.trace) and (
                [p['basis'] for p in inputs] == [p['basis'] for p in returned]):
            return compact_artifact(inputs, returned, self.trace)
        if self.state != returned:
            self.steps.append(self.route(self.state, returned))
        if not self.steps:
            self.steps.append(self.identity(returned))
        root = self.sequence(self.steps) if len(self.steps) > 1 else self.steps[0]
        return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
            definitions=self.definitions, meanings=self.meanings, encodings=self.encodings,
            proofs=self.proofs, entry=dict(implementation=root, proof=root))


def compact_artifact(inputs, outputs, trace):
    """Untrusted routing normalization, retaining explicit typed boundaries.

    Structural source operations only change the ordered axis/owner views.
    Unpack once, tensor independent gates, and repack once. Finite leaves stay
    one bit. Consecutive CNOTs sharing a control factor through one control
    node; this rule does not commute any intervening operation.
    """
    fourier = factor_fourier_trace(inputs, outputs, trace)
    if fourier is not None:
        return fourier
    c = Producer()
    c.owner = 100000

    # Independent one-axis operations retain recursive register tails. This
    # avoids flattening an eight-bit provider merely to act on its low bit.
    if (len(inputs) == len(outputs) == 1 and wires(inputs) == wires(outputs) and
            inputs[0]['basis'] == [dict(tag='bits', width=len(wires(inputs)))] and
            all(g[0] in ('h', 'x', 'phase') for g in trace)):
        by_axis = {a: [g for g in trace if g[1] == a] for a in wires(inputs)}
        def local(p):
            width = len(p['axes'])
            active = [a for a in p['axes'] if by_axis[a]]
            if not active:
                return c.identity([p])
            axis = active[0]
            position = p['axes'].index(axis)
            bit = c.fresh(('bit',), [axis]).port
            rest = c.fresh(('bits', width-1), [a for a in p['axes'] if a != axis]).port
            take = c.structural([p], [bit, rest], 'take_bit', width, position)
            gates = []
            for g in by_axis[axis]:
                if g[0] == 'phase':
                    _, _, j, k = g
                    gates.append(c.add([bit], [bit], dict(tag='dyadic_phase', target=bit['owner'], j=j, k=k),
                                       dict(tag='phase', j=j, k=k), 'phase'))
                else:
                    gates.append(c.gate(g[0], Quantum(('bit',), bit)))
            action = gates[0] if len(gates) == 1 else c.sequence(gates)
            return c.sequence([take, c.tensor(action, local(rest)),
                               c.structural([bit, rest], [p], 'put_bit', width, position)])
        root = c.sequence([local(inputs[0]), c.rewire(inputs, outputs)])
        return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
            definitions=c.definitions, meanings=c.meanings, encodings=c.encodings,
            proofs=c.proofs, entry=dict(implementation=root, proof=root))

    # A parallel register-to-register gate layer can retain the register tails
    # instead of flattening every wire into a header. Match actual gates/axes,
    # never a source function name or a claimed algorithm contract.
    if (len(inputs) == 2 and all(p['basis'] == [dict(tag='bits', width=len(p['axes']))]
                                for p in inputs) and len(inputs[0]['axes']) == len(inputs[1]['axes'])
            and trace == [('cnot', a, b) for a, b in zip(inputs[0]['axes'], inputs[1]['axes'])]
            and wires(inputs) == wires(outputs)):
        def parallel(left, right):
            width = len(left['axes'])
            if width == 0:
                return c.identity([left, right])
            a = c.fresh(('bit',), left['axes'][:1]).port
            b = c.fresh(('bit',), right['axes'][:1]).port
            if width == 1:
                def bit_view(p, q):
                    body = dict(tag='structural', operation=dict(tag='bits_to_bit'))
                    return c.add([p], [q], body, body, 'structural')
                opening = c.tensor(bit_view(left, a), bit_view(right, b))
                xgate = c.gate('x', Quantum(('bit',), b))
                gate = c.add([a, b], [a, b], dict(tag='control', definition=xgate, polarity=True),
                             dict(tag='control', child=xgate, polarity=True), 'control', [xgate])
                closing = c.add([a, b], [left, right], dict(tag='inverse', definition=opening),
                                dict(tag='inverse', child=opening), 'inverse', [opening])
                return c.sequence([opening, gate, closing])
            x = c.fresh(('bits', width-1), left['axes'][1:]).port
            y = c.fresh(('bits', width-1), right['axes'][1:]).port
            opening = c.tensor(c.structural([left], [a, x], 'take_bit', width, 0),
                               c.structural([right], [b, y], 'take_bit', width, 0))
            grouped = [a, b, x, y]
            route = c.route([a, x, b, y], grouped)
            opening = c.sequence([opening, route])
            xgate = c.gate('x', Quantum(('bit',), b))
            gate = c.add([a, b], [a, b], dict(tag='control', definition=xgate, polarity=True),
                         dict(tag='control', child=xgate, polarity=True), 'control', [xgate])
            action = c.tensor(gate, parallel(x, y))
            closing = c.add(grouped, [left, right], dict(tag='inverse', definition=opening),
                            dict(tag='inverse', child=opening), 'inverse', [opening])
            return c.sequence([opening, action, closing])
        body = parallel(*inputs)
        root = c.sequence([body, c.rewire(inputs, outputs)])
        return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
            definitions=c.definitions, meanings=c.meanings, encodings=c.encodings,
            proofs=c.proofs, entry=dict(implementation=root, proof=root))

    def tensor(nodes):
        result = nodes[0]
        for node in nodes[1:]:
            result = c.tensor(result, node)
        return result

    def unpack(p):
        if p['basis'] == [dict(tag='bit')] or not p['axes']:
            return c.identity([p])
        width = len(p['axes'])
        bit = c.fresh(('bit',), p['axes'][:1]).port
        rest = c.fresh(('bits', width-1), p['axes'][1:]).port
        take = c.structural([p], [bit, rest], 'take_bit', width, 0)
        return c.sequence([take, c.tensor(c.identity([bit]), unpack(rest))])

    opening = tensor([unpack(p) for p in inputs])
    atoms = c.ends(opening)[1]
    by_axis = {p['axes'][0]: Quantum(('bit',), p) for p in atoms if p['axes']}
    layers, layer, used, index = [], [], set(), 0
    while index < len(trace):
        gate = trace[index]
        index += 1
        if gate[0] == 'phase':
            _, target, j, k = gate
            selected = [target]
            p = by_axis[target].port
            node = c.add([p], [p], dict(tag='dyadic_phase', target=p['owner'], j=j, k=k),
                         dict(tag='phase', j=j, k=k), 'phase')
        elif gate[0] == 'controlled_phase':
            _, control, target, j, k = gate
            selected = [control, target]
            p = by_axis[target].port
            phase = c.add([p], [p], dict(tag='dyadic_phase', target=p['owner'], j=j, k=k),
                          dict(tag='phase', j=j, k=k), 'phase')
            ps = [by_axis[a].port for a in selected]
            node = c.add(ps, ps, dict(tag='control', definition=phase, polarity=True),
                         dict(tag='control', child=phase, polarity=True), 'control', [phase])
        elif gate[0] == 'cnot':
            control, target = gate[1:]
            targets = [target]
            while index < len(trace) and trace[index][0] == 'cnot' and (
                    trace[index][1] == control and trace[index][2] not in targets):
                targets.append(trace[index][2])
                index += 1
            selected = [control, *targets]
            child = tensor([c.gate('x', by_axis[a]) for a in targets])
            ps = [by_axis[a].port for a in selected]
            node = c.add(ps, ps, dict(tag='control', definition=child, polarity=True),
                         dict(tag='control', child=child, polarity=True), 'control', [child])
        else:
            selected = [gate[1]]
            node = c.gate(gate[0], by_axis[gate[1]])
        if used.intersection(selected):
            layers.append(tensor(layer))
            layer, used = [], set()
        layer.append(node)
        used.update(selected)
    if layer:
        layers.append(tensor(layer))
    c.state = atoms
    c.steps = [opening]
    for node in layers:
        c.apply(node)
    # Output coordinates follow the actual source result's ordered axes. The
    # final relabelling is explicit, including all zero-width ownership slots.
    desired_bits = iter(wires(outputs))
    desired = [by_axis[next(desired_bits)].port if p['axes'] else p for p in atoms]
    owners = [p['owner'] for p in c.state]
    axes = wires(c.state)
    c.steps.append(c.rewire(c.state, atoms, [owners.index(p['owner']) for p in desired],
                           [axes.index(a) for a in wires(desired)]))
    closing = c.add(atoms, inputs, dict(tag='inverse', definition=opening),
                    dict(tag='inverse', child=opening), 'inverse', [opening])
    c.steps += [closing, c.rewire(inputs, outputs)]
    root = c.sequence(c.steps)
    return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
        definitions=c.definitions, meanings=c.meanings, encodings=c.encodings,
        proofs=c.proofs, entry=dict(implementation=root, proof=root))


def compile_source(source, entry, sizes, *, compact=True, modules=None, operations=None):
    return Producer(modules).compile(source, entry, sizes, compact, operations)


def factor_fourier_trace(inputs, outputs, trace):
    """Factor only the complete exact staircase, including result permutation.

    Both operands of controlled phase occur symmetrically in its exponent.
    Within one H-delimited stage these diagonal gates commute. Compare their
    complete multiset as exact dyadic fractions; no float or source name is used.
    The returned artifact still undergoes fresh independent Fourier checking.
    """
    if len(inputs) != 1 or len(outputs) != 1:
        return None
    width = len(inputs[0]['axes'])
    if not 1 <= width <= 8 or inputs[0]['basis'] != [dict(tag='bits', width=width)] or (
            inputs[0]['axes'] != list(range(width)) or outputs[0]['axes'] != list(reversed(range(width)))):
        return None
    index = 0
    for target in reversed(range(width)):
        if index >= len(trace) or trace[index] != ('h', target):
            return None
        index += 1
        found = []
        while index < len(trace) and trace[index][0] == 'controlled_phase':
            _, a, b, j, k = trace[index]
            found.append((min(a, b), max(a, b), Fraction(j, 1 << k)))
            index += 1
        expected = [(control, target, Fraction(1, 1 << (target-control+1)))
                    for control in range(target)]
        if sorted(found) != expected:
            return None
    if index != len(trace):
        return None
    return CorpusFourierCircuit().qft(width)


class CorpusFourierCircuit(SharedGradientCircuit):
    """Same shared staircase, with recursively typed explicit bit reversal."""
    def reversal(self, register):
        width = len(register['axes'])
        if width <= 1:
            return self.identity([register])
        bit = port(500+width, register['axes'][:1], True)
        rest = port(600+width, register['axes'][1:])
        # These output labels give the changed coordinate order explicitly.
        result = port(register['owner'], register['axes'][1:]+register['axes'][:1])
        steps = [self.structural([register], [bit, rest], 'take_bit', width, 0),
                 self.tensor(self.identity([bit]), self.reversal(rest)),
                 self.structural([bit, rest], [result], 'put_bit', width, width-1),
                 self.rewire([result], [register])]
        return self.sequence(steps)

    def qft(self, width):
        self.precision = width
        outer = [port(0, range(width))]
        inner = [self.register(width)]
        root = self.sequence([self.rewire(outer, inner), self.recursive(width),
                              self.rewire(inner, outer), self.reversal(outer[0])])
        return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
            definitions=self.definitions, meanings=self.meanings, encodings=self.encodings,
            proofs=self.proofs, entry=dict(implementation=root, proof=root))


def adjoint_artifact(artifact):
    """Wrap the actual unitary graph in an inverse, preserving all shared data."""
    result = copy.deepcopy(artifact)
    entry = artifact['entry']
    actual = artifact['definitions'][entry['implementation']]
    if actual['effect'] != 'unitary':
        raise SourceError('adjoint requires a unitary artifact')
    interface = dict(inputs=actual['interface']['outputs'], outputs=actual['interface']['inputs'])
    definition, meaning, proof = (len(result[k]) for k in ('definitions', 'meanings', 'proofs'))
    original = artifact['proofs'][entry['proof']]
    result['definitions'].append(dict(interface=interface, effect='unitary',
                                     body=dict(tag='inverse', definition=entry['implementation'])))
    result['meanings'].append(dict(interface=interface,
                                  body=dict(tag='inverse', child=original['meaning'])))
    result['proofs'].append(dict(kind='equation', rule=dict(tag='inverse'),
        premises=[entry['proof']], implementation=definition, meaning=meaning,
        input_encoding=original['output_encoding'], output_encoding=original['input_encoding'],
        witness=dict(template_version=1, parameters=[], references=[])))
    result['entry'] = dict(implementation=definition, proof=proof)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--entry', required=True)
    parser.add_argument('--size', action='append', default=[], metavar='NAME=N')
    parser.add_argument('--module', action='append', default=[], metavar='NAME=FILE')
    parser.add_argument('--operation', action='append', default=[], metavar='PARAM=MODULE::FUNCTION:N,...')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--adjoint', action='store_true')
    args = parser.parse_args()
    try:
        sizes = {}
        for parameter in args.size:
            name, value = parameter.split('=')
            if name in sizes:
                raise SourceError('duplicate static argument')
            sizes[name] = int(value)
        files = list(args.source.parent.glob('*.qli'))
        if len(files) > 64:
            raise SourceError('source directory exceeds 64 modules')
        modules = {p.stem: p.read_text() for p in files}
        for item in args.module:
            module, path = item.split('=', 1)
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', module) or module in modules:
                raise SourceError('invalid or duplicate source module')
            modules[module] = Path(path).read_text()
        operations = {}
        for item in args.operation:
            parameter, value = item.split('=', 1)
            name, values = value.rsplit(':', 1)
            if parameter in operations:
                raise SourceError('duplicate static operation argument')
            operations[parameter] = Operation(name, tuple(int(n) for n in values.split(',')))
        artifact = compile_source(args.source.read_text(), args.entry, sizes, modules=modules, operations=operations)
        if args.adjoint:
            artifact = adjoint_artifact(artifact)
        args.output.write_text(text(artifact)+'\n')
        print(json.dumps(dict(status='untrusted-proposal', definitions=len(artifact['definitions']),
                              bytes=len(text(artifact).encode()))))
    except (OSError, ValueError) as error:
        print(f'sized corpus: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
