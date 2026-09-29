"""First informed phase-gradient factorization, saved before execution.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This is an untrusted IR producer, not an accepted Fourier schema.
"""
from test_hierarchical_qft import Circuit, port


class FactoredCircuit(Circuit):
    def register(self, width):
        return port(200+width, range(width))

    def boundary(self, width):
        register = self.register(width)
        high = port(100+width-1, [width-1], True)
        rest = self.register(width-1)
        take = self.structural([register], [high,rest], 'take_bit', width, width-1)
        put = self.structural([high,rest], [register], 'put_bit', width, width-1)
        return high, rest, take, put

    def gradient(self, width, exponent):
        if width == 0:
            return self.identity([self.register(0)])
        high, rest, take, put = self.boundary(width)
        phase = self.add([high], [high],
            dict(tag='dyadic_phase',target=high['owner'],j=1,k=exponent),
            dict(tag='phase',j=1,k=exponent), 'phase')
        return self.sequence([take, self.tensor(phase,self.gradient(width-1,exponent+1)), put])

    def recursive(self, width):
        if width == 0:
            return self.identity([self.register(0)])
        high, rest, take, put = self.boundary(width)
        stages = [take,self.tensor(self.h(high), self.identity([rest]))]
        if width > 1:
            gradient = self.gradient(width-1,2)
            controlled = self.add([high,rest],[high,rest],
                dict(tag='control',definition=gradient,polarity=True),
                dict(tag='control',child=gradient,polarity=True),'control',[gradient])
            stages.append(controlled)
        stages += [self.tensor(self.identity([high]),self.recursive(width-1)),put]
        return self.sequence(stages)

    def qft(self, width):
        outer = [port(0,range(width))]
        inner = [self.register(width)]
        stages = [self.rewire(outer,inner),self.recursive(width),self.rewire(inner,outer)]
        for low in range(width//2):
            stages.append(self.lifted(width,width-1-low,low,swap_bits=True))
        entry = self.sequence(stages)
        return dict(format='qleisli.hierarchical-ir',version=1,profile='qpe-dyadic8-v1',
            definitions=self.definitions,meanings=self.meanings,encodings=self.encodings,
            proofs=self.proofs,entry=dict(implementation=entry,proof=entry))
