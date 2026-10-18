//! Structural links from an executed checked leaf to retained original Raw evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

/// Translate the already bounded exact native boundary without erasing type trees.
fn basis(ty: &BasisType) -> SourceType {
    match ty {
        BasisType::Unit => SourceType::unit(),
        BasisType::Bit => SourceType::bit(),
        BasisType::Bits(width) => SourceType::bits(*width),
        BasisType::Pair(a, b) => SourceType::pair(basis(a), basis(b)),
        BasisType::Tuple(fields) => SourceType::tuple(fields.iter().map(basis).collect()),
    }
}

impl Match<'_> {
    /// Check an actual leaf wrapper, keeping dormant dependency checking separate.
    pub(super) fn native_source(
        &mut self,
        trace: &NativeSourceTrace,
        operation: &SourceOperation,
        depth: usize,
    ) -> Result<usize> {
        if depth > 64 {
            return Err(p::invalid(
                "native source binding exceeds original operation depth",
            ));
        }
        let key = self.operation_key(operation)?;
        if trace.witness.key() != &key {
            return Err(p::invalid(
                "native source binding changes its original operation or depth",
            ));
        }
        let parts = self.sequence(trace.node, 2)?;
        if parts[1] != trace.actual {
            return Err(p::invalid(
                "native source binding substitutes the actual checked provider",
            ));
        }
        let actual = self.sequence(trace.actual, 2)?;
        let (input, output) = self.ports(actual[0])?;
        let boundary = trace.witness.boundary();
        let expected = basis(boundary.signature());
        for (ports, port) in [(&input, boundary.input()), (&output, boundary.output())] {
            if ports.len() != 1
                || ports[0].basis != expected
                || ports[0].owner != port.token.0
                || ports[0].axes != port.wires.iter().map(|wire| wire.0).collect::<Vec<_>>()
            {
                return Err(p::invalid(
                    "native source binding changes the exact checked leaf boundary",
                ));
            }
        }
        let leaf = p::field(self.node(actual[0])?, "body")?;
        if p::tag(leaf)? != "leaf" {
            return Err(p::invalid(
                "native source binding replaces its actual finite leaf",
            ));
        }
        self.rename(actual[1], &output, &input)?;
        let retained = p::field(self.node(parts[0])?, "body")?;
        if p::tag(retained)? != "repeat"
            || p::number(p::field(retained, "count")?)? != 0
            || self.ports(parts[0])? != (input.clone(), input.clone())
        {
            return Err(p::invalid(
                "native source dependency changes its zero-repeat role",
            ));
        }
        // A retained original graph is a dependency obligation, not a proof
        // that its mathematical action equals the executed native leaf.
        let retained = p::field(self.node(parts[0])?, "body")?;
        let closed = p::number(p::field(retained, "definition")?)?;
        let closed = self.sequence(closed, 2)?;
        let (first, last) = self.ports(closed[0])?;
        if first != input {
            return Err(p::invalid(
                "native source dependency changes its complete caller boundary",
            ));
        }
        let original = self.bound_links(closed[0], &input, &last, false)?;
        if original != trace.original {
            return Err(p::invalid(
                "native source dependency substitutes the retained original root",
            ));
        }
        self.original_operation(operation, original, depth + 1)?;
        self.rename(closed[1], &last, &input)?;
        if axes(&last) != axes(&input) {
            return Err(p::invalid(
                "native source dependency changes original returned coordinates",
            ));
        }
        Ok(actual[0])
    }
}
