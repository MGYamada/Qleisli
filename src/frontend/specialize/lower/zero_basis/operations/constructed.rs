//! Original constructor-tree correspondence for existing unitary hierarchy nodes.
//! These are transport bindings. Existing independent Lean rules remain mandatory.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

impl Match<'_> {
    /// Bind the actual full arrow to the original constructor's exact type trees.
    pub(super) fn constructed_operation(
        &mut self,
        operation: &SourceOperation,
        id: usize,
        depth: usize,
    ) -> Result<()> {
        let (kind, children, ports) = operation
            .constructed()
            .ok_or_else(|| p::invalid("missing original operation constructor"))?;
        let arity = match kind {
            OperationConstructor::Adjoint | OperationConstructor::Controlled => 1,
            _ => 2,
        };
        if ports.effect != Effect::Unitary || children.len() != arity {
            return Err(p::invalid(
                "zero-basis constructor changes original effect or arity",
            ));
        }
        let (before, after) = self.ports(id)?;
        if before.len() != 1
            || after.len() != 1
            || ports.input.quantum_basis() != Some(&before[0].basis)
            || ports.output.quantum_basis() != Some(&after[0].basis)
        {
            return Err(p::invalid(
                "zero-basis constructor changes original arrow type trees",
            ));
        }
        let body = if ports.input == ports.output {
            let parts = self.sequence(id, 2)?;
            let (first, last) = self.ports(parts[0])?;
            self.rename(parts[1], &last, &first)?;
            parts[0]
        } else {
            id
        };
        match kind {
            OperationConstructor::Adjoint => {
                let child = self.inverse(body)?;
                self.operation(&children[0], child, depth + 1)
            }
            OperationConstructor::Then | OperationConstructor::Conjugate => {
                self.composed(kind, children, body, depth + 1)
            }
            OperationConstructor::Tensor | OperationConstructor::Controlled => {
                self.packed(kind, children, body, depth + 1)
            }
        }
    }

    /// Match the two/three original actions and every ordered type-preserving bridge.
    fn composed(
        &mut self,
        kind: OperationConstructor,
        children: &[SourceOperation],
        id: usize,
        depth: usize,
    ) -> Result<()> {
        let conjugate = kind == OperationConstructor::Conjugate;
        let parts = self.sequence(id, if conjugate { 5 } else { 3 })?;
        let first = if conjugate {
            self.inverse(parts[0])?
        } else {
            parts[0]
        };
        self.operation(&children[0], first, depth)?;
        self.operation(&children[1], parts[2], depth)?;
        let (_, first_output) = self.ports(parts[0])?;
        let (middle_input, middle_output) = self.ports(parts[2])?;
        self.rename(parts[1], &first_output, &middle_input)?;
        if conjugate {
            if parts[4] != first {
                return Err(p::invalid(
                    "zero-basis conjugation substitutes its original outer action",
                ));
            }
            let (last_input, _) = self.ports(first)?;
            self.rename(parts[3], &middle_output, &last_input)?;
        }
        Ok(())
    }

    /// Check the producer's explicit binary split/join, including zero-width owners.
    fn packed_boundary(&mut self, id: usize, split: bool) -> Result<(Port, Vec<Port>)> {
        let (before, after) = self.ports(id)?;
        let (packed, fields) = if split {
            (before, after)
        } else {
            (after, before)
        };
        if packed.len() != 1
            || fields.len() != 2
            || packed[0].basis != SourceType::pair(fields[0].basis.clone(), fields[1].basis.clone())
            || packed[0].axes != axes(&fields)
            || fields.iter().any(|field| field.owner == packed[0].owner)
        {
            return Err(p::invalid(
                "zero-basis packed constructor changes ordered fields or owners",
            ));
        }
        let body = p::field(self.node(id)?, "body")?;
        let expected = if split { "split_tuple" } else { "join_tuple" };
        if p::tag(body)? != "structural" || p::tag(p::field(body, "operation")?)? != expected {
            return Err(p::invalid(
                "zero-basis packed constructor substitutes split/join",
            ));
        }
        Ok((packed[0].clone(), fields))
    }

    /// Bind tensor/control's split, factor bindings and join without flattening bases.
    fn packed(
        &mut self,
        kind: OperationConstructor,
        children: &[SourceOperation],
        id: usize,
        depth: usize,
    ) -> Result<()> {
        let parts = self.sequence(id, 3)?;
        let (_, inputs) = self.packed_boundary(parts[0], true)?;
        let (_, outputs) = self.packed_boundary(parts[2], false)?;
        if self.ports(parts[1])? != (inputs.clone(), outputs.clone()) {
            return Err(p::invalid(
                "zero-basis packed body changes its complete field interfaces",
            ));
        }
        if kind == OperationConstructor::Tensor {
            let body = p::field(self.node(parts[1])?, "body")?;
            if p::tag(body)? != "tensor" {
                return Err(p::invalid(
                    "zero-basis tensor replaces the original ordered factors",
                ));
            }
            let left = p::number(p::field(body, "left")?)?;
            let right = p::number(p::field(body, "right")?)?;
            self.bound(
                &children[0],
                left,
                &inputs[..1],
                &outputs[..1],
                false,
                depth,
            )?;
            self.bound(
                &children[1],
                right,
                &inputs[1..],
                &outputs[1..],
                false,
                depth,
            )
        } else {
            let body = p::field(self.node(parts[1])?, "body")?;
            if p::tag(body)? != "control"
                || p::field(body, "polarity")? != &Value::Bool(true)
                || inputs[0].basis != SourceType::bit()
                || inputs[0].axes.len() != 1
                || inputs != outputs
            {
                return Err(p::invalid(
                    "zero-basis constructed control changes original control/target",
                ));
            }
            let child = p::number(p::field(body, "definition")?)?;
            let closed = self.sequence(child, 2)?;
            let (first, last) = self.ports(closed[0])?;
            if first.as_slice() != &inputs[1..] {
                return Err(p::invalid(
                    "zero-basis constructed control changes target binding",
                ));
            }
            self.bound(&children[0], closed[0], &first, &last, false, depth)?;
            self.rename(closed[1], &last, &inputs[1..])?;
            if axes(&last) != axes(&inputs[1..]) {
                return Err(p::invalid(
                    "zero-basis constructed control changes returned target axes",
                ));
            }
            Ok(())
        }
    }
}
