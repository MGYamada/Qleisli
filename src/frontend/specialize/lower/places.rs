//! Lower original ordered places with checked hierarchy structural operations.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::preservation as replay;
use super::*;
use crate::frontend::specialize::elaborate::PlacePartition;
use crate::interchange::json::Value;

enum Operation {
    TakeBit(u32, u32),
    PutBit(u32, u32),
    PackEmpty,
    UnpackEmpty,
    Rename,
}

impl Operation {
    fn inverse(self) -> Self {
        match self {
            Self::TakeBit(width, position) => Self::PutBit(width, position),
            Self::PutBit(width, position) => Self::TakeBit(width, position),
            Self::PackEmpty => Self::UnpackEmpty,
            Self::UnpackEmpty => Self::PackEmpty,
            Self::Rename => Self::Rename,
        }
    }

    fn emit(self, graph: &mut Graph, input: Vec<Port>, output: Vec<Port>) -> Result<usize> {
        match self {
            Self::TakeBit(width, position) => {
                graph.structural(input, output, "take_bit", &[width, position])
            }
            Self::PutBit(width, position) => {
                graph.structural(input, output, "put_bit", &[width, position])
            }
            Self::PackEmpty => graph.structural(input, output, "pack_empty_bits", &[]),
            Self::UnpackEmpty => graph.structural(input, output, "unpack_empty_bits", &[]),
            Self::Rename => graph.rename(input, output),
        }
    }
}

impl Lower<'_> {
    pub(super) fn partition_step(
        &mut self,
        step: &SourceStep,
        partition: PlacePartition,
        before: Vec<Port>,
    ) -> Result<(usize, Vec<Port>)> {
        let partition_axes = |parent: &Port| {
            let mut remainder = parent.axes.clone();
            let selected = remainder
                .drain(partition.start as usize..partition.end as usize)
                .collect();
            vec![selected, remainder]
        };
        let (parent, parts, after) = if partition.taking {
            let [parent] = before.as_slice() else {
                return Err(fail("hierarchy place extraction requires one parent"));
            };
            if parent.axes.len() != partition.width as usize
                || partition.end > partition.width
                || partition.start > partition.end
            {
                return Err(fail("hierarchy place bounds differ from the parent"));
            }
            let parts = self.output_ports(step.output(), partition_axes(parent))?;
            (parent.clone(), parts.clone(), parts)
        } else {
            let [selected, remainder] = before.as_slice() else {
                return Err(fail("hierarchy place restoration requires two owners"));
            };
            let mut ordered = remainder.axes.clone();
            let start = partition.start as usize;
            if start > ordered.len()
                || selected.axes.len() + ordered.len() != partition.width as usize
            {
                return Err(fail(
                    "hierarchy place restoration differs from the original bounds",
                ));
            }
            ordered.splice(start..start, selected.axes.iter().copied());
            let after = self.output_ports(step.output(), vec![ordered])?;
            (after[0].clone(), before.clone(), after)
        };
        let mut actions = Vec::new();
        if partition.bit {
            actions.push((
                vec![parent],
                parts,
                Operation::TakeBit(partition.width, partition.start),
            ));
        } else {
            let [selected, remainder] = parts.as_slice() else {
                return Err(fail(
                    "hierarchy slice requires selected and remainder owners",
                ));
            };
            let size = partition.end - partition.start;
            let mut rest = parent;
            let mut slice = if size == 0 {
                selected.clone()
            } else {
                self.fresh_basis(&SourceType::bits(0), vec![])?
            };
            actions.push((vec![], vec![slice.clone()], Operation::PackEmpty));
            for offset in 0..size {
                let width = partition.width - offset;
                let start = partition.start as usize;
                let mut axes = rest.axes.clone();
                let bit = self.fresh_basis(&SourceType::bit(), vec![axes.remove(start)])?;
                let next = if offset + 1 == size {
                    remainder.clone()
                } else {
                    self.fresh_basis(&SourceType::bits(width - 1), axes)?
                };
                actions.push((
                    vec![rest],
                    vec![bit.clone(), next.clone()],
                    Operation::TakeBit(width, partition.start),
                ));
                rest = next;
                let joined = if offset + 1 == size {
                    selected.clone()
                } else {
                    let axes = [slice.axes.clone(), bit.axes.clone()].concat();
                    self.fresh_basis(&SourceType::bits(offset + 1), axes)?
                };
                actions.push((
                    vec![bit, slice],
                    vec![joined.clone()],
                    Operation::PutBit(offset + 1, offset),
                ));
                slice = joined;
            }
            if size == 0 {
                actions.push((vec![rest], vec![remainder.clone()], Operation::Rename));
            }
        }
        if !partition.taking {
            actions.reverse();
        }
        let nodes = actions
            .into_iter()
            .map(|(input, output, operation)| {
                if partition.taking {
                    operation.emit(&mut self.graph, input, output)
                } else {
                    operation.inverse().emit(&mut self.graph, output, input)
                }
            })
            .collect::<Result<Vec<_>>>()?;
        let node = self.graph.frame(before, &nodes, after.clone())?;
        Ok((node, after))
    }
}

/// Check the complete phase-free place interval and its original ordered ports.
/// Native checking still verifies every structural rule, map and child boundary.
pub(super) fn validate_partition(
    defs: &[Value],
    event: &replay::SourceEvent,
    partition: PlacePartition,
) -> Result<()> {
    let fail = || replay::invalid("hierarchy place changes its original axes or structural action");
    let root = event.node.ok_or_else(fail)?;
    let node = defs.get(root).ok_or_else(fail)?;
    let (before, after) = replay::endpoints(node)?;
    let (parent, parts) = if partition.taking {
        (&before, &after)
    } else {
        (&after, &before)
    };
    let ([parent], [selected, remainder]) = (parent.as_slice(), parts.as_slice()) else {
        return Err(fail());
    };
    let start = partition.start as usize;
    let end = partition.end as usize;
    if start > end || end > partition.width as usize || (partition.bit && end - start != 1) {
        return Err(fail());
    }
    let selected_basis = if partition.bit {
        SourceType::bit()
    } else {
        SourceType::bits(partition.end - partition.start)
    };
    if parent.basis != SourceType::bits(partition.width)
        || parent.axes.len() != partition.width as usize
        || selected.basis != selected_basis
        || remainder.basis != SourceType::bits(partition.width - (partition.end - partition.start))
        || parent.axes.get(start..end) != Some(selected.axes.as_slice())
        || parent.axes[..start]
            .iter()
            .chain(&parent.axes[end..])
            .ne(&remainder.axes)
    {
        return Err(fail());
    }

    // Every checked structural node preserves the actual wire labels.
    // A rewire may rename or change them, so match its actual axis map here.
    let mut pending = vec![root];
    let mut visits = 0;
    while let Some(id) = pending.pop() {
        visits += 1;
        if visits > 128 {
            return Err(fail());
        }
        let node = defs.get(id).ok_or_else(fail)?;
        let body = replay::field(node, "body")?;
        match replay::tag(body)? {
            "sequence" => {
                let children = replay::array(replay::field(body, "children")?)?;
                if children.len() > 128 {
                    return Err(fail());
                }
                for child in children {
                    let child = replay::number(child)?;
                    if child >= id {
                        return Err(fail());
                    }
                    pending.push(child);
                }
            }
            "tensor" => {
                for side in ["left", "right"] {
                    let child = replay::number(replay::field(body, side)?)?;
                    if child >= id {
                        return Err(fail());
                    }
                    pending.push(child);
                }
            }
            "structural" => {}
            "rewire" => {
                let (before, after) = replay::endpoints(node)?;
                let map =
                    replay::indices(replay::field(replay::field(body, "permutation")?, "axes")?)?;
                let wires = axes(&before);
                if map
                    .iter()
                    .map(|&index| wires.get(index).copied())
                    .ne(axes(&after).into_iter().map(Some))
                {
                    return Err(fail());
                }
            }
            _ => return Err(fail()),
        }
    }
    Ok(())
}

#[cfg(all(test, qleisli_native_tests))]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;
    use crate::interchange::hierarchical::Kernel;

    #[test]
    fn hierarchy_place_replay_refuses_a_native_valid_paired_axis_substitution() {
        let lower = |axis| {
            let source = format!(
                "unitary fn id(q:Q<Bit>)->Q<Bit>{{q}} \
                 pub unitary fn entry(q:Q<Bits<2>>)->Q<Bits<2>>{{id(excl q[{axis}]);q}}"
            );
            ParsedProgram::parse(
                crate::edition::Edition::E2026,
                BTreeMap::from([("main".into(), source)]),
            )
            .unwrap()
            .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower()
            .unwrap()
        };
        let original = lower(1);
        let mut changed = lower(0);
        let kernel = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
            original.source().edition(),
        );
        let accepted = kernel
            .check_against_native(changed.payload(), changed.comparison_request())
            .unwrap();
        changed.validate_pure_source_steps(&accepted).unwrap();
        assert!(original.validate_pure_source_steps(&accepted).is_err());
        // Both take/put pairs implement identity. Keep the other valid graph
        // and trace but require the original source's different selected axis.
        changed.source = original.source;
        let failure = changed.validate_pure_source_steps(&accepted).unwrap_err();
        assert_eq!(failure.code(), "preservation");
        assert!(failure.message().contains("original axes"), "{failure}");
    }
}
