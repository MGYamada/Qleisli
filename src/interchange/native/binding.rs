//! Bind the exact prepared allocations to the native QDV1 comparison.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{
    execution_view::finite,
    native_packet::{Caller, View},
};

impl Prepared {
    pub(super) fn graph(&self) -> finite::Graph<'_> {
        finite::Graph {
            graph: &self.decoded,
            root: &self.decoded.programs[self.decoded.root],
            interface: self.decoded.interface.as_ref(),
            effect: self.derived_effect,
            outputs: &self.output_ports,
        }
    }

    pub(super) fn description(&self) -> Result<Vec<u8>> {
        let graph = self.graph();
        finite::graph(
            graph.graph,
            graph.root,
            graph.interface,
            graph.effect,
            graph.outputs,
        )
    }
}

impl Kernel {
    pub(super) fn check_bound(
        &self,
        artifact: &[u8],
        request: Option<&[u8]>,
        mode: &str,
        describe: impl FnOnce(&Prepared) -> Result<Vec<u8>>,
        caller: Option<&Caller>,
    ) -> Result<Checked> {
        let subject = self.subject(artifact, request)?;
        let prepared = Prepared::new(Arc::clone(&subject)).and_then(|prepared| {
            let graph = describe(&prepared)?;
            Ok((prepared, graph))
        });
        let (prepared, graph) = match prepared {
            Ok(value) => value,
            Err(error) => {
                // Preserve the original native rejection if both decoders fail.
                // Inspection success cannot expose the failed prepared value.
                Self::inspect_subject(subject, mode)?;
                return Err(error);
            }
        };
        let native = Self::submit_subject(
            subject,
            mode,
            Some(View {
                graph: &graph,
                caller: caller.map(|c| (c.bytes.as_slice(), c.indices.as_slice())),
            }),
        )?;
        prepared.bind(native)
    }
}
