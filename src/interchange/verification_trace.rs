//! Optional observations for CLI routing. No observation grants acceptance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;

use super::{Error, native_context::Mode};

#[derive(Default)]
pub struct Trace {
    pub requests: Vec<Request>,
    pub omitted: usize,
}

pub struct Request {
    pub identity: String,
    pub subject: Option<String>,
    pub obligation: &'static str,
    pub edition: Option<u32>,
    pub scope: Option<&'static str>,
    pub decision: &'static str,
    pub diagnostic: Option<&'static str>,
}

thread_local! {
    static ACTIVE: RefCell<Option<Trace>> = const { RefCell::new(None) };
}

pub fn capture<T>(action: impl FnOnce() -> T) -> (T, Trace) {
    struct Restore(Option<Trace>);
    impl Drop for Restore {
        fn drop(&mut self) {
            ACTIVE.replace(self.0.take());
        }
    }

    let _restore = Restore(ACTIVE.replace(Some(Trace::default())));
    let result = action();
    (result, ACTIVE.take().expect("active trace"))
}

pub(super) fn pending(identity: &str, mode: Mode, packet: &[u8]) -> Option<Request> {
    ACTIVE.with_borrow_mut(|active| {
        let trace = active.as_mut()?;
        if trace.requests.len() >= 128 {
            trace.omitted += 1;
            return None;
        }
        let source = if mode == Mode::OpenQasmPlacement {
            let length = word(packet, 4)? as usize;
            packet.get(16..16usize.checked_add(length)?)?
        } else {
            packet
        };
        let envelope = source.strip_prefix(b"QLV3");
        let subject = envelope
            .and_then(|source| source.get(24..24usize.checked_add(word(source, 8)? as usize)?))
            .map(crate::digest::sha256);
        let scope = match envelope.and_then(|source| word(source, 4)) {
            Some(0) => Some("inspection"),
            Some(1) => Some("execution"),
            Some(2) => Some("caller"),
            _ => None,
        };
        Some(Request {
            identity: identity.to_owned(),
            subject,
            obligation: mode.argument(),
            edition: envelope.and_then(|source| word(source, 0)),
            scope,
            decision: mode.status(),
            diagnostic: None,
        })
    })
}

fn word(bytes: &[u8], offset: usize) -> Option<u32> {
    Some(u32::from_le_bytes(
        bytes.get(offset..offset + 4)?.try_into().ok()?,
    ))
}

pub(super) fn finish(mut trace: Request, error: Option<&Error>) {
    if let Some(error) = error {
        trace.decision = "failed";
        trace.diagnostic = Some(error.code);
    }
    ACTIVE.with_borrow_mut(|active| {
        if let Some(active) = active {
            active.requests.push(trace);
        }
    });
}
