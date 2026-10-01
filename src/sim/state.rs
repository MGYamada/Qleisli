//! Numerical state and owned wire bookkeeping for finite reference execution.
//! Neither numerical cleanup alarms nor this state representation issue evidence.
use std::collections::BTreeMap;

use super::{
    AUXILIARY_LEAKAGE_ALARM, SimulationError, SimulationLimits, bit, check_amplitude_cells,
    check_dimension,
};
use crate::ir::{ClassicalId, TokenId, WireId};

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Complex {
    pub(super) re: f64,
    pub(super) im: f64,
}

impl Complex {
    pub(super) const ZERO: Self = Self { re: 0.0, im: 0.0 };
    pub(super) const ONE: Self = Self { re: 1.0, im: 0.0 };

    pub(super) fn scaled(self, factor: f64) -> Self {
        Self {
            re: self.re * factor,
            im: self.im * factor,
        }
    }

    pub(super) fn norm_squared(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
}

impl std::ops::Add for Complex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl std::ops::AddAssign for Complex {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::Sub for Complex {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl std::ops::Mul for Complex {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Component {
    /// Axis 0 is the least significant bit in the state-vector index.
    pub(super) axes: Vec<WireId>,
    pub(super) amplitudes: Vec<Complex>,
    pub(super) tokens: BTreeMap<TokenId, Vec<WireId>>,
    pub(super) classical: BTreeMap<ClassicalId, bool>,
}

impl Component {
    pub(super) fn vacuum() -> Self {
        Self {
            axes: Vec::new(),
            amplitudes: vec![Complex::ONE],
            tokens: BTreeMap::new(),
            classical: BTreeMap::new(),
        }
    }

    pub(super) fn position(&self, wire: WireId) -> Result<usize, SimulationError> {
        self.axes
            .iter()
            .position(|candidate| *candidate == wire)
            .ok_or(SimulationError::InconsistentVerifiedIr(
                "wire axis is missing",
            ))
    }

    /// Resolve ordered interface wires without changing their axis order.
    pub(super) fn positions(&self, wires: &[WireId]) -> Result<Vec<usize>, SimulationError> {
        wires.iter().map(|wire| self.position(*wire)).collect()
    }

    pub(super) fn take(&mut self, token: TokenId) -> Result<Vec<WireId>, SimulationError> {
        self.tokens
            .remove(&token)
            .ok_or(SimulationError::InconsistentVerifiedIr("token is missing"))
    }

    pub(super) fn classical(&self, id: ClassicalId) -> Result<bool, SimulationError> {
        self.classical
            .get(&id)
            .copied()
            .ok_or(SimulationError::InconsistentVerifiedIr(
                "classical value is missing",
            ))
    }

    pub(super) fn add_zero_wire(
        &mut self,
        wire: WireId,
        limits: SimulationLimits,
    ) -> Result<(), SimulationError> {
        check_dimension(self.axes.len() + 1, limits)?;
        check_amplitude_cells(self.amplitudes.len() * 2, limits)?;
        self.axes.push(wire);
        self.amplitudes
            .resize(self.amplitudes.len() * 2, Complex::ZERO);
        Ok(())
    }

    /// Project one wire, then remove its axis. The probability weight remains
    /// in the norm of the resulting vector.
    pub(super) fn project_remove(
        &self,
        wire: WireId,
        outcome: bool,
    ) -> Result<Self, SimulationError> {
        let axis = self.position(wire)?;
        let mask = 1usize << axis;
        let mut projected = vec![Complex::ZERO; self.amplitudes.len() / 2];
        for (old_index, amplitude) in self.amplitudes.iter().copied().enumerate() {
            if (old_index & mask != 0) == outcome {
                let low = old_index & (mask - 1);
                let high = old_index >> (axis + 1);
                projected[low | (high << axis)] = amplitude;
            }
        }
        let mut component = Self {
            axes: self.axes.clone(),
            amplitudes: projected,
            tokens: self.tokens.clone(),
            classical: self.classical.clone(),
        };
        component.axes.remove(axis);
        Ok(component)
    }

    pub(super) fn weight(&self) -> f64 {
        self.amplitudes.iter().map(|z| z.norm_squared()).sum()
    }

    pub(super) fn remove_certified_zero(&self, wire: WireId) -> Result<Self, SimulationError> {
        let axis = self.position(wire)?;
        let mut scale = 0.0_f64;
        let mut total_weight = 0.0;
        for amplitude in &self.amplitudes {
            scale = scale.max(amplitude.re.abs()).max(amplitude.im.abs());
            total_weight += amplitude.norm_squared();
        }
        // Retain the non-finite-weight alarm, including overflow from finite
        // amplitudes, which the scaled diagnostic calculation could hide.
        if !total_weight.is_finite() {
            return Err(SimulationError::InconsistentVerifiedIr(
                "non-finite amplitude weight during certified auxiliary cleanup",
            ));
        }
        if scale > 0.0 {
            // Ensemble components are unnormalized. Scale only this ratio
            // calculation so squaring tiny amplitudes cannot erase leakage.
            // Divide directly: even a finite subnormal scale may have an
            // infinite reciprocal. Stored amplitudes remain untouched.
            let mut kept_weight = 0.0;
            let mut leaked_weight = 0.0;
            for (index, amplitude) in self.amplitudes.iter().enumerate() {
                let weight = Complex {
                    re: amplitude.re / scale,
                    im: amplitude.im / scale,
                }
                .norm_squared();
                if bit(index, axis) {
                    leaked_weight += weight;
                } else {
                    kept_weight += weight;
                }
            }
            if leaked_weight / (kept_weight + leaked_weight) > AUXILIARY_LEAKAGE_ALARM {
                return Err(SimulationError::InconsistentVerifiedIr(
                    "certified auxiliary has nonzero numerical leakage",
                ));
            }
        }
        // Exact raw-IR evidence is the only permission to release. Preserve
        // the projected amplitudes, including their numerical mass; do not
        // renormalize the component or turn this alarm into postselection.
        self.project_remove(wire, false)
    }
}
