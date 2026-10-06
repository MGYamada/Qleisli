//! Bounded exact linear implication by rational relaxation of integer constraints.
//! Unsatisfiability proves an obligation; incomplete search never supplies evidence.
use super::ast::{BinderKey, Compare};
use super::{Error, Result, Span};
use std::collections::{BTreeMap, BTreeSet};

/// Attach parser provenance at an obligation boundary, keeping the algebraic
/// representation and elimination procedure independent of source locations.
pub(super) fn at<T>(result: Result<T>, span: Span, obligation: &str) -> Result<T> {
    result.map_err(|mut error| {
        if error.span == Span::default() {
            error.span = span;
            error.message = format!("{obligation}: {}", error.message);
        }
        error
    })
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct Linear {
    pub constant: i128,
    pub terms: BTreeMap<BinderKey, i128>,
}
impl std::fmt::Debug for Linear {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct Terms<'a>(&'a BTreeMap<BinderKey, i128>);
        impl std::fmt::Debug for Terms<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_map()
                    .entries(self.0.iter().map(|(key, value)| (&key.name, value)))
                    .finish()
            }
        }
        f.debug_struct("Linear")
            .field("constant", &self.constant)
            .field("terms", &Terms(&self.terms))
            .finish()
    }
}
/// Diagnostic rendering preserves source names without replacing binder identity.
impl std::fmt::Display for Linear {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut written = false;
        for (key, coefficient) in &self.terms {
            if *coefficient == 0 {
                continue;
            }
            if *coefficient < 0 {
                f.write_str("-")?;
            } else if written {
                f.write_str("+")?;
            }
            let magnitude = coefficient.unsigned_abs();
            if magnitude != 1 {
                write!(f, "{magnitude}*")?;
            }
            f.write_str(&key.name)?;
            written = true;
        }
        if self.constant != 0 || !written {
            if self.constant < 0 {
                f.write_str("-")?;
            } else if written {
                f.write_str("+")?;
            }
            write!(f, "{}", self.constant.unsigned_abs())?;
        }
        Ok(())
    }
}
impl Linear {
    pub fn constant(n: i128) -> Self {
        Self {
            constant: n,
            terms: BTreeMap::new(),
        }
    }
    pub fn constant_budgeted(
        n: i128,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, 1)?;
        Ok(Self::constant(n))
    }
    pub fn variable_budgeted(
        name: &BinderKey,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, checked_cells(2, name.name.len())?)?;
        Ok(Self {
            constant: 0,
            terms: BTreeMap::from([(name.clone(), 1)]),
        })
    }
    /// Retained scalar/map cells and UTF-8 name bytes copied by a clone.
    pub fn storage_cells(&self) -> Result<usize> {
        self.terms.keys().try_fold(1usize, |n, key| {
            checked_cells(n, checked_cells(1, key.name.len())?)
        })
    }
    pub fn copy_budgeted(
        &self,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, checked_cells(1, self.terms.len())?)?;
        charge(span, self.storage_cells()?)?;
        Ok(self.clone())
    }
    pub fn scale_budgeted(
        &self,
        n: i128,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, 1)?;
        let overflow = || Error::new("limit", Span::default(), "linear arithmetic overflow");
        let constant = self.constant.checked_mul(n).ok_or_else(overflow)?;
        let mut terms = BTreeMap::new();
        for (key, value) in &self.terms {
            charge(span, 1)?;
            let value = value.checked_mul(n).ok_or_else(overflow)?;
            if value != 0 {
                charge(span, checked_cells(1, key.name.len())?)?;
                terms.insert(key.clone(), value);
            }
        }
        Ok(Self { constant, terms })
    }
    pub fn add_budgeted(
        &self,
        b: &Self,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        let mut result = self.copy_budgeted(span, charge)?;
        result.constant = result
            .constant
            .checked_add(b.constant)
            .ok_or_else(|| Error::new("limit", Span::default(), "linear constant overflow"))?;
        for (key, value) in &b.terms {
            charge(span, 1)?;
            let previous = result.terms.get(key).copied().unwrap_or(0);
            let n = previous.checked_add(*value).ok_or_else(|| {
                Error::new("limit", Span::default(), "linear coefficient overflow")
            })?;
            if n == 0 {
                result.terms.remove(key);
            } else {
                // Existing-key insert still clones the supplied String key.
                let node = usize::from(!result.terms.contains_key(key));
                charge(span, checked_cells(node, key.name.len())?)?;
                result.terms.insert(key.clone(), n);
            }
        }
        Ok(result)
    }
    pub fn sub_budgeted(
        &self,
        b: &Self,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        let negative = b.scale_budgeted(-1, span, charge)?;
        self.add_budgeted(&negative, span, charge)
    }
}
fn checked_cells(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b).ok_or_else(|| {
        Error::new(
            "limit",
            Span::default(),
            "linear storage accounting overflow",
        )
    })
}
#[derive(Clone, Debug)]
pub(in crate::frontend) struct Context {
    pub alternatives: Vec<Vec<Linear>>,
}
impl Context {
    pub fn copy_budgeted(
        &self,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, checked_cells(1, self.alternatives.len())?)?;
        let mut alternatives = Vec::new();
        for row in &self.alternatives {
            charge(span, checked_cells(1, row.len())?)?;
            let mut copied = Vec::new();
            for x in row {
                copied.push(x.copy_budgeted(span, charge)?);
            }
            alternatives.push(copied);
        }
        Ok(Self { alternatives })
    }
    /// Borrowed input prevents an iterator-side BinderKey clone before charge.
    pub fn natural_refs_budgeted<'a>(
        names: impl IntoIterator<Item = &'a BinderKey>,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, 2)?;
        let mut row = Vec::new();
        for name in names {
            charge(span, 1)?;
            let variable = Linear::variable_budgeted(name, span, charge)?;
            let constraint = variable.scale_budgeted(-1, span, charge)?;
            charge(span, 1)?;
            row.push(constraint);
        }
        Ok(Self {
            alternatives: vec![row],
        })
    }
    pub fn push_budgeted(
        &self,
        inequalities: &[Linear],
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        charge(span, self.alternatives.len())?;
        let mut alternatives = Vec::new();
        for a in &self.alternatives {
            charge(span, 1)?;
            let mut row = Vec::new();
            for constraint in a.iter().chain(inequalities) {
                let copy = constraint.copy_budgeted(span, charge)?;
                charge(span, 1)?;
                row.push(copy);
            }
            alternatives.push(row);
        }
        Ok(Self { alternatives })
    }
    pub fn compare_budgeted(
        &self,
        left: Linear,
        op: Compare,
        right: Linear,
        truth: bool,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        at(
            self.compare_inner(left, op, right, truth, span, charge),
            span,
            "while checking static comparison",
        )
    }
    fn compare_inner(
        &self,
        left: Linear,
        op: Compare,
        right: Linear,
        truth: bool,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        let difference = left.sub_budgeted(&right, span, charge)?;
        let neg = difference.scale_budgeted(-1, span, charge)?;
        let one = Linear::constant_budgeted(1, span, charge)?;
        let op = if truth {
            op
        } else {
            match op {
                Compare::Eq => Compare::Ne,
                Compare::Ne => Compare::Eq,
                Compare::Le => Compare::Gt,
                Compare::Lt => Compare::Ge,
                Compare::Ge => Compare::Lt,
                Compare::Gt => Compare::Le,
            }
        };
        charge(
            span,
            if matches!(op, Compare::Ne) {
                4
            } else if matches!(op, Compare::Eq) {
                3
            } else {
                2
            },
        )?;
        let branches = match op {
            Compare::Eq => vec![vec![difference, neg]],
            Compare::Ne => vec![
                vec![difference.add_budgeted(&one, span, charge)?],
                vec![neg.add_budgeted(&one, span, charge)?],
            ],
            Compare::Le => vec![vec![difference]],
            Compare::Lt => vec![vec![difference.add_budgeted(&one, span, charge)?]],
            Compare::Ge => vec![vec![neg]],
            Compare::Gt => vec![vec![neg.add_budgeted(&one, span, charge)?]],
        };
        if self.alternatives.len().saturating_mul(branches.len()) > 64 {
            return Err(Error::new(
                "limit",
                Span::default(),
                "static branch alternatives exceed 64",
            ));
        }
        let count = self
            .alternatives
            .len()
            .checked_mul(branches.len())
            .ok_or_else(|| {
                Error::new(
                    "limit",
                    Span::default(),
                    "linear storage accounting overflow",
                )
            })?;
        charge(span, count)?;
        let mut alternatives = Vec::new();
        for a in &self.alternatives {
            for b in &branches {
                charge(span, 1)?;
                let mut row = Vec::new();
                for constraint in a.iter().chain(b) {
                    let copy = constraint.copy_budgeted(span, charge)?;
                    charge(span, 1)?;
                    row.push(copy);
                }
                alternatives.push(row);
            }
        }
        Ok(Self { alternatives })
    }
    pub fn proves_le_budgeted(
        &self,
        a: &Linear,
        b: &Linear,
        span: Span,
        obligation: &str,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<bool> {
        at(self.proves_le_inner(a, b, span, charge), span, obligation)
    }
    fn proves_le_inner(
        &self,
        a: &Linear,
        b: &Linear,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<bool> {
        let difference = b.sub_budgeted(a, span, charge)?;
        let one = Linear::constant_budgeted(1, span, charge)?;
        let counterexample = difference.add_budgeted(&one, span, charge)?;
        for context in &self.alternatives {
            charge(span, checked_cells(context.len(), 1)?)?;
            let mut constraints = Vec::new();
            for constraint in context {
                constraints.push(constraint.copy_budgeted(span, charge)?);
            }
            constraints.push(counterexample.copy_budgeted(span, charge)?);
            if !unsatisfiable_budgeted(constraints, span, charge)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub fn feasible_budgeted(
        &self,
        span: Span,
        obligation: &str,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<bool> {
        at(self.feasible_inner(span, charge), span, obligation)
    }
    fn feasible_inner(
        &self,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<bool> {
        for a in &self.alternatives {
            charge(span, a.len())?;
            let mut constraints = Vec::new();
            for constraint in a {
                constraints.push(constraint.copy_budgeted(span, charge)?);
            }
            if !unsatisfiable_budgeted(constraints, span, charge)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
fn normalized_budgeted(
    mut x: Linear,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<Linear> {
    let mut divisor = 0u128;
    for n in std::iter::once(&x.constant).chain(x.terms.values()) {
        charge(span, 1)?;
        let mut a = divisor;
        let mut b = n.unsigned_abs();
        while b != 0 {
            charge(span, 1)?;
            let r = a % b;
            a = b;
            b = r;
        }
        divisor = a;
    }
    if divisor > 1 {
        let divisor = i128::try_from(divisor)
            .map_err(|_| Error::new("limit", Span::default(), "linear normalization overflow"))?;
        x.constant /= divisor;
        for value in x.terms.values_mut() {
            charge(span, 1)?;
            *value /= divisor;
        }
    }
    Ok(x)
}
fn unsatisfiable_budgeted(
    mut constraints: Vec<Linear>,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<bool> {
    let mut work = 0usize;
    loop {
        charge(span, 1)?;
        for c in &constraints {
            charge(span, 1)?;
            if c.terms.is_empty() && c.constant > 0 {
                return Ok(true);
            }
        }
        let mut variables = BTreeSet::new();
        for c in &constraints {
            charge(span, 1)?;
            for key in c.terms.keys() {
                charge(span, 1)?;
                let node = usize::from(!variables.contains(key));
                charge(span, checked_cells(node, key.name.len())?)?;
                variables.insert(key.clone());
            }
        }
        if variables.is_empty() {
            return Ok(false);
        }
        if variables.len() > 32 {
            return Err(Error::new(
                "limit",
                Span::default(),
                "linear implication exceeds 32 variables",
            ));
        }
        let mut best = None;
        for name in variables {
            charge(span, 1)?;
            let mut p = 0usize;
            let mut n = 0usize;
            for c in &constraints {
                charge(span, 1)?;
                p += usize::from(c.terms.get(&name).is_some_and(|x| *x > 0));
            }
            for c in &constraints {
                charge(span, 1)?;
                n += usize::from(c.terms.get(&name).is_some_and(|x| *x < 0));
            }
            let score = p.saturating_mul(n);
            if best.as_ref().is_none_or(|(_, prior)| score < *prior) {
                best = Some((name, score));
            }
        }
        let name = best.expect("nonempty solver variables").0;
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        let mut retained = BTreeSet::new();
        for mut c in constraints {
            charge(span, 1)?;
            let n = c.terms.remove(&name).unwrap_or(0);
            match n.cmp(&0) {
                std::cmp::Ordering::Greater => {
                    charge(span, 1)?;
                    positive.push((n, c));
                }
                std::cmp::Ordering::Less => {
                    charge(span, 1)?;
                    negative.push((n, c));
                }
                std::cmp::Ordering::Equal => {
                    let c = normalized_budgeted(c, span, charge)?;
                    if !retained.contains(&c) {
                        charge(span, 1)?;
                    }
                    retained.insert(c);
                }
            }
        }
        for (p, a) in &positive {
            for (n, b) in &negative {
                work += 1;
                if work > 50_000 || retained.len() >= 4096 {
                    return Err(Error::new(
                        "limit",
                        Span::default(),
                        "linear implication work exhausted",
                    ));
                }
                charge(span, 1)?;
                let negative = n.checked_neg().ok_or_else(|| {
                    Error::new("limit", Span::default(), "linear elimination overflow")
                })?;
                let left = a.scale_budgeted(negative, span, charge)?;
                let right = b.scale_budgeted(*p, span, charge)?;
                let sum = left.add_budgeted(&right, span, charge)?;
                let normalized = normalized_budgeted(sum, span, charge)?;
                if !retained.contains(&normalized) {
                    charge(span, 1)?;
                }
                retained.insert(normalized);
            }
        }
        charge(span, retained.len())?;
        constraints = retained.into_iter().collect();
    }
}
