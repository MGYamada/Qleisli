//! Bounded exact linear implication by rational relaxation of integer constraints.
//! Unsatisfiability proves an obligation; incomplete search never supplies evidence.
use super::ast::{Compare, Span};
use super::error::{Error, Result};
use super::resolve::locals::BinderKey;
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
    /// Simultaneous substitution over original binder identities. Replacement
    /// expressions belong to the caller: never substitute inside them again.
    /// This is exact affine arithmetic, not evaluation or acceptance evidence.
    pub fn substitute_budgeted(
        &self,
        values: &BTreeMap<BinderKey, Self>,
        span: Span,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<Self> {
        let mut result = Self::constant_budgeted(self.constant, span, charge)?;
        for (key, coefficient) in &self.terms {
            charge(span, 1)?;
            let replacement = values.get(key).ok_or_else(|| {
                Error::new(
                    "static",
                    span,
                    format!("unbound natural parameter {}", key.name),
                )
            })?;
            let scaled = replacement.scale_budgeted(*coefficient, span, charge)?;
            result = result.add_budgeted(&scaled, span, charge)?;
        }
        Ok(result)
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

#[cfg(test)]
mod substitution_tests {
    use super::*;
    use crate::frontend::parser::parse_module;
    use crate::frontend::resolve::Resolution;
    use crate::frontend::resolve::locals::Index;

    fn keys() -> (BinderKey, BinderKey, BinderKey) {
        let module =
            parse_module("fn f[static n:Nat,static p:Nat]()->Bit{0} fn g[static n:Nat]()->Bit{0}")
                .unwrap();
        let resolution = Resolution::new([("main", &module)]).unwrap();
        let owner = resolution.module("main").unwrap();
        let mut keys = Vec::new();
        for declaration in &module.decls {
            let id = resolution.local(owner, &declaration.name.text).unwrap();
            let index = Index::new_budgeted(
                id,
                declaration,
                |_| None,
                |_, _| Ok::<_, std::convert::Infallible>(()),
            )
            .unwrap();
            keys.extend(
                declaration
                    .static_params
                    .iter()
                    .map(|p| index.table.key(index.binder(&p.name)).clone()),
            );
        }
        (keys.remove(0), keys.remove(0), keys.remove(0))
    }
    fn unlimited(_: Span, _: usize) -> Result<()> {
        Ok(())
    }
    fn expression(constant: i128, terms: &[(BinderKey, i128)]) -> Linear {
        Linear {
            constant,
            terms: terms.iter().cloned().collect(),
        }
    }

    #[test]
    fn same_spelling_in_another_definition_cannot_supply_a_binding() {
        let (formal, _, caller) = keys();
        assert_eq!(formal.name, caller.name);
        let original = expression(0, &[(formal, 1)]);
        let values = BTreeMap::from([(caller, Linear::constant(3))]);
        let span = Span::new(17, 23);
        let error = original
            .substitute_budgeted(&values, span, &mut unlimited)
            .unwrap_err();
        assert_eq!(error.code(), "static");
        assert_eq!(error.span(), span);
    }

    #[test]
    fn replacements_are_simultaneous_even_when_keys_overlap() {
        let (n, p, _) = keys();
        let original = expression(0, &[(n.clone(), 1), (p.clone(), 1)]);
        let values = BTreeMap::from([
            (n, expression(1, &[(p.clone(), 1)])),
            (p.clone(), Linear::constant(8)),
        ]);
        let result = original
            .substitute_budgeted(&values, Span::default(), &mut unlimited)
            .unwrap();
        assert_eq!(result, expression(9, &[(p, 1)]));
    }

    #[test]
    fn affine_substitution_agrees_with_an_independent_scalar_calculation() {
        let (n, p, caller) = keys();
        // 7 + 3*n - 2*p, with n = 2*x+1 and p = x+4.
        let original = expression(7, &[(n.clone(), 3), (p.clone(), -2)]);
        let values = BTreeMap::from([
            (n, expression(1, &[(caller.clone(), 2)])),
            (p, expression(4, &[(caller.clone(), 1)])),
        ]);
        let result = original
            .substitute_budgeted(&values, Span::default(), &mut unlimited)
            .unwrap();
        for x in 0..=7 {
            let actual = result.constant + result.terms[&caller] * x;
            assert_eq!(actual, 7 + 3 * (2 * x + 1) - 2 * (x + 4));
        }
        assert_eq!(result, expression(2, &[(caller, 4)]));
    }

    #[test]
    fn overflow_is_a_capacity_failure_without_wrapping() {
        let (n, _, _) = keys();
        let original = expression(0, &[(n.clone(), 2)]);
        let values = BTreeMap::from([(n, Linear::constant(i128::MAX))]);
        let error = original
            .substitute_budgeted(&values, Span::default(), &mut unlimited)
            .unwrap_err();
        assert_eq!(error.code(), "limit");
    }

    #[test]
    fn accounting_failure_stops_before_retaining_a_replacement() {
        let (n, _, caller) = keys();
        let original = expression(0, &[(n.clone(), 1)]);
        let values = BTreeMap::from([(n, expression(0, &[(caller, 1)]))]);
        let span = Span::new(20, 25);
        let mut remaining = 3usize;
        let mut visits = 0;
        let error = original
            .substitute_budgeted(&values, span, &mut |site, cells| {
                visits += 1;
                remaining = remaining
                    .checked_sub(cells)
                    .ok_or_else(|| Error::new("limit", site, "test budget exhausted"))?;
                Ok(())
            })
            .unwrap_err();
        assert_eq!(error.code(), "limit");
        assert_eq!(error.span(), span);
        assert!(visits <= 5, "accounting continued after a refusal");
        assert_eq!(values.len(), 1);
    }
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
