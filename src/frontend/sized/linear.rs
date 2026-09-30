//! Bounded exact linear implication by rational relaxation of integer constraints.
//! Unsatisfiability proves an obligation; incomplete search never supplies evidence.
use super::ast::{Compare, NatKind, Natural, Predicate};
use super::{Error, Result, Span};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Linear {
    pub constant: i128,
    pub terms: BTreeMap<String, i128>,
}
impl Linear {
    pub fn constant(n: i128) -> Self {
        Self {
            constant: n,
            terms: BTreeMap::new(),
        }
    }
    pub fn variable(name: &str) -> Self {
        Self {
            constant: 0,
            terms: BTreeMap::from([(name.into(), 1)]),
        }
    }
    pub fn scale(&self, n: i128) -> Result<Self> {
        let overflow = || Error::new("limit", Span::default(), "linear arithmetic overflow");
        Ok(Self {
            constant: self.constant.checked_mul(n).ok_or_else(overflow)?,
            terms: self
                .terms
                .iter()
                .filter_map(|(key, value)| {
                    let value = value.checked_mul(n);
                    match value {
                        Some(0) => None,
                        Some(n) => Some(Ok((key.clone(), n))),
                        None => Some(Err(overflow())),
                    }
                })
                .collect::<Result<_>>()?,
        })
    }
    pub fn add(&self, b: &Self) -> Result<Self> {
        let mut r = self.clone();
        r.constant = r
            .constant
            .checked_add(b.constant)
            .ok_or_else(|| Error::new("limit", Span::default(), "linear constant overflow"))?;
        for (key, value) in &b.terms {
            let previous = r.terms.get(key).copied().unwrap_or(0);
            let n = previous.checked_add(*value).ok_or_else(|| {
                Error::new("limit", Span::default(), "linear coefficient overflow")
            })?;
            if n == 0 {
                r.terms.remove(key);
            } else {
                r.terms.insert(key.clone(), n);
            }
        }
        Ok(r)
    }
    pub fn sub(&self, b: &Self) -> Result<Self> {
        self.add(&b.scale(-1)?)
    }
}
#[derive(Clone, Debug)]
pub(super) struct Context {
    pub alternatives: Vec<Vec<Linear>>,
}
impl Context {
    pub fn natural(names: impl IntoIterator<Item = String>) -> Result<Self> {
        Ok(Self {
            alternatives: vec![
                names
                    .into_iter()
                    .map(|n| Linear::variable(&n).scale(-1))
                    .collect::<Result<_>>()?,
            ],
        })
    }
    pub fn push(&self, inequalities: &[Linear]) -> Self {
        Self {
            alternatives: self
                .alternatives
                .iter()
                .map(|a| a.iter().chain(inequalities).cloned().collect())
                .collect(),
        }
    }
    pub fn compare(&self, left: Linear, op: Compare, right: Linear, truth: bool) -> Result<Self> {
        let difference = left.sub(&right)?;
        let neg = difference.scale(-1)?;
        let one = Linear::constant(1);
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
        let branches = match op {
            Compare::Eq => vec![vec![difference, neg]],
            Compare::Ne => vec![vec![difference.add(&one)?], vec![neg.add(&one)?]],
            Compare::Le => vec![vec![difference]],
            Compare::Lt => vec![vec![difference.add(&one)?]],
            Compare::Ge => vec![vec![neg]],
            Compare::Gt => vec![vec![neg.add(&one)?]],
        };
        if self.alternatives.len().saturating_mul(branches.len()) > 64 {
            return Err(Error::new(
                "limit",
                Span::default(),
                "static branch alternatives exceed 64",
            ));
        }
        Ok(Self {
            alternatives: self
                .alternatives
                .iter()
                .flat_map(|a| {
                    branches
                        .iter()
                        .map(move |b| a.iter().chain(b).cloned().collect())
                })
                .collect(),
        })
    }
    pub fn proves_le(&self, a: &Linear, b: &Linear) -> Result<bool> {
        let counterexample = b.sub(a)?.add(&Linear::constant(1))?;
        for context in &self.alternatives {
            let mut constraints = context.clone();
            constraints.push(counterexample.clone());
            if !unsatisfiable(constraints)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub fn feasible(&self) -> Result<bool> {
        for a in &self.alternatives {
            if !unsatisfiable(a.clone())? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
fn normalized(mut x: Linear) -> Result<Linear> {
    let mut divisor = 0u128;
    for n in std::iter::once(&x.constant).chain(x.terms.values()) {
        let mut a = divisor;
        let mut b = n.unsigned_abs();
        while b != 0 {
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
            *value /= divisor;
        }
    }
    Ok(x)
}
fn unsatisfiable(mut constraints: Vec<Linear>) -> Result<bool> {
    let mut work = 0usize;
    loop {
        if constraints
            .iter()
            .any(|c| c.terms.is_empty() && c.constant > 0)
        {
            return Ok(true);
        }
        let variables: BTreeSet<_> = constraints
            .iter()
            .flat_map(|c| c.terms.keys().cloned())
            .collect();
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
        let name = variables
            .into_iter()
            .min_by_key(|name| {
                let p = constraints
                    .iter()
                    .filter(|c| c.terms.get(name).is_some_and(|x| *x > 0))
                    .count();
                let n = constraints
                    .iter()
                    .filter(|c| c.terms.get(name).is_some_and(|x| *x < 0))
                    .count();
                p.saturating_mul(n)
            })
            .unwrap();
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        let mut retained = BTreeSet::new();
        for mut c in constraints {
            let n = c.terms.remove(&name).unwrap_or(0);
            match n.cmp(&0) {
                std::cmp::Ordering::Greater => positive.push((n, c)),
                std::cmp::Ordering::Less => negative.push((n, c)),
                std::cmp::Ordering::Equal => {
                    retained.insert(normalized(c)?);
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
                retained.insert(normalized(
                    a.scale(n.checked_neg().ok_or_else(|| {
                        Error::new("limit", Span::default(), "linear elimination overflow")
                    })?)?
                    .add(&b.scale(*p)?)?,
                )?);
            }
        }
        constraints = retained.into_iter().collect();
    }
}
pub(super) fn natural(
    expr: &Natural,
    names: &BTreeMap<String, Linear>,
    context: &Context,
) -> Result<Linear> {
    let result = match &expr.kind {
        NatKind::Number(n) => Linear::constant(*n),
        NatKind::Name(name) => names.get(name).cloned().ok_or_else(|| {
            Error::new("static", expr.span, format!("unknown natural name {name}"))
        })?,
        NatKind::Add(a, b) => natural(a, names, context)?.add(&natural(b, names, context)?)?,
        NatKind::Sub(a, b) => {
            let a = natural(a, names, context)?;
            let b = natural(b, names, context)?;
            if !context.proves_le(&b, &a)? {
                return Err(Error::new(
                    "size",
                    expr.span,
                    "subtraction lacks a nonnegative guard",
                ));
            }
            a.sub(&b)?
        }
        NatKind::Mul(a, b) => {
            let a = natural(a, names, context)?;
            let b = natural(b, names, context)?;
            if a.terms.is_empty() {
                b.scale(a.constant)?
            } else if b.terms.is_empty() {
                a.scale(b.constant)?
            } else {
                return Err(Error::new(
                    "unsupported",
                    expr.span,
                    "multiplication of two symbolic sizes is nonlinear",
                ));
            }
        }
    };
    Ok(result)
}
pub(super) fn predicate(
    p: &Predicate,
    names: &BTreeMap<String, Linear>,
    context: &Context,
    truth: bool,
) -> Result<Context> {
    context.compare(
        natural(&p.left, names, context)?,
        p.comparison,
        natural(&p.right, names, context)?,
        truth,
    )
}
