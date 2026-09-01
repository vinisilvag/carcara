use crate::{
    ast::{
        Constant, MatchCase, Operator, Rc, Term, match_term,
        pool::TermPool, polyeq,
    },
    checker::{
        error::CheckerError,
        rules::assert_polyeq_expected,
    },
};
use std::{cmp, ops::{Deref, DerefMut}, time::Duration};

/// A normalized representation of a string concatenation term.
///
/// In this flat form:
/// - All nested `str.++` applications are dissolved.
/// - String constants are broken down into single-character constant terms.
/// - Empty string constants `""` are eliminated.
///
/// This representation is the canonical form used across string theory checking rules
/// (CPC calculus) for prefix/suffix extraction, unification, and comparison.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NormalizedConcat(pub Vec<Rc<Term>>);

impl NormalizedConcat {
    /// Creates a new `NormalizedConcat` wrapping a vector of terms.
    pub fn new(terms: Vec<Rc<Term>>) -> Self {
        Self(terms)
    }

    /// Normalizes a string term into flat form.
    ///
    /// Dissolves all `str.++` applications and splits string constants into
    /// single-character string terms. Empty strings are omitted.
    pub fn from_term(pool: &mut dyn TermPool, term: &Rc<Term>) -> Self {
        let mut terms = Vec::new();
        Self::flatten_term(pool, term, &mut terms);
        Self(terms)
    }

    /// Recursively flattens a term into an accumulator vector without allocating
    /// intermediate vectors.
    fn flatten_term(pool: &mut dyn TermPool, term: &Rc<Term>, acc: &mut Vec<Rc<Term>>) {
        if let Term::Const(Constant::String(s)) = term.as_ref() {
            acc.extend(
                s.chars()
                    .map(|c| pool.add(Term::Const(Constant::String(c.to_string())))),
            );
        } else if let Some(args) = match_term!((strconcat ...) = term) {
            for arg in args {
                Self::flatten_term(pool, arg, acc);
            }
        } else {
            acc.push(term.clone());
        }
    }

    /// Extracts subterms by flattening `str.++` applications, but without splitting
    /// string constants into single characters. Empty strings are omitted.
    pub fn from_term_unsplit(term: &Rc<Term>) -> Self {
        let mut terms = Vec::new();
        Self::extract_unsplit_inner(term, &mut terms);
        Self(terms)
    }

    fn extract_unsplit_inner(term: &Rc<Term>, acc: &mut Vec<Rc<Term>>) {
        if let Term::Const(Constant::String(s)) = term.as_ref() {
            if !s.is_empty() {
                acc.push(term.clone());
            }
        } else if let Some(args) = match_term!((strconcat ...) = term) {
            for arg in args {
                Self::extract_unsplit_inner(arg, acc);
            }
        } else {
            acc.push(term.clone());
        }
    }

    /// Converts this normalized sequence back into an AST [`Rc<Term>`].
    ///
    /// - If the sequence is empty, returns the empty string term `""`.
    /// - If it contains exactly one term, returns that term directly.
    /// - If it contains more than one term, returns an application `(str.++ ...)`.
    pub fn to_term(&self, pool: &mut dyn TermPool) -> Rc<Term> {
        match self.0.as_slice() {
            [] => pool.add(Term::new_string("")),
            [single] => single.clone(),
            _ => pool.add(Term::Op(Operator::StrConcat, self.0.clone())),
        }
    }

    /// Consumes `self` and converts it into an AST [`Rc<Term>`].
    pub fn into_term(self, pool: &mut dyn TermPool) -> Rc<Term> {
        match self.0.len() {
            0 => pool.add(Term::new_string("")),
            1 => self.0.into_iter().next().unwrap(),
            _ => pool.add(Term::Op(Operator::StrConcat, self.0)),
        }
    }

    /// Checks if two normalized slices are compatible prefixes of each other.
    ///
    /// Pairwise compares elements from head to tail. If either slice is empty,
    /// or if all overlapping elements match, returns `true`; otherwise `false`.
    pub fn is_compatible(s: &[Rc<Term>], t: &[Rc<Term>]) -> bool {
        s.iter().zip(t).all(|(a, b)| a == b)
    }

    /// Computes the minimal index offset where `s` and `t` become compatible.
    ///
    /// If `s` and `t` are already compatible, returns `0`. Otherwise, drops elements from
    /// the head of `s` until a compatible suffix is found, returning the number of dropped terms.
    pub fn overlap(s: &[Rc<Term>], t: &[Rc<Term>]) -> usize {
        let mut current = s;
        let mut dropped = 0;
        while current.len() > 1 {
            if Self::is_compatible(current, t) {
                return dropped;
            }
            current = &current[1..];
            dropped += 1;
        }
        dropped
    }

    /// Checks if `self` is a prefix of `target`.
    pub fn assert_is_prefix_of(
        &self,
        target: &Self,
        orig_prefix: &Rc<Term>,
        orig_target: &Rc<Term>,
        polyeq_time: &mut Duration,
    ) -> Result<(), CheckerError> {
        self.assert_is_prefix_or_suffix_of(target, orig_prefix, orig_target, false, polyeq_time)
    }

    /// Checks if `self` is a suffix of `target`.
    pub fn assert_is_suffix_of(
        &self,
        target: &Self,
        orig_suffix: &Rc<Term>,
        orig_target: &Rc<Term>,
        polyeq_time: &mut Duration,
    ) -> Result<(), CheckerError> {
        self.assert_is_prefix_or_suffix_of(target, orig_suffix, orig_target, true, polyeq_time)
    }

    /// Checks if `self` is a prefix (rev = `false`) or suffix (rev = `true`) of `target`.
    ///
    /// Asserts equality of each overlapping element using `polyeq`. Returns an error
    /// if `self` is longer than `target` or if any element does not match.
    pub fn assert_is_prefix_or_suffix_of(
        &self,
        target: &Self,
        orig_prefix: &Rc<Term>,
        orig_target: &Rc<Term>,
        rev: bool,
        polyeq_time: &mut Duration,
    ) -> Result<(), CheckerError> {
        if self.len() > target.len() {
            if rev {
                return Err(CheckerError::ExpectedToBeSuffix(
                    orig_prefix.clone(),
                    orig_target.clone(),
                ));
            } else {
                return Err(CheckerError::ExpectedToBePrefix(
                    orig_prefix.clone(),
                    orig_target.clone(),
                ));
            }
        }

        if rev {
            for (el, t_el) in self.iter().rev().zip(target.iter().rev()) {
                assert_polyeq_expected(el, t_el.clone(), polyeq_time)?;
            }
        } else {
            for (el, t_el) in self.iter().zip(target.iter()) {
                assert_polyeq_expected(el, t_el.clone(), polyeq_time)?;
            }
        }
        Ok(())
    }

    /// Removes the longest common prefix (rev = `false`) or suffix (rev = `true`) between
    /// `self` and `other`.
    ///
    /// Returns the remaining tails as a tuple `(remaining_self, remaining_other)`.
    /// Returns an error if either sequence is empty.
    pub fn strip_prefix_or_suffix(
        &self,
        other: &Self,
        orig_self: &Rc<Term>,
        orig_other: &Rc<Term>,
        rev: bool,
        polyeq_time: &mut Duration,
    ) -> Result<(Self, Self), CheckerError> {
        if self.is_empty() {
            return Err(CheckerError::TermOfWrongForm("(str.++ ...)", orig_self.clone()));
        }
        if other.is_empty() {
            return Err(CheckerError::TermOfWrongForm("(str.++ ...)", orig_other.clone()));
        }

        let mut prefix_len = 0;
        let min_len = cmp::min(self.len(), other.len());

        if rev {
            while prefix_len < min_len
                && polyeq(
                    &self[self.len() - 1 - prefix_len],
                    &other[other.len() - 1 - prefix_len],
                    polyeq_time,
                )
            {
                prefix_len += 1;
            }
            let s_rem = self[..self.len() - prefix_len].to_vec();
            let t_rem = other[..other.len() - prefix_len].to_vec();
            Ok((Self(s_rem), Self(t_rem)))
        } else {
            while prefix_len < min_len
                && polyeq(&self[prefix_len], &other[prefix_len], polyeq_time)
            {
                prefix_len += 1;
            }
            let s_rem = self.get(prefix_len..).unwrap_or_default().to_vec();
            let t_rem = other.get(prefix_len..).unwrap_or_default().to_vec();
            Ok((Self(s_rem), Self(t_rem)))
        }
    }

    /// Standardizes String constants and `str.++` applications across an entire AST term.
    ///
    /// - Constants of length > 1 are broken into `str.++` of single characters.
    /// - Nested `str.++` applications are dissolved into a single flat application.
    pub fn expand_constants(pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::Const(Constant::String(s)) => {
                let args: Vec<Rc<Term>> = s
                    .chars()
                    .map(|c| pool.add(Term::Const(Constant::String(c.to_string()))))
                    .collect();
                match args.len() {
                    0 => pool.add(Term::new_string("")),
                    1 => args[0].clone(),
                    _ => pool.add(Term::Op(Operator::StrConcat, args)),
                }
            }
            Term::Op(op, args) => match op {
                Operator::StrConcat => {
                    let mut new_args = Vec::new();
                    for arg in args {
                        Self::flatten_term(pool, arg, &mut new_args);
                    }
                    pool.add(Term::Op(*op, new_args))
                }
                _ => {
                    let new_args = args
                        .iter()
                        .map(|a| Self::expand_constants(pool, a))
                        .collect();
                    pool.add(Term::Op(*op, new_args))
                }
            },
            Term::App(func, args) => {
                let new_args = args
                    .iter()
                    .map(|term| Self::expand_constants(pool, term))
                    .collect();
                pool.add(Term::App(func.clone(), new_args))
            }
            Term::Let(binding, inner) => {
                let new_inner = Self::expand_constants(pool, inner);
                pool.add(Term::Let(binding.clone(), new_inner))
            }
            Term::Binder(q, bindings, inner) => {
                let new_inner = Self::expand_constants(pool, inner);
                pool.add(Term::Binder(*q, bindings.clone(), new_inner))
            }
            Term::ParamOp { op, op_args, args } => {
                let new_args = args
                    .iter()
                    .map(|term| Self::expand_constants(pool, term))
                    .collect();
                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args: new_args,
                })
            }
            Term::AsOp(op, sort, args) => {
                let new_args = args
                    .iter()
                    .map(|term| Self::expand_constants(pool, term))
                    .collect();
                pool.add(Term::AsOp(*op, sort.clone(), new_args))
            }
            Term::Match(t, cases) => {
                let new_t = Self::expand_constants(pool, t);
                let new_cases = cases
                    .iter()
                    .map(|case| MatchCase {
                        pattern: case.pattern.clone(),
                        body: Self::expand_constants(pool, &case.body),
                    })
                    .collect();
                pool.add(Term::Match(new_t, new_cases))
            }
            Term::Var(..) | Term::Const(_) => term.clone(),
        }
    }

    /// Checks if a term is a string constant of length 1.
    pub fn assert_length_one(term: &Rc<Term>) -> Result<(), CheckerError> {
        if let Term::Const(Constant::String(s)) = term.as_ref()
            && s.len() == 1
        {
            return Ok(());
        }
        Err(CheckerError::ExpectedStringConstantOfLengthOne(term.clone()))
    }
}

// Deref & trait implementations for ergonomic usage
impl Deref for NormalizedConcat {
    type Target = [Rc<Term>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for NormalizedConcat {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl IntoIterator for NormalizedConcat {
    type Item = Rc<Term>;
    type IntoIter = std::vec::IntoIter<Rc<Term>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a NormalizedConcat {
    type Item = &'a Rc<Term>;
    type IntoIter = std::slice::Iter<'a, Rc<Term>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl From<Vec<Rc<Term>>> for NormalizedConcat {
    fn from(v: Vec<Rc<Term>>) -> Self {
        Self(v)
    }
}

impl From<NormalizedConcat> for Vec<Rc<Term>> {
    fn from(n: NormalizedConcat) -> Self {
        n.0
    }
}
