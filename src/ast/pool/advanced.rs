use super::{Datatype, PrimitivePool, TermPool};
use crate::ast::{Rc, Sort, Term};
use indexmap::IndexSet;
use std::{
    borrow::Cow,
    sync::{Arc, RwLock},
};

/// A pool with a shared mutable *context pool*, and a shared immutable *global pool*.
#[derive(Clone)]
pub struct ContextPool {
    pub(crate) global_pool: Arc<PrimitivePool>,
    pub(crate) inner: Arc<RwLock<PrimitivePool>>,
}

impl Default for ContextPool {
    fn default() -> Self {
        Self::new()
    }
}

impl ContextPool {
    /// Constructs a `ContextPool` with a fresh, empty global pool and a fresh, empty inner pool.
    pub fn new() -> Self {
        Self {
            global_pool: Arc::new(PrimitivePool::new()),
            inner: Arc::new(RwLock::new(PrimitivePool::new())),
        }
    }

    /// Constructs a `ContextPool` that shares the given global pool, with a fresh, empty inner
    /// pool.
    pub fn from_global(global_pool: &Arc<PrimitivePool>) -> Self {
        Self {
            global_pool: global_pool.clone(),
            inner: Arc::new(RwLock::new(PrimitivePool::new())),
        }
    }
}

impl TermPool for ContextPool {
    fn add(&mut self, term: Term) -> Rc<Term> {
        // If the global pool has the term
        if let Some(entry) = self.global_pool.terms.get(&term) {
            return entry.clone();
        }
        let mut ctx_guard = self.inner.write().unwrap();
        let term = ctx_guard.terms.add(term);
        ctx_guard.compute_sort(&term);
        term
    }

    fn add_sort(&mut self, sort: Sort) -> Rc<Sort> {
        // If the global pool has the sort
        if let Some(entry) = self.global_pool.sorts.get(&sort) {
            return entry.clone();
        }
        let mut ctx_guard = self.inner.write().unwrap();
        ctx_guard.sorts.add(sort)
    }

    fn sort(&self, term: &Rc<Term>) -> Rc<Sort> {
        if let Some(sort) = self.global_pool.sorts_cache.get(term) {
            sort.clone()
        } else {
            // A sort inserted by context
            self.inner.read().unwrap().sorts_cache[term].clone()
        }
    }

    fn free_vars(&'_ mut self, term: &Rc<Term>) -> Cow<'_, IndexSet<Rc<Term>>> {
        Cow::Owned(
            self.inner
                .write()
                .unwrap()
                .free_vars_with_priorities(term, [&self.global_pool])
                .clone(),
        )
    }

    fn get_datatype(&self, name: &str) -> &Datatype {
        self.global_pool.get_datatype(name)
    }
}

/// A thread local pool, layered on top of a shared [`ContextPool`].
pub struct LocalPool {
    pub(crate) ctx_pool: ContextPool,
    pub(crate) inner: PrimitivePool,
}

impl Default for LocalPool {
    fn default() -> Self {
        Self::new()
    }
}

impl LocalPool {
    /// Constructs a `LocalPool` with a fresh `ContextPool` and a fresh, empty thread-local pool.
    pub fn new() -> Self {
        Self {
            ctx_pool: ContextPool::new(),
            inner: PrimitivePool::new(),
        }
    }

    /// Instantiates a new `LocalPool` from a previous `ContextPool` (makes sure the context is
    /// shared between threads).
    pub fn from_previous(ctx_pool: &ContextPool) -> Self {
        Self {
            ctx_pool: ctx_pool.clone(),
            inner: PrimitivePool::new(),
        }
    }
}

impl TermPool for LocalPool {
    fn add(&mut self, term: Term) -> Rc<Term> {
        // If there is a constant pool and has the term
        if let Some(entry) = self.ctx_pool.global_pool.terms.get(&term) {
            entry.clone()
        }
        // If this term was inserted by the context
        else if let Some(entry) = self.ctx_pool.inner.read().unwrap().terms.get(&term) {
            entry.clone()
        } else {
            self.inner.add(term)
        }
    }

    fn add_sort(&mut self, sort: Sort) -> Rc<Sort> {
        // If there is a constant pool and has the sort
        if let Some(entry) = self.ctx_pool.global_pool.sorts.get(&sort) {
            entry.clone()
        }
        // If this sort was inserted by the context
        else if let Some(entry) = self.ctx_pool.inner.read().unwrap().sorts.get(&sort) {
            entry.clone()
        } else {
            self.inner.add_sort(sort)
        }
    }

    fn sort(&self, term: &Rc<Term>) -> Rc<Sort> {
        if let Some(sort) = self.ctx_pool.global_pool.sorts_cache.get(term) {
            sort.clone()
        }
        // A sort inserted by context
        else if let Some(entry) = self.ctx_pool.inner.read().unwrap().sorts_cache.get(term) {
            entry.clone()
        } else {
            self.inner.sorts_cache[term].clone()
        }
    }

    fn free_vars(&'_ mut self, term: &Rc<Term>) -> Cow<'_, IndexSet<Rc<Term>>> {
        Cow::Owned(
            self.inner
                .free_vars_with_priorities(
                    term,
                    [
                        &self.ctx_pool.global_pool,
                        &self.ctx_pool.inner.read().unwrap(),
                    ],
                )
                .clone(),
        )
    }

    fn get_datatype(&self, name: &str) -> &Datatype {
        self.inner.get_datatype(name)
    }
}
