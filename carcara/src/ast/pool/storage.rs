//* The behaviour of the term pool could be modeled by a hash map from `Term` to `Rc<Term>`, but
//* that would require allocating two copies of each term, one in the key of the hash map, and one
//* inside the `Rc`. Instead, we store a hash set of `Rc<Term>`s, combining the key and the value
//* into a single object. We access this hash set using a `&Term`, and if the entry is present, we
//* clone it; otherwise, we allocate a new `Rc`.

use crate::ast::*;
use indexmap::IndexSet;
use std::{borrow::Borrow, hash::Hash};

/// Since `ast::Rc` intentionally implements hashing and equality by reference (instead of by
/// value), we cannot safely implement `Borrow<Term>` for `Rc<Term>`, so we cannot access a
/// `HashSet<Rc<Term>>` using a `&Term` as a key. To go around that, we use this struct that wraps
/// an `Rc<Term>` and that re-implements hashing and equality by value, meaning we can implement
/// `Borrow<Term>` for it, and use it as the contents of the hash set instead.
#[derive(Debug, Clone, Eq)]
struct ByValue<T>(Rc<T>);

impl<T: Eq> PartialEq for ByValue<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl<T: Hash> Hash for ByValue<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_ref().hash(state);
    }
}

impl<T> Borrow<T> for ByValue<T> {
    fn borrow(&self) -> &T {
        self.0.as_ref()
    }
}

#[derive(Debug, Clone)]
pub struct Storage<T>(IndexSet<ByValue<T>>);

impl<T> Default for Storage<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T: Hash + Eq> Storage<T> {
    pub fn add(&mut self, object: T) -> Rc<T> {
        // If the `hash_set_entry` feature was stable, this would be much simpler to do using
        // `get_or_insert_with` (and would avoid rehashing the object)
        match self.0.get(&object) {
            Some(o) => o.0.clone(),
            None => {
                // SAFETY: We have just checked that the object does not exist in the pool, so we can
                // create a new allocation.
                let result = unsafe { Rc::new_raw(object) };
                self.0.insert(ByValue(result.clone()));
                result
            }
        }
    }

    pub fn get(&self, term: &T) -> Option<&Rc<T>> {
        self.0.get(term).map(|t| &t.0)
    }

    // This method is only necessary for the hash consing tests
    #[cfg(test)]
    pub fn into_vec(self) -> Vec<Rc<T>> {
        self.0.into_iter().map(|ByValue(t)| t).collect()
    }
}
