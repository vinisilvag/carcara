use super::Rc;
use indexmap::{map::Entry, IndexMap};

/// The sort of a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// A function sort.
    ///
    /// The last term indicates the return sort of the function. The remaining terms are the sorts
    /// of the parameters of the function.
    Function(Vec<Rc<Sort>>),

    /// A user-declared sort, from a `declare-sort` command.
    ///
    /// The associated string is the sort name, and the associated terms are the sort arguments for
    /// this sort.
    Atom(Box<str>, Box<[Rc<Sort>]>),

    /// A sort variable
    Var(String),

    /// The `Bool` primitive sort.
    Bool,

    /// The `Int` primitive sort.
    Int,

    /// The `Real` primitive sort.
    Real,

    /// The `String` primitive sort.
    String,

    /// The `RegLan` primitive sort.
    RegLan,

    /// An `Array` sort.
    ///
    /// The two associated terms are the sort arguments for this sort.
    Array(Rc<Sort>, Rc<Sort>),

    /// A `BitVec` sort with a constant width parameter.
    ///
    /// The associated `usize` is the bitvector width of this sort.
    BitVec(usize),

    /// A `BitVec`, parameterized by width parameter that is not statically known.
    ///
    /// The motivation for the existence of this sort is that Rare files can contain bitvector sorts
    /// whose width is parameterized by integer variables. For example:
    /// ```text
    /// (declare-rare-rule bv-extract-whole ((@n0 Int) (x1 (BitVec @n0)) (n1 Int))
    ///   :premises ((= (>= n1 (- (@bvsize x1) 1)) true))
    ///   :args (x1 n1)
    ///   :conclusion (= (extract n1 0 x1) x1)
    /// )
    /// ```
    /// Here, `x1` is a bitvector with width `@n0`, which is not statically known.
    ///
    /// The most precise way of representing this type would be to use a dependent type constructor
    /// that takes a series of variables and produces a parametric sort that uses these variables.
    /// For example, a bitvector term with parametric width `x` would have sort `Π x. BitVec(x)`,
    /// where `Π` is the dependent type constructor.
    ///
    /// Due to operators such as `concat` and `extract`, the term passed to the `BitVec` constructor
    /// can be a more complicated expression than just a simple variable. For example, for
    /// bitvectors `u`, `v` of widths `x`, `y`, `(concat u v)` would have sort `Π x, y. BitVec(x +
    /// y)`, and `(extract i j v)` would have sort `Π i, j. BitVec(i - j + 1)`. As you can imagine,
    /// the nesting of these operators can lead to arbitrarily complex width expressions.
    ///
    /// Type checking these parametric sorts can be difficult. Say we want to ensure the two terms
    /// `(extract i j v)` and `(concat (extract i (+ j 2) v) (extract (+ j 1) j v))` have compatible
    /// sorts. Their parametric widths will be, respectively, `i - j + 1` and `(i - (j + 2) + 1) +
    /// ((j + 1) - j + 1)`. These two expressions are equivalent, but determining that would require
    /// implementing a general simplification procedure for width expressions, which will get even
    /// harder as we consider more operators such as `repeat`.
    ///
    /// Finally, since SMT-LIB and Alethe do not currently include full support for dependent types,
    /// there is no actual use for keeping these parametric width expressions, and for accurately
    /// type checking such dependent types. The upcoming SMT-LIB version 3.0 aims to officially
    /// include dependent types in the language specification, and will determine precisely to
    /// which extent this needs to be supported. Until that is settled, however, we choose a more
    /// pragmatic approach, and don't store the parametric width expressions, instead considering
    /// all parametric bitvector sorts to be compatible.
    ///
    /// Carcara only has support for parametric bitvector sorts to allow correct parsing of Rare
    /// files, and this simplified representation is sufficient in this case, as long as we make
    /// sure to type check the concretely-sorted terms that are created when instantiating the
    /// parametric sorts in the Rare rules.
    // TODO: actually perform this extra type checking
    ParamBitVec,

    /// A datatype sort, specified by its name and the provided sort arguments.
    ///
    /// The actual contents of the datatype (that is, its constructors) are stored in the term pool,
    /// indexed by the datatype name.
    Datatype {
        /// The unique name of this sort.
        name: Box<str>,

        /// The arguments that were provided to this sort (e.g., the `Int` in `(Option Int)`)
        args: Vec<Rc<Sort>>,
    },

    // TODO delete this and incorporate it to function sort?
    /// A parametric sort, with a set of sort variables that can appear in the second argument.
    ParamSort(Vec<Rc<Sort>>, Rc<Sort>),

    /// The sort of sorts.
    Type,
}

impl Sort {
    /// Returns `true` if the sort is a sort variable.
    pub fn is_var(&self) -> bool {
        match self {
            // TODO: double representation of sort vars?
            Sort::Atom(_, args) if args.is_empty() => true,
            Sort::Var(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if the sort is a bitvector sort of any width.
    pub fn is_bitvec(&self) -> bool {
        matches!(self, Sort::BitVec(_) | Sort::ParamBitVec)
    }

    /// Returns `true` if the sort is a datatype sort.
    pub fn is_datatype(&self) -> bool {
        matches!(self, Sort::Datatype { .. })
    }

    pub fn is_parametric(&self) -> bool {
        matches!(self, Sort::ParamSort(_, _))
    }

    /// Whether this sort is equal to another, modulo bitvector sorts with width parameters that are
    /// not statically known.
    pub fn param_eq(&self, other: &Self) -> bool {
        self == other
            || *self == Sort::ParamBitVec && other.is_bitvec()
            || *other == Sort::ParamBitVec && self.is_bitvec()
    }

    // TODO: merge this with `match_with`
    pub fn is_compatible_with(&self, other: &Self) -> bool {
        fn all_compatible<'i, I: IntoIterator<Item = &'i Rc<Sort>>>(xs: I, ys: I) -> bool {
            xs.into_iter().zip(ys).all(|(x, y)| x.is_compatible_with(y))
        }

        match (self, other) {
            (Sort::Var(_), _) | (_, Sort::Var(_)) => true,
            (Sort::ParamBitVec, Sort::BitVec(_) | Sort::ParamBitVec)
            | (Sort::BitVec(_), Sort::ParamBitVec) => true,

            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && all_compatible(sorts_a, sorts_b)
            }
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => all_compatible(sorts_a, sorts_b),
            // The datatype name and arguments are sufficient to uniquely specify a datatype sort,
            // so we don't need to look at the constructors
            (
                Sort::Datatype { name: name_a, args: args_a, .. },
                Sort::Datatype { name: name_b, args: args_b, .. },
            ) => name_a == name_b && all_compatible(args_a, args_b),
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                all_compatible([x_a, y_a], [x_b, y_b])
            }

            _ => self == other,
        }
    }

    /// Whether this sort can be matched with another, i.e., whether we
    /// can find a substitution to the sort variables of `self` that
    /// will make it equal to `target`. The map argument will store the
    /// substitution
    pub fn match_with(&self, target: &Sort, map: &mut IndexMap<String, Sort>) -> bool {
        fn match_all<'i, I>(xs: I, ys: I, map: &mut IndexMap<String, Sort>) -> bool
        where
            I: IntoIterator<Item = &'i Rc<Sort>>,
        {
            xs.into_iter().zip(ys).all(|(x, y)| x.match_with(y, map))
        }

        match (self, target) {
            (Sort::Var(a), _) => {
                match map.entry(a.clone()) {
                    Entry::Vacant(e) => e.insert(target.clone()),
                    Entry::Occupied(e) => return e.get() == target,
                };
                true
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && match_all(sorts_a, sorts_b, map)
            }
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => match_all(sorts_a, sorts_b, map),

            // The datatype name and arguments are sufficient to uniquely specify a datatype sort,
            // so we don't need to look at the constructors
            (
                Sort::Datatype { name: name_a, args: args_a, .. },
                Sort::Datatype { name: name_b, args: args_b, .. },
            ) => name_a == name_b && match_all(args_a, args_b, map),
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                match_all([x_a, y_a], [x_b, y_b], map)
            }
            _ => self.param_eq(target),
        }
    }
}
