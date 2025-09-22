// use crate::automata::Automata;

// // Implementação quase idêntica à AST que já temos por padrão
// #[derive(Clone, Debug)]
// pub enum Regex {
//     Empty,                         // re.none
//     All,                           // re.all
//     AllChar,                       // re.allchar
//     Literal(String),               // str.to_re ***
//     Concat(Vec<Regex>),            // re.++
//     Union(Vec<Regex>),             // re.union
//     Inter(Box<Regex>, Box<Regex>), // re.inter
//     Star(Box<Regex>),              // re.*
// }

// impl Regex {
//     pub fn to_dfa(&self) -> Automata {
//         match self {
//             Regex::Empty => Automata::empty(),
//             Regex::All => Automata::all(),
//             Regex::AllChar => Automata::allchar(),
//             Regex::Literal(s) => Automata::from_literal(s),
//             Regex::Concat(parts) => parts
//                 .iter()
//                 .map(|p| p.to_dfa())
//                 .reduce(|a, b| Automaton::concat(&a, &b))
//                 .unwrap(),
//             Regex::Union(parts) => parts
//                 .iter()
//                 .map(|p| p.to_dfa())
//                 .reduce(|a, b| Automata::union(&a, &b))
//                 .unwrap(),
//             Regex::Inter(a, b) => Automata::inter(&a.to_dfa(), &b.to_dfa()),
//             Regex::Star(r) => Automata::star(&r.to_dfa()),
//         }
//     }
// }
