use std::collections::HashSet;

pub struct Automaton {
    initial: State
}

impl Automaton {
    fn new(initial: State) -> Self {
        Automaton {
            initial
        }
    }

    fn get_states(&self) -> HashSet<State> {    
        HashSet<State> visited = HashSet::new();
        HashSet<State> worklist = HashSet::new();
        visited.insert(self.initial);
        worklist.insert(self.initial);

        // finaliza a dfs
    }

    fn get_accept_states(&self) -> HashSet<State> {
        HashSet<State> accepts = HashSet::new();
        HashSet<State> visited = HashSet::new();
        HashSet<State> worklist = HashSet::new();
        visited.insert(self.initial);
        worklist.insert(self.initial);

        // finaliza a dfs
        // insere os nós de aceitação em accepts
    }

    fn get_transitions(&self) -> HashSet<State> {}
}