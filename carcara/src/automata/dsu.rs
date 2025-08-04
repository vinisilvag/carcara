// DSU with union by size
// find() and union(): O(a(n)) ~ O(1) amortized
pub struct DSU {
    repr: Vec<usize>,
    size: Vec<usize>,
}

impl DSU {
    fn new(n: usize) -> Self {
        DSU {
            repr: (0..n).collect(),
            size: vec![1; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.repr[x] != x {
            self.repr[x] = self.find(self.repr[x]);
        }
        self.repr[x]
    }

    fn union(&mut self, x: usize, y: usize) {
        let mut x_repr = self.find(x);
        let mut y_repr = self.find(y);

        if x_repr == y_repr {
            return;
        }

        if self.size[x_repr] < self.size[y_repr] {
            std::mem::swap(&mut x_repr, &mut y_repr);
        }
        self.size[x_repr] += self.size[y_repr];
        self.repr[y_repr] = x_repr;
    }
}
