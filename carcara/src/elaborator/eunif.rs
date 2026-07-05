use super::{add_refl_step, IdHelper};
use crate::{
    ast::*,
    cc::{CongruenceClosure, EqProof, EqProofRule},
    checker::error::CheckerError,
};
use std::collections::HashMap;

/// Elaborates a `g_eunif` step into a proof using only the `trans`, `cong`, `symm`, `refl` and
/// `and` rules, whose leaves are the original premises (each an equality or a conjunction of
/// equalities).
pub fn g_eunif(
    pool: &mut PrimitivePool,
    cc: &mut Option<CongruenceClosure>,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);
    let (t, u) = match_term_err!((= t u) = &step.clause[0])?;

    // As in the checker, the congruence closure's term index starts empty, is filled on demand,
    // and is shared by all `g_eunif` steps; only the premise equalities are fresh in each
    // invocation
    let cc = cc.get_or_insert_with(CongruenceClosure::new);
    cc.reset();

    // Since premises may be conjunctions of equalities, the equalities given to the congruence
    // closure are identified by a flat index, which maps to a premise and, for conjunctions, the
    // index of the conjunct in it
    let mut premise_table: Vec<(usize, Option<usize>)> = Vec::new();
    for (i, premise) in step.premises.iter().enumerate() {
        assert_eq!(premise.clause().len(), 1);
        let term = &premise.clause()[0];
        if let Some((a, b)) = match_term!((= a b) = term) {
            cc.add_equality(a, b, premise_table.len());
            premise_table.push((i, None));
        } else {
            let conjuncts = match_term_err!((and ...) = term)?;
            for (j, conjunct) in conjuncts.iter().enumerate() {
                let (a, b) = match_term_err!((= a b) = conjunct)?;
                cc.add_equality(a, b, premise_table.len());
                premise_table.push((i, Some(j)));
            }
        }
    }
    let proof = cc
        .explain(t, u)
        .ok_or_else(|| CheckerError::TermsNotCongruent(t.clone(), u.clone()))?;

    let mut converter = Converter {
        pool,
        premises: &step.premises,
        premise_table,
        depth: step.depth,
        ids: IdHelper::new(&step.id),
        cache: HashMap::new(),
    };
    Ok(converter.convert_root(&proof, step))
}

struct Converter<'a> {
    pool: &'a mut PrimitivePool,
    premises: &'a [Rc<ProofNode>],
    /// Maps each flat equality index to its premise and, if the premise is a conjunction, the
    /// index of the conjunct in it
    premise_table: Vec<(usize, Option<usize>)>,
    depth: usize,
    ids: IdHelper,
    /// Explanations are DAGs, so we cache converted sub-proofs (keyed by their conclusion, which
    /// determines them) to share the corresponding steps
    cache: HashMap<(Rc<Term>, Rc<Term>), Rc<ProofNode>>,
}

impl<'a> Converter<'a> {
    /// Converts the root of the explanation, which must keep the original step's id and clause.
    fn convert_root(&mut self, proof: &EqProof, step: &StepNode) -> Rc<ProofNode> {
        let (rule, premises) = match &proof.rule {
            // If the conclusion is proved directly by a premise, we wrap it in a single-premise
            // `trans` step, so that the elaborated step still exists and keeps the original id
            EqProofRule::Premise(i) => ("trans", vec![self.premise_node(*i)]),
            EqProofRule::Symm(inner) => ("symm", vec![self.convert(inner)]),
            EqProofRule::Refl => ("refl", Vec::new()),
            EqProofRule::Trans(links) => ("trans", links.iter().map(|l| self.convert(l)).collect()),
            EqProofRule::Cong(args) => ("cong", self.convert_cong_premises(args)),
        };
        Rc::new(ProofNode::Step(StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: rule.to_owned(),
            premises,
            ..StepNode::default()
        }))
    }

    fn convert(&mut self, proof: &EqProof) -> Rc<ProofNode> {
        let (lhs, rhs) = proof.conclusion.clone();
        if let Some(node) = self.cache.get(&(lhs.clone(), rhs.clone())) {
            return node.clone();
        }
        // All new steps are created at the depth of the `g_eunif` step being elaborated (even
        // when all their premises live at outer depths), so that no step ends up outside a
        // subproof while referencing steps inside it
        let node = match &proof.rule {
            EqProofRule::Premise(i) => self.premise_node(*i),
            EqProofRule::Symm(inner) => {
                let inner = self.convert(inner);
                self.new_step(&lhs, &rhs, "symm", vec![inner])
            }
            EqProofRule::Refl => add_refl_step(
                self.pool,
                lhs.clone(),
                rhs.clone(),
                self.ids.next_id(),
                self.depth,
            ),
            EqProofRule::Trans(links) => {
                let links: Vec<_> = links.iter().map(|l| self.convert(l)).collect();
                self.new_step(&lhs, &rhs, "trans", links)
            }
            EqProofRule::Cong(args) => {
                let premises = self.convert_cong_premises(args);
                self.new_step(&lhs, &rhs, "cong", premises)
            }
        };
        self.cache.insert((lhs, rhs), node.clone());
        node
    }

    /// Returns the proof node for the equality with the given flat index: the premise itself, or,
    /// if it is a conjunct of a conjunction premise, an `and` step deriving it.
    fn premise_node(&mut self, flat: usize) -> Rc<ProofNode> {
        let (pi, conjunct) = self.premise_table[flat];
        let premise = self.premises[pi].clone();
        let Some(j) = conjunct else {
            return premise;
        };
        let conjunct_term = match_term!((and ...) = &premise.clause()[0]).unwrap()[j].clone();
        let index = self.pool.add(Term::new_int(j));
        Rc::new(ProofNode::Step(StepNode {
            id: self.ids.next_id(),
            depth: self.depth,
            clause: vec![conjunct_term],
            rule: "and".to_owned(),
            premises: vec![premise],
            args: vec![index],
            ..StepNode::default()
        }))
    }

    fn new_step(
        &mut self,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        rule: &str,
        premises: Vec<Rc<ProofNode>>,
    ) -> Rc<ProofNode> {
        let clause = vec![build_term!(self.pool, (= {lhs.clone()} {rhs.clone()}))];
        Rc::new(ProofNode::Step(StepNode {
            id: self.ids.next_id(),
            depth: self.depth,
            clause,
            rule: rule.to_owned(),
            premises,
            ..StepNode::default()
        }))
    }

    /// Converts the argument sub-proofs of a congruence. Syntactically equal argument pairs
    /// (`None`) need no premise, since the `cong` rule skips them.
    fn convert_cong_premises(
        &mut self,
        args: &[Option<crate::cc::EqProofRc>],
    ) -> Vec<Rc<ProofNode>> {
        args.iter().flatten().map(|arg| self.convert(arg)).collect()
    }
}
