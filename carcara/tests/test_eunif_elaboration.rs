//! End-to-end tests for the elaboration of the `g_eunif` rule: proofs are checked, elaborated,
//! and the elaborated proofs (which must not contain `g_eunif` steps anymore) are checked again.

use carcara::*;
use std::io::Cursor;

const PROBLEM_PRELUDE: &str = "
    (declare-sort T 0)
    (declare-fun a () T)
    (declare-fun b () T)
    (declare-fun c () T)
    (declare-fun d () T)
    (declare-fun f (T) T)
    (declare-fun g (T) T)
    (declare-fun h (T T) T)
    (declare-fun p (T) Bool)
";

fn any_step_uses_rule(commands: &[ast::ProofCommand], rule: &str) -> bool {
    commands.iter().any(|command| match command {
        ast::ProofCommand::Step(step) => step.rule == rule,
        ast::ProofCommand::Subproof(subproof) => any_step_uses_rule(&subproof.commands, rule),
        ast::ProofCommand::Assume { .. } => false,
    })
}

fn run_test(asserts: &str, proof: &str) {
    let problem = format!("{}{}", PROBLEM_PRELUDE, asserts);
    let (problem, proof, mut pool) = parser::parse_instance(
        Cursor::new(problem.as_str()),
        Cursor::new(proof),
        parser::Config::new(),
    )
    .expect("parser error");

    let checker_config = checker::Config {
        elaborated: false,
        ignore_unknown_rules: false,
        allowed_rules: ["hole".to_owned()].into(),
    };

    // First, we check the original proof
    checker::ProofChecker::new(&mut pool, checker_config.clone())
        .check(&problem, &proof)
        .expect("original proof is invalid");

    // Then we elaborate it, and make sure no `g_eunif` step is left
    let config = elaborator::Config {
        lia_options: None,
        hole_options: None,
        uncrowd_rotation: true,
    };
    let node = ast::ProofNode::from_commands(proof.commands.clone());
    let elaborated_node = elaborator::Elaborator::new(&mut pool, &problem, config.clone())
        .elaborate_with_default_pipeline(&node);
    let elaborated = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: elaborated_node.into_commands(),
    };
    assert!(
        !any_step_uses_rule(&elaborated.commands, "g_eunif"),
        "elaborated proof still uses `g_eunif`"
    );

    // After that, we check the elaborated proof
    checker::ProofChecker::new(&mut pool, checker_config.clone())
        .check(&problem, &elaborated)
        .expect("elaborated proof is invalid");

    // Then we make sure the elaboration is idempotent
    let elaborated_twice = elaborator::Elaborator::new(&mut pool, &problem, config.clone())
        .elaborate_with_default_pipeline(&elaborated_node);
    assert!(
        elaborated.commands == elaborated_twice.into_commands(),
        "elaboration was not idempotent"
    );

    // Finally, we run the pipeline consisting of only the `eunif` step, which should suffice to
    // remove all `g_eunif` steps and yield a checkable proof, and also be idempotent
    let node = ast::ProofNode::from_commands(proof.commands.clone());
    let eunif_only_node = elaborator::Elaborator::new(&mut pool, &problem, config.clone())
        .elaborate(&node, vec![elaborator::ElaborationStep::Eunif]);
    let eunif_only = ast::Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands: eunif_only_node.clone().into_commands(),
    };
    assert!(
        !any_step_uses_rule(&eunif_only.commands, "g_eunif"),
        "eunif-only elaborated proof still uses `g_eunif`"
    );
    checker::ProofChecker::new(&mut pool, checker_config)
        .check(&problem, &eunif_only)
        .expect("eunif-only elaborated proof is invalid");
    let eunif_only_twice = elaborator::Elaborator::new(&mut pool, &problem, config)
        .elaborate(&eunif_only_node, vec![elaborator::ElaborationStep::Eunif]);
    assert!(
        eunif_only.commands == eunif_only_twice.into_commands(),
        "eunif-only elaboration was not idempotent"
    );
}

#[test]
fn direct_premise() {
    run_test(
        "(assert (= a b))",
        "(assume h1 (= a b))
        (step t2 (cl (= a b)) :rule g_eunif :premises (h1))
        (step end (cl) :rule hole :premises (t2))",
    );
}

#[test]
fn symmetry() {
    run_test(
        "(assert (= a b))",
        "(assume h1 (= a b))
        (step t2 (cl (= b a)) :rule g_eunif :premises (h1))
        (step end (cl) :rule hole :premises (t2))",
    );
}

#[test]
fn reflexivity() {
    run_test(
        "(assert (= a a))",
        "(step t1 (cl (= (f a) (f a))) :rule g_eunif)
        (step end (cl) :rule hole :premises (t1))",
    );
}

#[test]
fn transitivity() {
    run_test(
        "(assert (= b a)) (assert (= c b)) (assert (= c d))",
        "(assume h1 (= b a)) (assume h2 (= c b)) (assume h3 (= c d))
        (step t4 (cl (= a d)) :rule g_eunif :premises (h1 h2 h3))
        (step end (cl) :rule hole :premises (t4))",
    );
}

#[test]
fn congruence() {
    run_test(
        "(assert (= a b)) (assert (= c d))",
        "(assume h1 (= a b)) (assume h2 (= c d))
        (step t3 (cl (= (h (g a) c) (h (g b) d))) :rule g_eunif :premises (h1 h2))
        (step end (cl) :rule hole :premises (t3))",
    );
}

#[test]
fn congruence_and_transitivity() {
    run_test(
        "(assert (= a b)) (assert (= (f b) c)) (assert (= c d))",
        "(assume h1 (= a b)) (assume h2 (= (f b) c)) (assume h3 (= c d))
        (step t4 (cl (= (f a) d)) :rule g_eunif :premises (h1 h2 h3))
        (step end (cl) :rule hole :premises (t4))",
    );
}

#[test]
fn predicate_congruence() {
    run_test(
        "(assert (= a b)) (assert (= b c))",
        "(assume h1 (= a b)) (assume h2 (= b c))
        (step t3 (cl (= (p a) (p c))) :rule g_eunif :premises (h1 h2))
        (step end (cl) :rule hole :premises (t3))",
    );
}

#[test]
fn deep_congruence() {
    run_test(
        "(assert (= a b)) (assert (= (h a a) c)) (assert (= (h b b) d))",
        "(assume h1 (= a b)) (assume h2 (= (h a a) c)) (assume h3 (= (h b b) d))
        (step t4 (cl (= c d)) :rule g_eunif :premises (h1 h2 h3))
        (step end (cl) :rule hole :premises (t4))",
    );
}

#[test]
fn conjunction_premises() {
    run_test(
        "(assert (and (= a b) (= c d))) (assert (= (f b) c))",
        "(assume h1 (and (= a b) (= c d))) (assume h2 (= (f b) c))
        (step t3 (cl (= (f a) d)) :rule g_eunif :premises (h1 h2))
        (step t4 (cl (= (h a c) (h b d))) :rule g_eunif :premises (h1))
        (step end (cl) :rule hole :premises (t3 t4))",
    );
}

#[test]
fn multiple_steps() {
    run_test(
        "(assert (= a b)) (assert (= c d)) (assert (= (f c) a))",
        "(assume h1 (= a b)) (assume h2 (= c d)) (assume h3 (= (f c) a))
        (step t4 (cl (= (f a) (f b))) :rule g_eunif :premises (h1))
        (step t5 (cl (= (f d) b)) :rule g_eunif :premises (h1 h2 h3))
        (step t6 (cl (= (h a c) (h b d))) :rule g_eunif :premises (h1 h2))
        (step end (cl) :rule hole :premises (t4 t5 t6))",
    );
}
