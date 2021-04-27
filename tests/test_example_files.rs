use std::{
    ffi::OsStr,
    fs::{self, File},
    io::{self, BufReader},
    path::Path,
};

use verit_proof_checker::*;

fn test_file(problem_path: &Path, proof_path: &Path) -> Option<()> {
    use checker::CheckerError;
    use parser::error::{ErrorKind, ParserError};

    let problem_reader = BufReader::new(File::open(problem_path).ok()?);
    let proof_reader = BufReader::new(File::open(proof_path).ok()?);

    let proof = match parser::parse_problem_proof(problem_reader, proof_reader) {
        Err(ParserError(ErrorKind::NotYetImplemented, _)) => return Some(()),
        p => p.ok()?,
    };
    match checker::ProofChecker::new(proof).check() {
        Ok(_) | Err(CheckerError::UnknownRule(_)) => Some(()),
        Err(CheckerError::FailedOnRule(_)) => None,
    }
}

fn test_examples_from_dir(dir_path: &str) {
    fn is_problem_file(entry: &io::Result<fs::DirEntry>) -> bool {
        let entry = entry.as_ref().unwrap();
        entry.file_type().unwrap().is_file()
            && entry.path().extension() != Some(OsStr::new("proof"))
    }
    let dir_path = String::from("test-examples/") + dir_path;
    let rd = fs::read_dir(dir_path).unwrap();
    for entry in rd.filter(is_problem_file) {
        let entry = entry.unwrap();
        let problem_path = entry.path();
        let proof_path = {
            let mut cloned = problem_path.clone();
            let mut file_name = cloned.file_name().unwrap().to_owned();
            file_name.push(".proof");
            cloned.pop();
            cloned.push(file_name);
            cloned
        };
        test_file(&problem_path, &proof_path)
            .unwrap_or_else(|| panic!("failed on problem: {}", &problem_path.to_str().unwrap()));
    }
}

macro_rules! generate_tests {
    ( $( $test_name:ident : $dir_name:literal ,)* ) => {
        $(
            #[test]
            fn $test_name() {
                test_examples_from_dir($dir_name)
            }
        )*
    };
}

generate_tests! {
    sh_problems: "SH_problems_all_filtered",
    sh_problems_green_verit: "SH_problems_all_filtered/Green_veriT",
    sh_problems_ordered_resolution_prover_verit:
        "SH_problems_all_filtered/Ordered_Resolution_Prover_veriT",
    sh_problems_ordered_resolution_prover_verit_mirabelle_z3:
        "SH_problems_all_filtered/Ordered_Resolution_Prover_veriT/Mirabelle_z3",
    sh_problems_isabelle_mirabelle: "SH_problems_all_filtered/isabelle-mirabelle",
    sh_problems_isabelle_mirabelle_bo_cvc42: "SH_problems_all_filtered/isabelle-mirabelle/BO_cvc42",
    sh_problems_isabelle_mirabelle_green_cvc42:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_cvc42",
    sh_problems_isabelle_mirabelle_green_verit:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_veriT",
    sh_problems_isabelle_mirabelle_green_verit2:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_veriT2",
    sh_problems_isabelle_mirabelle_green_z32:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_z32",
    sh_problems_isabelle_mirabelle_hol_library:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library",
    sh_problems_isabelle_mirabelle_hol_library_smt_cvc4:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_cvc4",
    sh_problems_isabelle_mirabelle_hol_library_smt_verit:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_verit",
    sh_problems_isabelle_mirabelle_hol_library_pnt_cvc42:
        "SH_problems_all_filtered/isabelle-mirabelle/PNT_cvc42",
    sh_problems_isabelle_mirabelle_hol_library_pnt_z32:
        "SH_problems_all_filtered/isabelle-mirabelle/PNT_z32",
    sh_problems_all_filtered: "SH_problems_all_filtered/isabelle-mirabelle/Zeta_cvc42",
    simple_tests: "simple-tests",
}