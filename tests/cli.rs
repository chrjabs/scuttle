//! # Basic tests to not break the CLI

const SCUTTLE: &str = env!("CARGO_BIN_EXE_scuttle");

fn defaults(alg: &str) {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let output = std::process::Command::new(SCUTTLE)
        .args([alg, &format!("{manifest}/data/small.mcnf")])
        .output()
        .expect("failed to run `scuttle` binary");
    println!("=== STDOUT ===");
    println!(
        "{}",
        str::from_utf8(&output.stdout).expect("invalid UTF8 in stdout")
    );
    println!();
    println!("=== STDERR ===");
    println!(
        "{}",
        str::from_utf8(&output.stderr).expect("invalid UTF8 in stdout")
    );
    assert!(output.status.success());
}

#[test]
fn p_minimal_defaults() {
    defaults("p-minimal");
}

#[test]
fn bioptsat_defaults() {
    defaults("bioptsat");
}

#[test]
fn lower_bounding_defaults() {
    defaults("lower-bounding");
}

#[test]
fn pareto_ihs_defaults() {
    defaults("pareto-ihs");
}
