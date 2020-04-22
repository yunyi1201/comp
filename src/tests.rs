use lang_c::ast::*;
use std::fs::{self, File};
use std::io::{stderr, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use tempfile::tempdir;
use wait_timeout::ChildExt;

use crate::*;

pub fn test_write_c(unit: &TranslationUnit, _path: &Path) {
    let temp_dir = tempdir().expect("temp dir creation failed");
    let temp_file_path = temp_dir.path().join("temp.c");
    let mut temp_file = File::create(&temp_file_path).unwrap();

    crate::write(unit, &mut temp_file).unwrap();

    let new_unit = c::Parse::default()
        .translate(&temp_file_path.as_path())
        .expect("parse failed while parsing the output from implemented printer");
    drop(temp_file);
    c::assert_ast_equiv(&unit, &new_unit);
    temp_dir.close().expect("temp dir deletion failed");
}

pub fn test_irgen(unit: &TranslationUnit, path: &Path) {
    // Check if the file has .c extension
    assert_eq!(path.extension(), Some(std::ffi::OsStr::new("c")));

    // Test parse
    c::Parse::default()
        .translate(&path)
        .expect("failed to parse the given program");

    let file_path = path.display().to_string();
    let bin_path = path.with_extension("irgen").as_path().display().to_string();

    // Compile c file: If fails, test is vacuously success
    if !Command::new("gcc")
        .args(&["-O1", &file_path, "-o", &bin_path])
        .stderr(Stdio::null())
        .status()
        .unwrap()
        .success()
    {
        return;
    }

    // Execute compiled executable
    let mut child = Command::new(fs::canonicalize(bin_path.clone()).unwrap())
        .spawn()
        .expect("failed to execute the compiled executable");

    Command::new("rm")
        .arg(bin_path)
        .status()
        .expect("failed to remove compiled executable");

    let status = some_or!(
        child
            .wait_timeout_ms(500)
            .expect("failed to obtain exit status from child process"),
        {
            println!("timeout occurs");
            child.kill().unwrap();
            child.wait().unwrap();
            return;
        }
    );
    let status = some_or!(status.code(), return);

    let ir = match Irgen::default().translate(unit) {
        Ok(ir) => ir,
        Err(irgen_error) => panic!("{}", irgen_error),
    };

    let args = Vec::new();
    let result = match ir::interp(&ir, args) {
        Ok(result) => result,
        Err(interp_error) => panic!("{}", interp_error),
    };
    // We only allow main function whose return type is `int`
    let (value, width, is_signed) = result.get_int().expect("non-integer value occurs");
    assert_eq!(width, 32);
    assert!(is_signed);

    // When obtain status from `gcc` executable process, value is truncated to byte size.
    // For this reason, we make `fuzzer` generate the C source code which returns value
    // typecasted to `unsigned char`. However, during `creduce` reduce the code, typecasting
    // may be deleted. So, we truncate result value to byte size one more time here.
    println!("gcc: {}, kecc: {}", status as i8, value as i8);
    assert_eq!(status as i8, value as i8);
}

pub fn test_irparse(unit: &TranslationUnit, path: &Path) {
    // Check if the file has .c extension
    assert_eq!(path.extension(), Some(std::ffi::OsStr::new("c")));

    // Test parse
    c::Parse::default()
        .translate(&path)
        .expect("failed to parse the given program");

    let file_path = path.display().to_string();
    let bin_path = path
        .with_extension("irparse")
        .as_path()
        .display()
        .to_string();

    // Compile c file: If fails, test is vacuously success
    if !Command::new("gcc")
        .args(&["-O1", &file_path, "-o", &bin_path])
        .stderr(Stdio::null())
        .status()
        .unwrap()
        .success()
    {
        return;
    }

    // Execute compiled executable
    let mut child = Command::new(fs::canonicalize(bin_path.clone()).unwrap())
        .spawn()
        .expect("failed to execute the compiled executable");

    Command::new("rm")
        .arg(bin_path)
        .status()
        .expect("failed to remove compiled executable");

    let status = some_or!(
        child
            .wait_timeout_ms(500)
            .expect("failed to obtain exit status from child process"),
        {
            println!("timeout occurs");
            child.kill().unwrap();
            child.wait().unwrap();
            return;
        }
    );
    let _status = some_or!(status.code(), return);

    let ir = match Irgen::default().translate(unit) {
        Ok(ir) => ir,
        Err(irgen_error) => panic!("{}", irgen_error),
    };

    let temp_dir = tempdir().expect("temp dir creation failed");
    let temp_file_path = temp_dir.path().join("temp.c");
    let mut temp_file = File::create(&temp_file_path).unwrap();

    crate::write(&ir, &mut temp_file).unwrap();

    let new_ir = ir::Parse::default()
        .translate(&temp_file_path.as_path())
        .expect("parse failed while parsing the output from implemented printer");
    drop(temp_file);
    assert_eq!(ir, new_ir);
    temp_dir.close().expect("temp dir deletion failed");
}

pub fn test_opt<P1: AsRef<Path>, P2: AsRef<Path>, O: Optimize<ir::TranslationUnit>>(
    from: &P1,
    to: &P2,
    opt: &mut O,
) {
    let from = ir::Parse::default()
        .translate(from)
        .expect("parse failed while parsing the output from implemented printer");
    let mut ir = from.clone();
    let to = ir::Parse::default()
        .translate(to)
        .expect("parse failed while parsing the output from implemented printer");
    opt.optimize(&mut ir);

    if ir != to {
        stderr()
            .lock()
            .write_fmt(format_args!(
                "[test_opt] actual outcome mismatches with the expected outcome.\n\n[before opt]"
            ))
            .unwrap();
        crate::write(&from, &mut stderr()).unwrap();
        stderr()
            .lock()
            .write_fmt(format_args!("\n[after opt]"))
            .unwrap();
        crate::write(&ir, &mut stderr()).unwrap();
        stderr()
            .lock()
            .write_fmt(format_args!("\n[after opt (expected)]"))
            .unwrap();
        crate::write(&to, &mut stderr()).unwrap();
        panic!("[test_opt]");
    }
}
