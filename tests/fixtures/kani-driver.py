import json
import os
import pathlib
import sys

args = sys.argv[1:]
trace = os.environ.get("TASK_TRACE")
base = pathlib.Path(trace).parent
config = json.loads((base / "driver.json").read_text())
with open(trace, "a") as log:
    log.write(" ".join(args) + "\n")
if args[0] == "metadata":
    manifest = pathlib.Path(args[args.index("--manifest-path") + 1])
    print(json.dumps(config.get("cargoMetadata", {
        "version": 1, "workspace_root": str(manifest.parent),
        "packages": [{"source": None, "manifest_path": str(manifest), "dependencies": []}],
    })))
    sys.exit(config.get("cargoMetadataStatus", 0))
kani_home = os.environ.get("KANI_HOME")
bundle_home = pathlib.Path(__file__).resolve().parents[2]
if config.get("expectResolvedHome") and kani_home != str(bundle_home):
    sys.exit(f"KANI_HOME is {kani_home!r}, expected the resolved {bundle_home}")
library_path = os.environ.get("DYLD_FALLBACK_LIBRARY_PATH") if sys.platform == "darwin" else os.environ.get("LD_LIBRARY_PATH")
if "expectLibraryPath" in config and library_path != config["expectLibraryPath"]:
    sys.exit(f"loader path is {library_path!r}, expected {config['expectLibraryPath']!r}")
if args == ["--version"]:
    print(f"Kani Rust Verifier {config['version']} (cargo plugin)\nCBMC 6.11.0")
    sys.exit()
target = pathlib.Path(args[args.index("--target-dir") + 1])
crate = pathlib.Path(args[args.index("--manifest-path") + 1]).parent
if "--only-codegen" in args:
    if "listError" in config:
        sys.exit(config["listError"])
    if config.get("deleteDriverAfterList"):
        (pathlib.Path(kani_home) / f"kani-{config['version']}/bin/kani-driver").unlink()
    target.mkdir(parents=True, exist_ok=True)
    harnesses = config["harnesses"]
    metadata = config.get("metadata", {"proof_harnesses": [
        {"pretty_name": name, "original_file": config.get("harnessSources", {}).get(name, "src/lib.rs"),
         "attributes": {"kind": "Proof", "unwind_value": bound}} for name, bound in harnesses.items()]})
    (target / "crate.kani-metadata.json").write_text(json.dumps(metadata))
else:
    mutated = (crate / "src/lib.rs").is_file() and (crate / "src/lib.rs").read_text() == "new\n"
    if config.get("compileError") and mutated:
        print("error: compilation failed")
        sys.exit(1)
    for relative, contents in (config.get("requiredCrateFiles", {}) if mutated else {}).items():
        path = crate / relative
        if not path.is_file() or path.read_text() != contents:
            sys.exit(f"missing or changed crate input: {relative}")
    report_file = base / ("baseline.json" if not mutated and (base / "baseline.json").is_file() else "report.json")
    report = json.loads(report_file.read_text())
    if report_file.name == "baseline.json":
        report["verification_results"]["results"][0]["harness_id"] = args[args.index("--harness") + 1]
    pathlib.Path(args[args.index("--export-json") + 1]).write_text(json.dumps(report))
    print("Concrete playback unit test fixture")
    sys.exit(1 if report["verification_results"]["results"][0]["status"] == "Failure" else 0)
