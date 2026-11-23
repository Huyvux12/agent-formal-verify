# Rust and Kani brief

Use Kani for a Rust function whose inputs and loops can be bounded. Call the real
function from one `#[kani::proof]` harness per property. Do not transcribe its
implementation. Edit an existing harness in place unless it moves, as "Moving
a harness" says, and start a new one from
[the bounded queue template](../examples/kani-template/src/lib.rs).

## Files

Work in the target repository. `<skill-dir>` means the absolute path to this
plugin's `skills/formal-verify` directory, not a directory in the target crate.
Write the harnesses in a `#[cfg(kani)] mod proofs` at the end of the production
file that defines the function, with the header comment directly above it, as
the template does. Write `<Name>.mutations` beside that file, where `<Name>` is
the file's stem, such as `lib`. The mutation runner applies a mutation only to
the file beside the mutations file and checks the harnesses of that file's
crate, so a harness in another crate cannot detect a mutation of the production
code. `#[cfg(kani)]` leaves the module out of every other build, and the main
thread declares `cfg(kani)` in the crate's `Cargo.toml`; if a check warns about
an unexpected `cfg` condition named `kani`, report it and leave `Cargo.toml`
alone. Own only that module and the mutations file, and change no other line of
the production file unless the user has authorized a production fix. Move a
harness that an earlier run wrote in a crate of its own into its production
file, as "Moving a harness" says, unless it copies a production function or
calls functions from more than one file. Edit such a harness and its mutations
file where they are.

Cite the production source paths and line numbers that each property models in
the harness header, the functions it calls, and the commit they were read at as
`Source read at <commit>`. List caller constraints, bounds and stub assumptions
there, with source citations or an explicit statement that each is an
assumption. Call the production function through its real crate or module
interface.

## Existing model

The row in your task gives the commits since the harness was last synced and
says whether any of them changed the guarantee on purpose. The harness calls the
production code, so drift shows as a compile error or a failed check. Update its
bounds, stubs, contracts and covers where they no longer fit the code. Change a
property only with that evidence or a specification correction accepted by the
main thread under step 3 of the skill. Add a mutation, with `detects`
naming the harness, for each branch or step the update adds. Update the header
to the code you read.

## Moving a harness

A harness that an earlier run wrote in a crate of its own can mutate only that
crate's files, so none of its mutations reach the production code. Move it into
the production file that defines the functions it calls:

1. Move its helpers and harnesses into the `#[cfg(kani)] mod proofs` at the
   end of the production file, creating the module if the file has none, and
   its header comment to directly above that module. Add `use crate as prod;`
   at the top of the module, with the name the old harness gave the
   production crate, so each `use`, stub, assumption and cover that names
   `prod::` keeps its text. Change nothing else in this step: the moved lines
   differ only in indentation. The main thread compares the moved
   harnesses with its record of the old ones and reads any other difference as
   a change that needs the evidence your row cites.
2. Move its `.mutations` file beside the production file as `<Name>.mutations`,
   or append its mutations to the one already there. Rename each `detects` to
   the harness's new qualified name as Kani prints it, such as
   `proofs::claim_keeps_invariant` for `claim_keeps_invariant`, or
   `queue::proofs::claim_keeps_invariant` in `src/queue.rs`. Replace each mutation that edits the harness
   with one that edits the production function, and replay the row's fix
   commits there.
3. Leave the old harness file and the rest of its crate in place, so the
   workspace still builds, and name the file and the crate in your report. The
   main thread deletes them.
4. Run the checker on the production crate and the mutation runner on the new
   mutations file. Then make any update your row asks for, as "Existing model"
   says.

Keep the old layout for a harness that names its own crate's items through
`crate::`, and report it. Stop and restore the old layout when the checker's
discovery fails in production code or a dependency, as the Check section
describes, and report it. Report the old module path and the new one, each
relative to its file, such as the crate root and `proofs`, even when the
production file is `src/queue.rs`.

## Model

Use `kani::any()` for inputs and `kani::assume` for caller constraints. Record
integer widths, input bounds and each assumption beside the harness. If a callee
needs a stub or a function contract, name that assumption in the header comment.
Put `#[kani::unwind(N)]` on every harness, above its real loop bounds. The checker
requires this explicit bound and passes it to Kani. A failed unwinding assertion
means the bound is too low and fails the check. Discovery and verification both
enable `-Z stubbing`, so documented `#[kani::stub]` attributes work in either step.
The checker rejects a harness marked `#[kani::should_panic]` when it would verify
that harness, before it verifies any. Assert the condition that leads to the panic
instead.

Kani stops a harness at `KANI_HARNESS_TIMEOUT`, five minutes by default. Symbolic
inputs that reach an error constructor that builds a message with `format!`, or
a wide division by a symbolic divisor, can stop the solver finishing within it. Give
those parameters concrete values or write one harness per variant, and keep the
symbolic inputs on the arithmetic the property is about.

Add `kani::cover!` witnesses for the boundary or blocking states each property
depends on, such as a full window or an empty queue. The checker rejects
unsatisfiable, unreachable and undetermined covers, even when Kani exits
successfully. Ordinary unreachable assertions are allowed because they describe
impossible panic branches. Every passing harness must have at least one
`Satisfied` cover after its assumptions. Successful assertions alone do not
establish reachability: Kani also labels compiler safety checks as assertions,
and one before contradictory assumptions can pass while the property is
unreachable. Existing coverless harnesses must add an explicit boundary
witness. Every cover must have status `Satisfied`.

## Check

Stay in the target repository and use absolute paths:

```sh
bash <skill-dir>/scripts/kani-check.sh /absolute/path/to/crate
python3 <skill-dir>/scripts/mutate.py /absolute/path/to/crate/src/Name.mutations
```

Append fully qualified harness names to check only those properties. The helper
prints one verdict per harness with the unwind bound and number of checks. It
requires a complete Kani 0.68.0 bundle and Python 3.9 or later. It checks and invokes the
bundle's driver directly, without invoking the auto-installing Cargo wrapper.
A registered Cargo installer is not required after setup. Relative `KANI_HOME`
paths resolve against the caller's directory before any temporary work begins.
The helper installs no Kani runtime. `UNAVAILABLE` means not checked; follow the
printed remedy before making any claim about the code. A compilation
error, missing harness or incomplete verifier report fails.

A discovery failure that names Kani's bundled toolchain means that code Kani
compiles uses a feature the toolchain lacks. When an error location is in
harness code, rewrite the harness without that feature. When every location is
in production code or a dependency, do not add a feature attribute to the
production crate, and report the target as not checked by Kani. A harness in a
separate crate that copies the function checks the copy, not the production
code, so report it as a model and name the copied source and commit.

Put `<Name>.mutations` beside the production file `<Name>.rs`. Use
`detects <fully-qualified-harness>` for each mutation. The mutation runner uses
the bundled Cargo to find the crate's workspace and local dependencies, copies
them to temporary storage with their relative paths intact, and checks the
copied manifest from the original crate directory so Cargo retains configuration
and relative paths to external files. Each selected harness must first pass on
the unmutated source; a compiler error or inconclusive check never counts as
detection. Every harness declared in the adjacent Rust file needs a mutation.
An explicit property failure or a lost cover witness can detect a mutation;
missing covers and unreachable assertions alone are inconclusive.
An explicit `detects` may also name a harness in another file; unrelated
harnesses in other files do not contribute to this file’s coverage requirement.

Direct checks and discovery run from the crate directory so Cargo reads crate
and ancestor configuration. Discovery uses code generation metadata in an
isolated target directory and does not write a `kani-list.json` into the source
tree. Cargo may create or update its normal lockfile.

For each fix commit in your row whose fixed code is in the file beside the
mutations file, add a mutation that restores the code before the fix, with the
commit's short hash in its label. The runner edits only that file, so report a
fix in any other file as not replayed.

## Counter-examples

The helper prints failed checks with source locations and Kani's generated
concrete playback test when available. Copy that test into the harness module in
a temporary crate copy. Stay in the target repository and run:

```sh
cargo kani playback --manifest-path /absolute/path/to/temporary-crate/Cargo.toml -Z concrete-playback -- <generated-test-name>
```

A printed test has not yet reproduced the failure. Record whether this command
actually fails on the expected assertion. Kani cannot generate playback for
every failure, including unwinding failures; report that limitation explicitly.
Never disable unwinding checks to obtain a pass.

## Report

Report each property, input bounds, integer widths, unwind bound, assumptions,
cover witnesses, mutation results and source location. Give each fix commit from
the row with the verdict of its mutation, or say it was not replayed. For each
counter-example, include its inputs and reproducing test and say whether shipped
callers can pass those inputs. Use `reproduced`, `reachable at shipped settings` or `model-only`
as appropriate. A pass covers the stated bounded inputs only. Report unavailable
tools as not checked with the remedy, never as a pass or a model failure.
