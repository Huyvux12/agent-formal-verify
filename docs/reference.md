# Reference

## Skills and slash commands

| Skill | Claude Code command | Purpose |
| --- | --- | --- |
| `setup` | `/agent-formal-verify:setup` | Prepare the complete shared toolset once |
| `formal-verify` | `/agent-formal-verify:formal-verify` | Model-check protocols, prove invariants and check bounded Rust functions |

In Codex, type `$` and pick the skill, run `/skills`, or request the skill by name. The plugin ships no Codex prompts or slash commands. Parallel targets use the host's agent tools and your configured models. Hosts without delegation can process targets sequentially.

In Pi, use `/skill:setup` and `/skill:formal-verify`, or request a skill by name. The package ships no Pi extensions, prompts or themes.

In OpenCode, request `setup` or `formal-verify` by name; the agent loads it through the `skill` tool. The plugin's `opencode.mjs` registers the two skills from `skills/` and leaves any existing skill with the same name in place. It adds no tools, commands, agents or MCP servers. It needs OpenCode 2.2 or later; with an older version, use a skills-only installation.

In Antigravity, request `setup` or `formal-verify` by name. The `.antigravity-plugin/plugin.json` manifest exposes both skills from `skills/` and the plugin icon from the assets folder. It adds no hooks or MCP servers.

## Shared installation

To test a local checkout in Claude Code:

```shell
claude --plugin-dir /absolute/path/to/agent-formal-verify
```

To test a local checkout in Antigravity:

```shell
agy plugin validate /absolute/path/to/agent-formal-verify
agy plugin install /absolute/path/to/agent-formal-verify
```

To test a local checkout in Pi:

```shell
pi -e /absolute/path/to/agent-formal-verify
```

To test a local checkout in OpenCode, add it to `plugins` in a project's `opencode.json`:

```json
{
  "plugins": ["/absolute/path/to/agent-formal-verify"]
}
```

For a skills-only installation, use `skills/`. Its references, helpers and templates stay inside that tree. Copy both the `setup` and `formal-verify` skills so their references resolve.

Installing the plugin adds skills and helpers. Run setup to prepare the verification tools. The plugin has no hooks.

## Runtime setup and tool pins

The [setup skill](../skills/setup/SKILL.md) prepares a working JDK, Python 3.9 or later, a SHA256 tool, elan, Lean, Rust, Kani and the pinned TLC JAR. It reuses existing prerequisites and installs missing ones through your package manager or the upstream documented installer, within your installation constraints. It prepares all three verification tools and needs no target repository.

[Tool setup](../skills/formal-verify/references/setup.md) is the reference for everything after that first run: how verification prepares a changed Lean pin or tool version without a setup rerun, what global installations share, where caches live, the version pins, the direct helper commands, environment settings and CI.

## Plugin updates

For Claude Code, run in your terminal:

```shell
claude plugin update agent-formal-verify@agent-formal-verify
```

Run `/reload-plugins` in an existing session to load the update. You can enable marketplace auto-updates through `/plugin`. See [Claude Code plugin updates](https://code.claude.com/docs/en/discover-plugins#keep-plugins-updated).

For Codex:

```shell
codex plugin marketplace upgrade agent-formal-verify
```

Start a new session to use the refreshed plugin. See [Codex marketplace management](https://developers.openai.com/plugins/build/plugins#add-a-marketplace-from-the-cli).

For Pi:

```shell
pi update --extensions
```

Pin a release by installing `npm:agent-formal-verify@<version>` or `git:github.com/michael-denyer/agent-formal-verify@v<version>`; a pinned package does not move on update.

For OpenCode, `opencode plugin check` reports a newer release on npm, or a newer commit on the default branch for a Git install. To install it, pass the specifier you installed:

```shell
opencode plugin update agent-formal-verify
opencode plugin update 'git+https://github.com/michael-denyer/agent-formal-verify.git'
```

Pin a release in OpenCode by installing `agent-formal-verify@<version>`.

Tool caches survive plugin updates. Run setup again only if a release introduces a new system prerequisite.

## Scope and evidence

TLC explores thread interleavings for the model sizes in the check matrix. Lean proves properties of the model for every input satisfying the theorem's hypotheses. Kani checks the production Rust function within the harness's input and loop bounds. A passing harness needs a satisfied cover condition, which the harness author places at a boundary of interest. If you specify a tool, the agent uses it and reports what it leaves unchecked. See the [verification skill](../skills/formal-verify/SKILL.md).

In a repository that already has models, the agent starts by reading changes to the code each model covers, following renames and moves. It starts from the model's `Source read at` commit if that commit is an ancestor of the current revision. Otherwise it uses the last commit that touched the model files, or compares the model with the source in full if neither commit is available. It updates stale models and proposes retirement only after finding the commit that deleted the covered code. The report gives each model's status alongside its verdict.

A helper that cannot run a tool prints `UNAVAILABLE` and exits 3. Report that target as "not checked" with the remedy, never as a pass or a model failure. Failed checks exit 1 and usage errors exit 2.

**Checking the properties.** Before editing an existing model, the agent records its specification. After modelling, it reruns the checkers and mutations itself, compares the recorded guarantees, and reads the diff for changes the record cannot see, such as a removed Rust assertion. It reverts unsupported changes. A caller, test or checked witness can justify correcting a specification even when production code is unchanged. The agent records the evidence and the old and new guarantees.

Each model keeps its mutations in an adjacent file. Before reporting a pass, each checked property must detect a relevant mutation. The agent replays past bug fixes as mutations where the runner can express them. For each frozen public Lean theorem, the existing proof must fail on at least one mutation of the model. The runner identifies the theorem by its fully qualified name. A failing proof alone leaves open whether the mutated statement is false.

**Independent review.** The skill offers one reviewer per model. The reviewer reads the properties and callers without seeing the modelling agent's report and proposes bugs that might still pass. A missed mutation that changes behaviour a caller can observe goes back for a modelling change and another check. When a headless run cannot ask and you gave no review preference, the agent skips the review and reports that.

**Lean evidence.** The checker audits every declaration for unfinished proofs (`sorry`) and axioms beyond Lean's three standard ones. It checks any supplied witness that the theorem's hypotheses can hold together and reports missing witnesses. It also replays built modules through the kernel when the pinned Lean version supplies `leanchecker`. For a closed proof, the report gives the number of test inputs on which the model and production function agreed and the integer widths used, or says the comparison was skipped. See [evidence meanings](../skills/formal-verify/references/evidence.md).

**Failures and follow-up.** The agent maps a counter-example to source lines, checks shipped settings and callers, and tries to reproduce it. It labels the result `reproduced`, `reachable at shipped settings`, or `model-only` according to the evidence. If you request a fix for a reachable bug, the agent updates the code and model together and reruns the checks. When a reproduction is impractical, it gives the model configuration and explains the limitation. Commits and pull requests also require a request. Each PR covers one bug, names the failed property and includes any reproducing test.

The report includes commands to rerun the checks and mutations. The agent adds CI steps when you ask for them or when the repository already runs models in CI.

Replies, pull requests and documents are written for a reader who knows the code and has used none of these tools. They lead with what goes wrong in the code, state each property as what it guarantees, and say what a TLC pass, a Lean proof and a detected mutation each mean.

A passing model establishes its stated properties under its assumptions. Reports must identify omitted code constraints and unfinished proofs. These models do not check memory ordering below the mutex; keep ThreadSanitizer or race-detector checks. They do not establish correctness of the entire program or guarantee a particular number of discovered bugs.
