Several active, open-source Lean 4 repositories track and formalize open mathematical conjectures and research-level results. Depending on whether you want to attack unproved open problems, formalize explicit analytic bounds, or benchmark automated proof search, four primary codebases serve as immediate entry points.

---

### 1. Active Lean 4 Repositories for Current Math Problems

* **Google DeepMind’s `formal-conjectures` (`google-deepmind/formal-conjectures`)**
* **Scope & Attribution:** Maintained by the Formal Conjectures Authors (Google DeepMind and community contributors, licensed under Apache 2.0). As of late 2026, the repository contains roughly 4,900 formalized theorem statements built on top of Mathlib—spanning ~1,881 open conjectures and 1,146 formally proved statements—annotated with `@[category]` tags (`research open`, `research solved`) and AMS MSC2020 subject codes.
* **Problem Domains:** Covers Erdős problems (`erdosproblems.com`), named conjectures (Riemann Hypothesis, Collatz conjecture), Millennium Prize problems, Hilbert's problems, and recent arXiv preprints. It also maintains frozen benchmark targets (`FC100OpenSet1.lean` and `FC100SolvedSet1.lean`) tagged by Mathlib/toolchain version (e.g., `bench-vN-lean4.X.Y`) for reproducible local testing.


* **Integrated Explicit Analytic Number Theory Network (`teorth/IEANTN` & `AlexKontorovich/PrimeNumberTheoremAnd`)**
* **Scope & Attribution:** Initiated by Terence Tao and Alex Kontorovich. Originally launched as the *Prime Number Theorem and More* (`PNT+`) project in 2024 and expanded into `IEANTN` in January 2026, the repository was refactored in August 2026 so new explicit analytic number theory contributions live in `teorth/IEANTN`.
* **Architecture:** Unlike monolithic lemma blueprints, `IEANTN` organizes mathematics as a living dependency network where each node corresponds to a published paper establishing explicit bounds—such as Chebyshev functions $\psi(x)$ and $\theta(x)$, prime counting $\pi(x)$, zero-free regions, and prime gap estimates. Individual node proofs are verified independently using external checkers like `comparator`.


* **Erdős Problems Lean 4 Formalizations (`hongjin-he/erdos-lean` & `erdosproblems.com`)**
* **Scope & Attribution:** Tracks formalizations of both open and recently resolved Erdős problems (such as Erdős #514, #728, #790, and #956), incorporating contributions from Terence Tao's community database (`erdosproblems.com`), Kevin Barreto / Harmonic (`Aristotle`), Samuel Korsky, and HongJin He.
* **Verification Standard:** Files are strictly audited via `#print axioms` to guarantee reliance solely on Lean's three standard foundational axioms (`propext`, `Classical.choice`, and `Quot.sound`) with zero `sorry` placeholders, custom axioms, or `native_decide` shortcuts.


* **Flagship Theory Formalizations (`ImperialCollegeLondon/FLT`)**
* **Scope & Attribution:** Led by Kevin Buzzard at Imperial College London, this ongoing project formalizes the proof of Fermat's Last Theorem in Lean 4 + Mathlib, sitting alongside completed 2026 milestones such as the 24-dimensional sphere packing formalization (originally ~500K SLOC generated via Math Inc.'s Gauss system and pruned to ~200K SLOC).



---

### 2. Local Toolchain Setup & Reproducible Build Workflow

To run Lean 4 locally on a Linux environment without executing un-audited remote scripts via pipe-to-shell, install `elan` (the Lean version manager) directly from verified GitHub release artifacts, then use `lake` (Lean's build system) to pull precompiled Mathlib `.olean` binaries.

```bash
# 1. Create a local bin directory and fetch the elan release archive directly for inspection
mkdir -p ~/.local/bin && cd /tmp
curl -fLO https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
curl -fLO https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz.sha256

# 2. Verify SHA-256 checksum before extracting and initializing
sha256sum -c elan-x86_64-unknown-linux-gnu.tar.gz.sha256
tar -xzf elan-x86_64-unknown-linux-gnu.tar.gz
./elan-init -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

# 3. Clone formal-conjectures (or teorth/IEANTN)
git clone https://github.com/google-deepmind/formal-conjectures.git
cd formal-conjectures

# 4. Pull precompiled Mathlib oleans (avoids compiling Mathlib from scratch) and build
lake exe cache get
lake build

```

#### Kernel Trust & Independent Verification

Following the soundness bugs uncovered in Lean 4 during mid-2026 ("Summer of Soundness Bugs") and the Lean FRO Year 4 roadmap, standard `lake build` checks are routinely paired with external typecheckers and axiom audits:

* **External Kernel Checking:** Use `lake check` or `lake check --paranoid` (which runs external checkers such as `comparator` and `nanoda` over exported environments) to ensure no elaboration bug or kernel invariant violation slipped into a proof.
* **Axiom Auditing:** Append `#print axioms <theorem_name>` at the bottom of any target file. A valid, constructive-plus-classical mathematical proof must output only `[propext, Classical.choice, Quot.sound]`—any appearance of `sorryAx` or `Lean.ofReduceBool` (`native_decide`) flags an incomplete or unverified step.

---

### 3. Tacticals & Local Proof-Search Options

When working through open goals or filling `sorry` blocks in `formal-conjectures` or `IEANTN`:

1. **Built-in Lean 4 Automation (`grind` and `bv_decide`):** Recent Lean 4 releases hardened the `grind` congruence-closure/E-matching tactic and `bv_decide` (bit-blasting SAT solver integration with LRAT proof certificates). `grind` is particularly effective for algebraic and order-theoretic inequalities in explicit number theory bounds.
2. **Local Open-Weights Prover Models:** If you want to run automated tactic generation or whole-proof search locally against a Lean 4 REPL (such as `LeanDojo` or `Pantograph`), open-weights models specifically fine-tuned on Lean 4 + Mathlib include **Goedel-Prover-V2** (Princeton University), **DeepSeek-Prover-V2** (DeepSeek AI), and **Kimina-Prover** (Moonshot AI). Note that benchmark saturation on undergraduate sets like PutnamBench (672/672 solved by top systems in 2026) means research-level open problems in `FC100OpenSet1` still require human decomposition into intermediate lemmas before automated tactics can close the subgoals.
