# Verification

The target is
`UniversalGroup.exists_two_generator_thirteen_relator_universal_group`
in [UniversalGroup.lean](UniversalGroup.lean).
The repository pins Lean **4.35.0-rc2** and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Build and axiom audit

Run from the repository root:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The cache command downloads the pinned Mathlib build artifacts. Lake compiles
the proof library and reuses up-to-date local artifacts on subsequent builds.
To rebuild the project's Lean modules from source, remove `.lake/build` before
running `lake build`; the dependency packages under `.lake/packages` can remain.

[AxiomAudit.lean](AxiomAudit.lean) checks the main
theorem and intermediate results, including the preparation step, the input
embedding, both product-subgroup embeddings, and the final compression.
Each `#audit_axioms` command prints the declaration's
transitive axiom dependencies and fails if any axiom falls outside
`propext`, `Classical.choice`, and `Quot.sound`. In particular, it rejects
`sorryAx` from admitted proofs in the audited dependency chains.

## Continuous integration

[GitHub Actions](.github/workflows/lean.yml) installs the pinned toolchain and
Mathlib cache, runs `lake --wfail build`, and executes the Lean axiom audit.
Warnings in the proof-library build cause CI to fail. The independent challenge
is compiled separately because its intentional `sorry` produces a warning.
The workflow logs contain the build and audit results.

## Independent challenge

[Challenge.lean](Challenge.lean) contains the statement and its presentation
definitions independently of the proof. It can be compiled with:

```sh
lake build Challenge
```

This command checks that the challenge elaborates; comparing it against the
proof requires the external Lean Comparator. [comparator.json](comparator.json)
selects `Challenge` and `UniversalGroup` and permits the three standard axioms.
The two modules define the same names and must be loaded in separate Lean
environments. The challenge imports only Mathlib and is maintained independently
of the proof; the solution module imports the full modular library.

Install the external Comparator and its required tools using the
[official instructions](https://github.com/leanprover/comparator#comparator),
then run it on this project with the root `comparator.json`. The configuration
sets `solution_module` to `UniversalGroup`. The repository does not vendor
Comparator or its export and sandbox tools. An external comparator run is not
recorded.

## Maintenance

The maintained proof is the library under `UniversalGroup/`, with its public
theorem in [UniversalGroup.lean](UniversalGroup.lean). To check a change, run:

```sh
lake --wfail build
lake env lean AxiomAudit.lean
lake build Challenge
```

Keep the public statement and presentation conventions stable unless a change
explicitly requires otherwise. An embedding is an injective group homomorphism.
Keep the independent challenge's statement and presentation definitions
consistent with the library.
The proof library must contain no admitted proofs or additional axioms.

All project Lean files use the module system, including `Challenge.lean` and
`AxiomAudit.lean`. Library modules use `public import` and an
`@[expose] public section` so downstream proofs can use their declarations and
unfold their definitions. Preserve these interfaces when adding or moving files.

For Palomar submissions, keep the Lean and Mathlib versions aligned and at or
above [Palomar's minimum toolchain](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json).
[formalization.yaml](formalization.yaml) uses the upstream `v0.4` schema and
records the project description, human author and responsible maintainer,
mathematical sources, reused formalizations, and AI contributions.

Prefer simplification lemmas over an arbitrary group for word calculations.
Registering identities specialized to the full HNN model with `@[simp]` can
produce very large simplifier indexes. Use concrete coordinate lemmas
explicitly with `rw` or `exact`, and keep automatic simplification in the generic
group layer where practical.

Update [FORMALIZATION.md](FORMALIZATION.md) when a change affects the mathematical
construction, and this document when it affects verification. Explain the
mathematical effect of a contribution and the checks performed. Contributions
to this repository's code and documentation are under the [MIT license](LICENSE);
retain attribution and license notices when adapting third-party material.

## Scope

Lean checks the formal statements encoded in the source. The axiom audit rules
out unpermitted axioms in the audited dependency chains. Understanding that
these statements express the intended mathematics also requires reading the
[presentation conventions](FORMALIZATION.md) and the public theorem.

The [bibliography](FORMALIZATION.md#references) records mathematical sources,
including the simulator subgroup results recorded in Kegel–Li–Ren and proved
within this library. The axiom audit checks formal dependencies; it does not
establish originality or independence from those mathematical sources.
