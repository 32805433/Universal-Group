# A universal group with thirteen relators

A Lean 4 proof that there exists a **two-generator, thirteen-relator group**
containing an isomorphic copy of every finitely presented group.

The main theorem is in [UniversalGroup.lean](UniversalGroup.lean).
[FORMALIZATION.md](FORMALIZATION.md) explains the construction and links its
mathematical steps to the modular proofs under `UniversalGroup/`.

## Statement

Inside the namespace `UniversalGroup`:

```lean
theorem exists_two_generator_thirteen_relator_universal_group :
    ∃ P : FP 2 13,
      ∀ (n m : ℕ) (Q : FP n m),
        ∃ f : PresentedGroup Q.relSet →* PresentedGroup P.relSet,
          Function.Injective f
```

`FP n m` represents a group presentation with `n` generators and `m` relators.
`PresentedGroup P.relSet` is the quotient of the free group by the normal
closure of the relators. One target presentation `P` works for every input
presentation `Q`.

## Build

Install [Lean through elan](https://lean-lang.org/install/), then run:

```sh
lake exe cache get
lake build
```

The repository pins **Lean 4.35.0-rc2** and Mathlib in `lean-toolchain` and
`lake-manifest.json`. All local proof dependencies are included.
To build the independent comparator challenge as well:

```sh
lake build Challenge
```

The single `sorry` in `Challenge.lean` is the intentional comparator target.
The proof library contains no admitted proofs. Import `UniversalGroup` to use
the main theorem from another Lean file.

## Construction

Higman's embedding theorem supplies a finitely presented universal input.
Positive preparation and word recognition embed it in a six-generator,
nineteen-relator group. A free triple preserved by the preparation and a
positive simulator symmetry supply two specified copies of `F₂ × F₃`.
An HNN extension identifies their bases; five generator eliminations and
six redundant relations give the final presentation.

The [proof guide](FORMALIZATION.md) explains the full argument, including
preparation by a marked quotient and an explicit permutation action.
The [bibliography](FORMALIZATION.md#references) records the mathematical sources.
The simulator subgroup calculations follow Borisov's normal-form machinery
and Kegel–Li–Ren's structural results. The host also adapts Kegel–Li–Ren's
first HNN symmetry, using a positive-sign variant. The required counterparts
are proved in this library for the input-dependent coding rules.

## Verification

Build the proof and run the Lean axiom audit:

```sh
lake build
lake env lean AxiomAudit.lean
```

The audit checks the main theorem and intermediate results,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
[VERIFICATION.md](VERIFICATION.md) explains the checks. GitHub Actions builds
the library with warnings treated as failures and runs the audit on pushes
and pull requests.

The [comparator inputs](VERIFICATION.md#independent-challenge) are the independent
[Challenge.lean](Challenge.lean) and the modular proof exposed by
[UniversalGroup.lean](UniversalGroup.lean). [comparator.json](comparator.json)
selects these modules for the external Lean Comparator. An external comparator
run is not recorded.
See [the maintenance notes](VERIFICATION.md#maintenance) for source conventions
and required checks.

## AI authorship

The library reuses and adapts Lean code from the earlier
[Adian–Rabin project](https://github.com/32805433/Adian-Rabin), including
finite-presentation, HNN, simulator, and machine-compilation infrastructure.
The [software provenance notes](FORMALIZATION.md#software-provenance) describe
this reuse; the upstream copyright notice is retained in [LICENSE](LICENSE).

Essentially everything in this repository, including the Lean formalization
and documentation, was produced by GPT-6 Astra under human
direction. [formalization.yaml](formalization.yaml) records the automation and
review status.

## License

The repository's own code and documentation are under the [MIT license](LICENSE).
Lean, Mathlib, and their dependencies retain their respective licenses.
