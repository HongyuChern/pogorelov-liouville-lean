# Comparator verification

## Independent challenge for the four main results

Theorems 1.1, 1.2, 1.3 and Corollary 1.4 have an independent
[challenge](MathlibOnly/Challenge.lean) and [configuration](MathlibOnly/config.json).
The challenge imports [Statements.lean](MathlibOnly/Statements.lean), which imports
only Mathlib modules. The statements use real Euclidean coordinates on
ℂⁿ, explicit Wirtinger formulas, continuous extensions of the interior derivatives
to the closure, and the entrywise maximum of the scalar Lebesgue `L∞` seminorms.
Theorem 1.1 uses the manuscript's sign-free hypotheses.

[Bridge.lean](MathlibOnly/Bridge.lean) proves both directions of equivalence with
the original propositions. [Solution.lean](MathlibOnly/Solution.lean) applies
these equivalences to the existing `CHS.Paper` proofs. The four proof holes are
in the independent challenge and never enter the solution. To build the two modules
from the repository root, run

```sh
lake build +CHSComparator.MathlibOnly.Challenge +CHSComparator.MathlibOnly.Solution
```

## Original full-manuscript suite

The original check covers all 12 numbered results from the frozen manuscript. Lemmas 2.2 and 2.3 each have two separate conclusions, for a total of 14 declarations. [Statements.lean](Statements.lean) records the propositions using the shared definitions for the Hessians, boundary jets, and norms. The theorem proofs enter through [Solution.lean](Solution.lean). The proof holes in [Challenge.lean](Challenge.lean) represent the work assigned to the solution. The `CHS` library's default build is independent of both challenges.

| Manuscript result | Declaration in `CHSComparator.Targets` |
| --- | --- |
| Theorems 1.1, 1.2, 1.3 and Corollary 1.4 | `theorem_1_1`, `theorem_1_2`, `theorem_1_3`, `corollary_1_4` |
| Lemma 2.1 | `lemma_2_1` |
| Lemma 2.2 | `lemma_2_2_nonnegative`, `lemma_2_2_positive` |
| Lemma 2.3 | `lemma_2_3_identity`, `lemma_2_3_nonpositive` |
| Proposition 2.4 and Lemmas 2.5, 2.6 | `proposition_2_4`, `lemma_2_5`, `lemma_2_6` |
| Lemma 3.1 and Proposition 3.2 | `lemma_3_1`, `proposition_3_2` |

## Reproduce the check on Linux

Comparator checks statement equality and the transitive axiom allowlist, then replays
the exported declarations in Lean and Nanoda. Both suites permit `propext`,
`Classical.choice`, and `Quot.sound`. Review the propositions against the manuscript
as well as checking the formal proofs.

Install Elan, Git and the dependencies for [Landrun](https://github.com/Zouuup/landrun) and [Nanoda](https://github.com/ammkrn/nanoda_lib). Use an unprivileged Linux account with Landlock and a working systemd user session. Prepare the project dependencies with `lake exe cache get`. The repository uses the standalone Comparator compatible with its Lean 4.33.1 pin.

In a separate tools directory, check out [Comparator `3927ad3`](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097) and run `lake +leanprover/lean4:v4.33.1 build comparator lean4export` from that checkout. Its lock file pins [lean4export `15f6055`](https://github.com/leanprover/lean4export/tree/15f6055e299ad5b89345e533cc2192f4cc00f659). Set the two executable paths below. The Nanoda binary distributed with Lean 4.35.0 can be used as a standalone verifier for the exported proofs. Use the Landrun version from [revision `811cfff`](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4) or a compatible Linux build.

```sh
export CHS_COMPARATOR=/absolute/path/to/Comparator/.lake/build/bin/comparator
export COMPARATOR_LEAN4EXPORT=/absolute/path/to/Comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
export COMPARATOR_NANODA=/absolute/path/to/nanoda_bin
export TMPDIR="$HOME/chs-comparator-tmp"
mkdir -p "$TMPDIR"
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$PWD" \
  --setenv="PATH=$PATH" --setenv="TMPDIR=$TMPDIR" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
  --setenv="COMPARATOR_NANODA=$COMPARATOR_NANODA" \
  lake env "$CHS_COMPARATOR" CHSComparator/MathlibOnly/config.json
```

Use `CHSComparator/config.json` in the same command to run the original suite.

An accepted run reports `Nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, and `Your solution is okay!`. Record the checked Git revision and the full log for the release. The upstream invocation and trust assumptions are documented in the [standalone Comparator guide](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097).

The [independent challenge receipt](MathlibOnly/linux-verification.json) records
the isolated Mathlib build, four verified targets, axiom reports, and SHA-256 hashes
of the proof and build inputs. The Ubuntu 24.04 ARM64 run used Landlock ABI 4 and
the pinned Comparator's Landrun best-effort mode. Control checks confirmed that
Landrun blocked a write outside the writable directory and systemd blocked
AF_UNIX socket creation. The [v0.1.0 receipt](linux-verification.json) records
the run of the original suite.
