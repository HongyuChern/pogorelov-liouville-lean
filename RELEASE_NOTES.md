# v0.1.1 — Independent Comparator for the four main CHS results

Theorems 1.1, 1.2, and 1.3 and Corollary 1.4 now have an independent
[Mathlib-only challenge](CHSComparator/MathlibOnly/Challenge.lean). The
[statements](CHSComparator/MathlibOnly/Statements.lean) spell out the Hessians,
boundary regularity, and norms. Lean proves that each proposition is equivalent
to its counterpart in the original suite. The solution applies the existing
`CHS.Paper` proofs through these equivalences.

The challenge built in a standalone Lake project with Mathlib as its sole
direct dependency. On Ubuntu 24.04 ARM64, the repository build succeeded and
the Linux Comparator accepted all four proofs in both Lean and Nanoda. The
axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`.
The [Linux verification receipt](CHSComparator/MathlibOnly/linux-verification.json)
records the tool revisions, axiom reports, and SHA-256 hashes of the checked
sources. The [verification guide](CHSComparator/README.md) gives the commands.

The [original Comparator suite](CHSComparator/config.json) covers all 12
numbered results in [arXiv:2609.18265v1](https://arxiv.org/abs/2609.18265v1).
Its full-manuscript run is recorded in the
[v0.1.0 verification receipt](CHSComparator/linux-verification.json).

[Full changes from v0.1.0](https://github.com/HongyuChern/pogorelov-liouville-lean/compare/v0.1.0...v0.1.1)
