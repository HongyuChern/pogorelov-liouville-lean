# First public release of the CHS formalization

This release accompanies the Lean 4 formalization of *Pogorelov interior estimates and a Liouville theorem for the complex Monge–Ampère equation* by Hongyu Chen, Jingchen Hu, and Li Sheng. It covers the three main theorems, Corollary 1.4, and the eight numbered supporting results in [arXiv:2609.18265v1](https://arxiv.org/abs/2609.18265v1).

The formalization proves interior estimates for the full real Hessian and quadratic rigidity for entire smooth solutions. The Liouville argument proves the Hessian Hölder estimate needed for the complex Monge–Ampère equation and uses its scaling on expanding balls. Corollary 1.4 allows real convexity outside a compact set.

- **Lean entry point** `import CHS`. See [the public declarations](CHS/PaperTargets.lean).
- **Reproducibility** Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. See [build instructions](README.md#build) and [Comparator targets and commands](CHSComparator/README.md).
- **Verification** The default build passed on Ubuntu 24.04 ARM64. All 14 declarations passed Comparator in the Linux Landrun sandbox and were accepted by the Lean and Nanoda kernels. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. [Verification receipt](CHSComparator/linux-verification.json)
- **Attribution** The source includes the De Giorgi modules used in the proofs. [Source revisions, licenses, and modifications](THIRD_PARTY.md)
- **License** CHS code is available under [Apache-2.0](LICENSE).
