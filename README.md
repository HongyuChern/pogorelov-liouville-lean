# Pogorelov estimates and Liouville rigidity in Lean

This repository contains the Lean 4 formalization of *Pogorelov interior estimates and a Liouville theorem for the complex Monge–Ampère equation* by Hongyu Chen, Jingchen Hu, and Li Sheng. The source paper is [arXiv:2609.18265v1](https://arxiv.org/abs/2609.18265v1).

`import CHS` exposes all 12 numbered results. The four main results are listed below. The eight supporting results are indexed in [CHS/PaperTargets.lean](CHS/PaperTargets.lean).

| Paper | Lean declaration | Result |
| --- | --- | --- |
| Theorem 1.1 | `CHS.Paper.theorem_1_1` | Pogorelov interior estimate under the Schur complement inequality |
| Theorem 1.2 | `CHS.Paper.theorem_1_2` | Pogorelov interior estimate for real convex solutions |
| Theorem 1.3 | `CHS.Paper.theorem_1_3` | An entire smooth real convex solution is a real quadratic polynomial |
| Corollary 1.4 | `CHS.Paper.corollary_1_4` | The same rigidity holds under real convexity outside a compact set |

The Liouville proof establishes a local Hessian Hölder estimate for the complex Monge–Ampère equation and applies it on expanding balls. The theorem covers all positive complex dimensions.

## Build

With [Elan](https://github.com/leanprover/elan) installed, run the following commands from the repository root. The project uses Lean 4.33.1 and Mathlib at revision `0df444a360eaa60ab8c11dca51a86af692955474`. Lake obtains the dependencies listed in `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

## Verify

Comparator checks the 12 numbered results through 14 declarations, with separate declarations for the two conclusions of Lemmas 2.2 and 2.3. The challenge uses the definitions of the Hessians, closure jets, and norms listed in the verification guide. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. [Targets and reproduction instructions](CHSComparator/README.md)

The default build and the Comparator run passed on Ubuntu 24.04 ARM64. Comparator ran under Landrun and a systemd user service and accepted all targets in both Lean and Nanoda. [Verification receipt and source hashes](CHSComparator/linux-verification.json)

## Source and attribution

CHS code is licensed under [Apache-2.0](LICENSE). The repository includes the De Giorgi modules used in the proofs and the corresponding license and modification records. [Sources, credits, and licenses](THIRD_PARTY.md)
