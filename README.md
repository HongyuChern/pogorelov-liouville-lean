# Pogorelov estimates and Liouville rigidity in Lean

This repository contains the Lean 4 formalization of *Pogorelov interior estimates and a Liouville theorem for the complex Monge–Ampère equation* by Hongyu Chen, Jingchen Hu, and Li Sheng. The source paper is [arXiv:2609.18265v1](https://arxiv.org/abs/2609.18265v1).

`import CHS` exposes all 12 numbered results. The four main results are listed below. The eight supporting results are indexed in [CHS/PaperTargets.lean](CHS/PaperTargets.lean).

| Paper | Lean declaration | Result | Proof |
| --- | --- | --- | --- |
| Theorem 1.1 | `CHS.Paper.theorem_1_1` | Pogorelov interior estimate under the Schur complement inequality | [General estimate](CHS/Pogorelov/GeneralTheorem.lean#L29) |
| Theorem 1.2 | `CHS.Paper.theorem_1_2` | Pogorelov interior estimate for real convex solutions | [Convex estimate](CHS/Pogorelov/ConvexEstimate.lean#L78) |
| Theorem 1.3 | `CHS.Paper.theorem_1_3` | An entire smooth real convex solution is a real quadratic polynomial | [Liouville proof](CHS/Liouville/Entire.lean#L49) |
| Corollary 1.4 | `CHS.Paper.corollary_1_4` | The same rigidity holds under real convexity outside a compact set | [Exterior convexity proof](CHS/Liouville/ExteriorConvexity.lean#L146) |

The Liouville proof establishes a local Hessian Hölder estimate for the complex Monge–Ampère equation and applies it on expanding balls. The theorem covers all positive complex dimensions.

## Build

With [Elan](https://github.com/leanprover/elan) installed, run the following commands from the repository root. The project uses Lean 4.33.1 and Mathlib at revision `0df444a360eaa60ab8c11dca51a86af692955474`. Lake obtains the dependencies listed in `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The formalization of all 12 numbered results spans **74,663 lines across 247 Lean files**, counting `CHS.PaperTargets` and its transitive imports within this repository. The [v0.1.1 release](https://github.com/HongyuChern/pogorelov-liouville-lean/releases/tag/v0.1.1) ships **84,104 lines across 299 Lean files**, including the Comparator and audit files. Both counts include bundled De Giorgi sources, comments, and blank lines. Lake fetches Mathlib and its transitive dependencies separately.

## Comparator

The four main results have an independent challenge that uses only Mathlib. The statements spell out the Hessians, boundary regularity, and norms, and the bridge proves that each proposition is equivalent to its counterpart in the original suite. The four `sorry` placeholders in the challenge stand in for the proofs supplied by the solution.

[Challenge](CHSComparator/MathlibOnly/Challenge.lean) · [Statements](CHSComparator/MathlibOnly/Statements.lean) · [Bridge](CHSComparator/MathlibOnly/Bridge.lean) · [Solution](CHSComparator/MathlibOnly/Solution.lean) · [Configuration](CHSComparator/MathlibOnly/config.json) · [Linux verification receipt](CHSComparator/MathlibOnly/linux-verification.json)

The [original suite](CHSComparator/config.json) covers all 12 numbered results through 14 declarations using the shared CHS definitions. Both suites use Lean and Nanoda and allow only `propext`, `Classical.choice`, and `Quot.sound`. [Targets and Linux reproduction instructions](CHSComparator/README.md)

The independent challenge built in a standalone Lake project whose sole direct dependency was Mathlib. On Ubuntu 24.04 ARM64, the repository build succeeded and both kernels accepted the four main proofs. The receipt records the tool revisions, axiom audit, and SHA-256 hashes of the checked inputs.

## Source and attribution

The bundled De Giorgi modules provide weak Harnack estimates, localization, and the strong minimum principle. The Jacobi formula for determinant differentiation adapts a PoincareLib proof through the companion KE-Ball project. [Jacobi formula implementation](CHS/Calculus/CofactorDivergence.lean) · [Upstream sources, credits, and licenses](THIRD_PARTY.md)

CHS code is licensed under [Apache-2.0](LICENSE).
