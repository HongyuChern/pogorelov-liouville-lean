# Third-party code

## De Giorgi–Nash–Moser theory

CHS uses weak Harnack estimates, localization, and the strong minimum principle from the De Giorgi library. DifferentialGeometry v0.1.3 adapts the Lean development by Scott Armstrong and Julia Kempe and adds the strong minimum principle and other weak formulation results. CHS includes the 95 Lean files from its `DifferentialGeometry/External/DeGiorgi/` subtree at revision `7a48598d35109aa99d1cc678e2724c213cdf4ff3`. [Armstrong and Kempe, *Formalization of De Giorgi–Nash–Moser Theory in Lean*](https://arxiv.org/abs/2604.05984) · [Original software revision](https://github.com/scottnarmstrong/DeGiorgi/tree/4c1b3077d3782b24065184df4ba59501b2e56fc7) · [DifferentialGeometry v0.1.3 revision](https://github.com/qinz1yang/differential-geometry/commit/7a48598d35109aa99d1cc678e2724c213cdf4ff3)

CHS narrows the Mathlib imports in seven files and provides the local `DifferentialGeometry.lean` entry point. The seven changed files carry modification notices. The source manifest records the upstream Git blobs and SHA-256 hashes for all 95 Lean files. [Source manifest](docs/DeGiorgi-source.json) · [CHS imports patch](docs/DeGiorgi-imports.patch) · [Upstream modifications](docs/DeGiorgi-upstream-modifications.md) · [Citation metadata](docs/DeGiorgi-CITATION.cff)

The bundled sources are distributed under Apache-2.0. [DeGiorgi license](LICENSES/DeGiorgi.LICENSE) · [DifferentialGeometry license](LICENSES/differential-geometry.LICENSE) · [DifferentialGeometry notice](LICENSES/differential-geometry.NOTICE)

## PoincareLib determinant differentiation

The Jacobi formula proof in [CofactorDivergence.lean](CHS/Calculus/CofactorDivergence.lean) adapts the real matrix proof by the PoincareLib contributors through our companion KE-Ball project. CHS uses complex matrices, restriction of scalars to the reals, and its own Wirtinger derivatives. The PoincareLib file credits Chow, Liao, and Qin's DifferentialGeometry development for the statement of Jacobi's formula. [Original PoincareLib file](https://github.com/frenzymath/Poincare-Conjecture/blob/432c38f2aa5a30efb13871292d17b4a3309a496a/PoincareConjecture/PoincareLib/Analysis/Matrix/Determinant.lean)

The file at revision `62db01af9388dc1d9b56b66d6674f4c09b2318a2` of the companion proof repository is byte identical to the source at revision `432c38f2aa5a30efb13871292d17b4a3309a496a` of the Apache-2.0 repository. Its SHA-256 is `aee0ebefe285dad65523a8e802deaf0fc35e6c0644ec0f15878eb1d48272862f`. The distribution includes the [original repository license](LICENSES/Poincare-Conjecture.LICENSE), its [NOTICE](LICENSES/Poincare-Conjecture.NOTICE), and the [PoincareLib contributors' notice](LICENSES/PoincareLib.NOTICE). [Pinned upstream license declaration](https://github.com/frenzymath/Poincare-Conjecture/blob/432c38f2aa5a30efb13871292d17b4a3309a496a/README.md) · [PoincareLib import record](https://github.com/frenzymath/PoincareConjecture/blob/62db01af9388dc1d9b56b66d6674f4c09b2318a2/MODIFICATIONS.md)

## Mathlib and verification tools

Lake obtains Mathlib and its dependencies at the pinned revisions. The direct Mathlib dependency is `0df444a360eaa60ab8c11dca51a86af692955474`. [Mathlib license](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/LICENSE)

Comparator, lean4export, Nanoda, and Landrun are external verification tools. Their source and installation instructions are listed in the [Comparator guide](CHSComparator/README.md).
