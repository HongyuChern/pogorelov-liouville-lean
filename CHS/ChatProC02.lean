import CHS.ChatProC01
import CHS.Pogorelov.ConvexEstimate
import CHS.Algebra.SignBranch
import CHS.Algebra.PositiveCone
import CHS.Calculus.ClosureNegation
import CHS.Calculus.SignPropagation
import CHS.Pogorelov.SignNorms
import CHS.Pogorelov.GeneralTheorem
import CHS.Pogorelov.AffineGeometry
import CHS.Sections.NormalizedEntire
import CHS.Sections.SectionScale
import CHS.Sections.SectionExhaustion
import CHS.Sections.GlobalHessian
import CHS.Sections.JohnContactBound
import CHS.Analysis.HessianUpperEnvelope
import CHS.Analysis.HessianOscillationRigidity
import CHS.Liouville.ExteriorConvexity

/-!
# Chat Pro C02 proof batch

C01 interface repairs, actual C² boundary jets, compact real-translation
quotients, strict negativity, maximum attainment, exact real Hessian bounds,
and the positive-branch and convex L∞ endpoints.  The strict projected
extremum and fixed-kernel rank argument also close the sign reduction in
the independent statement of Theorem 1.1, exported as
`CHS.general_pogorelov_linf`.

The subsequent section modules prove the actual normalization (3.3),
compact transverse sections and real quotients, the exact ellipsoid
sandwich (3.4), comparisons and scale bound (3.5), (3.6), and the analytic
chain (3.7)--(3.9) and exhaustion.  The ellipsoid is constructed by a
maximum-determinant affine normalization and an explicit perturbation;
its real dimension radius ratio gives exactly the paper's `4 n²`.
Proposition 3.2 is exported unconditionally as
`CHS.proposition_3_2_global_hessian_bound`, with the stronger C4 theorem
`CHS.entire_convex_hessian_bound` also available.
The global ellipticity, actual directional subsolutions, scale-independent
weak-Harnack mean bounds, and a common Loewner upper envelope in the actual
Hessian range closure are now proved without an Evans--Krylov premise.
The separate general local Hessian Holder theorem is proved from actual
directional supersolutions, log-determinant support, finite cone directions,
weak Harnack, and geometric oscillation iteration. It requires only C4
regularity and the equation on B2. Exact quadratic rescaling gives constants
independent of centre and radius. The radius-to-infinity argument and exact
quadratic integration give `CHS.theorem_1_3_liouville`; an actual
dimension-one lift preserves n>=1.
`CHS.corollary_1_4_exterior_convexity` closes the exterior-convexity conclusion
in the same dimension range. The older whole-space upper-envelope proof
is retained as an independently proved alternative route.
-/
