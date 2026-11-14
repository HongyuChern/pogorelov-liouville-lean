import CHS.Analysis.WeakHarnackMean

/-! # Actual extrema and oscillations on compact sets -/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Analysis

variable {X : Type*} [TopologicalSpace X]

def compactSup (f : X → ℝ) (K : Set X) : ℝ := sSup (f '' K)
def compactInf (f : X → ℝ) (K : Set X) : ℝ := sInf (f '' K)
def compactOsc (f : X → ℝ) (K : Set X) : ℝ := compactSup f K - compactInf f K

theorem le_compactSup {K : Set X} (hK : IsCompact K) {f : X → ℝ}
    (hf : ContinuousOn f K) {x : X} (hx : x ∈ K) : f x ≤ compactSup f K :=
  le_csSup (hK.bddAbove_image hf) (mem_image_of_mem _ hx)

theorem compactInf_le {K : Set X} (hK : IsCompact K) {f : X → ℝ}
    (hf : ContinuousOn f K) {x : X} (hx : x ∈ K) : compactInf f K ≤ f x :=
  csInf_le (hK.bddBelow_image hf) (mem_image_of_mem _ hx)

theorem compactSup_attained {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) :
    ∃ x ∈ K, compactSup f K = f x := hK.exists_sSup_image_eq hne hf

theorem compactInf_attained {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) :
    ∃ x ∈ K, compactInf f K = f x := hK.exists_sInf_image_eq hne hf

theorem compactSup_mono {K L : Set X} (hK : IsCompact K) (hL : L.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) (hsub : L ⊆ K) :
    compactSup f L ≤ compactSup f K := by
  apply csSup_le (hL.image f)
  rintro _ ⟨x, hx, rfl⟩
  exact le_compactSup hK hf (hsub hx)

theorem compactInf_mono {K L : Set X} (hK : IsCompact K) (hL : L.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) (hsub : L ⊆ K) :
    compactInf f K ≤ compactInf f L := by
  apply le_csInf (hL.image f)
  rintro _ ⟨x, hx, rfl⟩
  exact compactInf_le hK hf (hsub hx)

theorem compactOsc_nonneg {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) : 0 ≤ compactOsc f K := by
  obtain ⟨x, hx⟩ := hne
  exact sub_nonneg.mpr ((compactInf_le hK hf hx).trans (le_compactSup hK hf hx))

theorem compactOsc_le_of_sub_le {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) {C : ℝ}
    (hbound : ∀ x ∈ K, ∀ y ∈ K, f x - f y ≤ C) : compactOsc f K ≤ C := by
  obtain ⟨x, hx, hmax⟩ := compactSup_attained hK hne hf
  obtain ⟨y, hy, hmin⟩ := compactInf_attained hK hne hf
  simpa only [compactOsc, hmax, hmin] using hbound x hx y hy

theorem abs_sub_le_compactOsc {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    |f x - f y| ≤ compactOsc f K := by
  have hxu := le_compactSup hK hf hx
  have hyu := le_compactSup hK hf hy
  have hxl := compactInf_le hK hf hx
  have hyl := compactInf_le hK hf hy
  dsimp only [compactOsc]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem compactOsc_mono {K L : Set X} (hK : IsCompact K) (hL : L.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) (hsub : L ⊆ K) :
    compactOsc f L ≤ compactOsc f K :=
  sub_le_sub (compactSup_mono hK hL hf hsub) (compactInf_mono hK hL hf hsub)

end CHS.Analysis
