import LongTails.Proofs.HsProfile
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.HsProfile

namespace LongTails.Proofs.HsChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rank1 (a : E) : E →L[ℝ] E := (innerSL ℝ a).smulRight a

lemma rank1_apply (a v : E) : rank1 a v = ⟪a, v⟫ • a := by
  simp [rank1]

lemma rank1_inner (a v w : E) : ⟪rank1 a v, w⟫ = ⟪a, v⟫ * ⟪a, w⟫ := by
  rw [rank1_apply, real_inner_smul_left]

section Chain

variable (p : ℕ) (a h : ℝ) {ι : Type*} [Fintype ι] (n : ι → E) (c : ι → ℝ)

noncomputable def lin (i : ι) (u : E) : ℝ := ⟪n i, u⟫ + c i

noncomputable def Cv (u : E) : ℝ := ∑ i, sp0 p a h (lin n c i u)

noncomputable def Cg (u : E) : E := ∑ i, sp1 p a h (lin n c i u) • n i

noncomputable def CH (u : E) : E →L[ℝ] E := ∑ i, sp2 p a h (lin n c i u) • rank1 (n i)

omit [Fintype ι] in
lemma hasFDerivAt_lin (i : ι) (u : E) : HasFDerivAt (lin n c i) (innerSL ℝ (n i)) u := by
  exact ((innerSL ℝ (n i)).hasFDerivAt (x := u)).add_const (c i)

variable {h}

lemma hasFDerivAt_Cv (hh : 0 < h) (u : E) : HasFDerivAt (Cv p a h n c) (innerSL ℝ (Cg p a h n c u)) u := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun u => sp0 p a h (lin n c i u))
      (sp1 p a h (lin n c i u) • innerSL ℝ (n i)) u := fun i _ =>
    (hasDerivAt_sp0 p a hh (lin n c i u)).comp_hasFDerivAt u (hasFDerivAt_lin n c i u)
  have hs := HasFDerivAt.fun_sum hterm
  have e : (∑ i, sp1 p a h (lin n c i u) • innerSL ℝ (n i)) = innerSL ℝ (Cg p a h n c u) := by
    ext v
    simp [Cg]
  exact hs.congr_fderiv e

lemma hasFDerivAt_Cg (u : E) : HasFDerivAt (Cg p a h n c) (CH p a h n c u) u := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun u => sp1 p a h (lin n c i u) • n i)
      ((sp2 p a h (lin n c i u) • innerSL ℝ (n i)).smulRight (n i)) u := fun i _ =>
    ((hasDerivAt_sp1 p a (lin n c i u) (h := h)).comp_hasFDerivAt u (hasFDerivAt_lin n c i u)).smul_const
      (n i)
  have hs := HasFDerivAt.fun_sum hterm
  have e : (∑ i, (sp2 p a h (lin n c i u) • innerSL ℝ (n i)).smulRight (n i)) =
      CH p a h n c u := by
    ext v
    simp [CH, rank1, smul_smul]
  exact hs.congr_fderiv e

lemma CH_inner (u v w : E) :
    ⟪CH p a h n c u v, w⟫ = ∑ i, sp2 p a h (lin n c i u) * (⟪n i, v⟫ * ⟪n i, w⟫) := by
  simp only [CH, sum_apply, smul_apply, sum_inner,
    real_inner_smul_left, rank1_inner]

lemma Cg_inner (u v : E) : ⟪Cg p a h n c u, v⟫ = ∑ i, sp1 p a h (lin n c i u) * ⟪n i, v⟫ := by
  simp only [Cg, sum_inner, real_inner_smul_left]

end Chain

section Instance

variable (p p2 : ℕ) (a h w2 lam κ C0 : ℝ) {ι : Type*} [Fintype ι] (n : ι → E) (c : ι → ℝ)

noncomputable def Rv (u : E) : ℝ := κ / 2 * ‖u‖ ^ 2 - C0

noncomputable def zv (u : E) : ℝ := Rv κ C0 u - Cv p a h n c u

noncomputable def dv (u : E) : E := κ • u - Cg p a h n c u

noncomputable def fv (u : E) : ℝ :=
  lam / 2 * ‖u‖ ^ 2 + Cv p a h n c u + sp0 p2 0 w2 (zv p a h κ C0 n c u)

noncomputable def Fv (u : E) : E :=
  lam • u + Cg p a h n c u + sp1 p2 0 w2 (zv p a h κ C0 n c u) • dv p a h κ n c u

noncomputable def DFv (u : E) : E →L[ℝ] E :=
  lam • ContinuousLinearMap.id ℝ E + CH p a h n c u +
    sp1 p2 0 w2 (zv p a h κ C0 n c u) • (κ • ContinuousLinearMap.id ℝ E - CH p a h n c u) +
    sp2 p2 0 w2 (zv p a h κ C0 n c u) • rank1 (dv p a h κ n c u)

variable {h w2}

lemma hasFDerivAt_normsq (u : E) :
    HasFDerivAt (fun u : E => ‖u‖ ^ 2) (2 • innerSL ℝ u) u :=
  (hasStrictFDerivAt_norm_sq u).hasFDerivAt

lemma hasFDerivAt_Rv (u : E) : HasFDerivAt (Rv κ C0) (innerSL ℝ (κ • u)) u := by
  have h1 := ((hasFDerivAt_normsq u).const_mul (κ / 2)).sub_const C0
  refine h1.congr_fderiv ?_
  ext v
  simp
  ring

lemma hasFDerivAt_zv (hh : 0 < h) (u : E) :
    HasFDerivAt (zv p a h κ C0 n c) (innerSL ℝ (dv p a h κ n c u)) u := by
  have h1 := (hasFDerivAt_Rv κ C0 u).sub (hasFDerivAt_Cv p a n c hh u)
  refine h1.congr_fderiv ?_
  ext v
  simp [dv]

lemma hasFDerivAt_dv (u : E) :
    HasFDerivAt (dv p a h κ n c) (κ • ContinuousLinearMap.id ℝ E - CH p a h n c u) u := by
  exact ((hasFDerivAt_id u).const_smul κ).sub (hasFDerivAt_Cg p a n c u (h := h))

lemma hasFDerivAt_fv (hh : 0 < h) (hw : 0 < w2) (u : E) :
    HasFDerivAt (fv p p2 a h w2 lam κ C0 n c) (innerSL ℝ (Fv p p2 a h w2 lam κ C0 n c u)) u := by
  have h1 := (hasFDerivAt_normsq u).const_mul (lam / 2)
  have h2 := hasFDerivAt_Cv p a n c hh u
  have h3 := (hasDerivAt_sp0 p2 0 hw (zv p a h κ C0 n c u)).comp_hasFDerivAt u
    (hasFDerivAt_zv p a κ C0 n c hh u)
  have hs := (h1.add h2).add h3
  refine hs.congr_fderiv ?_
  ext v
  simp [Fv]
  ring

lemma hasFDerivAt_Fv (hh : 0 < h) (u : E) :
    HasFDerivAt (Fv p p2 a h w2 lam κ C0 n c) (DFv p p2 a h w2 lam κ C0 n c u) u := by
  have h1 := (hasFDerivAt_id (𝕜 := ℝ) u).const_smul lam
  have h2 := hasFDerivAt_Cg p a n c u (h := h)
  have h3 := (hasDerivAt_sp1 p2 0 (zv p a h κ C0 n c u) (h := w2)).comp_hasFDerivAt u
    (hasFDerivAt_zv p a κ C0 n c hh u)
  have h4 := h3.smul (hasFDerivAt_dv p a κ n c u (h := h))
  have hs := (h1.add h2).add h4
  refine hs.congr_fderiv ?_
  ext v
  simp [DFv, rank1, add_assoc, smul_smul]

lemma DFv_inner (u v w : E) :
    ⟪DFv p p2 a h w2 lam κ C0 n c u v, w⟫ =
      lam * ⟪v, w⟫ + ⟪CH p a h n c u v, w⟫ +
        sp1 p2 0 w2 (zv p a h κ C0 n c u) * (κ * ⟪v, w⟫ - ⟪CH p a h n c u v, w⟫) +
        sp2 p2 0 w2 (zv p a h κ C0 n c u) *
          (⟪dv p a h κ n c u, v⟫ * ⟪dv p a h κ n c u, w⟫) := by
  simp only [DFv, add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply, inner_add_left,
    real_inner_smul_left, inner_sub_left, rank1_inner]

lemma DFv_symm (u v w : E) :
    ⟪DFv p p2 a h w2 lam κ C0 n c u v, w⟫ = ⟪v, DFv p p2 a h w2 lam κ C0 n c u w⟫ := by
  rw [real_inner_comm (DFv p p2 a h w2 lam κ C0 n c u w) v, DFv_inner, DFv_inner, CH_inner,
    CH_inner, real_inner_comm w v]
  have e : ∑ i, sp2 p a h (lin n c i u) * (⟪n i, w⟫ * ⟪n i, v⟫) =
      ∑ i, sp2 p a h (lin n c i u) * (⟪n i, v⟫ * ⟪n i, w⟫) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

end Instance

section Convex

variable (p p2 : ℕ) (a h w2 lam κ C0 : ℝ) {ι : Type*} [Fintype ι] (n : ι → E) (c : ι → ℝ)

variable {h w2}

omit [Fintype ι] in
lemma lin_sub (i : ι) (x y : E) : lin n c i y - lin n c i x = ⟪n i, y - x⟫ := by
  simp only [lin, inner_sub_right]; ring

lemma Cv_tangent (hh : 0 < h) (x y : E) :
    Cv p a h n c x + ⟪Cg p a h n c x, y - x⟫ ≤ Cv p a h n c y := by
  rw [Cg_inner]
  unfold Cv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have := sp0_tangent p a hh (lin n c i x) (lin n c i y)
  rw [lin_sub] at this
  exact this

lemma Rv_tangent (hκ : 0 ≤ κ) (x y : E) : Rv κ C0 x + ⟪κ • x, y - x⟫ ≤ Rv κ C0 y := by
  unfold Rv
  have e : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
    have : y = x + (y - x) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real]
  rw [real_inner_smul_left, e]
  nlinarith [sq_nonneg ‖y - x‖, mul_nonneg hκ (sq_nonneg ‖y - x‖)]

lemma fv_tangent (hp2 : 1 ≤ p2) (hh : 0 < h) (hw : 0 < w2) (hκ : 0 ≤ κ)
    (hlam : 0 ≤ lam) (x y : E) :
    fv p p2 a h w2 lam κ C0 n c x + ⟪Fv p p2 a h w2 lam κ C0 n c x, y - x⟫ ≤
      fv p p2 a h w2 lam κ C0 n c y := by
  have hC := Cv_tangent p a n c hh x y
  have hR := Rv_tangent κ C0 hκ x y
  set P := sp1 p2 0 w2 (zv p a h κ C0 n c x) with hP
  have hP0 : 0 ≤ P := sp1_nonneg p2 0 hp2 _
  have hP1 : P ≤ 1 := sp1_le_one p2 0 hp2 _
  have hpsi := sp0_tangent p2 0 hw (zv p a h κ C0 n c x) (zv p a h κ C0 n c y)
  have hridge : lam / 2 * ‖x‖ ^ 2 + lam * ⟪x, y - x⟫ ≤ lam / 2 * ‖y‖ ^ 2 := by
    have e : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
      have : y = x + (y - x) := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq_real]
    rw [e]
    nlinarith [sq_nonneg ‖y - x‖, mul_nonneg hlam (sq_nonneg ‖y - x‖)]
  have hz : P * (zv p a h κ C0 n c y - zv p a h κ C0 n c x) =
      P * (Rv κ C0 y - Rv κ C0 x) - P * (Cv p a h n c y - Cv p a h n c x) := by
    unfold zv; ring
  unfold fv Fv
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  unfold dv
  rw [inner_sub_left, ← hP]
  rw [← hP] at hpsi
  have h1 : P * (Rv κ C0 y - Rv κ C0 x) ≥ P * ⟪κ • x, y - x⟫ :=
    mul_le_mul_of_nonneg_left (by linarith) hP0
  have h2 : (1 - P) * (Cv p a h n c y - Cv p a h n c x) ≥ (1 - P) * ⟪Cg p a h n c x, y - x⟫ :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

lemma Cv_nonneg (hp : 1 ≤ p) (hh : 0 < h) (u : E) : 0 ≤ Cv p a h n c u :=
  Finset.sum_nonneg fun _ _ => sp0_nonneg p a hp hh _

lemma fv_ge (hp : 1 ≤ p) (hp2 : 1 ≤ p2) (hh : 0 < h) (hw : 0 < w2) (u : E) :
    lam / 2 * ‖u‖ ^ 2 ≤ fv p p2 a h w2 lam κ C0 n c u := by
  have h1 := Cv_nonneg p a n c hp hh u
  have h2 := sp0_nonneg p2 0 hp2 hw (zv p a h κ C0 n c u)
  unfold fv
  linarith

lemma continuous_fv (hh : 0 < h) (hw : 0 < w2) : Continuous (fv p p2 a h w2 lam κ C0 n c) :=
  continuous_iff_continuousAt.mpr fun u =>
    (hasFDerivAt_fv p p2 a lam κ C0 n c hh hw u).continuousAt

lemma exists_minimizer [FiniteDimensional ℝ E] (hp : 1 ≤ p) (hp2 : 1 ≤ p2) (hh : 0 < h)
    (hw : 0 < w2) (hlam : 0 < lam) :
    ∃ xs : E, ∀ y, fv p p2 a h w2 lam κ C0 n c xs ≤ fv p p2 a h w2 lam κ C0 n c y := by
  set f := fv p p2 a h w2 lam κ C0 n c
  set ρ := Real.sqrt (2 * f 0 / lam) with hρ
  have hcomp : IsCompact (Metric.closedBall (0 : E) ρ) := isCompact_closedBall 0 ρ
  have hne : (Metric.closedBall (0 : E) ρ).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (Real.sqrt_nonneg _)⟩
  obtain ⟨xs, _, hxs⟩ := hcomp.exists_isMinOn hne (continuous_fv p p2 a lam κ C0 n c hh hw).continuousOn
  refine ⟨xs, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall (0 : E) ρ
  · exact hxs hy
  · have h0 : f xs ≤ f 0 := hxs (Metric.mem_closedBall_self (Real.sqrt_nonneg _))
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    have hf0 : 0 ≤ f 0 := by
      have := fv_ge p p2 a lam κ C0 n c hp hp2 hh hw (0 : E)
      simp at this
      linarith [this]
    have hρ2 : ρ ^ 2 = 2 * f 0 / lam := Real.sq_sqrt (by positivity)
    have hy2 : ρ ^ 2 < ‖y‖ ^ 2 := by
      have := Real.sqrt_nonneg (2 * f 0 / lam)
      nlinarith
    have hfy := fv_ge p p2 a lam κ C0 n c hp hp2 hh hw y
    rw [hρ2] at hy2
    have : f 0 < lam / 2 * ‖y‖ ^ 2 := by
      rw [div_lt_iff₀ hlam] at hy2
      linarith
    linarith

lemma Fv_eq_zero_of_min (hh : 0 < h) (hw : 0 < w2) (xs : E)
    (hmin : ∀ y, fv p p2 a h w2 lam κ C0 n c xs ≤ fv p p2 a h w2 lam κ C0 n c y) :
    Fv p p2 a h w2 lam κ C0 n c xs = 0 := by
  have hloc : IsLocalMin (fv p p2 a h w2 lam κ C0 n c) xs :=
    Filter.Eventually.of_forall hmin
  have h0 := hloc.hasFDerivAt_eq_zero (hasFDerivAt_fv p p2 a lam κ C0 n c hh hw xs)
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L (Fv p p2 a h w2 lam κ C0 n c xs)) h0
  simp only [innerSL_apply_apply, zero_apply] at h1
  exact inner_self_eq_zero.mp h1

end Convex

end LongTails.Proofs.HsChain
