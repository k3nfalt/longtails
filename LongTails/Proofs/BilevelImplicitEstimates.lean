import LongTails.Proofs.BilevelCurvature
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option maxSynthPendingDepth 3

namespace LongTails.Proofs.BilevelImplicitEstimates
open scoped RealInnerProductSpace

lemma third_swap_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b a c := by
  have hd : ContDiff ℝ 2 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  exact DFunLike.congr_fun (hd.contDiffAt.isSymmSndFDerivAt (by norm_num) |>.eq a b) c

lemma third_swap_last {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x a b c : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a c b := by
  have hd : ContDiff ℝ 2 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  have hdd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) :=
    (contDiff_succ_iff_fderiv.mp hd).2.2
  have hl : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a |>.const_add x
  have h := ((hdd.differentiable (by norm_num) (x + (0 : ℝ) • a)).hasFDerivAt).comp_hasDerivAt 0 hl
  have hbc := (h.clm_apply (hasDerivAt_const (0 : ℝ) b)).clm_apply
    (hasDerivAt_const (0 : ℝ) c)
  have hcb := (h.clm_apply (hasDerivAt_const (0 : ℝ) c)).clm_apply
    (hasDerivAt_const (0 : ℝ) b)
  have he : (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • a) b c) =
      (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • a) c b) := by
    funext t
    exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) |>.eq b c
  simp only [Function.comp_def, zero_smul, add_zero, map_zero] at hbc hcb
  rw [he] at hbc
  exact hbc.unique hcb

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]


lemma scaled_response_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (P : Seminorm ℝ E) {L μ q : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hq : 0 ≤ q) (he : μ * q ^ 2 = L)
    (hP : ∀ v, L * (P v) ^ 2 = ⟪H v, v⟫)
    {v : E} (hn : μ * ‖v‖ ≤ L) (hv : μ * ⟪H v, v⟫ ≤ L ^ 2) :
    ‖v‖ ≤ q ^ 2 ∧ P v ≤ q := by
  have hn' : ‖v‖ ≤ q ^ 2 := by nlinarith
  have hP0 : 0 ≤ P v := apply_nonneg P v
  rw [← hP] at hv
  have hv' : μ * (P v) ^ 2 ≤ L := by nlinarith
  have hs : (P v) ^ 2 ≤ q ^ 2 := by nlinarith
  exact ⟨hn', (sq_le_sq₀ hP0 hq).mp hs⟩

lemma scaled_coercivity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (P : Seminorm ℝ E) {L μ q : ℝ}
    (hμ : 0 < μ) (hq : 0 ≤ q) (he : μ * q ^ 2 = L)
    (hP : ∀ v, L * (P v) ^ 2 = ⟪H v, v⟫)
    (hc : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪H v, v⟫) (v : E) : ‖v‖ ≤ q * P v := by
  have h := hc v
  rw [← hP, ← he] at h
  have hs : ‖v‖ ^ 2 ≤ q ^ 2 * (P v) ^ 2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (apply_nonneg P v))).mp
  simpa only [mul_pow] using hs

lemma implicit_second_energy
    (T : (X × Y) →L[ℝ] (X × Y) →L[ℝ] (X × Y) →L[ℝ] ℝ)
    (P : Seminorm ℝ Y) {q : ℝ} (hq : 1 ≤ q)
    (hbound : ∀ w a b, |T w a b| ≤ ‖w‖ * ‖a‖ * ‖b‖)
    (hsym : ∀ w a b, T w a b = T a w b)
    (hsym2 : ∀ w a b, T w a b = T w b a)
    (hmix : ∀ w u v, |T w (0, u) (0, v)| ≤
      2 * ‖w‖ * (‖u‖ * P v + ‖v‖ * P u))
    {a b : X} {u v z : Y} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ‖u‖ ≤ q ^ 2) (hv : ‖v‖ ≤ q ^ 2) (hPu : P u ≤ q) (hPv : P v ≤ q)
    (hco : ‖z‖ ≤ q * P z)
    (he : (P z) ^ 2 = -T (0, z) (a, u) (b, v)) :
    P z ≤ 16 * q ^ 4 ∧ ‖z‖ ≤ 16 * q ^ 5 := by
  have hq0 : 0 ≤ q := by linarith
  have hPz : 0 ≤ P z := apply_nonneg P z
  have hxx : |T (0, z) (a, 0) (b, 0)| ≤ ‖z‖ := by
    have h := hbound (0, z) (a, 0) (b, 0)
    simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), max_eq_left (norm_nonneg _)] at h
    calc
      _ ≤ ‖z‖ * ‖a‖ * ‖b‖ := h
      _ ≤ ‖z‖ * 1 * 1 := by gcongr
      _ = ‖z‖ := by ring
  have hxy : |T (0, z) (a, 0) (0, v)| ≤ 2 * (‖z‖ * q + q ^ 2 * P z) := by
    rw [hsym (0, z) (a, 0)]
    have h := hmix (a, 0) z v
    simp only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)] at h
    refine h.trans ?_
    calc
      _ ≤ 2 * 1 * (‖z‖ * q + q ^ 2 * P z) := by gcongr
      _ = _ := by ring
  have hyx : |T (0, z) (0, u) (b, 0)| ≤ 2 * (‖z‖ * q + q ^ 2 * P z) := by
    rw [hsym2 (0, z) (0, u), hsym (0, z) (b, 0)]
    have h := hmix (b, 0) z u
    simp only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)] at h
    refine h.trans ?_
    calc
      _ ≤ 2 * 1 * (‖z‖ * q + q ^ 2 * P z) := by gcongr
      _ = _ := by ring
  have hyy : |T (0, z) (0, u) (0, v)| ≤ 4 * ‖z‖ * q ^ 3 := by
    have h := hmix (0, z) u v
    simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] at h
    refine h.trans ?_
    calc
      _ ≤ 2 * ‖z‖ * (q ^ 2 * q + q ^ 2 * q) := by gcongr
      _ = _ := by ring
  have heq : T (0, z) (a, u) (b, v) = T (0, z) (a, 0) (b, 0) +
      T (0, z) (a, 0) (0, v) + T (0, z) (0, u) (b, 0) + T (0, z) (0, u) (0, v) := by
    have hau : (a, u) = (a, 0) + (0, u) := by simp
    have hbv : (b, v) = (b, 0) + (0, v) := by simp
    rw [hau, hbv]
    simp only [map_add, add_apply]
    ring
  have ht : (P z) ^ 2 ≤ ‖z‖ + 4 * (‖z‖ * q + q ^ 2 * P z) + 4 * ‖z‖ * q ^ 3 := by
    rw [he, heq]
    have h1 := (abs_le.mp hxx).1
    have h2 := (abs_le.mp hxy).1
    have h3 := (abs_le.mp hyx).1
    have h4 := (abs_le.mp hyy).1
    linarith
  have ht2 : (P z) ^ 2 ≤ (q + 8 * q ^ 2 + 4 * q ^ 4) * P z := by
    calc
      _ ≤ ‖z‖ + 4 * (‖z‖ * q + q ^ 2 * P z) + 4 * ‖z‖ * q ^ 3 := ht
      _ ≤ q * P z + 4 * (q * P z * q + q ^ 2 * P z) + 4 * (q * P z) * q ^ 3 := by gcongr
      _ = _ := by ring
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1)]
  have hcoef : q + 8 * q ^ 2 + 4 * q ^ 4 ≤ 16 * q ^ 4 := by nlinarith [sq_nonneg (q ^ 2)]
  have hp : P z ≤ 16 * q ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hcoef hPz
    nlinarith
  refine ⟨hp, hco.trans ?_⟩
  calc q * P z ≤ q * (16 * q ^ 4) := mul_le_mul_of_nonneg_left hp hq0
    _ = 16 * q ^ 5 := by ring


lemma implicit_third_transport_term
    (T : (X × Y) →L[ℝ] (X × Y) →L[ℝ] (X × Y) →L[ℝ] ℝ)
    (P : Seminorm ℝ Y) {q : ℝ} (hq : 1 ≤ q)
    (hbound : ∀ w a b, |T w a b| ≤ ‖w‖ * ‖a‖ * ‖b‖)
    (hmix : ∀ w u v, |T w (0, u) (0, v)| ≤
      2 * ‖w‖ * (‖u‖ * P v + ‖v‖ * P u))
    {a : X} {u z s : Y} (ha : ‖a‖ ≤ 1)
    (hu : ‖u‖ ≤ q ^ 2) (hPu : P u ≤ q)
    (hz : ‖z‖ ≤ 16 * q ^ 5) (hPz : P z ≤ 16 * q ^ 4) (hs : ‖s‖ ≤ q ^ 2) :
    |T (0, s) (0, z) (a, u)| ≤ 80 * q ^ 8 := by
  have hq0 : 0 ≤ q := by linarith
  have h1 : |T (0, s) (0, z) (a, 0)| ≤ 16 * q ^ 7 := by
    have h := hbound (0, s) (0, z) (a, 0)
    simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _),
      max_eq_left (norm_nonneg _)] at h
    refine h.trans ?_
    calc
      _ ≤ q ^ 2 * (16 * q ^ 5) * 1 := by gcongr
      _ = _ := by ring
  have h2 : |T (0, s) (0, z) (0, u)| ≤ 64 * q ^ 8 := by
    have h := hmix (0, s) z u
    simp only [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] at h
    refine h.trans ?_
    calc
      _ ≤ 2 * q ^ 2 * (16 * q ^ 5 * q + q ^ 2 * (16 * q ^ 4)) := by gcongr
      _ = _ := by ring
  have he : (a, u) = (a, 0) + (0, u) := by simp
  rw [he, map_add]
  have hpow : q ^ 7 ≤ q ^ 8 := by
    calc q ^ 7 = q ^ 7 * 1 := by ring
      _ ≤ q ^ 7 * q := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = q ^ 8 := by ring
  exact (abs_add_le _ _).trans (by linarith)


lemma inverse_transport_norm {X₁ Y₁ : Type*}
    [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    [NormedAddCommGroup Y₁] [InnerProductSpace ℝ Y₁] [CompleteSpace Y₁]
    (T : (X₁ × Y₁) →L[ℝ] (X₁ × Y₁) →L[ℝ] (X₁ × Y₁) →L[ℝ] ℝ)
    (C : (X₁ × Y₁) →L[ℝ] (X₁ × Y₁) →L[ℝ] Y₁) (R : Y₁ →L[ℝ] Y₁)
    (P : Seminorm ℝ Y₁) {q : ℝ} (hq : 1 ≤ q)
    (hbound : ∀ w a b, |T w a b| ≤ ‖w‖ * ‖a‖ * ‖b‖)
    (hmix : ∀ w u v, |T w (0, u) (0, v)| ≤
      2 * ‖w‖ * (‖u‖ * P v + ‖v‖ * P u))
    (hC : ∀ a b r, ⟪C a b, r⟫ = T (0, r) a b)
    (hR : ∀ a b, ⟪R a, b⟫ = ⟪a, R b⟫) (hRn : ‖R‖ ≤ q ^ 2)
    {a : X₁} {u z : Y₁} (ha : ‖a‖ ≤ 1) (hu : ‖u‖ ≤ q ^ 2) (hPu : P u ≤ q)
    (hz : ‖z‖ ≤ 16 * q ^ 5) (hPz : P z ≤ 16 * q ^ 4) :
    ‖R (C (0, z) (a, u))‖ ≤ 80 * q ^ 8 := by
  have hn : ‖(InnerProductSpace.toDual ℝ Y₁) (R (C (0, z) (a, u)))‖ ≤ 80 * q ^ 8 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro r hr
    change ‖⟪R (C (0, z) (a, u)), r⟫‖ ≤ _
    rw [Real.norm_eq_abs, hR, hC]
    apply implicit_third_transport_term T P hq hbound hmix ha hu hPu hz hPz
    calc ‖R r‖ ≤ ‖R‖ * ‖r‖ := R.le_opNorm r
      _ ≤ q ^ 2 := by simpa [hr] using hRn
  simpa using hn

end LongTails.Proofs.BilevelImplicitEstimates
