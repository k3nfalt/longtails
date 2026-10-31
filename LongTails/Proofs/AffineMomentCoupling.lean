import LongTails.Proofs.AffineMomentConcentration
import LongTails.Proofs.AffineMomentPrimal
import LongTails.Proofs.AffineMomentParameters

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentAcceleratedGeometry

namespace LongTails.Proofs.AffineMomentCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma coupling_support {f : E → ℝ} {g : E → E} {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a)
    (hs : ∀ x y, f x + inner ℝ (g x) (y - x) ≤ f y) (x z u : E) :
    (A + a) * (f (couplingPoint A a x z) - f u) ≤ A * (f x - f u) +
      a * inner ℝ (g (couplingPoint A a x z)) (z - u) := by
  have hB : 0 < A + a := by positivity
  have hτ : 0 < a / (A + a) := div_pos ha hB
  have hτ1 : a / (A + a) ≤ 1 := (div_le_one hB).mpr (by linarith)
  have ht := OracleTemplate.AcceleratedCoordinate.convex_coupling
    (μ := 0) (τ := a / (A + a)) (η := a) (by norm_num) hτ hτ1 ha.le
    (fun x y => by simpa using hs x y) x z u
  have he : a / (a / (A + a)) = A + a := by field_simp
  have he' : a * (1 - a / (A + a)) / (a / (A + a)) = A := by
    field_simp
    ring
  simpa only [couplingPoint, he, he', mul_zero, zero_div, zero_mul, sub_zero] using ht

lemma point_radius {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    (k : ℕ) (s : E × E) (hx : ‖s.1‖ ≤ 4) (hz : ‖s.2‖ ≤ 1) : ‖point t k s‖ ≤ 4 := by
  have hA := LongTails.Proofs.AffineMomentParameters.accumulatedWeight_nonneg ht k
  have ha := LongTails.Proofs.AffineMomentParameters.weight_pos ht k
  have hB : 0 < accumulatedWeight t k + weight t k := by positivity
  have hτ : 0 ≤ weight t k / (accumulatedWeight t k + weight t k) := by positivity
  have hτ1 : weight t k / (accumulatedWeight t k + weight t k) ≤ 1 :=
    (div_le_one hB).mpr (by linarith)
  unfold point couplingPoint
  calc
    _ ≤ ‖(weight t k / (accumulatedWeight t k + weight t k)) • s.2‖ +
        ‖(1 - weight t k / (accumulatedWeight t k + weight t k)) • s.1‖ := norm_add_le _ _
    _ ≤ 4 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hτ, abs_of_nonneg (sub_nonneg.mpr hτ1)]
      have h1 := mul_le_mul_of_nonneg_left hz hτ
      have h2 := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hτ1)
      nlinarith

lemma advance_radius {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    (k : ℕ) (s : E × E) (hx : ‖s.1‖ ≤ 4) (hz : ‖s.2‖ ≤ 1) (h G : E) :
    ‖(advance t k s h G).1‖ ≤ 4 ∧ ‖(advance t k s h G).2‖ ≤ 1 := by
  exact ⟨LongTails.Proofs.AffineMomentPrimal.primal_radius _ _ (point_radius ht k s hx hz),
    OracleTemplate.norm_clip_le (by norm_num) _⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma coupled_energy_mgf {p A a fx fy fw fu b ν : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (u v q : E) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hs : (A + a) * (fy - fu) ≤ A * (fx - fu) + a * inner ℝ q (v - u))
    (hd : (A + a) * (fw - fy) ≤ -(A + a) * ‖q‖ ^ 2 / 1024 + (A + a) * ν ^ 2)
    (habs : 20 * a ^ p * (‖q‖ ^ p + ν ^ p) + (A + a) * ν ^ 2 ≤ (A + a) * ‖q‖ ^ 2 / 1024 + b)
    {G : Ω → E} (hG : Measurable G) (hGi : Integrable G P)
    (hGp : Integrable (fun ω => ‖G ω‖ ^ p) P)
    (hmean : (∫ ω, G ω ∂P) = q) (hm : (∫ ω, ‖G ω‖ ^ p ∂P) ≤ 4 * (‖q‖ ^ p + ν ^ p)) :
    Integrable (fun ω => Real.exp (((A + a) * (fw - fu) + energy u (mirrorStep a v (G ω)) -
      (A * (fx - fu) + energy u v) - b) / 4)) P ∧
    (∫ ω, Real.exp (((A + a) * (fw - fu) + energy u (mirrorStep a v (G ω)) -
      (A * (fx - fu) + energy u v) - b) / 4) ∂P) ≤ 1 := by
  let M := ∫ ω, energy u (mirrorStep a v (G ω)) ∂P
  let C := (A + a) * (fw - fu) + M - (A * (fx - fu) + energy u v) - b
  have hmeanD := LongTails.Proofs.AffineMomentConcentration.mirror_mean_energy hp hp2 ha u v hu hv hG hGi hGp hm
  rw [hmean] at hmeanD
  have hC : C / 4 + a ^ p * (‖q‖ ^ p + ν ^ p) ≤ 0 := by
    dsimp [C, M]
    nlinarith only [hs, hd, hmeanD, habs]
  have hmgf := LongTails.Proofs.AffineMomentConcentration.mirror_centered_mgf hp hp2 ha
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    u v hu hv hG hGp hm
  have he (ω : Ω) :
      Real.exp (((A + a) * (fw - fu) + energy u (mirrorStep a v (G ω)) -
        (A * (fx - fu) + energy u v) - b) / 4) =
      Real.exp (C / 4) * Real.exp ((1 / 4) * (energy u (mirrorStep a v (G ω)) - M)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [C]
    ring
  simp_rw [he]
  refine ⟨hmgf.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ Real.exp (C / 4) * Real.exp (4 * (1 / 4) ^ 2 * a ^ p * (4 * (‖q‖ ^ p + ν ^ p))) :=
      mul_le_mul_of_nonneg_left hmgf.2 (Real.exp_nonneg _)
    _ = Real.exp (C / 4 + a ^ p * (‖q‖ ^ p + ν ^ p)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr hC

set_option maxHeartbeats 1000000 in
lemma advance_energy_mgf {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    {f : E → ℝ} {g : E → E} (u : E) (hu : ‖u‖ ≤ 1)
    (hs : ∀ x y, f x + inner ℝ (g x) (y - x) ≤ f y)
    (hsm : ∀ x y, f y ≤ f x + inner ℝ (g x) (y - x) + (1 / 2) * ‖y - x‖ ^ 2)
    (hmin : ∀ x, f u ≤ f x) (hzero : g u = 0)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖)
    (k : ℕ) (hk : k < iterations t) (s : E × E) (hx : ‖s.1‖ ≤ 4) (hz : ‖s.2‖ ≤ 1)
    (h : E) (hh : ‖h - g (point t k s)‖ ≤ ‖g (point t k s)‖ / 8 + pilotRadius t)
    {G : Ω → E} (hG : Measurable G) (hGi : Integrable G P)
    (hGp : Integrable (fun ω => ‖G ω‖ ^ t.p) P)
    (hmean : (∫ ω, G ω ∂P) = g (point t k s))
    (hm : (∫ ω, ‖G ω‖ ^ t.p ∂P) ≤ 4 * (‖g (point t k s)‖ ^ t.p + pilotRadius t ^ t.p)) :
    Integrable (fun ω => Real.exp ((accumulatedWeight t (k + 1) *
      (f (advance t k s h (G ω)).1 - f u) + energy u (advance t k s h (G ω)).2 -
      (accumulatedWeight t k * (f s.1 - f u) + energy u s.2) -
      1 / (iterations t : ℝ)) / 4)) P ∧
    (∫ ω, Real.exp ((accumulatedWeight t (k + 1) *
      (f (advance t k s h (G ω)).1 - f u) + energy u (advance t k s h (G ω)).2 -
      (accumulatedWeight t k * (f s.1 - f u) + energy u s.2) -
      1 / (iterations t : ℝ)) / 4) ∂P) ≤ 1 := by
  have hy := point_radius ht k s hx hz
  have hq : ‖g (point t k s)‖ ≤ 5 := by
    have hl := hlip (point t k s) u
    rw [hzero, sub_zero] at hl
    exact hl.trans ((norm_sub_le _ _).trans (by linarith))
  have hd := LongTails.Proofs.AffineMomentPrimal.mixed_primal_descent (point t k s) u
    (g (point t k s)) h hy hu hq
    (AffineMomentParameters.pilotRadius_pos ht).le (AffineMomentParameters.pilotRadius_le_one ht) hh (hs _ _) (hmin _) (hsm _ _)
  have hA := LongTails.Proofs.AffineMomentParameters.accumulatedWeight_nonneg ht k
  have ha := LongTails.Proofs.AffineMomentParameters.weight_pos ht k
  have hdw := mul_le_mul_of_nonneg_left hd (show 0 ≤ accumulatedWeight t k + weight t k by positivity)
  have habsQ := LongTails.Proofs.AffineMomentParameters.weight_energy_absorption ht k
    (norm_nonneg (g (point t k s)))
  have habsν := AffineMomentParameters.weight_additive_absorption ht hk
  have hhalf : 1 / (2 * (iterations t : ℝ)) + 1 / (2 * (iterations t : ℝ)) =
      1 / (iterations t : ℝ) := by ring
  have habs : 20 * weight t k ^ t.p *
      (‖g (point t k s)‖ ^ t.p + pilotRadius t ^ t.p) +
      accumulatedWeight t (k + 1) * pilotRadius t ^ 2 ≤
      accumulatedWeight t (k + 1) * ‖g (point t k s)‖ ^ 2 / 1024 +
      1 / (iterations t : ℝ) := by nlinarith only [habsQ, habsν, hhalf]
  rw [LongTails.Proofs.AffineMomentParameters.accumulatedWeight_succ] at habs ⊢
  exact coupled_energy_mgf (p := t.p) (A := accumulatedWeight t k) (a := weight t k)
    (fx := f s.1) (fy := f (point t k s)) (fw := f (primalStep (point t k s) h))
    (fu := f u) (ν := pilotRadius t) (b := 1 / (iterations t : ℝ))
    (le_of_lt ht.exponent_gt) ht.exponent_le ha.le u s.2
    (g (point t k s)) hu hz (coupling_support hA ha hs s.1 s.2 u)
    (by nlinarith only [hdw]) habs hG hGi hGp hmean hm

end LongTails.Proofs.AffineMomentCoupling
