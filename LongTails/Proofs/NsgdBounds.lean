import LongTails.Proofs.NsgdProcess
import Mathlib.MeasureTheory.Order.Group.Lattice

namespace LongTails.Proofs.NsgdBounds

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.SeparationInstance LongTails.Proofs.SeparationTrajectory
open LongTails.Proofs.GaussianBlocks LongTails.Proofs.GaussianStep LongTails.Proofs.GaussianFacts
open LongTails.Proofs.NsgdProcess LongTails.Proofs.GaussianLinear
open scoped NNReal

section

variable {r : ℕ} {ℓ c s η : ℝ} {φ : FlatShape} {B : ℕ}

local notation "S" => state r ℓ c s η φ B
local notation "ν" => gaussianReal 0 (1 / (B : ℝ≥0))

noncomputable def stepAt (r : ℕ) (ℓ c s : ℝ) (φ : FlatShape) (p : ℝ × ℝ) (z : ℝ) : ℝ :=
  step (beta r c φ p.2) (drive ℓ s p z)

noncomputable def meanStep (r : ℕ) (ℓ c s : ℝ) (φ : FlatShape) (B : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∫ z, stepAt r ℓ c s φ p z ∂gaussianReal 0 (1 / (B : ℝ≥0))

lemma measurable_stepAt (r : ℕ) (ℓ c s : ℝ) (φ : FlatShape) :
    Measurable (Function.uncurry (stepAt r ℓ c s φ)) := by
  have hslope : Measurable φ.slope := φ.continuous_slope.measurable
  unfold stepAt beta drive
  exact measurable_step₂.comp ((measurable_const.mul ((measurable_const.mul
    (hslope.comp (measurable_fst.snd))).abs)).prodMk
    ((measurable_const.mul measurable_fst.fst).add (measurable_const.mul measurable_snd)))

lemma measurable_meanStep (r : ℕ) (ℓ c s : ℝ) (φ : FlatShape) (B : ℕ) :
    Measurable (meanStep r ℓ c s φ B) :=
  (measurable_stepAt r ℓ c s φ).stronglyMeasurable.integral_prod_right'.measurable

lemma abs_meanStep_le (r : ℕ) (ℓ c s : ℝ) (φ : FlatShape) (B : ℕ) (p : ℝ × ℝ) :
    |meanStep r ℓ c s φ B p| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 (1 / (B : ℝ≥0)))
    (f := stepAt r ℓ c s φ p) (C := 1) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_step_le _ _)
  simpa [Real.norm_eq_abs, meanStep] using h

lemma beta_le (hc : 0 ≤ c) (y : ℝ) : beta r c φ y ≤ Real.sqrt (r - 1 : ℕ) * c := by
  unfold beta
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg hc]
  nlinarith [φ.bounded y, abs_nonneg (φ.slope y)]

lemma beta_nonneg (y : ℝ) : 0 ≤ beta r c φ y := by
  unfold beta; positivity

lemma state_x_succ (ξ : ℕ → ℝ) (t : ℕ) :
    (S ξ (t + 1)).1 = (S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ) := by
  rw [state_succ]; rfl

variable (hB : 0 < B) (hs : 0 < s) (hc : 0 ≤ c)
  (hb : Real.sqrt (r - 1 : ℕ) * c ≤ Real.sqrt (s ^ 2 / B) / 4)

include hB hs hc hb in
lemma moments_at (p : ℝ × ℝ) :
    2 / 5 ≤ (∫ z, stepAt r ℓ c s φ p z ^ 2 ∂ν) ∧ 14 / 25 ≤ ∫ z, |stepAt r ℓ c s φ p z| ∂ν := by
  have hV : (s ^ 2 / B).toNNReal ≠ 0 := by
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
    have : 0 < s ^ 2 / B := by positivity
    simpa using this
  have hsqrt : Real.sqrt ((s ^ 2 / B).toNNReal : ℝ) = Real.sqrt (s ^ 2 / B) := by
    rw [Real.coe_toNNReal _ (by positivity)]
  have hβ : |beta r c φ p.2| ≤ Real.sqrt (r - 1 : ℕ) * c := by
    rw [abs_of_nonneg (beta_nonneg p.2)]; exact beta_le hc p.2
  have hm := gaussian_step_moments _ hV (ℓ * p.1) (beta r c φ p.2) _ hβ (by rwa [hsqrt])
  unfold stepAt drive
  rw [noise_scale hB hs (fun y => step (beta r c φ p.2) (ℓ * p.1 + y) ^ 2)
      (((measurable_step _).comp (by fun_prop)).pow_const 2),
    noise_scale hB hs (fun y => |step (beta r c φ p.2) (ℓ * p.1 + y)|)
      (continuous_abs.measurable.comp ((measurable_step _).comp (by fun_prop)))]
  exact hm

include hB hs in
lemma meanStep_bound (p : ℝ × ℝ) :
    |meanStep r ℓ c s φ B p| ≤ 4 / 5 * |ℓ * p.1| / Real.sqrt (s ^ 2 / B) := by
  have hV : (s ^ 2 / B).toNNReal ≠ 0 := by
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
    have : 0 < s ^ 2 / B := by positivity
    simpa using this
  have hsqrt : Real.sqrt ((s ^ 2 / B).toNNReal : ℝ) = Real.sqrt (s ^ 2 / B) := by
    rw [Real.coe_toNNReal _ (by positivity)]
  have hm := gaussian_step_mean _ hV (beta r c φ p.2) (ℓ * p.1)
  rw [hsqrt] at hm
  unfold meanStep stepAt drive
  rw [noise_scale hB hs (fun y => step (beta r c φ p.2) (ℓ * p.1 + y))
    ((measurable_step _).comp (by fun_prop))]
  exact hm

lemma state_x_abs_le (hη : 0 ≤ η) (ξ : ℕ → ℝ) (t : ℕ) : |(S ξ t).1| ≤ η * t := by
  induction t with
  | zero => simp [state, nsgdScalar]
  | succ t ih =>
      rw [state_x_succ]
      have h1 := abs_step_le (beta r c φ (S ξ t).2) (drive ℓ s (S ξ t) (blockMean B t ξ))
      have h2 : |(S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| ≤
          |(S ξ t).1| + η * |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| := by
        calc _ ≤ |(S ξ t).1| + |η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| := abs_sub _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hη]
      have h3 : η * |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| ≤ η :=
        mul_le_of_le_one_right hη h1
      push_cast
      linarith

lemma integrable_state_abs (hη : 0 ≤ η) (u : ℕ) :
    Integrable (fun ξ => |(S ξ u).1|) stdStream := by
  have hstate := measurable_state r ℓ c s η φ B u
  apply Integrable.of_bound (continuous_abs.measurable.comp hstate.fst).aestronglyMeasurable (η * u)
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_abs]
    exact state_x_abs_le hη ξ u

include hB hs hc hb in
lemma kick (hη : 0 ≤ η) (t : ℕ) :
    η * (14 / 25) ≤ (∫ ξ, |(S ξ t).1| ∂stdStream) + ∫ ξ, |(S ξ (t + 1)).1| ∂stdStream := by
  have hm := measurable_state r ℓ c s η φ B t
  have hcond := condition r ℓ c s η φ hB t (G := fun _ => 1) (fun _ _ _ => rfl)
    measurable_const (CG := 1) (fun _ => by simp)
    (Φ := fun p z => |stepAt r ℓ c s φ p z|) (measurable_stepAt r ℓ c s φ).abs (CΦ := 1)
    (fun p z => by rw [abs_abs]; exact abs_step_le _ _)
  simp only [one_mul] at hcond
  have hstepm : Measurable (fun ξ => |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)|) :=
    ((measurable_stepAt r ℓ c s φ).comp (hm.prodMk (measurable_blockMean B t))).abs
  have hstepi : Integrable (fun ξ => |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)|) stdStream :=
    Integrable.of_bound hstepm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_abs]; exact abs_step_le _ _)
  have hlow : (14 / 25 : ℝ) ≤ ∫ ξ, |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| ∂stdStream := by
    rw [hcond]
    calc (14 / 25 : ℝ) = ∫ _ξ, (14 / 25 : ℝ) ∂stdStream := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _)
        · apply Integrable.of_bound _ 1
          · exact Filter.Eventually.of_forall fun ξ => by
              have h := norm_integral_le_of_norm_le_const (μ := ν)
                (f := fun z => |stepAt r ℓ c s φ (S ξ t) z|) (C := 1)
                (Filter.Eventually.of_forall fun z => by
                  rw [Real.norm_eq_abs, abs_abs]; exact abs_step_le (beta r c φ (S ξ t).2)
                    (drive ℓ s (S ξ t) z))
              simpa [stepAt] using h
          · exact (((measurable_stepAt r ℓ c s φ).abs.stronglyMeasurable.integral_prod_right'.measurable).comp
              hm).aestronglyMeasurable
        · intro ξ
          exact (moments_at hB hs hc hb (S ξ t)).2
  have hpt : ∀ ξ, η * |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| ≤
      |(S ξ t).1| + |(S ξ (t + 1)).1| := by
    intro ξ
    rw [state_x_succ]
    have := abs_sub_abs_le_abs_sub (S ξ t).1 ((S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ))
    have he : (S ξ t).1 - ((S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)) =
        η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ) := by ring
    have h2 := abs_sub (S ξ t).1 ((S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ))
    rw [he, abs_mul, abs_of_nonneg hη] at h2
    have h3 : |(S ξ t).1 - ((S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ))| ≤
        |(S ξ t).1| + |(S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| := by
      have := abs_sub (S ξ t).1 ((S ξ t).1 - η * stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ))
      exact this
    rw [he, abs_mul, abs_of_nonneg hη] at h3
    exact h3
  have hsumi : Integrable (fun ξ => |(S ξ t).1| + |(S ξ (t + 1)).1|) stdStream :=
    (integrable_state_abs hη t).add (integrable_state_abs hη (t + 1))
  have hmono : (∫ ξ, η * |stepAt r ℓ c s φ (S ξ t) (blockMean B t ξ)| ∂stdStream) ≤
      ∫ ξ, (|(S ξ t).1| + |(S ξ (t + 1)).1|) ∂stdStream :=
    integral_mono (hstepi.const_mul η) hsumi hpt
  rw [integral_const_mul, integral_add (integrable_state_abs hη t)
    (integrable_state_abs hη (t + 1))] at hmono
  nlinarith

def Good (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (B : ℕ) (θ : ℝ) (n : ℕ) (ξ : ℕ → ℝ) : Prop :=
  ∀ u ≤ n, (state r ℓ c s η φ B ξ u).2 ≤ θ

open Classical in
noncomputable def goodInd (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (B : ℕ) (θ : ℝ) (n : ℕ)
    (ξ : ℕ → ℝ) : ℝ :=
  if Good r ℓ c s η φ B θ n ξ then 1 else 0

noncomputable def increment (u : ℕ) (ξ : ℕ → ℝ) : ℝ := (S ξ (u + 1)).2 - (S ξ u).2

open Classical in
noncomputable def travel (θ : ℝ) (n : ℕ) (ξ : ℕ → ℝ) : ℝ :=
  ∑ u ∈ Finset.range n, goodInd r ℓ c s η φ B θ u ξ * increment (r := r) (ℓ := ℓ) (c := c)
    (s := s) (η := η) (φ := φ) (B := B) u ξ

lemma good_local (θ : ℝ) (n : ℕ) : Local (B * n) (fun ξ => goodInd r ℓ c s η φ B θ n ξ) := by
  intro ξ ξ' h
  have hS : ∀ u ≤ n, state r ℓ c s η φ B ξ u = state r ℓ c s η φ B ξ' u := by
    intro u hu
    apply state_local
    intro k hk
    exact h k (lt_of_lt_of_le hk (Nat.mul_le_mul_left B hu))
  have hiff : Good r ℓ c s η φ B θ n ξ ↔ Good r ℓ c s η φ B θ n ξ' := by
    unfold Good
    constructor
    · intro hg u hu; rw [← hS u hu]; exact hg u hu
    · intro hg u hu; rw [hS u hu]; exact hg u hu
  unfold goodInd
  dsimp only
  by_cases hg : Good r ℓ c s η φ B θ n ξ
  · rw [ite_eq_left hg, ite_eq_left (hiff.mp hg)]
  · rw [ite_eq_right hg, ite_eq_right (mt hiff.mpr hg)]

lemma measurable_good (θ : ℝ) (n : ℕ) : Measurable (fun ξ => goodInd r ℓ c s η φ B θ n ξ) := by
  classical
  have hset : MeasurableSet {ξ : ℕ → ℝ | Good r ℓ c s η φ B θ n ξ} := by
    have : {ξ : ℕ → ℝ | Good r ℓ c s η φ B θ n ξ} =
        ⋂ u ∈ Finset.range (n + 1), {ξ | (state r ℓ c s η φ B ξ u).2 ≤ θ} := by
      ext ξ
      simp only [Good, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
      constructor
      · intro h u hu; exact h u (by omega)
      · intro h u hu; exact h u (by omega)
    rw [this]
    exact Finset.measurableSet_biInter _ fun u _ =>
      measurableSet_le (measurable_state r ℓ c s η φ B u).snd measurable_const
  have : (fun ξ => goodInd r ℓ c s η φ B θ n ξ) =
      {ξ : ℕ → ℝ | Good r ℓ c s η φ B θ n ξ}.indicator (fun _ => 1) := by
    funext ξ
    by_cases h : Good r ℓ c s η φ B θ n ξ <;> simp [goodInd, h]
  rw [this]
  exact measurable_const.indicator hset

noncomputable def flatStep (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (p : ℝ × ℝ) (z : ℝ) : ℝ :=
  -(η * (c * φ.slope p.2 / Real.sqrt (drive ℓ s p z ^ 2 + beta r c φ p.2 ^ 2)))

lemma increment_eq (u : ℕ) (ξ : ℕ → ℝ) :
    increment (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) u ξ =
      flatStep r ℓ c s η φ (S ξ u) (blockMean B u ξ) := by
  unfold increment flatStep
  rw [state_succ]
  ring

lemma flatStep_bounds {θ : ℝ} (hη : 0 ≤ η) (hc : 0 < c) (hr : 2 ≤ r)
    (hfar : ∀ y ≤ θ, φ.slope y ≤ -(1 / 2)) (p : ℝ × ℝ) (z : ℝ) (hy : p.2 ≤ θ) :
    0 ≤ flatStep r ℓ c s η φ p z ∧
      flatStep r ℓ c s η φ p z ≤ η * c / max |drive ℓ s p z| (Real.sqrt (r - 1 : ℕ) * c / 2) := by
  have hsl := hfar p.2 hy
  have hb1 := φ.bounded p.2
  have hr1 : (1 : ℝ) ≤ (r - 1 : ℕ) := by
    have : 1 ≤ r - 1 := by omega
    exact_mod_cast this
  have hsq1 : 1 ≤ Real.sqrt (r - 1 : ℕ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have hbeta : Real.sqrt (r - 1 : ℕ) * c / 2 ≤ beta r c φ p.2 := by
    unfold beta
    rw [abs_mul, abs_of_pos hc, abs_of_neg (by linarith)]
    have hs0 : 0 ≤ Real.sqrt ((r - 1 : ℕ) : ℝ) * c := mul_nonneg (Real.sqrt_nonneg _) hc.le
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ -φ.slope p.2 by linarith) hs0]
  have hb0 : 0 < Real.sqrt (r - 1 : ℕ) * c / 2 := by positivity
  have hform : flatStep r ℓ c s η φ p z = -(η * (c * φ.slope p.2)) *
      (Real.sqrt (drive ℓ s p z ^ 2 + beta r c φ p.2 ^ 2))⁻¹ := by
    unfold flatStep
    ring
  set N := Real.sqrt (drive ℓ s p z ^ 2 + beta r c φ p.2 ^ 2)
  have hN1 : |drive ℓ s p z| ≤ N := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (beta r c φ p.2)])
  have hN2 : beta r c φ p.2 ≤ N := by
    rw [← Real.sqrt_sq (beta_nonneg p.2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (drive ℓ s p z)])
  have hNpos : 0 < N := hb0.trans_le (hbeta.trans hN2)
  have hmax : max |drive ℓ s p z| (Real.sqrt (r - 1 : ℕ) * c / 2) ≤ N :=
    max_le hN1 (hbeta.trans hN2)
  have hmpos : 0 < max |drive ℓ s p z| (Real.sqrt (r - 1 : ℕ) * c / 2) :=
    lt_max_of_lt_right hb0
  have hηc : 0 ≤ η * c := mul_nonneg hη hc.le
  have hnum0 : 0 ≤ -(η * (c * φ.slope p.2)) := by
    have := mul_nonneg hη (mul_nonneg hc.le (show 0 ≤ -φ.slope p.2 by linarith))
    linarith
  rw [hform]
  constructor
  · exact mul_nonneg hnum0 (inv_nonneg.mpr hNpos.le)
  · have hnum : -(η * (c * φ.slope p.2)) ≤ η * c := by
      have h1 : -(φ.slope p.2) ≤ 1 := by linarith [neg_abs_le (φ.slope p.2), (abs_le.mp hb1).1]
      have := mul_le_mul_of_nonneg_left h1 hηc
      linarith
    calc -(η * (c * φ.slope p.2)) * N⁻¹ ≤ η * c * N⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hNpos.le)
      _ ≤ η * c / max |drive ℓ s p z| (Real.sqrt (r - 1 : ℕ) * c / 2) := by
          rw [← div_eq_mul_inv]
          exact div_le_div_of_nonneg_left hηc hmpos hmax

lemma travel_nonneg {θ : ℝ} (hη : 0 ≤ η) (hc : 0 < c) (hr : 2 ≤ r)
    (hfar : ∀ y ≤ θ, φ.slope y ≤ -(1 / 2)) (ξ : ℕ → ℝ) (u : ℕ) :
    0 ≤ goodInd r ℓ c s η φ B θ u ξ * increment (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η)
      (φ := φ) (B := B) u ξ := by
  classical
  unfold goodInd
  split_ifs with hg
  · rw [one_mul, increment_eq]
    exact (flatStep_bounds hη hc hr hfar _ _ (hg u le_rfl)).1
  · simp

lemma travel_good {θ : ℝ} (n : ℕ) (ξ : ℕ → ℝ) (hg : Good r ℓ c s η φ B θ n ξ) :
    travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ (n + 1) ξ =
      (S ξ (n + 1)).2 := by
  classical
  induction n with
  | zero =>
      simp only [travel, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, goodInd,
        ite_eq_left hg, one_mul, increment]
      simp [state, nsgdScalar]
  | succ n ih =>
      have hg' : Good r ℓ c s η φ B θ n ξ := fun u hu => hg u (by omega)
      rw [travel, Finset.sum_range_succ, ← travel, ih hg']
      simp only [goodInd, ite_eq_left hg, one_mul, increment]
      ring

lemma travel_ge {θ : ℝ} (hη : 0 ≤ η) (hc : 0 < c) (hr : 2 ≤ r)
    (hfar : ∀ y ≤ θ, φ.slope y ≤ -(1 / 2)) (hθ : 0 ≤ θ) (n : ℕ) (ξ : ℕ → ℝ)
    (hn : ¬ Good r ℓ c s η φ B θ n ξ) :
    θ ≤ travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ n ξ := by
  classical
  have hex : ∃ u, θ < (S ξ u).2 := by
    by_contra h
    push Not at h
    exact hn (fun u _ => h u)
  have hu₀ : θ < (S ξ (Nat.find hex)).2 := Nat.find_spec hex
  have hmin : ∀ v < Nat.find hex, (S ξ v).2 ≤ θ := fun v hv => not_lt.mp (Nat.find_min hex hv)
  have hu₀n : Nat.find hex ≤ n := by
    by_contra h
    push Not at h
    exact hn (fun u hu => hmin u (by omega))
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hu₀
    simp [state, nsgdScalar] at hu₀
    linarith
  obtain ⟨v, hv⟩ : ∃ v, Nat.find hex = v + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hgv : Good r ℓ c s η φ B θ v ξ := fun u hu => hmin u (by omega)
  have htv := travel_good (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) v ξ hgv
  have hmono : travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ (v + 1) ξ ≤
      travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ n ξ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun u _ _ => travel_nonneg hη hc hr hfar ξ u)
  rw [hv] at hu₀
  linarith

open Classical in
noncomputable def cutStep (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (θ : ℝ) (p : ℝ × ℝ) (z : ℝ) : ℝ :=
  if p.2 ≤ θ then flatStep r ℓ c s η φ p z else 0

lemma measurable_flatStep (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) :
    Measurable (Function.uncurry (flatStep r ℓ c s η φ)) := by
  have hslope : Measurable φ.slope := φ.continuous_slope.measurable
  unfold flatStep drive beta
  apply Measurable.neg
  apply measurable_const.mul
  apply ((measurable_const.mul (hslope.comp measurable_fst.snd))).div
  apply Measurable.sqrt
  exact (((measurable_const.mul measurable_fst.fst).add (measurable_const.mul measurable_snd)).pow_const
    2).add ((measurable_const.mul ((measurable_const.mul (hslope.comp measurable_fst.snd)).abs)).pow_const 2)

lemma measurable_cutStep (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (θ : ℝ) :
    Measurable (Function.uncurry (cutStep r ℓ c s η φ θ)) := by
  classical
  unfold cutStep
  exact Measurable.ite (measurableSet_le measurable_fst.snd measurable_const)
    (measurable_flatStep r ℓ c s η φ) measurable_const

include hB hs in
lemma travel_expectation {θ : ℝ} (hη : 0 ≤ η) (hc' : 0 < c) (hr : 2 ≤ r)
    (hfar : ∀ y ≤ θ, φ.slope y ≤ -(1 / 2))
    (hb0 : Real.sqrt (r - 1 : ℕ) * c / 2 ≤ Real.sqrt (s ^ 2 / B)) (n : ℕ) :
    Integrable (travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ n)
      stdStream ∧
    (∫ ξ, travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ n ξ ∂stdStream) ≤
      n * (η * c * ((2 + Real.log (Real.sqrt (s ^ 2 / B) / (Real.sqrt (r - 1 : ℕ) * c / 2))) /
        Real.sqrt (s ^ 2 / B))) := by
  classical
  set b₀ := Real.sqrt (r - 1 : ℕ) * c / 2 with hb₀def
  set σ' := Real.sqrt (s ^ 2 / B)
  set J := (2 + Real.log (σ' / b₀)) / σ'
  have hr1 : (1 : ℝ) ≤ (r - 1 : ℕ) := by
    have : 1 ≤ r - 1 := by omega
    exact_mod_cast this
  have hb0pos : 0 < b₀ := by
    have : 0 < Real.sqrt ((r - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hσpos : 0 < σ' := hb0pos.trans_le hb0
  have hJ : 0 ≤ J := by
    have : 0 ≤ Real.log (σ' / b₀) := Real.log_nonneg ((one_le_div hb0pos).mpr hb0)
    exact div_nonneg (by linarith) hσpos.le
  have hcut_bound (p : ℝ × ℝ) (z : ℝ) : |cutStep r ℓ c s η φ θ p z| ≤ η * c / b₀ := by
    unfold cutStep
    split_ifs with hy
    · have h := flatStep_bounds (ℓ := ℓ) (s := s) hη hc' hr hfar p z hy
      rw [abs_of_nonneg h.1]
      exact h.2.trans (div_le_div_of_nonneg_left (mul_nonneg hη hc'.le) hb0pos (le_max_right _ _))
    · simp only [abs_zero]
      exact div_nonneg (mul_nonneg hη hc'.le) hb0pos.le
  have hterm (u : ℕ) : (∫ ξ, goodInd r ℓ c s η φ B θ u ξ * increment (r := r) (ℓ := ℓ) (c := c)
      (s := s) (η := η) (φ := φ) (B := B) u ξ ∂stdStream) ≤ η * c * J := by
    have hrw (ξ : ℕ → ℝ) : goodInd r ℓ c s η φ B θ u ξ * increment (r := r) (ℓ := ℓ) (c := c)
        (s := s) (η := η) (φ := φ) (B := B) u ξ =
        goodInd r ℓ c s η φ B θ u ξ * cutStep r ℓ c s η φ θ (S ξ u) (blockMean B u ξ) := by
      unfold goodInd
      split_ifs with hg
      · rw [increment_eq, cutStep, ite_eq_left (hg u le_rfl)]
      · simp
    simp_rw [hrw]
    rw [condition r ℓ c s η φ hB u (good_local θ u) (measurable_good θ u) (CG := 1)
      (fun ξ => by unfold goodInd; split_ifs <;> simp)
      (measurable_cutStep r ℓ c s η φ θ) hcut_bound]
    have hinner (p : ℝ × ℝ) : (∫ z, cutStep r ℓ c s η φ θ p z ∂gaussianReal 0 (1 / (B : ℝ≥0))) ≤
        η * c * J := by
      unfold cutStep
      split_ifs with hy
      · have hV : (s ^ 2 / B).toNNReal ≠ 0 := by
          have : 0 < s ^ 2 / B := by
            have : (0 : ℝ) < B := by exact_mod_cast hB
            positivity
          simpa using this
        have hsqrt : Real.sqrt ((s ^ 2 / B).toNNReal : ℝ) = σ' := by
          rw [Real.coe_toNNReal _ (by positivity)]
        obtain ⟨hint, hle⟩ := inv_max_integral _ hV (ℓ * p.1) b₀ hb0pos (by rwa [hsqrt])
        rw [hsqrt] at hle
        have hscale := noise_scale hB hs (fun y => 1 / max |ℓ * p.1 + y| b₀)
          (by fun_prop)
        calc (∫ z, flatStep r ℓ c s η φ p z ∂gaussianReal 0 (1 / (B : ℝ≥0))) ≤
              ∫ z, η * c * (1 / max |ℓ * p.1 + s * z| b₀) ∂gaussianReal 0 (1 / (B : ℝ≥0)) := by
                apply integral_mono_of_nonneg
                · exact Filter.Eventually.of_forall fun z =>
                    (flatStep_bounds (ℓ := ℓ) (s := s) hη hc' hr hfar p z hy).1
                · apply Integrable.const_mul
                  apply Integrable.of_bound
                    (by fun_prop : Measurable fun z : ℝ => 1 / max |ℓ * p.1 + s * z| b₀).aestronglyMeasurable
                    (1 / b₀)
                  exact Filter.Eventually.of_forall fun z => by
                    rw [Real.norm_of_nonneg (by positivity)]
                    exact one_div_le_one_div_of_le hb0pos (le_max_right _ _)
                · exact Filter.Eventually.of_forall fun z => by
                    have h := (flatStep_bounds (ℓ := ℓ) (s := s) hη hc' hr hfar p z hy).2
                    simp only [drive] at h
                    dsimp only
                    rw [mul_one_div]
                    exact h
          _ = η * c * ∫ y, 1 / max |ℓ * p.1 + y| b₀ ∂gaussianReal 0 (s ^ 2 / B).toNNReal := by
                rw [integral_const_mul, hscale]
          _ ≤ η * c * J := mul_le_mul_of_nonneg_left hle (mul_nonneg hη hc'.le)
      · simp only [integral_zero]
        exact mul_nonneg (mul_nonneg hη hc'.le) hJ
    calc (∫ ξ, goodInd r ℓ c s η φ B θ u ξ *
          ∫ z, cutStep r ℓ c s η φ θ (S ξ u) z ∂gaussianReal 0 (1 / (B : ℝ≥0)) ∂stdStream) ≤
          ∫ _ξ, η * c * J ∂stdStream := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun ξ => by
                refine mul_nonneg ?_ (integral_nonneg fun z => ?_)
                · unfold goodInd; split_ifs <;> norm_num
                unfold cutStep
                split_ifs with hy
                · exact (flatStep_bounds (ℓ := ℓ) (s := s) hη hc' hr hfar _ z hy).1
                · exact le_rfl
            · exact integrable_const _
            · exact Filter.Eventually.of_forall fun ξ => by
                unfold goodInd
                dsimp only
                split_ifs
                · rw [one_mul]; exact hinner _
                · rw [zero_mul]
                  exact mul_nonneg (mul_nonneg hη hc'.le) hJ
      _ = η * c * J := by simp
  have hint (u : ℕ) : Integrable (fun ξ => goodInd r ℓ c s η φ B θ u ξ * increment (r := r)
      (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) u ξ) stdStream := by
    have hrw (ξ : ℕ → ℝ) : goodInd r ℓ c s η φ B θ u ξ * increment (r := r) (ℓ := ℓ) (c := c)
        (s := s) (η := η) (φ := φ) (B := B) u ξ =
        goodInd r ℓ c s η φ B θ u ξ * cutStep r ℓ c s η φ θ (S ξ u) (blockMean B u ξ) := by
      unfold goodInd
      split_ifs with hg
      · rw [increment_eq, cutStep, ite_eq_left (hg u le_rfl)]
      · simp
    simp_rw [hrw]
    apply Integrable.of_bound ((measurable_good θ u).mul ((measurable_cutStep r ℓ c s η φ θ).comp
      ((measurable_state r ℓ c s η φ B u).prodMk (measurable_blockMean B u)))).aestronglyMeasurable
      (η * c / b₀)
    exact Filter.Eventually.of_forall fun ξ => by
      simp only [Pi.mul_apply, Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs,
        abs_mul]
      have h1 : |goodInd r ℓ c s η φ B θ u ξ| ≤ 1 := by unfold goodInd; split_ifs <;> simp
      have h2 := hcut_bound (S ξ u) (blockMean B u ξ)
      nlinarith [abs_nonneg (goodInd r ℓ c s η φ B θ u ξ), abs_nonneg (cutStep r ℓ c s η φ θ (S ξ u) (blockMean B u ξ))]
  refine ⟨integrable_finsetSum _ (fun u _ => hint u), ?_⟩
  unfold travel
  rw [integral_finsetSum _ (fun u _ => hint u)]
  calc (∑ u ∈ Finset.range n, ∫ ξ, goodInd r ℓ c s η φ B θ u ξ * increment (r := r) (ℓ := ℓ)
        (c := c) (s := s) (η := η) (φ := φ) (B := B) u ξ ∂stdStream) ≤
        ∑ _u ∈ Finset.range n, η * c * J := Finset.sum_le_sum fun u _ => hterm u
    _ = n * (η * c * J) := by simp

end

end LongTails.Proofs.NsgdBounds
