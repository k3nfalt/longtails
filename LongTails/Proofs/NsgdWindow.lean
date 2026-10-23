import LongTails.Proofs.NsgdBounds

namespace LongTails.Proofs.NsgdWindow

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.SeparationInstance LongTails.Proofs.SeparationTrajectory
open LongTails.Proofs.GaussianBlocks LongTails.Proofs.GaussianStep LongTails.Proofs.GaussianFacts
open LongTails.Proofs.NsgdProcess LongTails.Proofs.NsgdBounds LongTails.Proofs.GaussianLinear
open scoped NNReal

section

variable {r : ℕ} {ℓ c s η : ℝ} {φ : FlatShape} {B : ℕ}

local notation "S" => state r ℓ c s η φ B
local notation "ν" => gaussianReal 0 (1 / (B : ℝ≥0))

noncomputable def centered (r : ℕ) (ℓ c s : ℝ) (φ : FlatShape) (B : ℕ) (p : ℝ × ℝ) (z : ℝ) : ℝ :=
  stepAt r ℓ c s φ p z - meanStep r ℓ c s φ B p

noncomputable def dev (j : ℕ) (ξ : ℕ → ℝ) : ℝ := centered r ℓ c s φ B (S ξ j) (blockMean B j ξ)

noncomputable def mart (t n : ℕ) (ξ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + i) ξ

lemma measurable_centered :
    Measurable (Function.uncurry (centered r ℓ c s φ B)) :=
  (measurable_stepAt r ℓ c s φ).sub ((measurable_meanStep r ℓ c s φ B).comp measurable_fst)

lemma abs_centered_le (p : ℝ × ℝ) (z : ℝ) : |centered r ℓ c s φ B p z| ≤ 2 := by
  unfold centered stepAt
  have h1 := abs_step_le (beta r c φ p.2) (drive ℓ s p z)
  have h2 := abs_meanStep_le r ℓ c s φ B p
  have := abs_sub (step (beta r c φ p.2) (drive ℓ s p z)) (meanStep r ℓ c s φ B p)
  linarith

lemma measurable_dev (j : ℕ) :
    Measurable (dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) j) :=
  measurable_centered.comp ((measurable_state r ℓ c s η φ B j).prodMk (measurable_blockMean B j))

lemma abs_dev_le (j : ℕ) (ξ : ℕ → ℝ) :
    |dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) j ξ| ≤ 2 :=
  abs_centered_le _ _

lemma dev_local (j : ℕ) :
    Local (B * (j + 1)) (dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) j) := by
  intro ξ ξ' h
  unfold dev
  have hS : S ξ j = S ξ' j := state_local r ℓ c s η φ B ξ ξ' j (fun k hk =>
    h k (lt_of_lt_of_le hk (Nat.mul_le_mul_left B (Nat.le_succ j))))
  have hm : blockMean B j ξ = blockMean B j ξ' := by
    unfold blockMean
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply h
    have := Finset.mem_range.mp hi
    rw [Nat.mul_succ]
    omega
  rw [hS, hm]

lemma mart_local (t n : ℕ) :
    Local (B * (t + n)) (mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n) := by
  intro ξ ξ' h
  unfold mart
  apply Finset.sum_congr rfl
  intro i hi
  apply dev_local
  intro k hk
  apply h
  have := Finset.mem_range.mp hi
  exact lt_of_lt_of_le hk (Nat.mul_le_mul_left B (by omega))

lemma measurable_mart (t n : ℕ) :
    Measurable (mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n) :=
  Finset.measurable_sum _ fun i _ => measurable_dev (t + i)

lemma abs_mart_le (t n : ℕ) (ξ : ℕ → ℝ) :
    |mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n ξ| ≤ 2 * n := by
  unfold mart
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _i ∈ Finset.range n, (2 : ℝ) := Finset.sum_le_sum fun i _ => abs_dev_le _ _
    _ = 2 * n := by simp; ring

lemma integral_centered_zero (p : ℝ × ℝ) : (∫ z, centered r ℓ c s φ B p z ∂ν) = 0 := by
  unfold centered meanStep
  have hi : Integrable (fun z => stepAt r ℓ c s φ p z) ν :=
    Integrable.of_bound ((measurable_stepAt r ℓ c s φ).comp (measurable_const.prodMk
      measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_step_le _ _)
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

variable (hB : 0 < B)

include hB in
lemma orthogonal {j : ℕ} {G : (ℕ → ℝ) → ℝ} (hloc : Local (B * j) G) (hGm : Measurable G)
    {CG : ℝ} (hGb : ∀ ξ, |G ξ| ≤ CG) :
    (∫ ξ, G ξ * dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) j ξ ∂stdStream) = 0 := by
  have h := condition r ℓ c s η φ hB j hloc hGm hGb (Φ := centered r ℓ c s φ B)
    measurable_centered abs_centered_le
  unfold dev
  rw [h]
  simp only [integral_centered_zero, mul_zero, integral_zero]

lemma mart_succ (t n : ℕ) (ξ : ℕ → ℝ) :
    mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t (n + 1) ξ =
      mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n ξ +
        dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n) ξ := by
  unfold mart
  rw [Finset.sum_range_succ]

lemma integrable_of_bound {F : (ℕ → ℝ) → ℝ} (hF : Measurable F) {C : ℝ} (hb : ∀ ξ, |F ξ| ≤ C) :
    Integrable F stdStream :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs]; exact hb ξ)

include hB in
lemma mart_sq_succ (t n : ℕ) :
    (∫ ξ, mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t (n + 1) ξ ^ 2 ∂stdStream) =
      (∫ ξ, mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n ξ ^ 2 ∂stdStream) +
        ∫ ξ, dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n) ξ ^ 2 ∂stdStream := by
  set M := mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n
  set d := dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n)
  have hM := measurable_mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n
  have hd := measurable_dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n)
  have hMb := abs_mart_le (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n
  have hdb := abs_dev_le (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n)
  have horth := orthogonal (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) hB
    (j := t + n) (mart_local t n) hM hMb
  simp_rw [mart_succ, add_sq]
  have i1 : Integrable (fun ξ => M ξ ^ 2) stdStream :=
    integrable_of_bound (hM.pow_const 2) (C := (2 * n) ^ 2) fun ξ => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hMb ξ) 2
  have i2 : Integrable (fun ξ => 2 * M ξ * d ξ) stdStream :=
    integrable_of_bound ((measurable_const.mul hM).mul hd) (C := 2 * (2 * n) * 2) fun ξ => by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hMb ξ) (by norm_num)) (hdb ξ) (abs_nonneg _)
        (by positivity)
  have i3 : Integrable (fun ξ => d ξ ^ 2) stdStream :=
    integrable_of_bound (hd.pow_const 2) (C := 2 ^ 2) fun ξ => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hdb ξ) 2
  have i12 : Integrable (fun ξ => M ξ ^ 2 + 2 * M ξ * d ξ) stdStream := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2]
  have h2 : (∫ ξ, 2 * M ξ * d ξ ∂stdStream) = 0 := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, horth, mul_zero]
  rw [h2, add_zero]

include hB in
lemma mart_sq_le (t n : ℕ) :
    (∫ ξ, mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n ξ ^ 2 ∂stdStream) ≤
      4 * n := by
  induction n with
  | zero => simp [mart]
  | succ n ih =>
      rw [mart_sq_succ hB]
      have hd : (∫ ξ, dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n) ξ ^ 2
          ∂stdStream) ≤ 4 := by
        calc _ ≤ ∫ _ξ, (4 : ℝ) ∂stdStream := by
              apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
                (integrable_const _)
              exact Filter.Eventually.of_forall fun ξ => by
                have := abs_dev_le (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B)
                  (t + n) ξ
                dsimp only
                rw [← sq_abs]; nlinarith [abs_nonneg (dev (r := r) (ℓ := ℓ) (c := c) (s := s)
                  (η := η) (φ := φ) (B := B) (t + n) ξ)]
          _ = 4 := by simp
      push_cast
      linarith

include hB in
lemma mart_fourth_le (t n : ℕ) :
    (∫ ξ, mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n ξ ^ 4 ∂stdStream) ≤
      112 * n ^ 2 := by
  induction n with
  | zero => simp [mart]
  | succ n ih =>
      set M := mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n
      set d := dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n)
      have hM := measurable_mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n
      have hd := measurable_dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n)
      have hMb := abs_mart_le (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) t n
      have hdb := abs_dev_le (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) (t + n)
      have horth := orthogonal (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) hB
        (j := t + n) (G := fun ξ => M ξ ^ 3)
        (fun ξ ξ' h => by
          show M ξ ^ 3 = M ξ' ^ 3
          rw [show M ξ = M ξ' from mart_local (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η)
            (φ := φ) t n ξ ξ' h]) (hM.pow_const 3)
        (CG := (2 * n) ^ 3) (fun ξ => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hMb ξ) 3)
      have hpt (ξ : ℕ → ℝ) : (M ξ + d ξ) ^ 4 ≤
          M ξ ^ 4 + 4 * (M ξ ^ 3 * d ξ) + 24 * M ξ ^ 2 + 16 * (M ξ ^ 2 + 1) + 16 := by
        have hd2 : d ξ ^ 2 ≤ 4 := by
          have := hdb ξ; rw [← sq_abs]; nlinarith [abs_nonneg (d ξ)]
        have h3 : 4 * M ξ * d ξ ^ 3 ≤ 16 * (M ξ ^ 2 + 1) := by
          have hab : |4 * M ξ * d ξ ^ 3| ≤ 32 * |M ξ| := by
            rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
            have : |d ξ| ^ 3 ≤ 8 := by
              have := hdb ξ
              calc |d ξ| ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (abs_nonneg _) this 3
                _ = 8 := by norm_num
            nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg (M ξ))]
          have : 32 * |M ξ| ≤ 16 * (M ξ ^ 2 + 1) := by
            nlinarith [sq_nonneg (|M ξ| - 1), sq_abs (M ξ)]
          linarith [le_abs_self (4 * M ξ * d ξ ^ 3)]
        have h4 : d ξ ^ 4 ≤ 16 := by nlinarith [sq_nonneg (d ξ)]
        have h2 : 6 * M ξ ^ 2 * d ξ ^ 2 ≤ 24 * M ξ ^ 2 := by nlinarith [sq_nonneg (M ξ)]
        nlinarith
      have iM4 : Integrable (fun ξ => M ξ ^ 4) stdStream :=
        integrable_of_bound (hM.pow_const 4) (C := (2 * n) ^ 4) fun ξ => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hMb ξ) 4
      have iM3d : Integrable (fun ξ => M ξ ^ 3 * d ξ) stdStream :=
        integrable_of_bound ((hM.pow_const 3).mul hd) (C := (2 * n) ^ 3 * 2) fun ξ => by
          rw [abs_mul, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hMb ξ) 3) (hdb ξ) (abs_nonneg _)
            (by positivity)
      have iM2 : Integrable (fun ξ => M ξ ^ 2) stdStream :=
        integrable_of_bound (hM.pow_const 2) (C := (2 * n) ^ 2) fun ξ => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hMb ξ) 2
      have iL : Integrable (fun ξ => (M ξ + d ξ) ^ 4) stdStream :=
        integrable_of_bound ((hM.add hd).pow_const 4) (C := (2 * n + 2) ^ 4) fun ξ => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (add_le_add (hMb ξ) (hdb ξ))) 4
      have iR : Integrable (fun ξ => M ξ ^ 4 + 4 * (M ξ ^ 3 * d ξ) + 24 * M ξ ^ 2 +
          16 * (M ξ ^ 2 + 1) + 16) stdStream :=
        ((((iM4.add (iM3d.const_mul 4)).add (iM2.const_mul 24)).add
          ((iM2.add (integrable_const 1)).const_mul 16)).add (integrable_const 16))
      have hmono := integral_mono iL iR hpt
      simp_rw [mart_succ]
      change (∫ ξ, (M ξ + d ξ) ^ 4 ∂stdStream) ≤ _
      refine hmono.trans ?_
      have iA : Integrable (fun ξ => M ξ ^ 4 + 4 * (M ξ ^ 3 * d ξ)) stdStream :=
        iM4.add (iM3d.const_mul 4)
      have iB : Integrable (fun ξ => M ξ ^ 4 + 4 * (M ξ ^ 3 * d ξ) + 24 * M ξ ^ 2) stdStream :=
        iA.add (iM2.const_mul 24)
      have iC : Integrable (fun ξ => 16 * (M ξ ^ 2 + 1)) stdStream :=
        (iM2.add (integrable_const 1)).const_mul 16
      have iD : Integrable (fun ξ => M ξ ^ 4 + 4 * (M ξ ^ 3 * d ξ) + 24 * M ξ ^ 2 +
          16 * (M ξ ^ 2 + 1)) stdStream := iB.add iC
      rw [integral_add iD (integrable_const 16), integral_add iB iC,
        integral_add iA (iM2.const_mul 24), integral_add iM4 (iM3d.const_mul 4), integral_const_mul,
        integral_const_mul, integral_const_mul, integral_add iM2 (integrable_const 1)]
      have hz : (∫ ξ, M ξ ^ 3 * d ξ ∂stdStream) = 0 := horth
      rw [hz]
      have hsq := mart_sq_le (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) hB t n
      simp only [integral_const, probReal_univ, one_smul] at *
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]

variable (hs : 0 < s) (hc : 0 ≤ c) (hℓ : 0 ≤ ℓ)
  (hb : Real.sqrt (r - 1 : ℕ) * c ≤ Real.sqrt (s ^ 2 / B) / 4)

include hB hs hc hb hℓ in
lemma dev_sq_lower (j : ℕ) (hη : 0 ≤ η) :
    2 / 5 - 4 / 5 * ℓ / Real.sqrt (s ^ 2 / B) * (∫ ξ, |(S ξ j).1| ∂stdStream) ≤
      ∫ ξ, dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) j ξ ^ 2 ∂stdStream := by
  have hσ : 0 < Real.sqrt (s ^ 2 / B) := by
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) < B := by exact_mod_cast hB
    positivity
  have hcond := condition r ℓ c s η φ hB j (G := fun _ => 1) (fun _ _ _ => rfl)
    measurable_const (CG := 1) (fun _ => by simp)
    (Φ := fun p z => centered r ℓ c s φ B p z ^ 2) (measurable_centered.pow_const 2) (CΦ := 4)
    (fun p z => by
      rw [abs_pow]
      have := abs_centered_le (r := r) (ℓ := ℓ) (c := c) (s := s) (φ := φ) (B := B) p z
      nlinarith [abs_nonneg (centered r ℓ c s φ B p z)])
  simp only [one_mul] at hcond
  have hinner (p : ℝ × ℝ) : 2 / 5 - 4 / 5 * ℓ / Real.sqrt (s ^ 2 / B) * |p.1| ≤
      ∫ z, centered r ℓ c s φ B p z ^ 2 ∂ν := by
    have hm := (moments_at (r := r) (ℓ := ℓ) (c := c) (s := s) (φ := φ) (B := B) hB hs hc hb p).1
    have hmean := meanStep_bound (r := r) (c := c) (φ := φ) hB hs p (ℓ := ℓ)
    have hmean1 := abs_meanStep_le r ℓ c s φ B p
    have hi : Integrable (fun z => stepAt r ℓ c s φ p z) ν :=
      Integrable.of_bound ((measurable_stepAt r ℓ c s φ).comp (measurable_const.prodMk
        measurable_id)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_step_le _ _)
    have hi2 : Integrable (fun z => stepAt r ℓ c s φ p z ^ 2) ν :=
      Integrable.of_bound (((measurable_stepAt r ℓ c s φ).comp (measurable_const.prodMk
        measurable_id)).pow_const 2).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_pow]
          have : |stepAt r ℓ c s φ p z| ≤ 1 := abs_step_le _ _
          nlinarith [abs_nonneg (stepAt r ℓ c s φ p z)])
    have hexp : (∫ z, centered r ℓ c s φ B p z ^ 2 ∂ν) =
        (∫ z, stepAt r ℓ c s φ p z ^ 2 ∂ν) - meanStep r ℓ c s φ B p ^ 2 := by
      unfold centered
      simp_rw [sub_sq]
      have hA : Integrable (fun z => 2 * stepAt r ℓ c s φ p z * meanStep r ℓ c s φ B p) ν :=
        (hi.const_mul 2).mul_const _
      have hAB : Integrable (fun z => stepAt r ℓ c s φ p z ^ 2 -
          2 * stepAt r ℓ c s φ p z * meanStep r ℓ c s φ B p) ν := hi2.sub hA
      rw [integral_add hAB (integrable_const _), integral_sub hi2 hA, integral_mul_const,
        integral_const_mul, integral_const, probReal_univ, one_smul]
      unfold meanStep
      ring
    rw [hexp]
    have hsq : meanStep r ℓ c s φ B p ^ 2 ≤ |meanStep r ℓ c s φ B p| := by
      rw [← sq_abs]; nlinarith [abs_nonneg (meanStep r ℓ c s φ B p)]
    rw [abs_mul, abs_of_nonneg hℓ] at hmean
    have : 4 / 5 * (ℓ * |p.1|) / Real.sqrt (s ^ 2 / B) = 4 / 5 * ℓ / Real.sqrt (s ^ 2 / B) * |p.1| := by
      ring
    linarith
  change _ ≤ ∫ ξ, centered r ℓ c s φ B (S ξ j) (blockMean B j ξ) ^ 2 ∂stdStream
  rw [hcond]
  have hxi := integrable_state_abs (r := r) (ℓ := ℓ) (c := c) (s := s) (φ := φ) (B := B) hη j
  calc 2 / 5 - 4 / 5 * ℓ / Real.sqrt (s ^ 2 / B) * (∫ ξ, |(S ξ j).1| ∂stdStream) =
        ∫ ξ, (2 / 5 - 4 / 5 * ℓ / Real.sqrt (s ^ 2 / B) * |(S ξ j).1|) ∂stdStream := by
          rw [integral_sub (integrable_const _) (hxi.const_mul _), integral_const_mul,
            integral_const, probReal_univ, one_smul]
    _ ≤ _ := by
          apply integral_mono ((integrable_const _).sub (hxi.const_mul _))
          · apply Integrable.of_bound _ 4
            · exact Filter.Eventually.of_forall fun ξ => by
                rw [Real.norm_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
                calc _ ≤ ∫ _z, (4 : ℝ) ∂ν := by
                      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
                        (integrable_const _)
                      exact Filter.Eventually.of_forall fun z => by
                        have := abs_centered_le (r := r) (ℓ := ℓ) (c := c) (s := s) (φ := φ)
                          (B := B) (S ξ j) z
                        dsimp only
                        rw [← sq_abs]; nlinarith [abs_nonneg (centered r ℓ c s φ B (S ξ j) z)]
                  _ = 4 := by simp
            · exact (((measurable_centered.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable).comp
                (measurable_state r ℓ c s η φ B j)).aestronglyMeasurable
          · intro ξ; exact hinner _

lemma window_identity (t k : ℕ) (ξ : ℕ → ℝ) :
    (S ξ (t + k)).1 = (S ξ t).1 - η * (mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ)
      (B := B) t k ξ + ∑ i ∈ Finset.range k, meanStep r ℓ c s φ B (S ξ (t + i))) := by
  induction k with
  | zero => simp [mart]
  | succ k ih =>
      rw [← add_assoc, state_x_succ, ih, mart_succ, Finset.sum_range_succ]
      unfold dev centered
      ring

end

end LongTails.Proofs.NsgdWindow
