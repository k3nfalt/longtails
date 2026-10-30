import LongTails.Algorithms.CappedProximal
import LongTails.Proofs.CappedProximalSampling

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CappedProximalPotential

open LongTails.Algorithms.CappedProximal
open CappedProximalGeometry

noncomputable def weights (lam : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => weights lam n + nextWeight lam (weights lam n)

lemma weights_bounds {lam : ℝ} (hl : 0 < lam) (n : ℕ) :
    0 ≤ weights lam n ∧ (n : ℝ) ^ 2 / (4 * lam) ≤ weights lam n ∧
      weights lam n ≤ (n : ℝ) ^ 2 / lam := by
  induction n with
  | zero => simp [weights]
  | succ n ih =>
    obtain ⟨hn, hlo, hup⟩ := ih
    have ha := accelerated_weight_properties hl hn
    have hal := accelerated_weight_lower hl hn (Nat.cast_nonneg n) hlo
    have hau := accelerated_weight_upper hl hn (Nat.cast_nonneg n) hup
    change 0 < nextWeight lam (weights lam n) ∧ _ at ha
    change (n + 1 : ℝ) / (2 * lam) ≤ nextWeight lam (weights lam n) at hal
    change nextWeight lam (weights lam n) ≤ (n + 1 : ℝ) / lam at hau
    simp only [weights, Nat.cast_succ]
    refine ⟨add_nonneg hn ha.1.le, ?_, ?_⟩
    · have he : (n : ℝ) ^ 2 / (4 * lam) + (n + 1 : ℝ) / (2 * lam) =
          (n + 1 : ℝ) ^ 2 / (4 * lam) + 1 / (4 * lam) := by
        field_simp
        ring
      have hz : 0 ≤ 1 / (4 * lam) := by positivity
      linarith
    · have he : (n : ℝ) ^ 2 / lam + (n + 1 : ℝ) / lam =
          (n + 1 : ℝ) ^ 2 / lam - n / lam := by ring
      have hz : 0 ≤ (n : ℝ) / lam := by positivity
      linarith

lemma weights_sum_bound {lam : ℝ} (hl : 0 < lam) (T : ℕ) :
    (∑ i ∈ Finset.range T, weights lam (i + 1)) ≤ (T : ℝ) ^ 3 / lam := by
  calc
    _ ≤ ∑ _i ∈ Finset.range T, (T : ℝ) ^ 2 / lam := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : ((i + 1 : ℕ) : ℝ) ≤ T := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      exact (weights_bounds hl (i + 1)).2.2.trans
        (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg (i + 1)) hn 2) hl.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

lemma weights_increment_sum (lam : ℝ) (T : ℕ) :
    (∑ n ∈ Finset.range T, nextWeight lam (weights lam n)) = weights lam T := by
  induction T with
  | zero => simp [weights]
  | succ T ih => rw [Finset.sum_range_succ, ih, weights]

lemma predictor_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {lam : ℝ} (hl : 0 < lam) (state : State E) (hB : 0 ≤ state.weight) :
    (state.weight + nextWeight lam state.weight) • predictor lam state =
      state.weight • state.primal + nextWeight lam state.weight • state.dual := by
  have ha := (accelerated_weight_properties hl hB).1
  change 0 < nextWeight lam state.weight at ha
  have hn : state.weight + nextWeight lam state.weight ≠ 0 := by linarith
  have h1 : (state.weight + nextWeight lam state.weight) *
      (state.weight / (state.weight + nextWeight lam state.weight)) = state.weight := by
    field_simp
  have h2 : (state.weight + nextWeight lam state.weight) *
      (nextWeight lam state.weight / (state.weight + nextWeight lam state.weight)) =
      nextWeight lam state.weight := by field_simp
  dsimp [predictor]
  rw [smul_add, smul_smul, smul_smul, h1, h2]

lemma advance_weight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (state : State E) (z : E) (n : ℕ) (hn : state.weight = weights lam n) :
    (advance lam state z).weight = weights lam (n + 1) := by
  simp only [advance, weights, hn]

lemma advance_primal_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {lam : ℝ} (hl : 0 < lam) (state : State E) (hB : 0 ≤ state.weight) (z : E) :
    (state.weight + nextWeight lam state.weight) • z =
      state.weight • state.primal + nextWeight lam state.weight • (advance lam state z).dual := by
  let a := nextWeight lam state.weight
  let A := state.weight + a
  have ha := (accelerated_weight_properties hl hB).2
  change lam * a ^ 2 = A at ha
  have hc : a * (a * lam) = A := by nlinarith only [ha]
  have hx := predictor_identity hl state hB
  change A • predictor lam state = state.weight • state.primal + a • state.dual at hx
  change A • z = state.weight • state.primal + a •
    (state.dual - (a * lam) • (predictor lam state - z))
  rw [smul_sub, smul_smul, hc, ← add_sub_assoc, ← hx]
  module

lemma weighted_squared_distance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y v z xs : E) {A B a : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hs : A = B + a) (hz : A • z = B • y + a • v) :
    A * ‖z - xs‖ ^ 2 ≤ B * ‖y - xs‖ ^ 2 + a * ‖v - xs‖ ^ 2 := by
  have hsum : B / A + a / A = 1 := by rw [← add_div, ← hs, div_self hA.ne']
  have he : z = (B / A) • y + (a / A) • v := by
    calc
      z = A⁻¹ • (A • z) := by rw [smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
      _ = _ := by rw [hz, smul_add, smul_smul, smul_smul]; simp only [div_eq_mul_inv, mul_comm]
  have hq := squared_convex_combination y v xs
    (div_nonneg hB hA.le) (div_nonneg ha hA.le) hsum
  rw [← he] at hq
  have hn : 0 ≤ (B / A) * (a / A) * ‖y - v‖ ^ 2 := by positivity
  have ht : ‖z - xs‖ ^ 2 ≤ B / A * ‖y - xs‖ ^ 2 + a / A * ‖v - xs‖ ^ 2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_left ht hA.le
  have h1 : A * (B / A) = B := by field_simp
  have h2 : A * (a / A) = a := by field_simp
  simpa only [mul_add, ← mul_assoc, h1, h2] using hm

lemma expected_weighted_distance {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω]
    (y v z : Ω → E) (xs : E) {A B a R : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hs : A = B + a) (hz : ∀ ω, A • z ω = B • y ω + a • v ω)
    (hy : (𝔼 ω, ‖y ω - xs‖ ^ 2) ≤ R) (hv : (𝔼 ω, ‖v ω - xs‖ ^ 2) ≤ R) :
    (𝔼 ω, ‖z ω - xs‖ ^ 2) ≤ R := by
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) =>
    weighted_squared_distance (y ω) (v ω) (z ω) xs hA hB ha hs (hz ω))
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at ht
  have hy' := mul_le_mul_of_nonneg_left hy hB
  have hv' := mul_le_mul_of_nonneg_left hv ha
  rw [hs] at ht
  nlinarith

lemma anchor_distance_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x w xs : E) : ‖x - w‖ ^ 2 ≤ 2 * ‖x - xs‖ ^ 2 + 2 * ‖w - xs‖ ^ 2 := by
  have hn := sq_nonneg ‖(x - xs) + (w - xs)‖
  rw [norm_add_sq_real] at hn
  rw [show x - w = (x - xs) - (w - xs) by abel,
    norm_sub_sq_real (x - xs) (w - xs)]
  nlinarith

noncomputable def potential {E : Type*} [NormedAddCommGroup E]
    (F : E → ℝ) (xs : E) (state : State E) : ℝ :=
  state.weight * (F state.primal - F xs) + ‖state.dual - xs‖ ^ 2 / 2

lemma dual_distance_le_potential {E : Type*} [NormedAddCommGroup E]
    (F : E → ℝ) (xs : E) (state : State E) (hw : 0 ≤ state.weight)
    (hgap : F xs ≤ F state.primal) : ‖state.dual - xs‖ ^ 2 ≤ 2 * potential F xs state := by
  have hn := mul_nonneg hw (sub_nonneg.mpr hgap)
  dsimp [potential]
  linarith

lemma expected_advance_potential {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω] [Nonempty Ω]
    (F : E → ℝ) (xs : E) (state : State E) (z : Ω → E)
    {lam noise : ℝ} (hl : 0 < lam) (hB : 0 ≤ state.weight)
    (hc : ∀ v, (𝔼 ω, (F (z ω) - F v)) ≤
      (𝔼 ω, ⟪lam • (predictor lam state - z ω), z ω - v⟫) +
      lam / 8 * (𝔼 ω, ‖predictor lam state - z ω‖ ^ 2) + noise) :
    (𝔼 ω, potential F xs (advance lam state (z ω))) ≤
      potential F xs state + (state.weight + nextWeight lam state.weight) * noise := by
  let a := nextWeight lam state.weight
  let A := state.weight + a
  let x := predictor lam state
  let D := (𝔼 ω, ‖x - z ω‖ ^ 2)
  have ha := accelerated_weight_properties hl hB
  change 0 < a ∧ lam * a ^ 2 = A at ha
  have hA : 0 ≤ A := add_nonneg hB ha.1.le
  have hD : 0 ≤ D := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hnorm : (𝔼 ω, ‖lam • (x - z ω)‖ ^ 2) = lam ^ 2 * D := by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Finset.mul_expect]
    rfl
  have ht := CappedProximalSampling.expected_potential_step
    (fy := F state.primal) (fs := F xs) (err := lam / 8 * D + noise)
    (fun ω => F (z ω)) z (fun ω => lam • (x - z ω)) x state.primal state.dual xs
    hB ha.1.le hl rfl (by simpa only [mul_comm] using ha.2)
    (predictor_identity hl state hB) (fun _ => rfl)
    (by dsimp [x, D]; linarith [hc state.primal])
    (by dsimp [x, D]; linarith [hc xs])
  rw [hnorm] at ht
  have he : -(A / (2 * lam) * (lam ^ 2 * D)) +
      A * (lam / 8 * D + noise) = A * noise - 3 * A * lam / 8 * D := by
    field_simp
    ring
  have hn : 0 ≤ 3 * A * lam / 8 * D := by positivity
  have ht' : (𝔼 ω, potential F xs (advance lam state (z ω))) ≤
      potential F xs state - A / (2 * lam) * (lam ^ 2 * D) +
        A * (lam / 8 * D + noise) := by
    simpa only [potential, advance, smul_smul, A, a, x, D] using ht
  dsimp only [A, a] at he hn
  dsimp only [A, a] at ht'
  linarith

lemma expected_predictor_distance {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω]
    (state : Ω → State E) (xs : E) {lam B R : ℝ} (hl : 0 < lam) (hB : 0 ≤ B)
    (hw : ∀ ω, (state ω).weight = B)
    (hy : (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) ≤ R)
    (hv : (𝔼 ω, ‖(state ω).dual - xs‖ ^ 2) ≤ R) :
    (𝔼 ω, ‖predictor lam (state ω) - xs‖ ^ 2) ≤ R := by
  have ha := (accelerated_weight_properties hl hB).1
  change 0 < nextWeight lam B at ha
  apply expected_weighted_distance (fun ω => (state ω).primal) (fun ω => (state ω).dual)
    (fun ω => predictor lam (state ω)) xs (show 0 < B + nextWeight lam B by linarith)
    hB ha.le rfl _ hy hv
  intro ω
  have hh := predictor_identity hl (state ω) (by rw [hw]; exact hB)
  simpa only [hw] using hh

lemma expected_dual_distance {E Ω : Type*} [NormedAddCommGroup E] [Fintype Ω]
    (F : E → ℝ) (xs : E) (state : Ω → State E)
    (hw : ∀ ω, 0 ≤ (state ω).weight) (hmin : ∀ x, F xs ≤ F x) :
    (𝔼 ω, ‖(state ω).dual - xs‖ ^ 2) ≤ 2 * (𝔼 ω, potential F xs (state ω)) := by
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) =>
    dual_distance_le_potential F xs (state ω) (hw ω) (hmin _))
  simpa only [← Finset.mul_expect] using ht

lemma expected_query_distance {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω] [Nonempty Ω]
    (F : E → ℝ) (xs w : E) (state : Ω → State E)
    {lam B : ℝ} (hl : 0 < lam) (hB : 0 ≤ B) (hw : ∀ ω, (state ω).weight = B)
    (hmin : ∀ x, F xs ≤ F x) :
    (𝔼 ω, ‖predictor lam (state ω) - w‖ ^ 2) ≤
      2 * max (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) (2 * (𝔼 ω, potential F xs (state ω))) +
        2 * ‖w - xs‖ ^ 2 := by
  let R := max (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) (2 * (𝔼 ω, potential F xs (state ω)))
  have hd := expected_dual_distance F xs state (fun ω => by rw [hw]; exact hB) hmin
  have hy : (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) ≤ R := le_max_left _ _
  have hv : (𝔼 ω, ‖(state ω).dual - xs‖ ^ 2) ≤ R := hd.trans (le_max_right _ _)
  have hq := expected_predictor_distance state xs hl hB hw hy hv
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) =>
    anchor_distance_bound (predictor lam (state ω)) w xs)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at ht
  change (𝔼 ω, ‖predictor lam (state ω) - w‖ ^ 2) ≤ 2 * R + 2 * ‖w - xs‖ ^ 2
  linarith

lemma expected_gap_weighted {E Ω : Type*} [NormedAddCommGroup E] [Fintype Ω]
    (F : E → ℝ) (xs : E) (state : Ω → State E) (A : ℝ)
    (hw : ∀ ω, (state ω).weight = A) :
    A * (𝔼 ω, (F (state ω).primal - F xs)) ≤ (𝔼 ω, potential F xs (state ω)) := by
  have hp (ω : Ω) : A * (F (state ω).primal - F xs) ≤ potential F xs (state ω) := by
    dsimp [potential]
    rw [hw]
    have hn := sq_nonneg ‖(state ω).dual - xs‖
    linarith
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) => hp ω)
  simpa only [← Finset.mul_expect] using ht

lemma expected_gap_from_potential {E Ω : Type*} [NormedAddCommGroup E] [Fintype Ω]
    (F : E → ℝ) (xs : E) (state : Ω → State E) {lam A R : ℝ}
    (hl : 0 < lam) (T : ℕ) (hT : 0 < T) (hmin : ∀ x, F xs ≤ F x)
    (hw : ∀ ω, (state ω).weight = A) (hA : (T : ℝ) ^ 2 / (4 * lam) ≤ A)
    (hP : (𝔼 ω, potential F xs (state ω)) ≤ R) :
    (𝔼 ω, (F (state ω).primal - F xs)) ≤ 4 * lam * R / (T : ℝ) ^ 2 := by
  have hg : 0 ≤ (𝔼 ω, (F (state ω).primal - F xs)) :=
    Finset.expect_nonneg (fun ω _ => sub_nonneg.mpr (hmin _))
  have hp := (expected_gap_weighted F xs state A hw).trans hP
  have ha := (div_le_iff₀ (show 0 < 4 * lam by positivity)).mp hA
  have hm := mul_le_mul_of_nonneg_right ha hg
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * lam by positivity)
  have ht : 0 < (T : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hT)
  apply (le_div_iff₀ ht).2
  nlinarith only [hm, hp']

lemma trajectory_weights {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (state : (n : ℕ) → (Fin n → Ω) → State E)
    (z : (n : ℕ) → (Fin n → Ω) → Ω → E)
    (hzero : ∀ ξ, (state 0 ξ).weight = 0)
    (hstep : ∀ n ξ ω, state (n + 1) (Fin.snoc ξ ω) = advance lam (state n ξ) (z n ξ ω)) :
    ∀ n ξ, (state n ξ).weight = weights lam n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    intro ξ
    rw [← Fin.snoc_init_self ξ, hstep]
    exact advance_weight lam (state n (Fin.init ξ)) (z n (Fin.init ξ) (ξ (Fin.last n))) n
      (ih (Fin.init ξ))

lemma trajectory_potential_step {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω] [Nonempty Ω]
    (F : E → ℝ) (xs w : E) {lam gamma : ℝ} (hl : 0 < lam)
    (state : (n : ℕ) → (Fin n → Ω) → State E)
    (z : (n : ℕ) → (Fin n → Ω) → Ω → E)
    (hweight : ∀ n ξ, (state n ξ).weight = weights lam n)
    (hstep : ∀ n ξ ω, state (n + 1) (Fin.snoc ξ ω) = advance lam (state n ξ) (z n ξ ω))
    (n : ℕ)
    (hc : ∀ ξ v, (𝔼 ω, (F (z n ξ ω) - F v)) ≤
      (𝔼 ω, ⟪lam • (predictor lam (state n ξ) - z n ξ ω), z n ξ ω - v⟫) +
      lam / 8 * (𝔼 ω, ‖predictor lam (state n ξ) - z n ξ ω‖ ^ 2) +
      gamma * ‖predictor lam (state n ξ) - w‖ ^ 2) :
    (𝔼 ξ, potential F xs (state (n + 1) ξ)) ≤
      (𝔼 ξ, potential F xs (state n ξ)) + weights lam (n + 1) * gamma *
        (𝔼 ξ, ‖predictor lam (state n ξ) - w‖ ^ 2) := by
  rw [CappedProximalSampling.uniform_snoc]
  simp_rw [hstep]
  have hp (ξ : Fin n → Ω) := expected_advance_potential F xs (state n ξ) (z n ξ) hl
    (by rw [hweight]; exact (weights_bounds hl n).1) (hc ξ)
  have ht := Finset.expect_le_expect (fun ξ (_ : ξ ∈ Finset.univ) => hp ξ)
  simp only [hweight, Finset.expect_add_distrib, ← Finset.mul_expect] at ht
  simpa only [weights, mul_assoc] using! ht

lemma trajectory_primal_bound {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω] [Nonempty Ω]
    (F : E → ℝ) (xs : E) {lam : ℝ} (hl : 0 < lam) (hmin : ∀ x, F xs ≤ F x)
    (state : (n : ℕ) → (Fin n → Ω) → State E)
    (z : (n : ℕ) → (Fin n → Ω) → Ω → E)
    (hweight : ∀ n ξ, (state n ξ).weight = weights lam n)
    (hstep : ∀ n ξ ω, state (n + 1) (Fin.snoc ξ ω) = advance lam (state n ξ) (z n ξ ω))
    (n : ℕ) :
    (𝔼 ξ, ‖(state (n + 1) ξ).primal - xs‖ ^ 2) ≤
      max (𝔼 ξ, ‖(state n ξ).primal - xs‖ ^ 2)
        (2 * (𝔼 ξ, potential F xs (state (n + 1) ξ))) := by
  let B := weights lam n
  let a := nextWeight lam B
  let A := B + a
  have hB : 0 ≤ B := (weights_bounds hl n).1
  have ha : 0 < a := (accelerated_weight_properties hl hB).1
  have hA : 0 < A := add_pos_of_nonneg_of_pos hB ha
  have hp (ξ : Fin n → Ω) (ω : Ω) :
      A * ‖(state (n + 1) (Fin.snoc ξ ω)).primal - xs‖ ^ 2 ≤
        B * ‖(state n ξ).primal - xs‖ ^ 2 +
          a * ‖(state (n + 1) (Fin.snoc ξ ω)).dual - xs‖ ^ 2 := by
    have hb : 0 ≤ (state n ξ).weight := by rw [hweight]; exact hB
    have hi := advance_primal_identity hl (state n ξ) hb (z n ξ ω)
    simp only [hweight] at hi
    have ht := weighted_squared_distance (state n ξ).primal
      (advance lam (state n ξ) (z n ξ ω)).dual (z n ξ ω) xs hA hB ha.le rfl hi
    simpa only [hstep, advance] using ht
  have ht := Finset.expect_le_expect (fun ξ (_ : ξ ∈ Finset.univ) =>
    Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) => hp ξ ω))
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at ht
  rw [← CappedProximalSampling.uniform_snoc
      (fun ξ : Fin (n + 1) → Ω => ‖(state (n + 1) ξ).primal - xs‖ ^ 2),
    ← CappedProximalSampling.uniform_snoc
      (fun ξ : Fin (n + 1) → Ω => ‖(state (n + 1) ξ).dual - xs‖ ^ 2)] at ht
  have hd := expected_dual_distance F xs (state (n + 1))
    (fun ξ => by rw [hweight]; exact (weights_bounds hl (n + 1)).1) hmin
  let R := max (𝔼 ξ, ‖(state n ξ).primal - xs‖ ^ 2)
    (2 * (𝔼 ξ, potential F xs (state (n + 1) ξ)))
  have hy : (𝔼 ξ, ‖(state n ξ).primal - xs‖ ^ 2) ≤ R := le_max_left _ _
  have hv : (𝔼 ξ, ‖(state (n + 1) ξ).dual - xs‖ ^ 2) ≤ R := hd.trans (le_max_right _ _)
  have hy' := mul_le_mul_of_nonneg_left hy hB
  have hv' := mul_le_mul_of_nonneg_left hv ha.le
  change (𝔼 ξ, ‖(state (n + 1) ξ).primal - xs‖ ^ 2) ≤ R
  dsimp [A] at ht hA
  nlinarith

lemma finite_horizon_bootstrap (P Y X c : ℕ → ℝ) (T : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hc : ∀ k, 0 ≤ c k) (hP : P 0 ≤ R / 2) (hY : Y 0 ≤ R)
    (hsum : ∑ k ∈ Finset.range T, c k ≤ 1 / 12)
    (hstep : ∀ k < T, P (k + 1) ≤ P k + c k * X k)
    (hprimal : ∀ k < T, Y (k + 1) ≤ max (Y k) (2 * P (k + 1)))
    (hquery : ∀ k < T, X k ≤ 2 * max (Y k) (2 * P k) + 2 * R) :
    ∀ k ≤ T, P k ≤ R ∧ Y k ≤ 2 * R := by
  have hsumle (k : ℕ) (hk : k ≤ T) : ∑ i ∈ Finset.range k, c i ≤ 1 / 12 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun i _ _ => hc i)) hsum
  have hsmall (k : ℕ) (hk : k ≤ T) : R / 2 + 6 * R * (∑ i ∈ Finset.range k, c i) ≤ R := by
    have hh := mul_le_mul_of_nonneg_left (hsumle k hk) (show 0 ≤ 6 * R by positivity)
    linarith
  have hmain : ∀ k, k ≤ T →
      P k ≤ R / 2 + 6 * R * (∑ i ∈ Finset.range k, c i) ∧ Y k ≤ 2 * R := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      exact ⟨hP, by linarith⟩
    | succ k ih =>
      intro hk
      have hkt : k < T := Nat.lt_of_succ_le hk
      obtain ⟨hp, hy⟩ := ih (Nat.le_of_lt hkt)
      have hpk : P k ≤ R := hp.trans (hsmall k (Nat.le_of_lt hkt))
      have hm : max (Y k) (2 * P k) ≤ 2 * R := max_le hy (by linarith)
      have hx : X k ≤ 6 * R := by linarith [hquery k hkt]
      have hpnext : P (k + 1) ≤ R / 2 + 6 * R * (∑ i ∈ Finset.range (k + 1), c i) := by
        rw [Finset.sum_range_succ]
        have hh := mul_le_mul_of_nonneg_left hx (hc k)
        nlinarith [hstep k hkt]
      have hpn : P (k + 1) ≤ R := hpnext.trans (hsmall (k + 1) hk)
      exact ⟨hpnext, (hprimal k hkt).trans (max_le hy (by linarith))⟩
  intro k hk
  exact ⟨(hmain k hk).1.trans (hsmall k hk), (hmain k hk).2⟩

set_option maxHeartbeats 800000 in
lemma trajectory_potential_bound {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Ω] [Nonempty Ω]
    (F : E → ℝ) (xs w : E) {lam gamma : ℝ} (hl : 0 < lam) (hg : 0 ≤ gamma)
    (hmin : ∀ x, F xs ≤ F x)
    (state : (n : ℕ) → (Fin n → Ω) → State E)
    (z : (n : ℕ) → (Fin n → Ω) → Ω → E)
    (hzero : ∀ ξ, state 0 ξ = ⟨0, w, w⟩)
    (hstep : ∀ n ξ ω, state (n + 1) (Fin.snoc ξ ω) = advance lam (state n ξ) (z n ξ ω))
    (T : ℕ) (htune : gamma * (T : ℝ) ^ 3 / lam ≤ 1 / 12)
    (hc : ∀ n < T, ∀ ξ v, (𝔼 ω, (F (z n ξ ω) - F v)) ≤
      (𝔼 ω, ⟪lam • (predictor lam (state n ξ) - z n ξ ω), z n ξ ω - v⟫) +
      lam / 8 * (𝔼 ω, ‖predictor lam (state n ξ) - z n ξ ω‖ ^ 2) +
      gamma * ‖predictor lam (state n ξ) - w‖ ^ 2) :
    (𝔼 ξ, potential F xs (state T ξ)) ≤ ‖w - xs‖ ^ 2 := by
  have hw := trajectory_weights lam state z (fun ξ => by rw [hzero]) hstep
  let P := fun n => (𝔼 ξ, potential F xs (state n ξ))
  let Y := fun n => (𝔼 ξ, ‖(state n ξ).primal - xs‖ ^ 2)
  let X := fun n => (𝔼 ξ, ‖predictor lam (state n ξ) - w‖ ^ 2)
  let c := fun n => weights lam (n + 1) * gamma
  have hc0 (n : ℕ) : 0 ≤ c n := mul_nonneg (weights_bounds hl (n + 1)).1 hg
  have hp0 : P 0 ≤ ‖w - xs‖ ^ 2 / 2 := by
    simp only [P, hzero, potential, zero_mul, zero_add, Fintype.expect_const, le_refl]
  have hy0 : Y 0 ≤ ‖w - xs‖ ^ 2 := by simp only [Y, hzero, Fintype.expect_const, le_refl]
  have hsum : ∑ n ∈ Finset.range T, c n ≤ 1 / 12 := by
    calc
      _ = (∑ n ∈ Finset.range T, weights lam (n + 1)) * gamma := by
        simp only [c, Finset.sum_mul]
      _ ≤ ((T : ℝ) ^ 3 / lam) * gamma := mul_le_mul_of_nonneg_right (weights_sum_bound hl T) hg
      _ ≤ 1 / 12 := by
        convert htune using 1
        ring
  have hpstep (n : ℕ) (hn : n < T) : P (n + 1) ≤ P n + c n * X n := by
    exact trajectory_potential_step F xs w hl state z hw hstep n (hc n hn)
  have hyp (n : ℕ) (_hn : n < T) : Y (n + 1) ≤ max (Y n) (2 * P (n + 1)) :=
    trajectory_primal_bound F xs hl hmin state z hw hstep n
  have hx (n : ℕ) (_hn : n < T) : X n ≤ 2 * max (Y n) (2 * P n) + 2 * ‖w - xs‖ ^ 2 :=
    expected_query_distance F xs w (state n) hl (weights_bounds hl n).1 (hw n) hmin
  exact (finite_horizon_bootstrap P Y X c T (sq_nonneg _) hc0 hp0 hy0 hsum hpstep hyp hx T le_rfl).1

lemma finite_outer_bootstrap (P Y W u v : ℕ → ℝ) (T : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hP : P 0 ≤ R / 2) (hY : Y 0 ≤ R)
    (hsum : ∑ k ∈ Finset.range T, (u k + 8 * v k) ≤ 1 / 2)
    (hstep : ∀ k < T, P (k + 1) ≤ (1 + u k) * P k + v k * W k)
    (hprimal : ∀ k < T, Y (k + 1) ≤ max (Y k) (2 * P (k + 1)))
    (hwarm : ∀ k < T, W k ≤ 2 * Y k + 2 * max (Y k) (2 * P k)) :
    ∀ k ≤ T, P k ≤ R ∧ Y k ≤ 2 * R := by
  have hc (k : ℕ) : 0 ≤ u k + 8 * v k :=
    add_nonneg (hu k) (mul_nonneg (by norm_num) (hv k))
  have hsumle (k : ℕ) (hk : k ≤ T) : ∑ i ∈ Finset.range k, (u i + 8 * v i) ≤ 1 / 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun i _ _ => hc i)).trans hsum
  have hsmall (k : ℕ) (hk : k ≤ T) : R / 2 + R * (∑ i ∈ Finset.range k, (u i + 8 * v i)) ≤ R := by
    have hh := mul_le_mul_of_nonneg_left (hsumle k hk) hR
    linarith
  have hmain : ∀ k, k ≤ T →
      P k ≤ R / 2 + R * (∑ i ∈ Finset.range k, (u i + 8 * v i)) ∧ Y k ≤ 2 * R := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      exact ⟨hP, by linarith⟩
    | succ k ih =>
      intro hk
      have hkt : k < T := Nat.lt_of_succ_le hk
      obtain ⟨hp, hy⟩ := ih (Nat.le_of_lt hkt)
      have hpk := hp.trans (hsmall k (Nat.le_of_lt hkt))
      have hm : max (Y k) (2 * P k) ≤ 2 * R := max_le hy (by linarith)
      have hw : W k ≤ 8 * R := by linarith [hwarm k hkt]
      have hpnext : P (k + 1) ≤ R / 2 + R * (∑ i ∈ Finset.range (k + 1), (u i + 8 * v i)) := by
        rw [Finset.sum_range_succ]
        have h1 := mul_le_mul_of_nonneg_left hpk (hu k)
        have h2 := mul_le_mul_of_nonneg_left hw (hv k)
        nlinarith [hstep k hkt]
      have hpn := hpnext.trans (hsmall (k + 1) hk)
      exact ⟨hpnext, (hprimal k hkt).trans (max_le hy (by linarith))⟩
  intro k hk
  exact ⟨(hmain k hk).1.trans (hsmall k hk), (hmain k hk).2⟩

end LongTails.Proofs.CappedProximalPotential
