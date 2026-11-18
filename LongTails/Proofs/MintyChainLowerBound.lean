import LongTails.Setups.EuclideanWeakMinty
import LongTails.Proofs.MintyChainHiding
import LongTails.Proofs.Execution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MintyChainLowerBound

open LongTails.Setups.EuclideanWeakMinty MintyChainGeometry

noncomputable def hardOracle (p : Params) {k : ℕ} (κ r B : ℝ) (π : Fin (k + 1) ↪ Fin p.d) :
    Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) where
  answer _ q _ := field κ r B π (q.2 - p.x0)

lemma hard_admissible (p : Params) {k : ℕ} (κ r B : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hB : 0 < B)
    (π : Fin (k + 1) ↪ Fin p.d) (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2)
    (hL : 6 * κ ≤ p.L) (hRn : 0 ≤ p.R) (hR : ((k : ℝ) + 1) * r ^ 2 ≤ p.R ^ 2)
    (hρ : 0 ≤ p.ρ) :
    spec.admissible p (fun x => field κ r B π (x - p.x0)) (hardOracle p κ r B π) := by
  refine ⟨fun _ _ _ => rfl, ?_, p.x0 + target r π, ?_, ?_, ?_⟩
  · intro x y
    have h := field_lipschitz κ r B hκ hr hB π (x - p.x0) (y - p.x0)
    rw [sub_sub_sub_cancel_right] at h
    exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · change field κ r B π (p.x0 + target r π - p.x0) = 0
    rw [add_sub_cancel_left]
    exact field_target κ r B hr.le hB.le π hrad
  · rw [add_sub_cancel_left]
    have h := target_norm_sq r π
    have hs : ‖target r π‖ ^ 2 ≤ p.R ^ 2 := by rw [h]; exact hR
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hRn two_ne_zero).mp hs
  · intro x
    have h := field_minty κ r B hκ hr hB π hrad (x - p.x0)
    have e : x - (p.x0 + target r π) = x - p.x0 - target r π := by abel
    rw [e]
    have : 0 ≤ p.ρ * ‖field κ r B π (x - p.x0)‖ ^ 2 := by positivity
    linarith

lemma execute_hard (p : Params) {k : ℕ} (κ r B : ℝ) (π : Fin (k + 1) ↪ Fin p.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (hardOracle p κ r B π) A (fun _ => N) seed ξ =
      A.output ((fun s => A.update s (field κ r B π ((A.query s).2 - p.x0)))^[N]
        (A.initial seed)) := by
  rw [OracleTemplate.execute_eq_of_answer_eq (hardOracle p κ r B π)
    (fun x => field κ r B π (x - p.x0)) (fun _ _ _ => rfl)]
  exact OracleTemplate.execute_iterate (fun x => field κ r B π (x - p.x0)) A N seed

lemma rpow_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma budget_bounds (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : N ≤ ⌊min ((p.L * p.R / (28 * p.ε)) ^ 2) (((p.d : ℝ) / 257) ^ ((1 : ℝ) / 3))⌋₊ - 1) :
    ((N : ℝ) + 1) ≤ (p.L * p.R / (28 * p.ε)) ^ 2 ∧ 257 * ((N : ℝ) + 1) ^ 3 ≤ p.d := by
  obtain ⟨hL, -, -, hε, hLR, hd⟩ := hp
  have hq : 1 ≤ p.L * p.R / (28 * p.ε) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hq2 : 1 ≤ (p.L * p.R / (28 * p.ε)) ^ 2 := by nlinarith
  have hd' : (257 : ℝ) ≤ p.d := by exact_mod_cast hd
  set m := min ((p.L * p.R / (28 * p.ε)) ^ 2) (((p.d : ℝ) / 257) ^ ((1 : ℝ) / 3))
  have hm : 0 ≤ m := le_min (by positivity) (by positivity)
  by_cases hc : N + 1 ≤ ⌊m⌋₊
  · have h1 : ((N + 1 : ℕ) : ℝ) ≤ m := (Nat.le_floor_iff hm).mp hc
    push_cast at h1
    refine ⟨h1.trans (min_le_left _ _), ?_⟩
    have h2 := h1.trans (min_le_right _ _)
    have h3 := pow_le_pow_left₀ (by positivity) h2 3
    rw [rpow_cube _ (by positivity)] at h3
    linarith
  · have hN0 : N = 0 := by omega
    subst hN0
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_zero, zero_add]
      exact hq2
    · rw [Nat.cast_zero, zero_add, one_pow, mul_one]
      exact hd'

lemma exists_failure (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : N ≤ ⌊min ((p.L * p.R / (28 * p.ε)) ^ 2) (((p.d : ℝ) / 257) ^ ((1 : ℝ) / 3))⌋₊ - 1)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (F : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p F O ∧
        ¬ spec.successful p F
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hK, hdim⟩ := budget_bounds p hp N hN
  obtain ⟨hL, hρ, -, hε, hLR, -⟩ := hp
  have hR : 0 < p.R := by
    have : 0 < p.L * p.R := by linarith
    exact pos_of_mul_pos_right this hL.le
  let K : ℝ := (N : ℝ) + 1
  have hK0 : 0 < K := by positivity
  let κ := p.L / 6
  let r := 28 * p.ε / p.L
  let B := 2 * r * Real.sqrt K
  let D : ℝ := 256 * K ^ 3
  have hκ : 0 < κ := by positivity
  have hr : 0 < r := by positivity
  have hB : 0 < B := by positivity
  have hB2 : B ^ 2 = 4 * K * r ^ 2 := by
    dsimp only [B]
    rw [mul_pow, mul_pow, Real.sq_sqrt hK0.le]
    ring
  have hrad : 4 * ((N : ℝ) + 1) * r ^ 2 ≤ B ^ 2 := by rw [hB2]
  have hRr : ((N : ℝ) + 1) * r ^ 2 ≤ p.R ^ 2 := by
    have e : (p.L * p.R / (28 * p.ε)) ^ 2 = p.R ^ 2 / r ^ 2 := by
      dsimp only [r]
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at hK
    exact hK
  have hratio : B ^ 2 / (r / 4) ^ 2 = 64 * K := by
    rw [hB2]
    field_simp
    ring
  have hD : 0 < D := by positivity
  have hDs : D + (N + 1 : ℕ) ≤ p.d := by
    push_cast
    change 256 * K ^ 3 + K ≤ (p.d : ℝ)
    have : K ≤ K ^ 3 := by
      have h1 : 1 ≤ K := by dsimp only [K]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ h1
      have e : K ^ 3 = K * K ^ 2 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hK2 hK0.le]
    linarith
  have hsize : 4 * ((N + 1 : ℕ) ^ 2 * (B ^ 2 / (r / 4) ^ 2)) ≤ D := by
    rw [hratio]
    push_cast
    change 4 * (K ^ 2 * (64 * K)) ≤ 256 * K ^ 3
    nlinarith
  have hgap : 4 * p.ε ^ 2 ≤ 3 * κ ^ 2 * r ^ 2 / 16 := by
    have e : κ * r = 14 * p.ε / 3 := by
      dsimp only [κ, r]
      field_simp
      ring
    have e2 : 3 * κ ^ 2 * r ^ 2 / 16 = 3 * (κ * r) ^ 2 / 16 := by ring
    rw [e2, e]
    nlinarith [sq_nonneg p.ε]
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨π, hbad⟩ := LongTails.Proofs.MintyChainHiding.exists_failure (d := p.d) (k := N)
    κ r B D p.ε hκ hr hB hrad hD hDs hsize hε hgap
    (fun s => (A.query s).2 - p.x0) (fun s => A.output s - p.x0) A.update
    (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  refine ⟨fun x => field κ r B π (x - p.x0), hardOracle p κ r B π,
    hard_admissible p κ r B hκ.le hr hB π hrad (by dsimp only [κ]; linarith) hR.le hRr hρ, ?_⟩
  have hout :
      (fun w : A.Seed × (ℕ → Unit) =>
        ‖field κ r B π (execute (hardOracle p κ r B π) A (fun _ => N) w.1 w.2 - p.x0)‖) =
      fun w => ‖field κ r B π ((fun s => A.output s - p.x0)
        ((fun s => A.update s (field κ r B π ((fun s => (A.query s).2 - p.x0) s)))^[N]
          (A.initial w.1)))‖ := by
    funext w
    rw [execute_hard p κ r B π A N w.1 w.2]
  rintro ⟨hi, he⟩
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      ‖field κ r B π (execute (hardOracle p κ r B π) A (fun _ => N) w.1 w.2 - p.x0)‖)
      (P : Measure _) at hi
    rw [hout] at hi
    exact hi
  · change (∫ w : A.Seed × (ℕ → Unit),
      ‖field κ r B π (execute (hardOracle p κ r B π) A (fun _ => N) w.1 w.2 - p.x0)‖
        ∂(P : Measure _)) ≤ p.ε at he
    rw [hout] at he
    exact he

end LongTails.Proofs.MintyChainLowerBound
