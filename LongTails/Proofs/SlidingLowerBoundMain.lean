import LongTails.Proofs.SlidingWireScaling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerBoundMain

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingLowerHiding SlidingLowerAdmissible SlidingLowerFailure SlidingLowerCorners
open SlidingLowerScaling SlidingWireFailure SlidingWireAdmissible SlidingWireScaling

lemma chain_dim (q : Params) (hq : spec.valid q) (b : Fin 2 → ℕ) (H : ℝ) (hH0 : 0 ≤ H)
    (hHle : H ≤ q.ℓ * q.Δ / q.ε ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)))
    (hb : ((∑ i, b i : ℕ) : ℝ) ≤ q.K + H) :
    16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (2 * chainLength q + 1 : ℕ) * (64 * (scale q).R ^ 2) +
      (2 * chainLength q + 1 : ℕ) ≤ q.d := by
  obtain ⟨hℓ, hL, hσ, hε, hX⟩ := valid_facts q hq
  have hvalid := hq.2.2.2.2.2
  have hT := chainLength_bounds q hX
  set X := q.ℓ * q.Δ / q.ε ^ 2 with hXd
  set Y := 1 + Real.sqrt (q.L / q.ℓ) with hYd
  have hs := Real.sqrt_nonneg (q.L / q.ℓ)
  have hY1 : 1 ≤ Y := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hσ0 : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  set H0 := X * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) with hH0d
  have hTc : (chainLength q : ℝ) ≤ X := by
    linarith [hT.1]
  have hR2 : (scale q).R ^ 2 ≤ 2 ^ 26 * (1 + X) := by
    show (5280 * (1 + Real.sqrt (chainLength q))) ^ 2 ≤ _
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (chainLength q))
    have h1 : (1 + Real.sqrt (chainLength q)) ^ 2 ≤ 2 * (1 + X) := by
      linarith [sq_nonneg (Real.sqrt (chainLength q) - 1)]
    calc (5280 * (1 + Real.sqrt (chainLength q))) ^ 2 =
        5280 ^ 2 * (1 + Real.sqrt (chainLength q)) ^ 2 := by ring
      _ ≤ 5280 ^ 2 * (2 * (1 + X)) := by gcongr
      _ ≤ 2 ^ 26 * (1 + X) := by linarith
  have hlen : ((2 * chainLength q + 1 : ℕ) : ℝ) ≤ 3 * (1 + X) := by push_cast; linarith
  have hN : ((∑ i, b i : ℕ) : ℝ) + 1 ≤ 1 + q.K + H0 := by linarith
  have hK1 : (1 : ℝ) ≤ 1 + q.K + H0 := by
    have := Nat.cast_nonneg (α := ℝ) q.K
    have : 0 ≤ H0 := by positivity
    linarith
  have hX3 : (1 + X) ^ 2 ≤ (1 + X) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hY9 : (1 : ℝ) ≤ Y ^ 9 := one_le_pow₀ hY1
  calc 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (2 * chainLength q + 1 : ℕ) * (64 * (scale q).R ^ 2) +
        (2 * chainLength q + 1 : ℕ)
      ≤ 16 * (1 + q.K + H0) * (3 * (1 + X)) * (64 * (2 ^ 26 * (1 + X))) + 3 * (1 + X) := by
        gcongr
    _ ≤ 2 ^ 200 * (1 + q.K + H0) * (1 + X) ^ 3 * Y ^ 9 := by
        have e : 16 * (1 + q.K + H0) * (3 * (1 + X)) * (64 * (2 ^ 26 * (1 + X))) =
            3 * 2 ^ 36 * (1 + q.K + H0) * (1 + X) ^ 2 := by ring
        rw [e]
        have h1 : (1 + q.K + H0) * (1 + X) ^ 2 ≤ (1 + q.K + H0) * (1 + X) ^ 3 * Y ^ 9 := by
          have := mul_le_mul hX3 hY9 (by positivity) (by positivity)
          have h0 : 0 ≤ 1 + q.K + H0 := by linarith
          calc (1 + q.K + H0) * (1 + X) ^ 2 = (1 + q.K + H0) * ((1 + X) ^ 2 * 1) := by ring
            _ ≤ (1 + q.K + H0) * ((1 + X) ^ 3 * Y ^ 9) := mul_le_mul_of_nonneg_left this h0
            _ = (1 + q.K + H0) * (1 + X) ^ 3 * Y ^ 9 := by ring
        have h2 : 3 * (1 + X) ≤ 3 * ((1 + q.K + H0) * (1 + X) ^ 3 * Y ^ 9) := by
          have : (1 + X) ≤ (1 + X) ^ 3 := by
            calc (1 + X) = (1 + X) ^ 1 := (pow_one _).symm
              _ ≤ (1 + X) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
          have h3 := mul_le_mul this hY9 (by norm_num) (by positivity)
          have h4 := mul_le_mul hK1 h3 (by positivity) (by linarith)
          have e2 : (1 + q.K + H0) * ((1 + X) ^ 3 * Y ^ 9) = (1 + q.K + H0) * (1 + X) ^ 3 * Y ^ 9 := by
            ring
          linarith
        have h5 : 0 ≤ (1 + q.K + H0) * (1 + X) ^ 3 * Y ^ 9 := by positivity
        linarith
    _ ≤ q.d := hvalid

lemma failure_f (q : Params) (hq : spec.valid q) (A : SlidingLowerFailure.Alg q) (b : Fin 2 → ℕ)
    (hb0 : b 0 ≤ ⌊q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 60⌋₊) (hb1 : b 1 ≤ q.K) :
    ∃ (I : spec.Instance q) (O : Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) 2),
      spec.admissible q I O ∧
        ¬ spec.successful q I (fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hℓ, hL, hσ, hε, hX⟩ := valid_facts q hq
  have hV := scale_valid q hq
  have hT := chainLength_bounds q hX
  have hb0' : b 0 ≤ chainLength q := by
    have h1 : (b 0 : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 60 :=
      (Nat.cast_le.mpr hb0).trans (Nat.floor_le (by positivity))
    have : (b 0 : ℝ) ≤ chainLength q := by
      have : q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 60 ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 21 := by
        apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
      linarith [hT.2]
    exact_mod_cast this
  have hdim := chain_dim q hq b (b 0 : ℝ) (Nat.cast_nonneg _) (by
      have h1 : (b 0 : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 60 :=
        (Nat.cast_le.mpr hb0).trans (Nat.floor_le (by positivity))
      have : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
      have hs := Real.sqrt_nonneg (q.L / q.ℓ)
      have hX0 : 0 ≤ q.ℓ * q.Δ / q.ε ^ 2 := by linarith
      nlinarith) (by
      rw [Fin.sum_univ_two]; push_cast
      have : (b 1 : ℝ) ≤ q.K := by exact_mod_cast hb1
      linarith)
  obtain ⟨π, hπ⟩ := exists_failure q (scale q) hV hℓ (fCorner (chainLength q)) A b hdim
    (fun seed π => f_excess q (scale q) hV A b hb0' seed π) (cmin_bound q hq)
  exact ⟨hardInstance q (scale q) π, hardOracle q (scale q) hV.p_pos.le hV.p_le π,
    hard_admissible q (scale q) hV π, hπ⟩

lemma failure_hA (q : Params) (hq : spec.valid q) (A : SlidingLowerFailure.Alg q) (b : Fin 2 → ℕ)
    (hB : Real.sqrt (q.L / q.ℓ) < 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2)) (hb0 : b 0 ≤ q.K)
    (hb1 : b 1 ≤ ⌊q.ℓ * q.Δ / q.ε ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) / 2 ^ 60⌋₊) :
    ∃ (I : spec.Instance q) (O : Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) 2),
      spec.admissible q I O ∧
        ¬ spec.successful q I (fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hℓ, hL, hσ, hε, hX⟩ := valid_facts q hq
  have hV := scale_valid q hq
  have hT := chainLength_bounds q hX
  set X := q.ℓ * q.Δ / q.ε ^ 2 with hXd
  set H := X * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) with hHd
  have hσ0 : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hs := Real.sqrt_nonneg (q.L / q.ℓ)
  have hX0 : 0 ≤ X := by linarith
  have hH0 : 0 ≤ H := by positivity
  have hb1r : (b 1 : ℝ) ≤ H / 2 ^ 60 := (Nat.cast_le.mpr hb1).trans (Nat.floor_le (by positivity))
  have hTpos : 0 < chainLength q := by
    have : (1 : ℝ) ≤ chainLength q := by
      have : (1 : ℝ) ≤ X / 2 ^ 21 := by rw [le_div_iff₀ (by norm_num)]; linarith
      linarith [hT.2]
    exact_mod_cast (show (0 : ℝ) < chainLength q by linarith)
  have hp : coinProb q * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ 2 ^ 18 := by
    unfold coinProb
    split_ifs with h
    · have : q.σ ^ 2 / q.ε ^ 2 ≤ 2 ^ 17 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · push Not at h
      have hσ2 : 0 < q.σ ^ 2 := lt_of_le_of_lt (by positivity) h
      have hs2 : q.σ ^ 2 ≠ 0 := hσ2.ne'
      have hε2 : q.ε ^ 2 ≠ 0 := by positivity
      have e0 : 2 ^ 17 * q.ε ^ 2 / q.σ ^ 2 * (q.σ ^ 2 / q.ε ^ 2) = 2 ^ 17 := by
        rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hs2 hε2)]
        ring
      have e : 2 ^ 17 * q.ε ^ 2 / q.σ ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2) =
          2 ^ 17 * q.ε ^ 2 / q.σ ^ 2 + 2 ^ 17 := by rw [mul_add, mul_one, e0]
      rw [e]
      have : 2 ^ 17 * q.ε ^ 2 / q.σ ^ 2 ≤ 1 := by rw [div_le_one hσ2]; exact h.le
      linarith
  have hHA : H ≤ X * (1 + q.σ ^ 2 / q.ε ^ 2) * (1 + 2 ^ 12) := by
    have : Real.sqrt (q.L / q.ℓ) ≤ 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) := hB.le
    rw [hHd]; nlinarith
  have hcond : 4 * (scale q).p * (b 1 : ℝ) ≤ chainLength q := by
    show 4 * coinProb q * (b 1 : ℝ) ≤ chainLength q
    have hp0 := (coinProb_bounds q hε).1
    have h1 : 4 * coinProb q * (b 1 : ℝ) ≤ 4 * coinProb q * (H / 2 ^ 60) :=
      mul_le_mul_of_nonneg_left hb1r (by positivity)
    have h2 : 4 * coinProb q * (H / 2 ^ 60) ≤
        4 * (coinProb q * (1 + q.σ ^ 2 / q.ε ^ 2)) * X * (1 + 2 ^ 12) / 2 ^ 60 := by
      have := mul_le_mul_of_nonneg_left hHA (show 0 ≤ 4 * coinProb q / 2 ^ 60 by positivity)
      have e1 : 4 * coinProb q * (H / 2 ^ 60) = 4 * coinProb q / 2 ^ 60 * H := by ring
      have e2 : 4 * (coinProb q * (1 + q.σ ^ 2 / q.ε ^ 2)) * X * (1 + 2 ^ 12) / 2 ^ 60 =
          4 * coinProb q / 2 ^ 60 * (X * (1 + q.σ ^ 2 / q.ε ^ 2) * (1 + 2 ^ 12)) := by ring
      linarith
    have h3 : 4 * (coinProb q * (1 + q.σ ^ 2 / q.ε ^ 2)) * X * (1 + 2 ^ 12) / 2 ^ 60 ≤
        X / 2 ^ 21 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      have := mul_le_mul_of_nonneg_right hp (show 0 ≤ X by linarith)
      nlinarith
    linarith [hT.2]
  have hdim := chain_dim q hq b (b 1 : ℝ) (Nat.cast_nonneg _) (by
      have : H / 2 ^ 60 ≤ H := by rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith) (by
      rw [Fin.sum_univ_two]; push_cast
      have : (b 0 : ℝ) ≤ q.K := by exact_mod_cast hb0
      linarith)
  obtain ⟨π, hπ⟩ := exists_failure q (scale q) hV hℓ (hCorner (chainLength q)) A b hdim
    (fun seed π => h_excess q (scale q) hV hTpos A b hcond seed π) (cmin_bound q hq)
  exact ⟨hardInstance q (scale q) π, hardOracle q (scale q) hV.p_pos.le hV.p_le π,
    hard_admissible q (scale q) hV π, hπ⟩

lemma failure_hB (q : Params) (hq : spec.valid q) (A : SlidingLowerFailure.Alg q) (b : Fin 2 → ℕ)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) (hb0 : b 0 ≤ q.K)
    (hb1 : b 1 ≤ ⌊q.ℓ * q.Δ / q.ε ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) / 2 ^ 60⌋₊) :
    ∃ (I : spec.Instance q) (O : Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) 2),
      spec.admissible q I O ∧
        ¬ spec.successful q I (fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hV, hW⟩ := wire_valid q hq hB
  obtain ⟨π, hπ⟩ := exists_failureB q (wireT q) (wireScale q) hV hW A b
    (wire_hb q hq hB (b 1) hb1) (wire_dim q hq hB b hb0 hb1) (wire_acc q hq hB)
  exact ⟨wireInstance q (wireScale q) π, wireOracle q (wireScale q) π,
    wire_admissible q (wireT q) (wireScale q) hV π, hπ⟩

end LongTails.Proofs.SlidingLowerBoundMain
