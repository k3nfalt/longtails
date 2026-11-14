import LongTails.Proofs.AffineResidualCostMoments

namespace LongTails.Proofs.AffineResidualCostParameters

open LongTails.Algorithms.AffineResidualSaddle (localSteps)

noncomputable def localWork (m : ℕ) (τ μ L r : ℝ) : ℝ :=
  (1 + m * L * r ^ 2 / τ) * (1 + Real.sqrt (τ * Real.log m / (μ * r ^ 2))) +
    (L / μ) ^ 2 + m * L ^ 2 * r ^ 2 / (μ * τ) + 1

lemma localWork_nonneg (m : ℕ) {τ μ L r : ℝ} (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) :
    0 ≤ localWork m τ μ L r := by unfold localWork; positivity

lemma relative_steps_uniform (m : ℕ) [NeZero m] {τ μ L r k H : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hr : 0 < r)
    (hk : 1 ≤ k) (hkH : k ≤ 12200000 * H ^ 4) :
    (localSteps m τ μ L r (μ * r ^ 2 / k) : ℝ) ≤
      1000000000 * H ^ 4 * localWork m τ μ L r := by
  have hh := AffineResidualCost.localSteps_relative_bound m hτ hμ hL hr hk
  change _ ≤ 64 * k * localWork m τ μ L r at hh
  apply hh.trans
  have hW := localWork_nonneg m (r := r) hτ hμ hL
  apply mul_le_mul_of_nonneg_right _ hW
  nlinarith [sq_nonneg (H ^ 2)]

lemma outer_cost_scalar_bound {m H b N t T B ns np nm : ℝ}
    (hm : 0 ≤ m) (hH : 3 ≤ H) (hb : 0 ≤ b) (hbH : b ≤ 7 * H)
    (hNt : N ≤ 201 * H * t) (ht : 0 ≤ t) (hT : 0 ≤ T)
    (hB : B = 1000000000 * H ^ 4 * T)
    (hns : 0 ≤ ns) (hnsB : ns ≤ B) (hnp : 0 ≤ np) (hnpB : np ≤ B)
    (hnm : 0 ≤ nm) (hnmB : nm ≤ B) :
    N * ((2 * H + 9) * (m + b * (2 * ns + m)) +
      (m + 2 * np + (2 + 15 * H) * nm)) ≤
      30000000000000 * H ^ 7 * t * (m + T) := by
  have hH0 : 0 ≤ H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hsearch : (2 * H + 9) * (m + b * (2 * ns + m)) ≤
      40 * H ^ 2 * m + 70 * H ^ 2 * B := by
    calc
      _ ≤ (5 * H) * (m + (7 * H) * (2 * B + m)) := by gcongr; linarith
      _ ≤ (5 * H) * ((8 * H) * m + 14 * H * B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith only [mul_nonneg (sub_nonneg.mpr hH1) hm]
      _ = _ := by ring
  have hfinal : m + 2 * np + (2 + 15 * H) * nm ≤ H ^ 2 * m + 18 * H ^ 2 * B := by
    have h1 : 1 ≤ H ^ 2 := one_le_pow₀ hH1
    have h2 : H ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ m + 2 * B + (16 * H) * B := by gcongr; linarith
      _ ≤ H ^ 2 * m + 2 * (H ^ 2 * B) + 16 * (H ^ 2 * B) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr h1) hm,
          mul_nonneg (sub_nonneg.mpr h1) hB0, mul_nonneg (sub_nonneg.mpr h2) hB0]
      _ = _ := by ring
  have hsum : (2 * H + 9) * (m + b * (2 * ns + m)) +
      (m + 2 * np + (2 + 15 * H) * nm) ≤ 100 * H ^ 2 * (m + B) := by
    nlinarith [mul_nonneg (sq_nonneg H) hm, mul_nonneg (sq_nonneg H) hB0]
  have h4 : 1 ≤ H ^ 4 := one_le_pow₀ hH1
  have hmb : m + B ≤ 1000000000 * H ^ 4 * (m + T) := by
    rw [hB]
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) hm]
  calc
    _ ≤ (201 * H * t) * (100 * H ^ 2 * (1000000000 * H ^ 4 * (m + T))) := by
      apply mul_le_mul hNt (hsum.trans (mul_le_mul_of_nonneg_left hmb (by positivity)))
      · positivity
      · positivity
    _ ≤ _ := by ring_nf; nlinarith [mul_nonneg (show 0 ≤ H ^ 7 * t by positivity) (add_nonneg hm hT)]

open MeasureTheory
open LongTails.Algorithms.AffineResidualOuter
open LongTails.Algorithms.AffineResidualBudget

lemma referenceRunCost_bound (m : ℕ) [NeZero m] {τ L r floor t : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hf : 0 < floor) (ht : 0 ≤ t)
    (H b N J : ℕ) (hH : 3 ≤ H) (hb : b ≤ 7 * H) (hN : (N : ℝ) ≤ 201 * H * t)
    (hJ : J = 5 * H) :
    (∫ seeds, (referenceRunCost m τ L r floor H b N J seeds : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))) ≤
      30000000000000 * (H : ℝ) ^ 7 * t * (m + localWork m τ floor L r) := by
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hH1 : (1 : ℝ) ≤ H := by linarith
  have hH3 : (1 : ℝ) ≤ (H : ℝ) ^ 3 := one_le_pow₀ hH1
  have hH4 : (1 : ℝ) ≤ (H : ℝ) ^ 4 := one_le_pow₀ hH1
  have h34 : (H : ℝ) ^ 3 ≤ (H : ℝ) ^ 4 := pow_le_pow_right₀ hH1 (by omega)
  have hJr : (J : ℝ) = 5 * H := by exact_mod_cast hJ
  have hkr : 1 ≤ 2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * J) := by
    nlinarith [mul_nonneg (show 0 ≤ (H : ℝ) ^ 3 by positivity) (Nat.cast_nonneg J)]
  have hkbound : 2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * J) ≤ 12200000 * (H : ℝ) ^ 4 := by
    rw [hJr]
    have hh : 2 + 12 * (5 * (H : ℝ)) ≤ 61 * H := by linarith
    calc
      _ ≤ 2 * 100000 * (H : ℝ) ^ 3 * (61 * H) := by gcongr
      _ = _ := by ring
  have hs := relative_steps_uniform m hτ hf hL hr (by norm_num : (1 : ℝ) ≤ 32768)
    (show (32768 : ℝ) ≤ 12200000 * (H : ℝ) ^ 4 by nlinarith)
  have hp := relative_steps_uniform m hτ hf hL hr
    (show 1 ≤ 100000 * (H : ℝ) ^ 3 by nlinarith)
    (show 100000 * (H : ℝ) ^ 3 ≤ 12200000 * (H : ℝ) ^ 4 by nlinarith)
  have hm := relative_steps_uniform m hτ hf hL hr hkr hkbound
  have hmean := (AffineResidualCostMoments.referenceRunCost_moments m hτ hL hr hf H b N J (by omega)).2
  apply hmean.trans
  simp only [referenceProbeCost, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hJr, show (3 : ℝ) * (5 * (H : ℝ)) = 15 * H by ring]
  apply outer_cost_scalar_bound (Nat.cast_nonneg m) hHr (Nat.cast_nonneg b)
    (by exact_mod_cast hb) hN ht (localWork_nonneg m (r := r) hτ hf hL) rfl
    (Nat.cast_nonneg _) hs (Nat.cast_nonneg _) hp (Nat.cast_nonneg _)
  simpa only [hJr] using hm

open LongTails.Algorithms.AffineSoftmaxOuter (compilerFloor compilerCap compilerDepth compilerBoost compilerHorizon compilerScale)
open AffineSoftmaxOuterParameters

lemma computed_reference_mean (m : ℕ) [NeZero m] {τ L G r D ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    (∫ seeds, (referenceRunCost m τ L r (compilerFloor G D r ε)
      (compilerDepth G D r ε) (compilerBoost G D r ε) (compilerHorizon G D r ε)
      (5 * compilerDepth G D r ε) seeds : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))) ≤
      30000000000000 * (compilerDepth G D r ε : ℝ) ^ 7 * compilerScale D r *
        (m + localWork m τ (compilerFloor G D r ε) L r) := by
  exact referenceRunCost_bound m hτ hL hr (compilerFloor_pos hr hrD hε)
    (le_trans zero_le_one (compilerScale_bounds hr hrD).1) _ _ _ _
    (compilerDepth_ge_three G D r ε) (compilerBoost_bound hr hrD hε hsmall)
    (compilerHorizon_bounds hr hrD).2 rfl

lemma localWork_scaled_bound (m : ℕ) (hm : 2 ≤ m) {L r ε H t ell : ℝ}
    (hL : 0 ≤ L) (hr : 0 < r) (hε : 0 < ε) (hH : 1 ≤ H) (ht : 1 ≤ t)
    (hell : 1 ≤ ell) (hlog : Real.log m ≤ ell) :
    t * (m + localWork m (ε / Real.log m) (ε * H ^ 2 / (t * r ^ 2)) L r) ≤
      4 * ell * (m * t + t * Real.sqrt t + m * L * r ^ 2 * t * Real.sqrt t / ε +
        L ^ 2 * t ^ 3 * r ^ 4 / ε ^ 2 + m * L ^ 2 * t ^ 2 * r ^ 4 / ε ^ 2) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hl : 0 < Real.log m := Real.log_pos hm1
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hepos : 0 < ell := zero_lt_one.trans_le hell
  let τ := ε / Real.log m
  let μ := ε * H ^ 2 / (t * r ^ 2)
  let A := (m : ℝ) * L * r ^ 2 / ε
  let V := L ^ 2 * t ^ 3 * r ^ 4 / ε ^ 2
  let W := (m : ℝ) * L ^ 2 * t ^ 2 * r ^ 4 / ε ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH
  have hsqrt : 1 ≤ Real.sqrt t := by simpa using Real.sqrt_le_sqrt ht
  have hratio : τ * Real.log m / (μ * r ^ 2) = t / H ^ 2 := by dsimp [τ, μ]; field_simp
  have hs : Real.sqrt (τ * Real.log m / (μ * r ^ 2)) ≤ Real.sqrt t := by
    rw [hratio]
    exact Real.sqrt_le_sqrt (div_le_self htpos.le hH2)
  have haeq : (m : ℝ) * L * r ^ 2 / τ = A * Real.log m := by dsimp [A, τ]; field_simp
  have ha : 1 + (m : ℝ) * L * r ^ 2 / τ ≤ ell * (1 + A) := by
    rw [haeq]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hlog)]
  have hinit : t * ((1 + (m : ℝ) * L * r ^ 2 / τ) *
      (1 + Real.sqrt (τ * Real.log m / (μ * r ^ 2)))) ≤
      2 * ell * (t * Real.sqrt t) * (1 + A) := by
    calc
      _ ≤ t * ((ell * (1 + A)) * (2 * Real.sqrt t)) := by
        gcongr
        linarith
      _ = _ := by ring
  have hveq : t * (L / μ) ^ 2 = V / H ^ 4 := by dsimp [μ, V]; field_simp
  have hv : t * (L / μ) ^ 2 ≤ V := by rw [hveq]; exact div_le_self hV hH4
  have hweq : t * ((m : ℝ) * L ^ 2 * r ^ 2 / (μ * τ)) = W * (Real.log m / H ^ 2) := by
    dsimp [μ, τ, W]
    field_simp
  have hw : t * ((m : ℝ) * L ^ 2 * r ^ 2 / (μ * τ)) ≤ ell * W := by
    rw [hweq, mul_comm ell W]
    exact mul_le_mul_of_nonneg_left ((div_le_self hl.le hH2).trans hlog) hW
  have htroot : t ≤ t * Real.sqrt t := by nlinarith
  have hmt : (m : ℝ) * t ≤ ell * ((m : ℝ) * t) :=
    le_mul_of_one_le_left (by positivity) hell
  have hve : V ≤ ell * V := le_mul_of_one_le_left hV hell
  have hte : t * Real.sqrt t ≤ ell * (t * Real.sqrt t) :=
    le_mul_of_one_le_left (by positivity) hell
  have hprod : 0 ≤ ell * (t * Real.sqrt t) * A := by positivity
  have he : m * L * r ^ 2 * t * Real.sqrt t / ε = (t * Real.sqrt t) * A := by dsimp [A]; ring
  rw [he]
  change t * (m + ((1 + m * L * r ^ 2 / τ) *
    (1 + Real.sqrt (τ * Real.log m / (μ * r ^ 2))) + (L / μ) ^ 2 +
    m * L ^ 2 * r ^ 2 / (μ * τ) + 1)) ≤
      4 * ell * (m * t + t * Real.sqrt t + (t * Real.sqrt t) * A + V + W)
  nlinarith only [hinit, hv, hw, htroot, hmt, hve, hte, hprod,
    mul_nonneg hepos.le hV, mul_nonneg hepos.le hW,
    mul_nonneg hepos.le (show 0 ≤ t * Real.sqrt t by positivity), mul_nonneg hepos.le (show 0 ≤ (m : ℝ) * t by positivity)]

end LongTails.Proofs.AffineResidualCostParameters
