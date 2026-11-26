import LongTails.Proofs.RecursiveMomentumConvergence

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.RecursiveMomentumGapBatch

open RecursiveMomentum NormalizedStorm

private lemma error_sum (U C : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    (hu : ∀ j, 0 ≤ U j) (hc : ∀ j, 0 ≤ C j)
    (step : ∀ j, U (j+1) ≤ (1-a)^2 * U j + a * C j) (T : ℕ) :
    ∑ j ∈ Finset.range (T+1), U j ≤ (T+1 : ℝ) * U 0 + ∑ j ∈ Finset.range T, C j := by
  let V (j : ℕ) := max (U j - U 0) 0
  have hs j : V (j+1) ≤ (1-a) * V j + a * C j := by
    apply max_le
    · have h₁ := mul_le_mul_of_nonneg_right (show (1-a)^2 ≤ 1-a by nlinarith) (hu j)
      have h₂ := mul_le_mul_of_nonneg_left (le_max_left (U j - U 0) 0) (sub_nonneg.mpr ha')
      nlinarith [step j, mul_nonneg ha.le (hu 0)]
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha') (le_max_right _ _)) (mul_nonneg ha.le (hc j))
  have aux (n : ℕ) : a * ∑ j ∈ Finset.range (n+1), V j + (1-a) * V n ≤
      a * ∑ j ∈ Finset.range n, C j := by
    induction n with
    | zero => simp [V]
    | succ n ih =>
      rw [Finset.sum_range_succ (f := V), Finset.sum_range_succ (f := C)]
      linarith [hs n]
  have hv := aux T
  have hv' : ∑ j ∈ Finset.range (T+1), V j ≤ ∑ j ∈ Finset.range T, C j := by
    apply le_of_mul_le_mul_left (a := a) _ ha
    linarith [mul_nonneg (sub_nonneg.mpr ha') (show 0 ≤ V T from le_max_right _ _)]
  have h := Finset.sum_le_sum (s := Finset.range (T+1))
    (fun j _ => show U j ≤ U 0 + V j by linarith [le_max_left (U j - U 0) 0])
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  linarith

private lemma aggregate (U Q P G : ℕ → ℝ) {a γ ε : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    (hγ : 0 < γ) (hu : ∀ j, 0 ≤ U j) (hq : ∀ j, 0 ≤ Q j) (hp : ∀ j, 0 ≤ P j)
    (hg : ∀ j, 0 ≤ G j) (init : U 0 ≤ ε^2/4)
    (step : ∀ j, U (j+1) ≤ (1-a)^2 * U j + a * (Q (j+1)/4 + ε^2/16 + P j/4))
    (desc : ∀ j, G (j+1) ≤ G j - γ/2 * Q j - γ/4 * P j + γ/2 * U j)
    (T : ℕ) (gap : 2 * G 0 ≤ γ * ((T:ℝ)+1) * ε^2 * (2/5)) :
    ∑ j ∈ Finset.range (T+1), Q j ≤ ((T:ℝ)+1) * (57/60 * ε^2) := by
  have he := error_sum U (fun j => Q (j+1)/4 + ε^2/16 + P j/4) ha ha' hu
    (fun j => by have := hq (j+1); have := hp j; positivity) step T
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at he
  have hqt := Finset.sum_range_succ' Q T
  have hpt := Finset.sum_range_succ P T
  have hui := mul_le_mul_of_nonneg_left init (show 0 ≤ (T:ℝ)+1 by positivity)
  have hub : ∑ j ∈ Finset.range (T+1), U j ≤
      (∑ j ∈ Finset.range (T+1), Q j)/4 + (∑ j ∈ Finset.range (T+1), P j)/4 +
      ((T:ℝ)+1) * (5/16 * ε^2) := by linarith [hq 0, hp T, sq_nonneg ε]
  have hd (n : ℕ) : G n + γ/2 * ∑ j ∈ Finset.range n, Q j +
      γ/4 * ∑ j ∈ Finset.range n, P j ≤ G 0 + γ/2 * ∑ j ∈ Finset.range n, U j := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ]; linarith [desc n]
  apply le_of_mul_le_mul_left (a := γ) _ hγ
  linarith [hd (T+1), hg (T+1), mul_le_mul_of_nonneg_left hub hγ.le,
    mul_nonneg hγ.le (Finset.sum_nonneg (s := Finset.range (T+1)) (fun j _ => hp j))]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma mean_square_sum (H : AffineHyp p F g L Lbar Γ Λ lower) {γ a ε : ℝ} (hγ : 0 < γ)
    (hγL : γ * L ≤ 1/2) (ha : 0 < a) (ha' : a ≤ 1) (haΓ : a * Γ^2 ≤ 1/8)
    (haΛ : a * Λ^2 ≤ ε^2/32) (hc : 4 * (Lbar^2 + L^2) * γ^2 ≤ a/4)
    (b T : ℕ) (x : E) (init : ∫ ξ, ‖batchMean g x ξ b - gradient F x‖^2 ∂P ≤ ε^2/4)
    (gap : 2 * (F x - lower) ≤ γ * ((T:ℝ)+1) * ε^2 * (2/5)) :
    ∑ j ∈ Finset.range (T+1), ∫ ξ, ‖gradient F (momentumPair g γ a b x ξ j).1‖^2 ∂P ≤
      ((T:ℝ)+1) * (57/60 * ε^2) := by
  let U j := ∫ ξ, ‖momentumErr g F γ a b x ξ j‖^2 ∂P
  let Q j := ∫ ξ, ‖gradient F (momentumPair g γ a b x ξ j).1‖^2 ∂P
  let V j := ∫ ξ, ‖(momentumPair g γ a b x ξ j).2‖^2 ∂P
  let G j := ∫ ξ, (F (momentumPair g γ a b x ξ j).1 - lower) ∂P
  have hq j : 0 ≤ Q j := integral_nonneg fun _ => by positivity
  have hv j : 0 ≤ V j := integral_nonneg fun _ => by positivity
  apply aggregate U Q V G ha ha' hγ (fun j => integral_nonneg fun _ => by positivity)
    hq hv (fun j => integral_nonneg fun _ => sub_nonneg.mpr (H.low _)) init _
    (H.mean_descent hγ.le hγL ha.le ha' b x) T
  · change 2 * (∫ _ : ℕ → Ω, (F x - lower) ∂P) ≤ _
    simpa using gap
  · intro j
    have hi := H.integrable_all hγ.le hγL ha.le ha' b x
    have hs := (H.momentum_moment hγ.le ha.le ha' b x j (hi j).1 (hi (j+1)).2.2.1 (hi j).2.2.2).2
    change U (j+1) ≤ (1-a)^2 * U j + (2*a^2*(Γ^2*Q (j+1) + Λ^2) +
      4*(Lbar^2+L^2)*γ^2*V j) at hs
    linarith [mul_le_mul_of_nonneg_right haΓ (mul_nonneg ha.le (hq (j+1))),
      mul_le_mul_of_nonneg_right haΛ ha.le, mul_le_mul_of_nonneg_right hc (hv j)]

end OracleTemplate.RecursiveMomentumGapBatch
