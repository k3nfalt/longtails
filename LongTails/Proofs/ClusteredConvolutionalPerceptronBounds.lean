import LongTails.Proofs.ClusteredConvolutionalPerceptronDynamics
import LongTails.Proofs.ManySampleConvolutionalPerceptronConstants

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronBounds

open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronDynamics
open ClusteredConvolutionalPerceptronStability
open ManySampleConvolutionalPerceptronConstants

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c : Control} {b : ι → ℝ} {p r : ι → E}
    {x : ℕ → State E} {T : ℕ → ℝ} {i : ℕ → ι} {K : ℕ}

lemma time_mono (G : Geometry c b p r) (tr : Trajectory c b p r x T i K)
    {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ K) : T j ≤ T k := by
  have h : ∀ k, j ≤ k → k ≤ K → T j ≤ T k := by
    intro k hj
    induction k, hj using Nat.le_induction with
    | base => intro _; rfl
    | succ k _ ih =>
      intro hk
      have hi := ih (by omega)
      have hs := (trajectory_invariant G tr k (by omega)).signal
      rw [tr.time_update k (by omega)]
      linarith
  exact h k hjk hk

lemma time_lower (G : Geometry c b p r) (tr : Trajectory c b p r x T i K) :
    ∀ k, k ≤ K → (k : ℝ) ≤ T k := by
  intro k
  induction k with
  | zero => intro _; rw [tr.time_zero]; norm_num
  | succ k ih =>
    intro hk
    have hi := ih (by omega)
    have hs := (trajectory_invariant G tr k (by omega)).signal
    rw [tr.time_update k (by omega), Nat.cast_add, Nat.cast_one]
    linarith

lemma mass_decay (G : Geometry c b p r) (tr : Trajectory c b p r x T i K) :
    ∀ k, k ≤ K → mass (x k) ≤
      2 * c.C * (1 - c.ρ ^ 2 / 2) ^ (k / 2) +
        (12 * (c.C + c.e) / c.ρ ^ 2) * (c.δ * T k) := by
  have hr : 0 ≤ 1 - c.ρ ^ 2 / 2 := by nlinarith [c.rho_pos, c.rho_le]
  have hF : 0 ≤ c.C + c.e := add_nonneg c.C_pos.le c.e_nonneg
  have hB : 0 ≤ 12 * (c.C + c.e) / c.ρ ^ 2 := by positivity
  apply two_step_moving_bound hr hB
    (fun j k hjk hk => mul_le_mul_of_nonneg_left (time_mono G tr hjk hk) c.delta_pos.le)
  · rw [tr.initial, tr.time_zero]
    simp [mass, abs_of_pos c.C_pos]
    linarith
  · intro hk
    have h := (trajectory_invariant G tr 1 hk).mass_bound
    have ht : (x 1).t = 1 := by rw [tr.update 0 (by omega), tr.initial]; simp [step]
    rw [ht] at h
    have hn := mul_nonneg hB (mul_nonneg c.delta_pos.le
      (trajectory_invariant G tr 1 hk).time_nonneg)
    linarith
  · intro k hk
    have h0 := trajectory_invariant G tr k (by omega)
    have h1 := trajectory_invariant G tr (k + 1) (by omega)
    have hs := trajectory_mass_two_step G tr hk h0 h1
    have hf0 := mul_le_mul_of_nonneg_left (h0.plus (i k)) c.delta_pos.le
    have hf1 := mul_le_mul_of_nonneg_left (h1.plus (i (k + 1))) c.delta_pos.le
    have hm0 := mul_le_mul_of_nonneg_left (time_mono G tr (show k ≤ k + 2 by omega) hk)
      (mul_nonneg c.delta_pos.le hF)
    have hm1 := mul_le_mul_of_nonneg_left
      (time_mono G tr (show k + 1 ≤ k + 2 by omega) hk) (mul_nonneg c.delta_pos.le hF)
    have he : (1 - (1 - c.ρ ^ 2 / 2)) * (12 * (c.C + c.e) / c.ρ ^ 2) =
        6 * (c.C + c.e) := by field_simp [ne_of_gt c.rho_pos]; ring
    rw [he]
    rw [abs_mul, abs_of_pos c.delta_pos, abs_mul, abs_of_pos c.delta_pos] at hs
    nlinarith

lemma terminal_decay {ρ δ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) :
    (1 - ρ ^ 2 / 2) ^ ((⌈8 / ρ ^ 2 * Real.log (1 / δ)⌉₊ + 2) / 2) ≤ δ ^ 2 := by
  apply burnin_decay hρ hρ1 hδ
  have h := burnin_half (8 / ρ ^ 2 * Real.log (1 / δ))
  convert h using 1
  ring

lemma terminal_mass_gap {δ h L A B W t S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W) (ht : 1 ≤ t) (hS : 1 ≤ S)
    (hforce : δ * S ≤ L * t) (hinit : 2 * A ^ 2 ≤ h)
    (hnoise : B ^ 2 * L ≤ h) (hbound : W ≤ A * δ ^ 2 + B * δ * S) :
    W ^ 2 / 4 < δ * h * t * S := by
  have ht0 : 0 ≤ t := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hsum : 0 ≤ A * δ ^ 2 + B * δ * S := by positivity
  have hsq : W ^ 2 ≤ (A * δ ^ 2 + B * δ * S) ^ 2 := by nlinarith
  have hsplit : W ^ 2 ≤ 2 * A ^ 2 * δ ^ 4 + 2 * B ^ 2 * δ ^ 2 * S ^ 2 := by
    nlinarith [sq_nonneg (A * δ ^ 2 - B * δ * S)]
  have h3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h4 : δ ^ 4 ≤ δ := by
    have hm := mul_le_mul_of_nonneg_left h3 hδ.le
    nlinarith
  have hfirst1 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * A ^ 2 by positivity)
  have hfirst2 := mul_le_mul_of_nonneg_right hinit hδ.le
  have htS : 1 ≤ t * S := by nlinarith
  have hfirst3 := mul_le_mul_of_nonneg_left htS (mul_nonneg hδ.le hh.le)
  have hf := mul_le_mul_of_nonneg_left hforce (mul_nonneg hδ.le hS0)
  have hf' := mul_le_mul_of_nonneg_left hf (sq_nonneg B)
  have hn := mul_le_mul_of_nonneg_right hnoise (show 0 ≤ δ * t * S by positivity)
  have hpos : 0 < δ * h * t * S := by positivity
  nlinarith

lemma terminal_separates (G : Geometry c b p r) (tr : Trajectory c b p r x T i K)
    (hK : K = ⌈8 / c.ρ ^ 2 * Real.log (1 / c.δ)⌉₊ + 2)
    (hδ1 : c.δ ≤ 1) (hinit : 8 * c.C ^ 2 ≤ c.h)
    (hnoise : (12 * (c.C + c.e) / c.ρ ^ 2) ^ 2 * c.L ≤ c.h) :
    ∀ j, 0 < b j * (x K).a * (x K).q +
      c.δ * ((x K).a * ⟪p j, (x K).z⟫ + (x K).t * ⟪r j, (x K).z⟫) := by
  have inv := trajectory_invariant G tr K le_rfl
  have hd := mass_decay G tr K le_rfl
  have hdec : (1 - c.ρ ^ 2 / 2) ^ (K / 2) ≤ c.δ ^ 2 := by
    rw [hK]; exact terminal_decay c.rho_pos c.rho_le c.delta_pos
  have hmul := mul_le_mul_of_nonneg_left hdec
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) c.C_pos.le)
  have hforce := lorentz_forcing c.delta_pos.le c.h_pos c.L_nonneg
    (by linarith [inv.signal]) c.forcing_small inv.lorentz
  have hT : 1 ≤ T K := by
    have htime := time_lower G tr K le_rfl
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    linarith
  have hF : 0 ≤ c.C + c.e := add_nonneg c.C_pos.le c.e_nonneg
  have hgap := terminal_mass_gap c.delta_pos hδ1 c.h_pos
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) c.C_pos.le)
    (show 0 ≤ 12 * (c.C + c.e) / c.ρ ^ 2 by positivity)
    (show 0 ≤ mass (x K) by unfold mass; positivity) inv.signal hT hforce
    (show 2 * (2 * c.C) ^ 2 ≤ c.h by nlinarith) hnoise
    (show mass (x K) ≤ 2 * c.C * c.δ ^ 2 +
      (12 * (c.C + c.e) / c.ρ ^ 2) * c.δ * T K by nlinarith)
  intro j
  have hprod := mass_controls_product (x K).a (x K).q
  change |(x K).a * (x K).q| ≤ mass (x K) ^ 2 / 4 at hprod
  have hbprod : |b j * ((x K).a * (x K).q)| ≤ mass (x K) ^ 2 / 4 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right (G.background_upper j)
      (abs_nonneg ((x K).a * (x K).q))
    nlinarith
  have hn := neg_le_abs (b j * ((x K).a * (x K).q))
  have hm := mul_le_mul_of_nonneg_left (inv.margin j) c.delta_pos.le
  nlinarith

end LongTails.Proofs.ClusteredConvolutionalPerceptronBounds
