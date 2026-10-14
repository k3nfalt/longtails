import LongTails.Proofs.RobustGeneralizedCost
import LongTails.Proofs.RobustGeneralizedTuning
import LongTails.Proofs.RobustGeneralizedStoppedEnergy

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight)
open StochasticGeneralized (proofActive proofWeight target blockTrace blockCalls accumulated_eq_sum
  proofWeight_nonneg)

noncomputable def iterationLimit (p : Params) : ℕ :=
  ⌈16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+
    (p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))⌉₊

lemma pilot_power_bound {D δ : ℝ} (hD : 1 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k : ℕ) (hk : 64*Real.log (Real.exp 1*D/δ) ≤ k) :
    (1/2 : ℝ)^k ≤ δ/(524288*D^2) := by
  have hDp : 0 < D := by linarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlog2u : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2l : 1/2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
    linarith
  have hH : Real.log (Real.exp 1*D/δ) = 1+Real.log D-Real.log δ := by
    rw [Real.log_div (by positivity) hδ.ne', Real.log_mul (Real.exp_ne_zero _) hDp.ne', Real.log_exp]
  rw [hH] at hk
  have hK := mul_le_mul_of_nonneg_left hlog2l (show 0 ≤ (k : ℝ) by positivity)
  have hleft : Real.log ((1/2 : ℝ)^k) = -(k : ℝ)*Real.log 2 := by
    rw [Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have hright : Real.log (δ/(524288*D^2)) = Real.log δ-19*Real.log 2-2*Real.log D := by
    rw [Real.log_div hδ.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, show (524288 : ℝ) = 2^19 by norm_num, Real.log_pow]
    norm_num
    ring
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [hleft, hright]
  nlinarith only [hk, hK, hlogD, hlogδ, hlog2u]

lemma pilot_union_bound {D δ : ℝ} (hD : 1 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k N : ℕ) (hk : 64*Real.log (Real.exp 1*D/δ) ≤ k)
    (hN : (N : ℝ) ≤ 131072*D^2) :
    2*(N : ℝ)*(1/2 : ℝ)^k ≤ δ/2 := by
  have h := pilot_power_bound hD hδ hδ1 k hk
  have hDp : 0 < D := by linarith
  calc
    _ ≤ 2*(131072*D^2)*(δ/(524288*D^2)) := by gcongr
    _ = _ := by field_simp; ring

lemma comparison_shape_bound {A q L : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hL : 0 ≤ L) :
    1+Real.sqrt A+L+(q*L)^(2/3 : ℝ) ≤ 7*(1+A+q+L)^2 := by
  let D := 1+A+q+L
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hS : Real.sqrt A ≤ D := by
    have hsq := Real.sq_sqrt hA
    have hn := Real.sqrt_nonneg A
    dsimp [D]
    nlinarith [sq_nonneg A]
  have hqL : q*L ≤ D^2 := by
    have hqD : q+L ≤ D := by dsimp [D]; linarith
    have hs := pow_le_pow_left₀ (show 0 ≤ q+L by linarith) hqD 2
    nlinarith [sq_nonneg (q-L)]
  have hD2 : 1 ≤ D^2 := by nlinarith
  have hpow : (q*L)^(2/3 : ℝ) ≤ D^2 := by
    have h1 := Real.rpow_le_rpow (mul_nonneg hq hL) hqL (by norm_num : (0 : ℝ) ≤ 2/3)
    have h2 := Real.rpow_le_rpow_of_exponent_le hD2 (by norm_num : (2/3 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h2
    exact h1.trans h2
  have hLD : L ≤ D := by dsimp [D]; linarith
  change 1+Real.sqrt A+L+(q*L)^(2/3 : ℝ) ≤ 7*D^2
  nlinarith [sq_nonneg (D-1)]

lemma proofCost_le (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (s : Iterate p.E) (n : ℕ) (ξ : Fin n → p.Ω) :
    (proofCost p f u s : ℝ) ≤ 2*((pilotGroups p : ℝ)+1)+
      (2*1073741824*p.σ^2*(confidence p)^2/p.ε)*proofWeight p f u n s ξ+
      (2*(pilotGroups p : ℝ)*2359296*p.σ^2*(confidence p)^2/p.R^2)*(proofWeight p f u n s ξ)^2 := by
  classical
  by_cases hs : proofActive p f u s
  · have h := estimatorCost_le p hp.2.2.1 hp.2.2.2.2.2.1
      (GeneralizedAccelerated.tentativeWeight_pos s hs.2.1)
      (lt_trans zero_lt_one (StochasticGeneralized.confidence_log_gt_one
        hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2))
    simp only [proofCost, proofWeight, ite_eq_left hs, Nat.cast_mul, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · simp only [proofCost, proofWeight, ite_eq_right hs, Nat.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    positivity

lemma proofCalls_le (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) (n : ℕ) :
    (blockCalls (proofCost p f u) (proofNext p f u oracle) s ξ n : ℝ) ≤
      2*((pilotGroups p : ℝ)+1)*n+
        (1099511627776+1236950581248*(pilotGroups p : ℝ))*(p.σ^2*p.R^2*(confidence p)^2/p.ε^2) := by
  let q := blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ
  let m := fun i => proofCost p f u (q i).1
  let a := fun i => proofWeight p f u (m i) (q i).1 (fun j => (q i).2 j)
  have hw := proofTrace_weight_sum p hp f u oracle s hA hG ha ξ n
  rw [accumulated_eq_sum] at hw
  have hε := hp.2.2.2.2.2.1
  have hR := hp.2.2.1
  have h := weighted_calls_le m a n
    (show 0 ≤ 2*1073741824*p.σ^2*(confidence p)^2/p.ε by positivity)
    (show 0 ≤ 2*(pilotGroups p : ℝ)*2359296*p.σ^2*(confidence p)^2/p.R^2 by positivity)
    (fun i _ => proofWeight_nonneg p f u _ _ _)
    (fun i _ => proofCost_le p hp f u (q i).1 (m i) (fun j => (q i).2 j)) hw
  change (blockCalls (proofCost p f u) (proofNext p f u oracle) s ξ n : ℝ) ≤ _ at h
  apply h.trans_eq
  dsimp [target]
  field_simp; ring

noncomputable def shape (p : Params) : ℝ :=
  1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+
    (p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ)

noncomputable def comparisonScale (p : Params) : ℝ :=
  1+p.L0*p.R^2/p.ε+p.L1*p.R+Real.log (4+4*p.Δ/p.ε)

noncomputable def logScale (p : Params) : ℝ := Real.log (Real.exp 1*comparisonScale p/p.δ)

lemma comparisonScale_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ comparisonScale p := by
  have hL0 := hp.1
  have hL1 := hp.2.1
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  dsimp [comparisonScale]
  linarith [show 0 ≤ p.L0*p.R^2/p.ε by positivity,
    show 0 ≤ p.L1*p.R by positivity,
    Real.log_nonneg (show 1 ≤ 4+4*p.Δ/p.ε by linarith [show 0 ≤ 4*p.Δ/p.ε by positivity])]

lemma logScale_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ logScale p := by
  have hD := comparisonScale_ge_one p hp
  have hδ := hp.2.2.2.2.2.2.1
  have hδ1 := hp.2.2.2.2.2.2.2
  have hb : Real.exp 1 ≤ Real.exp 1*comparisonScale p/p.δ := by
    apply (le_div_iff₀ hδ).mpr
    gcongr
    linarith
  have h := Real.log_le_log (Real.exp_pos 1) hb
  simpa only [Real.log_exp, logScale] using h

lemma shape_ge_one (p : Params) (hp : spec.valid p) : 1 ≤ shape p := by
  have hε := hp.2.2.2.2.2.1
  have hΔ := hp.2.2.2.1
  have hL1 := hp.2.1
  have hR := hp.2.2.1
  have hlog : 0 ≤ Real.log (4+4*p.Δ/p.ε) := Real.log_nonneg (by linarith [show 0 ≤ 4*p.Δ/p.ε by positivity])
  have hrpow : 0 ≤ (p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ) := by positivity
  dsimp [shape]
  linarith [Real.sqrt_nonneg (p.L0*p.R^2/p.ε)]

lemma iterationLimit_le (p : Params) (hp : spec.valid p) :
    (iterationLimit p : ℝ) ≤ 16385*shape p := by
  have hW := shape_ge_one p hp
  have h := Nat.ceil_lt_add_one (show 0 ≤ 16384*shape p by positivity)
  change (iterationLimit p : ℝ) < 16384*shape p+1 at h
  linarith

lemma pilotGroups_bounds (p : Params) (hp : spec.valid p) :
    64*logScale p ≤ (pilotGroups p : ℝ) ∧ (pilotGroups p : ℝ) ≤ 65*logScale p := by
  have hH := logScale_ge_one p hp
  constructor
  · exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  · have h := StochasticGeneralized.rounded_batch_le (show 0 ≤ 64*logScale p by positivity)
    change (pilotGroups p : ℝ) ≤ 1+64*logScale p at h
    linarith

lemma iterationLimit_comparison (p : Params) (hp : spec.valid p) :
    (iterationLimit p : ℝ) ≤ 131072*(comparisonScale p)^2 := by
  have hD := comparisonScale_ge_one p hp
  have hL0 := hp.1
  have hL1 := hp.2.1
  have hR := hp.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hΔ := hp.2.2.2.1
  have hL : 0 ≤ Real.log (4+4*p.Δ/p.ε) :=
    Real.log_nonneg (by linarith [show 0 ≤ 4*p.Δ/p.ε by positivity])
  have h := comparison_shape_bound (show 0 ≤ p.L0*p.R^2/p.ε by positivity)
    (show 0 ≤ p.L1*p.R by positivity) hL
  have hW : shape p ≤ 7*(comparisonScale p)^2 := by
    simpa only [shape, comparisonScale, mul_div_assoc] using h
  have hN := iterationLimit_le p hp
  nlinarith [sq_nonneg (comparisonScale p)]

lemma total_pilot_failure_le (p : Params) (hp : spec.valid p) :
    (iterationLimit p : ℝ)*(2*(1/2 : ℝ)^(pilotGroups p)) ≤ p.δ/2 := by
  have h := pilot_union_bound (comparisonScale_ge_one p hp) hp.2.2.2.2.2.2.1
    hp.2.2.2.2.2.2.2.le (pilotGroups p) (iterationLimit p)
    (pilotGroups_bounds p hp).1 (iterationLimit_comparison p hp)
  nlinarith only [h]

lemma calls_public_bound (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) :
    (blockCalls (proofCost p f u) (proofNext p f u oracle) s ξ (iterationLimit p) : ℝ) ≤
      (4194304*shape p+140737488355328*(p.σ^2*p.R^2*(confidence p)^2/p.ε^2))*logScale p := by
  apply (proofCalls_le p hp f u oracle s hA hG ha ξ (iterationLimit p)).trans
  exact public_cost_bound (by positivity) (logScale_ge_one p hp)
    ((by norm_num : (0 : ℝ) ≤ 1).trans (shape_ge_one p hp)) (by positivity)
    (pilotGroups_bounds p hp).2 (iterationLimit_le p hp)

lemma public_budget_ge (p : Params) :
    (4194304*shape p+140737488355328*(p.σ^2*p.R^2*(confidence p)^2/p.ε^2))*logScale p ≤
      (⌈(2^22*(1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))+2^47*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)^2/p.ε^2)*Real.log (Real.exp 1*(1+p.L0*p.R^2/p.ε+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)⌉₊ : ℝ) := by
  have h := Nat.le_ceil ((2^22*(1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+
    (p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))+2^47*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)^2/p.ε^2)*
      Real.log (Real.exp 1*(1+p.L0*p.R^2/p.ε+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ))
  apply le_trans (le_of_eq ?_) h
  dsimp [shape, confidence, logScale, comparisonScale]
  rw [show (2 : ℝ)^22 = 4194304 by norm_num, show (2 : ℝ)^47 = 140737488355328 by norm_num]
  ring

end OracleTemplate.RobustGeneralized
