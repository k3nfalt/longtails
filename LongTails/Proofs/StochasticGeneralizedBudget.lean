import LongTails.Proofs.StochasticGeneralizedStoppedEnergy

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight energy)

lemma initial_valid (p : Params) (hp : spec.valid p) :
    0 ≤ (initialIterate p.L0 p.R p.Δ p.ε p.x0).A ∧
      0 < (initialIterate p.L0 p.R p.Δ p.ε p.x0).guess := by
  have hΔ := hp.2.2.2.1
  exact ⟨by dsimp [initialIterate]; positivity, lt_of_lt_of_le hp.1 (le_max_left _ _)⟩

lemma initial_weight_bound (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ) :
    tentativeWeight (initialIterate p.L0 p.R p.Δ p.ε p.x0) ≤ 2*target p.R p.ε := by
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hv := initial_valid p hp
  apply initial_weight_le (by dsimp [target]; positivity) ?_ (le_max_right _ _)
    (GeneralizedAccelerated.tentativeWeight_pos _ hv.2)
    (GeneralizedAccelerated.tentativeWeight_equation _ hv.1 hv.2)
  change p.R^2/(2*p.Δ) ≤ 16*p.R^2/p.ε
  apply (div_le_div_iff₀ (by positivity) hε).mpr
  have hm := mul_le_mul_of_nonneg_left hεΔ.le (sq_nonneg p.R)
  nlinarith [mul_nonneg (sq_nonneg p.R) hΔ.le]

lemma initial_energy_bound (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (u : p.E) (hdist : ‖p.x0-u‖ ≤ p.R) (hgap : f p.x0-f u ≤ p.Δ) :
    energy f u (initialIterate p.L0 p.R p.Δ p.ε p.x0) ≤ p.R^2 :=
  GeneralizedAccelerated.initial_energy (g := gradient f) (L0 := p.L0) (L1 := p.L1)
    hp.2.2.2.1 p.x0 u hdist hgap

lemma proofCost_le (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (s : Iterate p.E) (n : ℕ) (ξ : Fin n → p.Ω) :
    (proofCost p f u s : ℝ) ≤ 2+
      2*(1048576*p.σ^2*Real.log (Real.exp 1/p.δ)/p.ε)*proofWeight p f u n s ξ := by
  classical
  by_cases hs : proofActive p f u s
  · have ha := (GeneralizedAccelerated.tentativeWeight_pos s hs.2.1).le
    have hε := hp.2.2.2.2.2.1
    have hℓ := (confidence_log_gt_one hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2).le
    have hr : 0 ≤ 1048576*p.σ^2*tentativeWeight s*Real.log (Real.exp 1/p.δ)/p.ε := by positivity
    have hm := rounded_batch_le hr
    simp only [proofCost, proofWeight, ite_eq_left hs, Nat.cast_mul, Nat.cast_ofNat]
    change 2*(batchSize p.σ p.ε p.δ s : ℝ) ≤ _
    dsimp only [batchSize] at *
    calc
      _ ≤ 2*(1+1048576*p.σ^2*tentativeWeight s*Real.log (Real.exp 1/p.δ)/p.ε) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by ring
  · simp only [proofCost, proofWeight, ite_eq_right hs, Nat.cast_zero, mul_zero, add_zero]
    norm_num

lemma proofCalls_le (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) (n : ℕ) :
    (blockCalls (proofCost p f u) (proofNext p f u oracle) s ξ n : ℝ) ≤
      2*n+1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2 := by
  let C := 1048576*p.σ^2*Real.log (Real.exp 1/p.δ)/p.ε
  have hε := hp.2.2.2.2.2.1
  have hℓ := (confidence_log_gt_one hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw := proofTrace_weight_sum p hp f u oracle s hA hG ha ξ n
  rw [accumulated_eq_sum] at hw
  have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*C by positivity)
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    proofCost_le p hp f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i).1
      (proofCost p f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i).1)
      (fun j => (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i).2 j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hs
  have he : 2*C*(32*target p.R p.ε) =
      1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2 := by
    dsimp [C, target]
    field_simp; ring
  rw [he] at hm
  dsimp only [blockCalls]
  push_cast
  linarith only [hs, hm]

end OracleTemplate.StochasticGeneralized
