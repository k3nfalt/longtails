import LongTails.Proofs.AdaptiveRobustGeneralizedCost
import LongTails.Proofs.AdaptiveRobustGeneralizedTuning
import LongTails.Proofs.AdaptiveRobustGeneralizedStoppedEnergy
import LongTails.Proofs.AdaptiveRobustGeneralizedFailures
import LongTails.Proofs.StochasticGeneralizedCounting

namespace OracleTemplate.AdaptiveRobustGeneralized

open GeneralizedAccelerated (Iterate tentativeWeight coupling)
open StochasticGeneralized (proofActive proofWeight target blockTrace blockCalls accumulated_eq_sum
  proofWeight_nonneg)

noncomputable def iterationLimit (p : Params) : ℕ :=
  ⌈16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+
    (p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))⌉₊

noncomputable def shape (p : Params) : ℝ :=
  1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+
    (p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ)

noncomputable def comparisonScale (p : Params) : ℝ :=
  1+p.L0*p.R^2/p.ε+p.L1*p.R+Real.log (4+4*p.Δ/p.ε)

noncomputable def iterationScale (p : Params) : ℝ := 16385*shape p

noncomputable def pilotMass (p : Params) : ℝ :=
  1099511627776*(p.σ^2*p.R^2/p.ε^2)*(confidence p)^2/Real.sqrt (1+p.L0*p.R^2/p.ε)

noncomputable def charge (p : Params) : ℝ :=
  min 1 ((pilotMass p+iterationScale p*Real.exp (-28*level p))/iterationScale p)

noncomputable def callBound (p : Params) : ℝ :=
  116*iterationScale p+1099511627776*(p.σ^2*p.R^2/p.ε^2)*confidence p+
    156*level p*pilotMass p+
    112*level p*iterationScale p/Real.log (Real.exp 1+iterationScale p/
      (pilotMass p+iterationScale p*Real.exp (-28*level p)))

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

lemma level_eq (p : Params) : level p = Real.log (Real.exp 1*comparisonScale p/p.δ) := rfl

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
    (iterationLimit p : ℝ) ≤ iterationScale p := by
  have hW := shape_ge_one p hp
  have h := Nat.ceil_lt_add_one (show 0 ≤ 16384*shape p by positivity)
  change (iterationLimit p : ℝ) < 16384*shape p+1 at h
  dsimp [iterationScale]
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
  dsimp [iterationScale] at hN
  nlinarith [sq_nonneg (comparisonScale p)]

lemma total_pilot_failure_le (p : Params) (hp : spec.valid p) :
    (iterationLimit p : ℝ)*(2*Real.exp (-14*level p)) ≤ p.δ/2 := by
  have hD := comparisonScale_ge_one p hp
  have hδ := hp.2.2.2.2.2.2.1
  have hδ1 := hp.2.2.2.2.2.2.2
  have hN := iterationLimit_comparison p hp
  have hDp : 0 < comparisonScale p := by linarith
  have hx : 0 < Real.exp 1*comparisonScale p/p.δ := by positivity
  have hx1 : Real.exp 1 ≤ Real.exp 1*comparisonScale p/p.δ := by
    rw [le_div_iff₀ hδ]
    have := Real.exp_pos 1
    nlinarith
  have he : Real.exp (-14*level p) = (p.δ/(Real.exp 1*comparisonScale p))^14 := by
    rw [level_eq, show -14*Real.log (Real.exp 1*comparisonScale p/p.δ) =
      ((14 : ℕ) : ℝ)*Real.log ((Real.exp 1*comparisonScale p/p.δ)⁻¹) by
        rw [Real.log_inv]; push_cast; ring, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hx), inv_div]
  rw [he, div_pow, mul_pow]
  have he14 : (2 : ℝ)^20 ≤ (Real.exp 1)^14 := by
    have h := Real.exp_one_gt_d9
    calc (2 : ℝ)^20 ≤ (2.7 : ℝ)^14 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by linarith) 14
  have hδ14 : p.δ^14 ≤ p.δ := pow_le_of_le_one hδ.le hδ1.le (by norm_num)
  have hD14 : (comparisonScale p)^2 ≤ (comparisonScale p)^14 := pow_le_pow_right₀ hD (by norm_num)
  have hN0 : (0 : ℝ) ≤ (iterationLimit p : ℝ) := by positivity
  calc
    _ ≤ 131072*(comparisonScale p)^2*(2*(p.δ/((2 : ℝ)^20*(comparisonScale p)^14))) := by
      gcongr
    _ = p.δ/4*((comparisonScale p)^2/(comparisonScale p)^14) := by field_simp; ring
    _ ≤ p.δ/4*1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hD14) (by positivity)
    _ ≤ _ := by linarith


noncomputable def weightCap (p : Params) : ℝ := 725*(p.R^2/p.ε)/Real.sqrt (1+p.L0*p.R^2/p.ε)

lemma proofNext_guess_ge (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω)
    (hG : p.L0 ≤ s.guess) : p.L0 ≤ (proofNext p f u oracle n s ξ).guess := by
  classical
  have hL0 := hp.1
  have hL1 := hp.2.1
  by_cases hs : proofActive p f u s
  · rw [proofNext, ite_eq_left hs, guardedStep, StochasticGeneralized.step_guess]
    split_ifs with h
    · have hn := norm_nonneg (guardedReply p f (tentativeWeight s) oracle (coupling s)
        (StochasticGeneralized.firstHalf ξ))
      nlinarith [mul_nonneg hL1 hn]
    · linarith
  · simpa only [proofNext, ite_eq_right hs] using hG

lemma proofTrace_guess_ge (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hG : p.L0 ≤ s.guess) (ξ : ℕ → p.Ω) (n : ℕ) :
    p.L0 ≤ (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.guess := by
  induction n with
  | zero => exact hG
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ]
    exact proofNext_guess_ge p hp f u oracle _ _ _ ih

lemma active_weight_le_cap (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (s : Iterate p.E) (hs : proofActive p f u s) (hG : p.L0 ≤ s.guess) :
    tentativeWeight s ≤ weightCap p := by
  have hL0 := hp.1
  have hR := hp.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hA := hs.1
  have hguess := hs.2.1
  have hAT := hs.2.2.1
  have haT := hs.2.2.2.2
  have ha := GeneralizedAccelerated.tentativeWeight_pos s hguess
  have heq := GeneralizedAccelerated.tentativeWeight_equation s hA hguess
  have hT : target p.R p.ε = 16*p.R^2/p.ε := rfl
  let a := tentativeWeight s
  let Q := p.R^2/p.ε
  have hQ : 0 < Q := by positivity
  have h1 : a ≤ 512*Q := by
    have : a ≤ 32*target p.R p.ε := haT
    rw [hT] at this
    dsimp [Q]
    linarith [show 32*(16*p.R^2/p.ε) = 512*(p.R^2/p.ε) by ring]
  have h2 : p.L0*a^2 ≤ 528*Q := by
    have hg : p.L0*a^2 ≤ s.guess*a^2 := mul_le_mul_of_nonneg_right hG (sq_nonneg a)
    have : s.guess*a^2 = s.A+a := heq
    have hAT' : s.A ≤ 16*Q := by rw [hT] at hAT; dsimp [Q]; linarith [show 16*p.R^2/p.ε = 16*(p.R^2/p.ε) by ring]
    linarith
  have hsq : a^2*(1+p.L0*p.R^2/p.ε) ≤ (725*Q)^2 := by
    have h1' : a^2 ≤ (512*Q)^2 := pow_le_pow_left₀ ha.le h1 2
    have h2' : a^2*(p.L0*p.R^2/p.ε) ≤ 528*Q^2 := by
      have : a^2*(p.L0*p.R^2/p.ε) = (p.L0*a^2)*Q := by dsimp [Q]; ring
      rw [this]
      nlinarith
    nlinarith
  have hS : 0 < Real.sqrt (1+p.L0*p.R^2/p.ε) := Real.sqrt_pos.mpr (by positivity)
  unfold weightCap
  change a ≤ 725*Q/Real.sqrt (1+p.L0*p.R^2/p.ε)
  rw [le_div_iff₀ hS]
  have hss := Real.sq_sqrt (show 0 ≤ 1+p.L0*p.R^2/p.ε by positivity)
  have hprod : 0 ≤ a*Real.sqrt (1+p.L0*p.R^2/p.ε) := by positivity
  nlinarith [sq_nonneg (a*Real.sqrt (1+p.L0*p.R^2/p.ε)-725*Q)]

lemma proofCost_le (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (s : Iterate p.E) (n : ℕ) (ξ : Fin n → p.Ω) :
    (proofCost p f u s : ℝ) ≤
      2*(2+28*level p*(1/Real.log (4/τ))*(1+Real.exp (-28*level p)/τ))+
      (2*(1073741824*p.σ^2*confidence p/p.ε))*proofWeight p f u n s ξ+
      (2*((28*level p*(1/Real.log (4/τ))/τ+22*level p)*
        (2359296*p.σ^2*(confidence p)^2/p.R^2)))*(proofWeight p f u n s ξ)^2 := by
  classical
  have hL := level_ge_one p hp
  have hlt := log_four_div_ge hτ hτ1
  by_cases hs : proofActive p f u s
  · have h := estimatorCost_le p hp.2.2.1 hp.2.2.2.2.2.1
      (GeneralizedAccelerated.tentativeWeight_pos s hs.2.1)
      (lt_trans zero_lt_one (StochasticGeneralized.confidence_log_gt_one
        hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2)) hL hτ hτ1
    simp only [proofCost, proofWeight, ite_eq_left hs, Nat.cast_mul, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · simp only [proofCost, proofWeight, ite_eq_right hs, Nat.cast_zero, mul_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero]
    positivity

lemma proofCalls_le (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hG0 : p.L0 ≤ s.guess) (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) (n : ℕ)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (blockCalls (proofCost p f u) (proofNext p f u oracle) s ξ n : ℝ) ≤
      2*(2+28*level p*(1/Real.log (4/τ))*(1+Real.exp (-28*level p)/τ))*n+
      (2*(1073741824*p.σ^2*confidence p/p.ε))*(32*target p.R p.ε)+
      (2*((28*level p*(1/Real.log (4/τ))/τ+22*level p)*
        (2359296*p.σ^2*(confidence p)^2/p.R^2)))*(weightCap p*(32*target p.R p.ε)) := by
  classical
  let q := blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ
  let m := fun i => proofCost p f u (q i).1
  let a := fun i => proofWeight p f u (m i) (q i).1 (fun j => (q i).2 j)
  have hw := proofTrace_weight_sum p hp f u oracle s hA hG ha ξ n
  rw [accumulated_eq_sum] at hw
  have hε := hp.2.2.2.2.2.1
  have hR := hp.2.2.1
  have hL := level_ge_one p hp
  have hlt := log_four_div_ge hτ hτ1
  have hcap : 0 ≤ weightCap p := by unfold weightCap; positivity
  have hmax : ∀ i < n, a i ≤ weightCap p := by
    intro i _
    by_cases hs : proofActive p f u (q i).1
    · simp only [a, proofWeight, ite_eq_left hs]
      exact active_weight_le_cap p hp f u _ hs (proofTrace_guess_ge p hp f u oracle s hG0 ξ i)
    · simp only [a, proofWeight, ite_eq_right hs]
      exact hcap
  have h := weighted_calls_le m a n
    (show 0 ≤ 2*(1073741824*p.σ^2*confidence p/p.ε) by
      have := StochasticGeneralized.confidence_log_gt_one hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2
      unfold confidence; positivity)
    (show 0 ≤ 2*((28*level p*(1/Real.log (4/τ))/τ+22*level p)*
        (2359296*p.σ^2*(confidence p)^2/p.R^2)) by
      have : 0 < Real.log (4/τ) := by linarith
      positivity)
    (fun i _ => proofWeight_nonneg p f u _ _ _) hmax
    (fun i _ => proofCost_le p hp f u hτ hτ1 (q i).1 (m i) (fun j => (q i).2 j)) hw hcap
  exact h

lemma log_charge_ge {Q : ℝ} (hQ : 0 < Q) :
    Real.log (Real.exp 1+1/Q) ≤ Real.log (4/min 1 Q) := by
  have he := Real.exp_one_lt_d9
  apply Real.log_le_log (by positivity)
  rcases le_total Q 1 with h | h
  · rw [min_eq_right h]
    rw [show 4/Q = 3/Q+1/Q by ring]
    have : Real.exp 1 ≤ 3/Q := by
      rw [le_div_iff₀ hQ]; nlinarith
    linarith
  · rw [min_eq_left h]
    have : 1/Q ≤ 1 := by rw [div_le_one hQ]; exact h
    linarith

lemma charged_total_le (p : Params) (hp : spec.valid p) {N X : ℝ}
     (hN : N ≤ iterationScale p) (hX : X ≤ pilotMass p)
    {C : ℝ} (hC : C = 1099511627776*(p.σ^2*p.R^2/p.ε^2)*confidence p) :
    2*(2+28*level p*(1/Real.log (4/charge p))*(1+Real.exp (-28*level p)/charge p))*N+C+
      2*((28*level p*(1/Real.log (4/charge p))/charge p+22*level p))*X ≤ callBound p := by
  have hL := level_ge_one p hp
  have hNp : 0 < iterationScale p := by
    have := shape_ge_one p hp; unfold iterationScale; positivity
  have hPm : 0 ≤ pilotMass p := by unfold pilotMass; positivity
  have he28 : 0 < Real.exp (-28*level p) := Real.exp_pos _
  have hLe : level p*Real.exp (-28*level p) ≤ 1 := by
    have h := Real.add_one_le_exp (28*level p)
    have h2 : Real.exp (-28*level p)*Real.exp (28*level p) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (28*level p)]
  let Np := iterationScale p
  let Xp := pilotMass p
  let e := Real.exp (-28*level p)
  let Q := (Xp+Np*e)/Np
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hτ : 0 < charge p := lt_min one_pos hQ
  have hτ1 : charge p ≤ 1 := min_le_left _ _
  have hlt := log_four_div_ge hτ hτ1
  let φ := 1/Real.log (4/charge p)
  have hφ0 : 0 ≤ φ := by dsimp [φ]; positivity
  have hφ1 : φ ≤ 1 := by dsimp [φ]; rw [div_le_one (by linarith)]; exact hlt
  have hcore : 28*level p*φ*(N+(N*e+X)/charge p) ≤
      56*level p*Np*φ+56*level p*Xp+56*Np := by
    have hmono : N+(N*e+X)/charge p ≤ Np+(Np*e+Xp)/charge p := by
      have : N*e+X ≤ Np*e+Xp := by nlinarith
      have := div_le_div_of_nonneg_right this hτ.le
      linarith
    have hb := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 28*level p*φ by positivity)
    apply hb.trans
    rcases le_total Q 1 with h | h
    · have hc : charge p = Q := min_eq_right h
      rw [hc]
      have hXN : 0 < Xp+Np*e := by positivity
      have : (Np*e+Xp)/Q = Np := by
        show (Np*e+Xp)/((Xp+Np*e)/Np) = Np
        rw [show Np*e+Xp = Xp+Np*e by ring]
        field_simp
      rw [this]
      nlinarith [mul_nonneg (show 0 ≤ level p by linarith) hPm]
    · have hc : charge p = 1 := min_eq_left h
      rw [hc, div_one]
      have hNQ : Np ≤ Np*e+Xp := by
        have := (le_div_iff₀ hNp).mp (show 1 ≤ (Xp+Np*e)/Np from h)
        linarith
      have hX' : 28*level p*φ*(Np+(Np*e+Xp)) ≤ 28*level p*(2*(Np*e+Xp)) := by
        have := mul_le_mul_of_nonneg_left hφ1 (show 0 ≤ 28*level p by linarith)
        have h2 : 0 ≤ Np+(Np*e+Xp) := by positivity
        calc _ ≤ 28*level p*1*(Np+(Np*e+Xp)) := mul_le_mul_of_nonneg_right this h2
          _ ≤ _ := by nlinarith
      have hLeNp : level p*(Np*e) ≤ Np := by
        have := mul_le_mul_of_nonneg_left hLe hNp.le
        nlinarith
      nlinarith [mul_nonneg (show 0 ≤ level p by linarith) hPm, mul_nonneg hNp.le hφ0,
        mul_nonneg (show 0 ≤ level p by linarith) (mul_nonneg hNp.le hφ0)]
  have hφbound : Np*φ ≤ Np/Real.log (Real.exp 1+Np/(Xp+Np*e)) := by
    have hlog := log_charge_ge hQ
    have hpos : 0 < Real.log (Real.exp 1+1/Q) :=
      Real.log_pos (by
        have h1 := Real.exp_one_gt_d9
        have h2 : 0 < 1/Q := by positivity
        linarith)
    have h1Q : 1/Q = Np/(Xp+Np*e) := by
      show 1/((Xp+Np*e)/Np) = Np/(Xp+Np*e)
      rw [one_div_div]
    rw [← h1Q]
    dsimp [φ]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hNp.le hpos hlog
  have hsplit : 2*(2+28*level p*φ*(1+e/charge p))*N+C+
      2*((28*level p*φ/charge p+22*level p))*X =
      4*N+2*(28*level p*φ*(N+(N*e+X)/charge p))+C+44*level p*X := by
    field_simp
    ring
  change 2*(2+28*level p*φ*(1+e/charge p))*N+C+
      2*((28*level p*φ/charge p+22*level p))*X ≤ _
  rw [hsplit]
  unfold callBound
  change _ ≤ 116*Np+1099511627776*(p.σ^2*p.R^2/p.ε^2)*confidence p+156*level p*Xp+
    112*level p*Np/Real.log (Real.exp 1+Np/(Xp+Np*e))
  rw [← hC]
  have hXX : 44*level p*X ≤ 44*level p*Xp := by
    apply mul_le_mul_of_nonneg_left hX; linarith
  have hφb := mul_le_mul_of_nonneg_left hφbound (show 0 ≤ 112*level p by linarith)
  have hNN : 4*N ≤ 4*Np := by linarith
  have hfinal : 112*level p*(Np/Real.log (Real.exp 1+Np/(Xp+Np*e))) =
      112*level p*Np/Real.log (Real.exp 1+Np/(Xp+Np*e)) := by ring
  nlinarith [hcore, hφb]

end OracleTemplate.AdaptiveRobustGeneralized
