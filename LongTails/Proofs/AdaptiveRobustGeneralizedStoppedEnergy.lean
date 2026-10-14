import LongTails.Proofs.AdaptiveRobustGeneralizedProcess
import LongTails.Proofs.StochasticGeneralizedStoppedEnergy

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.AdaptiveRobustGeneralized

open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight energy)
open StochasticGeneralized (proofActive proofWeight proofWeight_nonneg target firstHalf secondHalf
  step_weights active_nominal_sum_le active_raw_weight_le)

lemma proofTrace_valid (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    0 ≤ (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.A ∧
      0 < (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.guess := by
  induction n with
  | zero => exact ⟨hA, hG⟩
  | succ n ih =>
    rw [blockTrace_succ]
    exact proofNext_valid p hp f u oracle _ _ _ ih.1 ih.2

lemma proofTrace_energy (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (ξ : ℕ → p.Ω) (n : ℕ) :
    energy f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1+
      accumulated (proofCost p f u) (proofNext p f u oracle) (proofDissipation p f u oracle) n s ξ ≤
      energy f u s+accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s ξ := by
  induction n generalizing s ξ with
  | zero => simp [blockTrace, accumulated]
  | succ n ih =>
    rw [blockTrace_start_succ, accumulated, accumulated]
    have hi := ih (proofNext p f u oracle (proofCost p f u s) s (fun i => ξ i))
      (fun i => ξ (proofCost p f u s+i))
    have hs := proofNext_energy p hp hc hg hdiff hH u oracle (proofCost p f u s) s (fun i => ξ i)
    linarith

lemma proofTrace_weight_sum (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) (n : ℕ) :
    accumulated (proofCost p f u) (proofNext p f u oracle) (proofWeight p f u) n s ξ ≤
      32*target p.R p.ε := by
  classical
  let q := blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ
  let a := fun i => tentativeWeight (q i).1
  let w := fun i => proofWeight p f u (proofCost p f u (q i).1) (q i).1 (fun j => (q i).2 j)
  let A := fun i => (q i).1.A
  rw [accumulated_eq_sum]
  have hε := hp.2.2.2.2.2.1
  apply active_nominal_sum_le a w A n (by dsimp [target]; positivity) (fun i _ => proofWeight_nonneg p f u _ _ _) hA ha
  · intro i hi hw
    by_cases hs : proofActive p f u (q i).1
    · exact ⟨by simp only [w, proofWeight, ite_eq_left hs, a], hs.2.2.1.le⟩
    · exact False.elim (hw (by simp only [w, proofWeight, ite_eq_right hs]))
  · intro i hi
    have hv := proofTrace_valid p hp f u oracle s hA hG ξ i
    dsimp only [a, w, A, q]
    rw [blockTrace_succ]
    exact proofNext_weight_recurrence p hp f u oracle _ _ _ hv.1 hv.2

lemma proofTrace_weight_bound (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) (n : ℕ)
    (hAn : (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.A ≤ target p.R p.ε) :
    tentativeWeight (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1 ≤
      22*target p.R p.ε := by
  let q := blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ
  let a := fun i => tentativeWeight (q i).1
  let w := fun i => proofWeight p f u (proofCost p f u (q i).1) (q i).1 (fun j => (q i).2 j)
  let A := fun i => (q i).1.A
  apply active_raw_weight_le a w A n (fun i _ => proofWeight_nonneg p f u _ _ _) hA ha hAn
  intro i hi
  have hv := proofTrace_valid p hp f u oracle s hA hG ξ i
  dsimp only [a, w, A, q]
  rw [blockTrace_succ]
  exact proofNext_weight_recurrence p hp f u oracle _ _ _ hv.1 hv.2

lemma proofTrace_inactive (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hs : ¬proofActive p f u s)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n = (s, ξ) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blockTrace_succ, ih]
    simp [blockAdvance, proofNext, proofCost, hs]

lemma proofTrace_no_energy_crossing (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (oracle : p.E → p.Ω → p.E) (s : Iterate p.E)
    (hinit : energy f u s ≤ p.R^2) (ξ : ℕ → p.Ω) (n : ℕ)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s ξ ≤ 2*p.R^2)
    (i : ℕ) (hi : i ≤ n) :
    energy f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i).1 ≤ 4*p.R^2 := by
  have he := proofTrace_energy p hp hc hg hdiff hH u oracle s ξ n
  have hd := accumulated_nonneg (proofCost p f u) (proofNext p f u oracle)
    (proofDissipation p f u oracle) (proofDissipation_nonneg p hp f u oracle) n s ξ
  have hend : energy f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1 ≤ 3*p.R^2 := by
    linarith
  by_contra h
  have hs : ¬proofActive p f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i).1 :=
    fun hs => h hs.2.2.2.1
  have hfrozen := proofTrace_inactive p f u oracle _ hs
    (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i).2 (n-i)
  rw [← blockTrace_add, Nat.add_sub_of_le hi] at hfrozen
  rw [hfrozen] at hend
  exact h (hend.trans (by nlinarith [sq_nonneg p.R]))

lemma proofTrace_active (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) (n : ℕ)
    (hAn : (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.A < target p.R p.ε)
    (hE : energy f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1 ≤ 4*p.R^2) :
    proofActive p f u (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1 := by
  have hv := proofTrace_valid p hp f u oracle s hA hG ξ n
  have hw := proofTrace_weight_bound p hp f u oracle s hA hG ha ξ n hAn.le
  have hε := hp.2.2.2.2.2.1
  have hT : 0 ≤ target p.R p.ε := by dsimp [target]; positivity
  exact ⟨hv.1, hv.2, hAn, hE, by linarith⟩

lemma proofTrace_dissipation_le (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (oracle : p.E → p.Ω → p.E) (s : Iterate p.E)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) (hinit : energy f u s ≤ p.R^2)
    (ξ : ℕ → p.Ω) (n : ℕ)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u oracle) (proofNoise p f u oracle) n s ξ ≤ 2*p.R^2) :
    accumulated (proofCost p f u) (proofNext p f u oracle) (proofDissipation p f u oracle) n s ξ ≤ 3*p.R^2 := by
  have he := proofTrace_energy p hp hc hg hdiff hH u oracle s ξ n
  have hv := proofTrace_valid p hp f u oracle s hA hG ξ n
  have hn := GeneralizedAccelerated.energy_nonneg hmin _ hv.1
  linarith

lemma proofNext_weight_mono (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) :
    s.A ≤ (proofNext p f u oracle n s ξ).A := by
  classical
  by_cases hs : proofActive p f u s
  · rw [proofNext, ite_eq_left hs]
    exact (step_weights hp.1 hp.2.1 (fun x => guardedReply p f (tentativeWeight s) oracle x (firstHalf ξ))
      (fun x => guardedReply p f (tentativeWeight s) oracle x (secondHalf ξ)) s hs.2.1).1.le
  · simp only [proofNext, ite_eq_right hs, le_refl]

lemma proofTrace_weight_mono (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (ξ : ℕ → p.Ω) :
    Monotone (fun n => (blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ n).1.A) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [blockTrace_succ]
  exact proofNext_weight_mono p hp f u oracle _ _ _

end OracleTemplate.AdaptiveRobustGeneralized
