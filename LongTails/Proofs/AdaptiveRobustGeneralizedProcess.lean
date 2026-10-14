import LongTails.Proofs.AdaptiveRobustGeneralizedOracle
import LongTails.Proofs.StochasticGeneralizedProcess

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.AdaptiveRobustGeneralized

open GeneralizedAccelerated (Iterate tentativeWeight coupling energy)
open StochasticGeneralized (proofActive proofWeight target prepare step dissipation noiseIncrement)

noncomputable def proofCost (p : Params) (f : p.E → ℝ) (u : p.E) (s : Iterate p.E) : ℕ := by
  classical
  exact if proofActive p f u s then 2*estimatorCost p (tentativeWeight s) else 0

noncomputable def guardedStep (p : Params) (f : p.E → ℝ) (oracle : p.E → p.Ω → p.E)
    (s : Iterate p.E) {n : ℕ} (ξ : Fin n → p.Ω) : Iterate p.E :=
  step p.L0 p.L1
    (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ))
    (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.secondHalf ξ)) s

noncomputable def proofNext (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : Iterate p.E := by
  classical
  exact if proofActive p f u s then guardedStep p f oracle s ξ else s

noncomputable def batchNoise (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) {m : ℕ} (ξ ζ : Fin m → p.Ω) : ℝ :=
  let a := tentativeWeight s
  let y := coupling s
  let v := guardedReply p f a oracle y ξ
  let pending := prepare p.L0 p.L1 s v
  let h := guardedReply p f a oracle pending.point ζ
  let b := s.guess/pending.curvature*a
  (-b)*⟪h-gradient f pending.point, s.z-u⟫+
    8*a^2*‖gradient f y-v‖^2+6*a^2*‖h-gradient f pending.point‖^2

noncomputable def proofNoise (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if proofActive p f u s then
    batchNoise p f u oracle s (StochasticGeneralized.firstHalf ξ) (StochasticGeneralized.secondHalf ξ) else 0

noncomputable def proofDissipation (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if proofActive p f u s then dissipation p.L0 p.L1
    (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ)) s else 0

noncomputable def proofIncrement (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : ℝ :=
  (confidence p/p.R^2)*proofNoise p f u oracle n s ξ-
    (confidence p*p.ε/(1048576*p.R^2))*proofWeight p f u n s ξ

lemma proofNext_valid (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    0 ≤ (proofNext p f u oracle n s ξ).A ∧ 0 < (proofNext p f u oracle n s ξ).guess := by
  classical
  by_cases hs : proofActive p f u s
  · rw [proofNext, ite_eq_left hs]
    have h := StochasticGeneralized.step_weights hp.1 hp.2.1
      (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ))
      (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.secondHalf ξ)) s hG
    exact ⟨hA.trans h.1.le, h.2.2⟩
  · simpa only [proofNext, ite_eq_right hs] using And.intro hA hG

lemma proofNext_weight_recurrence (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    tentativeWeight (proofNext p f u oracle n s ξ) ≤ tentativeWeight s-
      11/16*proofWeight p f u n s ξ+20*((proofNext p f u oracle n s ξ).A-s.A) := by
  classical
  by_cases hs : proofActive p f u s
  · simp only [proofNext, proofWeight, ite_eq_left hs]
    have h := StochasticGeneralized.step_nominal_recurrence hp.1 hp.2.1
      (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ))
      (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.secondHalf ξ)) s hA hG
    change tentativeWeight (guardedStep p f oracle s ξ) ≤
      5/16*tentativeWeight s+20*((guardedStep p f oracle s ξ).A-s.A) at h
    linarith
  · simp only [proofNext, proofWeight, ite_eq_right hs, mul_zero, sub_zero, sub_self, add_zero, le_refl]

lemma proofDissipation_nonneg (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) :
    0 ≤ proofDissipation p f u oracle n s ξ := by
  classical
  by_cases hs : proofActive p f u s
  · simpa only [proofDissipation, ite_eq_left hs] using
      StochasticGeneralized.dissipation_nonneg hp.1 hp.2.1
        (fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ)) s hs.1 hs.2.1
  · simp only [proofDissipation, ite_eq_right hs, le_refl]

lemma proofNext_energy (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) :
    energy f u (proofNext p f u oracle n s ξ)+proofDissipation p f u oracle n s ξ ≤
      energy f u s+proofNoise p f u oracle n s ξ := by
  classical
  by_cases hs : proofActive p f u s
  · simp only [proofNext, proofDissipation, proofNoise, ite_eq_left hs]
    let v := fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ)
    let h := fun x => guardedReply p f (tentativeWeight s) oracle x (StochasticGeneralized.secondHalf ξ)
    have he := StochasticGeneralized.step_energy hp.1 hp.2.1 hc hg hdiff hH v h u s hs.1 hs.2.1
    have hd := StochasticGeneralized.prepare_damping hp.1 hp.2.1 s (v (coupling s)) hs.2.1
    have ha := GeneralizedAccelerated.tentativeWeight_pos s hs.2.1
    have hb : (s.guess/(prepare p.L0 p.L1 s (v (coupling s))).curvature*tentativeWeight s)^2 ≤
        (tentativeWeight s)^2 :=
      pow_le_pow_left₀ (mul_nonneg hd.1.le ha.le) (mul_le_of_le_one_left ha.le hd.2) 2
    have hn : noiseIncrement p.L0 p.L1 (gradient f) v h u s ≤
        batchNoise p f u oracle s (StochasticGeneralized.firstHalf ξ) (StochasticGeneralized.secondHalf ξ) := by
      have h₁ := mul_le_mul_of_nonneg_right hb
        (show 0 ≤ 8*‖gradient f (coupling s)-v (coupling s)‖^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right hb
        (show 0 ≤ 6*‖h (prepare p.L0 p.L1 s (v (coupling s))).point-
          gradient f (prepare p.L0 p.L1 s (v (coupling s))).point‖^2 by positivity)
      dsimp [noiseIncrement, batchNoise, prepare, v, h] at *
      nlinarith only [h₁, h₂]
    exact he.trans (add_le_add le_rfl hn)
  · simp only [proofNext, proofDissipation, proofNoise, ite_eq_right hs, add_zero, le_refl]

lemma measurable_proofCost (p : Params) {f : p.E → ℝ} (hf : Measurable f) (u : p.E) :
    Measurable (proofCost p f u) := by
  unfold proofCost
  exact Measurable.ite (StochasticGeneralized.measurableSet_proofActive p hf u)
    ((measurable_const.mul ((measurable_estimatorCost p).comp
      StochasticGeneralized.measurable_tentativeWeight))) measurable_const

lemma measurable_guardedStep (p : Params) {f : p.E → ℝ}
    (hgrad : Measurable (gradient f)) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : Iterate p.E × (Fin n → p.Ω) => guardedStep p f oracle w.1 w.2) := by
  have hfirst := StochasticGeneralized.measurable_firstHalf (Ω := p.Ω) n
  have hsecond := StochasticGeneralized.measurable_secondHalf (Ω := p.Ω) n
  have hbatch := measurable_guardedReply p hgrad hg (n/2)
  unfold guardedStep step
  fun_prop

lemma measurable_proofNext (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofNext p f u oracle n)) := by
  unfold proofNext Function.uncurry
  exact Measurable.ite
    ((StochasticGeneralized.measurableSet_proofActive p hf u).preimage measurable_fst)
    (measurable_guardedStep p hgrad hg n) measurable_fst

lemma measurable_proofNoise (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofNoise p f u oracle n)) := by
  have hfirst := StochasticGeneralized.measurable_firstHalf (Ω := p.Ω) n
  have hsecond := StochasticGeneralized.measurable_secondHalf (Ω := p.Ω) n
  have hbatch := measurable_guardedReply p hgrad hg (n/2)
  unfold proofNoise Function.uncurry batchNoise
  apply Measurable.ite
    ((StochasticGeneralized.measurableSet_proofActive p hf u).preimage measurable_fst)
  · dsimp only
    fun_prop
  · exact measurable_const

lemma measurable_proofIncrement (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofIncrement p f u oracle n)) := by
  exact ((measurable_proofNoise p hf hgrad u hg n).const_mul _).sub
    ((StochasticGeneralized.measurable_proofWeight p hf u n).const_mul _)

end OracleTemplate.AdaptiveRobustGeneralized
