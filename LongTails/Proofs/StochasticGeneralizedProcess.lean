import LongTails.Proofs.StochasticGeneralizedOracle
import LongTails.Proofs.StochasticGeneralizedConcentration
import LongTails.Proofs.StochasticGeneralizedTuning
import LongTails.Proofs.StochasticGeneralizedDynamics
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling energy)

noncomputable def proofActive (p : Params) (f : p.E → ℝ) (u : p.E) (s : Iterate p.E) : Prop :=
  0 ≤ s.A ∧ 0 < s.guess ∧ s.A < target p.R p.ε ∧
    energy f u s ≤ 4*p.R^2 ∧ tentativeWeight s ≤ 32*target p.R p.ε

noncomputable def proofCost (p : Params) (f : p.E → ℝ) (u : p.E) (s : Iterate p.E) : ℕ := by
  classical
  exact if proofActive p f u s then 2*batchSize p.σ p.ε p.δ s else 0

noncomputable def proofNext (p : Params) (f : p.E → ℝ) (u : p.E) (oracle : p.E → p.Ω → p.E)
    (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : Iterate p.E := by
  classical
  exact if proofActive p f u s then prefixStep p.L0 p.L1 oracle s ξ else s

noncomputable def batchNoise (p : Params) (f : p.E → ℝ) (u : p.E) (oracle : p.E → p.Ω → p.E)
    (s : Iterate p.E) {m : ℕ} (ξ ζ : Fin m → p.Ω) : ℝ :=
  let a := tentativeWeight s
  let y := coupling s
  let v := batchReply oracle y ξ
  let pending := prepare p.L0 p.L1 s v
  let h := batchReply oracle pending.point ζ
  let b := s.guess/pending.curvature*a
  let e₁ := gradient f y-v
  let e₂ := h-gradient f pending.point
  (-b)*⟪e₂, s.z-u⟫+8*a^2*‖e₁‖^2+6*a^2*‖e₂‖^2

noncomputable def proofNoise (p : Params) (f : p.E → ℝ) (u : p.E) (oracle : p.E → p.Ω → p.E)
    (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if proofActive p f u s then batchNoise p f u oracle s (firstHalf ξ) (secondHalf ξ) else 0

noncomputable def proofWeight (p : Params) (f : p.E → ℝ) (u : p.E)
    (n : ℕ) (s : Iterate p.E) (_ : Fin n → p.Ω) : ℝ := by
  classical
  exact if proofActive p f u s then tentativeWeight s else 0

noncomputable def proofIncrement (p : Params) (f : p.E → ℝ) (u : p.E) (oracle : p.E → p.Ω → p.E)
    (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : ℝ :=
  let ℓ := Real.log (Real.exp 1/p.δ)
  let t := ℓ/p.R^2
  let η := p.ε/(32768*ℓ)
  t*proofNoise p f u oracle n s ξ-(14*t*η+32*t^2*η*p.R^2)*proofWeight p f u n s ξ

lemma measurableSet_proofActive (p : Params) {f : p.E → ℝ} (hf : Measurable f) (u : p.E) :
    MeasurableSet {s | proofActive p f u s} := by
  unfold proofActive
  exact (measurableSet_le measurable_const measurable_iterate_A).inter
    ((measurableSet_lt measurable_const measurable_iterate_guess).inter
      ((measurableSet_lt measurable_iterate_A measurable_const).inter
        ((measurableSet_le (measurable_energy hf u) measurable_const).inter
          (measurableSet_le measurable_tentativeWeight measurable_const))))

lemma measurable_proofCost (p : Params) {f : p.E → ℝ} (hf : Measurable f) (u : p.E) :
    Measurable (proofCost p f u) := by
  unfold proofCost
  exact Measurable.ite (measurableSet_proofActive p hf u) (by fun_prop) measurable_const

lemma measurable_firstHalf {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    Measurable (@firstHalf Ω n) := by
  unfold firstHalf
  fun_prop

lemma measurable_secondHalf {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    Measurable (@secondHalf Ω n) := by
  unfold secondHalf
  fun_prop

lemma measurable_prefixStep (p : Params) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : Iterate p.E × (Fin n → p.Ω) => prefixStep p.L0 p.L1 oracle w.1 w.2) := by
  have hfirst := measurable_firstHalf (Ω := p.Ω) n
  have hsecond := measurable_secondHalf (Ω := p.Ω) n
  have hbatch := measurable_batchReply hg (n/2)
  unfold prefixStep
  fun_prop

lemma measurable_proofNext (p : Params) {f : p.E → ℝ} (hf : Measurable f) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofNext p f u oracle n)) := by
  unfold proofNext Function.uncurry
  exact Measurable.ite ((measurableSet_proofActive p hf u).preimage measurable_fst)
    (measurable_prefixStep p hg n) measurable_fst

lemma measurable_proofWeight (p : Params) {f : p.E → ℝ} (hf : Measurable f) (u : p.E) (n : ℕ) :
    Measurable (Function.uncurry (proofWeight p f u n)) := by
  unfold proofWeight Function.uncurry
  exact Measurable.ite ((measurableSet_proofActive p hf u).preimage measurable_fst)
    (measurable_tentativeWeight.comp measurable_fst) measurable_const

lemma measurable_proofNoise (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofNoise p f u oracle n)) := by
  have hfirst := measurable_firstHalf (Ω := p.Ω) n
  have hsecond := measurable_secondHalf (Ω := p.Ω) n
  have hbatch := measurable_batchReply hg (n/2)
  unfold proofNoise Function.uncurry batchNoise
  apply Measurable.ite ((measurableSet_proofActive p hf u).preimage measurable_fst)
  · dsimp only
    fun_prop
  · exact measurable_const

lemma measurable_proofIncrement (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofIncrement p f u oracle n)) := by
  exact ((measurable_proofNoise p hf hgrad u hg n).const_mul _).sub
    ((measurable_proofWeight p hf u n).const_mul _)

lemma halves_preserving (p : Params) (μ : Measure p.Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ))
      (Measure.pi fun _ : Fin n => μ)
      ((Measure.pi fun _ : Fin (n/2) => μ).prod (Measure.pi fun _ : Fin (n/2) => μ)) := by
  have hfirst := measurable_firstHalf (Ω := p.Ω) n
  have hsecond := measurable_secondHalf (Ω := p.Ω) n
  refine ⟨hfirst.prodMk hsecond, ?_⟩
  rw [← (prefix_preserving μ n).map_eq, Measure.map_map (hfirst.prodMk hsecond) (by fun_prop)]
  exact (two_blocks_preserving μ (n/2)).map_eq

lemma active_distance_bound (p : Params) {f : p.E → ℝ} {u : p.E}
    (hmin : IsMinOn f Set.univ u) (s : Iterate p.E) (hs : proofActive p f u s) :
    ‖s.z-u‖^2 ≤ 8*p.R^2 := by
  have hf : 0 ≤ f s.x-f u := sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hp := mul_nonneg hs.1 hf
  have he := hs.2.2.2.1
  dsimp [energy] at he
  linarith

lemma batchNoise_exp_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f Set.univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : IsLightTailGradient p.E p.Ω μ f oracle p.σ)
    (s : Iterate p.E) (hs : proofActive p f u s) (m : ℕ) (hm : 0 < m)
    (hscale : 32*p.σ^2/m ≤ (p.ε/(32768*Real.log (Real.exp 1/p.δ)))/tentativeWeight s) :
    let ℓ := Real.log (Real.exp 1/p.δ)
    let t := ℓ/p.R^2
    let η := p.ε/(32768*ℓ)
    Integrable (fun w : (Fin m → p.Ω) × (Fin m → p.Ω) => Real.exp (t*batchNoise p f u oracle s w.1 w.2))
      ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) ∧
      (∫ w : (Fin m → p.Ω) × (Fin m → p.Ω), Real.exp (t*batchNoise p f u oracle s w.1 w.2)
        ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))) ≤
        Real.exp ((14*t*η+32*t^2*η*p.R^2)*tentativeWeight s) := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  let ℓ := Real.log (Real.exp 1/p.δ)
  let t := ℓ/p.R^2
  let η := p.ε/(32768*ℓ)
  let a := tentativeWeight s
  let v := η/a
  have hℓ : 0 < ℓ := lt_trans zero_lt_one (confidence_log_gt_one hδ hδ1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have ha : 0 < a := GeneralizedAccelerated.tentativeWeight_pos s hs.2.1
  have hv : 0 < v := div_pos hη ha
  have hsqrt : (Real.sqrt v)^2 = v := Real.sq_sqrt hv.le
  let r : (Fin m → p.Ω) → Pending p.E := fun ξ =>
    prepare p.L0 p.L1 s (batchReply oracle (coupling s) ξ)
  let X : (Fin m → p.Ω) → p.E := fun ξ => gradient f (coupling s)-batchReply oracle (coupling s) ξ
  let Y : (Fin m → p.Ω) × (Fin m → p.Ω) → p.E := fun w =>
    batchReply oracle (r w.1).point w.2-gradient f (r w.1).point
  let b : (Fin m → p.Ω) → ℝ := fun ξ => s.guess/(r ξ).curvature*a
  have hbatch := measurable_batchReply hg.measurable m
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hb : Measurable b := by dsimp [b]; fun_prop
  have hcontrol (x : p.E) := batchReply_control hg hσ x m hm hscale
  have hiX : Integrable (fun ξ => Real.exp (‖X ξ‖^2/(Real.sqrt v)^2))
      (Measure.pi fun _ : Fin m => μ) := by
    simpa only [X, hsqrt, norm_sub_rev] using (hcontrol (coupling s)).2.2.1
  have heX : (∫ ξ, Real.exp (‖X ξ‖^2/(Real.sqrt v)^2)
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ Real.exp 1 := by
    simpa only [X, hsqrt, norm_sub_rev] using (hcontrol (coupling s)).2.2.2
  have hiY (ξ : Fin m → p.Ω) : Integrable (fun ζ => Y (ξ, ζ))
      (Measure.pi fun _ : Fin m => μ) := by
    dsimp only [Y]
    exact (hcontrol (r ξ).point).1.sub (integrable_const _)
  have hzY (ξ : Fin m → p.Ω) : (∫ ζ, Y (ξ, ζ) ∂Measure.pi (fun _ : Fin m => μ)) = 0 := by
    dsimp [Y]
    rw [integral_sub (hcontrol (r ξ).point).1 (integrable_const _), (hcontrol (r ξ).point).2.1]
    simp
  have hiYexp (ξ : Fin m → p.Ω) : Integrable (fun ζ => Real.exp (‖Y (ξ, ζ)‖^2/(Real.sqrt v)^2))
      (Measure.pi fun _ : Fin m => μ) := by
    simpa only [Y, hsqrt] using (hcontrol (r ξ).point).2.2.1
  have heY (ξ : Fin m → p.Ω) : (∫ ζ, Real.exp (‖Y (ξ, ζ)‖^2/(Real.sqrt v)^2)
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ Real.exp 1 := by
    simpa only [Y, hsqrt] using (hcontrol (r ξ).point).2.2.2
  have hba (ξ : Fin m → p.Ω) : (b ξ)^2 ≤ a^2 := by
    have hd := prepare_damping hL0 hL1 s (batchReply oracle (coupling s) ξ) hs.2.1
    have hb0 : 0 ≤ b ξ := mul_nonneg hd.1.le ha.le
    exact pow_le_pow_left₀ hb0 (mul_le_of_le_one_left ha.le hd.2) 2
  have hvprod : a^2*v = η*a := by dsimp [v]; field_simp
  have hsmall : 12*t*a^2*(Real.sqrt v)^2 ≤ 1 := by
    rw [hsqrt]
    have he : 12*t*a^2*v = 12*t*η*a := by
      calc
        _ = 12*t*(a^2*v) := by ring
        _ = _ := by rw [hvprod]; ring
    rw [he]
    exact tuning_small hR hε hℓ hs.2.2.2.2
  have h := noise_exp_control (Real.sqrt_pos.mpr hv) ht.le hsmall hX hY hb hba
    hiX heX hiY hzY hiYexp heY (s.z-u)
  have hnorm := active_distance_bound p hmin s hs
  have hm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 4*t^2*η*a by positivity)
  have hexponent : 14*t*a^2*(Real.sqrt v)^2+4*t^2*a^2*(Real.sqrt v)^2*‖s.z-u‖^2 ≤
      (14*t*η+32*t^2*η*p.R^2)*a := by
    rw [hsqrt]
    calc
      _ = 14*t*(a^2*v)+4*t^2*(a^2*v)*‖s.z-u‖^2 := by ring
      _ = 14*t*(η*a)+4*t^2*(η*a)*‖s.z-u‖^2 := by rw [hvprod]
      _ ≤ _ := by nlinarith only [hm]
  refine ⟨?_, ?_⟩
  · simpa only [batchNoise, X, Y, b, r, a] using h.1
  · have hh := h.2.trans (Real.exp_le_exp.mpr hexponent)
    simpa only [batchNoise, X, Y, b, r, a] using hh

lemma proofIncrement_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f Set.univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : IsLightTailGradient p.E p.Ω μ f oracle p.σ)
    (s : Iterate p.E) :
    Integrable (fun ξ => Real.exp (proofIncrement p f u oracle (proofCost p f u s) s ξ))
      (Measure.pi fun _ : Fin (proofCost p f u s) => μ) ∧
      (∫ ξ, Real.exp (proofIncrement p f u oracle (proofCost p f u s) s ξ)
        ∂Measure.pi (fun _ : Fin (proofCost p f u s) => μ)) ≤ 1 := by
  classical
  by_cases hs : proofActive p f u s
  · let n := proofCost p f u s
    let m := n/2
    let ℓ := Real.log (Real.exp 1/p.δ)
    let t := ℓ/p.R^2
    let η := p.ε/(32768*ℓ)
    let C := (14*t*η+32*t^2*η*p.R^2)*tentativeWeight s
    have hmEq : m = batchSize p.σ p.ε p.δ s := by
      dsimp [m, n, proofCost]
      rw [ite_eq_left hs]
      omega
    have hm : 0 < m := by rw [hmEq]; exact batchSize_pos p.σ p.ε p.δ s
    have hscale : 32*p.σ^2/m ≤ (p.ε/(32768*Real.log (Real.exp 1/p.δ)))/tentativeWeight s := by
      rw [hmEq]
      exact batchSize_noise_scale hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2 s hs.2.1
    have h := batchNoise_exp_control p hp hgrad u hmin hg s hs m hm hscale
    let F : (Fin m → p.Ω) × (Fin m → p.Ω) → ℝ :=
      fun w => Real.exp (t*batchNoise p f u oracle s w.1 w.2-C)
    have heF : F = fun w => Real.exp (-C)*Real.exp (t*batchNoise p f u oracle s w.1 w.2) := by
      ext w
      dsimp [F]
      rw [← Real.exp_add]
      congr 1
      ring
    have hiF : Integrable F ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) := by
      rw [heF]
      exact h.1.const_mul _
    have hbF : (∫ w, F w ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))) ≤ 1 := by
      rw [heF, integral_const_mul]
      have hh := mul_le_mul_of_nonneg_left h.2 (Real.exp_nonneg (-C))
      simpa only [C, t, η, ℓ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using hh
    have hsplit := halves_preserving p μ n
    have hl : HasLaw (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ))
        ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
        (Measure.pi fun _ : Fin n => μ) := ⟨hsplit.measurable.aemeasurable, hsplit.map_eq⟩
    have he : (fun ξ : Fin n → p.Ω => Real.exp (proofIncrement p f u oracle n s ξ)) =
        F ∘ (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ)) := by
      ext ξ
      simp only [proofIncrement, proofNoise, proofWeight, ite_eq_left hs]
      rfl
    change Integrable (fun ξ : Fin n → p.Ω => Real.exp (proofIncrement p f u oracle n s ξ)) _ ∧ _
    rw [he]
    refine ⟨hl.integrable_comp hiF, ?_⟩
    rw [hl.integral_comp hiF.aestronglyMeasurable]
    exact hbF
  · simp only [proofIncrement, proofNoise, proofWeight, ite_eq_right hs, mul_zero, sub_zero, Real.exp_zero]
    exact ⟨integrable_const 1, by simp⟩

lemma proof_accumulated_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hf : Measurable f) (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f Set.univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : IsLightTailGradient p.E p.Ω μ f oracle p.σ)
    (k : ℕ) (s : Iterate p.E) :
    Integrable (fun ξ => Real.exp (accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofIncrement p f u oracle) k s ξ)) (Measure.infinitePi fun _ : ℕ => μ) ∧
      (∫ ξ, Real.exp (accumulated (proofCost p f u) (proofNext p f u oracle)
        (proofIncrement p f u oracle) k s ξ) ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ 1 := by
  exact accumulated_exp_control μ (measurable_proofCost p hf u)
    (measurable_proofNext p hf u hg.measurable) (measurable_proofIncrement p hf hgrad u hg.measurable)
    (fun s => (proofIncrement_control p hp hgrad u hmin hg s).1)
    (fun s => (proofIncrement_control p hp hgrad u hmin hg s).2) k s

end OracleTemplate.StochasticGeneralized
