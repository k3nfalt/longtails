import LongTails.Proofs.AdaptiveRobustGeneralizedCoupling
import LongTails.Proofs.AdaptiveRobustGeneralizedTrace
import LongTails.Proofs.AdaptiveRobustGeneralizedTerminal
import LongTails.Proofs.StochasticGeneralizedCap

open MeasureTheory ProbabilityTheory Set

namespace OracleTemplate.AdaptiveRobustGeneralized

open GeneralizedAccelerated (Iterate energy tentativeWeight)
open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma pilot_mass_le (p : Params) (hp : spec.valid p) :
    (2359296*p.σ^2*(confidence p)^2/p.R^2)*(weightCap p*(32*target p.R p.ε)) ≤ pilotMass p := by
  have hR := hp.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hL0 := hp.1
  have hS : 0 < Real.sqrt (1+p.L0*p.R^2/p.ε) := Real.sqrt_pos.mpr (by positivity)
  unfold weightCap pilotMass target
  have he : (2359296*p.σ^2*(confidence p)^2/p.R^2)*
      (725*(p.R^2/p.ε)/Real.sqrt (1+p.L0*p.R^2/p.ε)*(32*(16*p.R^2/p.ε))) =
      875770675200*(p.σ^2*p.R^2/p.ε^2)*(confidence p)^2/Real.sqrt (1+p.L0*p.R^2/p.ε) := by
    field_simp
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hS.le
  have : 0 ≤ (p.σ^2*p.R^2/p.ε^2)*(confidence p)^2 := by positivity
  nlinarith

lemma calls_callBound (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hG0 : p.L0 ≤ s.guess) (ha : tentativeWeight s ≤ 2*target p.R p.ε) (ξ : ℕ → p.Ω) :
    (blockCalls (proofCost p f u) (proofNext p f u oracle) s ξ (iterationLimit p) : ℝ) ≤
      callBound p := by
  have hR := hp.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hNp : 0 < iterationScale p := by
    have := shape_ge_one p hp; unfold iterationScale; positivity
  have hPm : 0 ≤ pilotMass p := by unfold pilotMass; positivity
  have hτ : 0 < charge p := lt_min one_pos (by positivity)
  have hτ1 : charge p ≤ 1 := min_le_left _ _
  have h := proofCalls_le p hp f u oracle s hA hG hG0 ha ξ (iterationLimit p) hτ hτ1
  apply h.trans
  have hX := pilot_mass_le p hp
  have hX0 : 0 ≤ (2359296*p.σ^2*(confidence p)^2/p.R^2)*(weightCap p*(32*target p.R p.ε)) := by
    unfold weightCap target; positivity
  have hb := charged_total_le p hp (N := (iterationLimit p : ℝ))
    (iterationLimit_le p hp) hX
    (C := (2*(1073741824*p.σ^2*confidence p/p.ε))*(32*target p.R p.ε))
    (by unfold target; field_simp; ring)
  apply le_trans (le_of_eq _) hb
  ring

lemma proofTrace_reaches_target (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    {f : p.E → ℝ} (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (hdist : ‖p.x0-u‖ ≤ p.R) (hgap : f p.x0-f u ≤ p.Δ)
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (N : ℕ)
    (hN : 16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
      min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))) ≤ N)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u g) (proofNoise p f u g) N
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ ≤ 2*p.R^2) :
    target p.R p.ε ≤ (blockTrace (proofCost p f u) (proofNext p f u g)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ N).1.A := by
  by_contra hT
  have hv := initial_valid p hp
  have hw := initial_weight_bound p hp hεΔ
  have he := initial_energy_bound p hp u hdist hgap
  have ht := trace_run_before_target p hp hc hg hdiff hH u hmin g _ hv.1 hv.2 hw he ξ N hnoise (lt_of_not_ge hT)
  have hb := run_target_min p hp hεΔ (traceFirst p f u g _ ξ) (traceSecond p f u g _ ξ) N hN ht.2
  rw [ht.1] at hb
  exact hT hb

lemma execute_trivial (p : Params) (P : ProbabilityMeasure (ℕ → p.Ω))
    (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (hεΔ : p.Δ ≤ p.ε) (K : ℕ) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm p) (fun _ => K) () ξ = p.x0 := by
  classical
  erw [StochasticGradient.execute_advance]
  change (algorithm p).output (rawAdvance p g ξ K 0 ((algorithm p).initial ())) = _
  have hi : (algorithm p).initial () = .done (initialIterate p.L0 p.R p.Δ p.ε p.x0) := by
    simp only [algorithm, ite_eq_left hεΔ]
  rw [hi, rawAdvance_done]
  rfl


lemma iterationLimit_suffices (p : Params) :
    16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
      min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε))
        (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))) ≤ iterationLimit p := by
  calc
    _ ≤ 16384*shape p := by
      dsimp [shape]
      have h := min_le_right ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε))
        (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))
      linarith
    _ ≤ _ := Nat.le_ceil _

lemma execute_accuracy_of_good (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    {f : p.E → ℝ} (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (hdist : ‖p.x0-u‖ ≤ p.R) (hgap : f p.x0-f u ≤ p.Δ)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (K : ℕ)
    (hK : callBound p ≤ K)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u g) (proofNoise p f u g) (iterationLimit p)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ ≤ 2*p.R^2)
    (hfailure : accumulated (proofCost p f u) (proofNext p f u g) (proofFailure p f u g) (iterationLimit p)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ < 1) :
    f (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm p) (fun _ => K) () ξ)-f u ≤ p.ε := by
  have hT := proofTrace_reaches_target p hp hεΔ hc hg hdiff hH u hmin hdist hgap g ξ
    (iterationLimit p) (iterationLimit_suffices p) hnoise
  have hv := initial_valid p hp
  have hw := initial_weight_bound p hp hεΔ
  have he := initial_energy_bound p hp u hdist hgap
  have hcalls := calls_callBound p hp f u g _ hv.1 hv.2 (le_max_left _ _) hw ξ
  have hcallK : blockCalls (proofCost p f u) (proofNext p f u g)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ (iterationLimit p) ≤ K := by
    exact_mod_cast hcalls.trans hK
  have hgood := proofFailure_zero_of_accumulated_lt p f u g _ ξ (iterationLimit p) hfailure
  erw [execute_after_target p P f u g ξ hεΔ (iterationLimit p) K hgood hcallK hT]
  exact proofTrace_target_accuracy p hp hc hg hdiff hH u hmin g _ he ξ (iterationLimit p) hnoise hT

lemma execution_high_probability (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (hdist : ‖p.x0-u‖ ≤ p.R) (hgap : f p.x0-f u ≤ p.Δ)
    (μ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : IID (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (P : Measure _))
    {g : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω (μ : Measure _) f g p.σ) (K : ℕ)
    (hK : callBound p ≤ K) :
    ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) |
      p.ε < f (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm p) (fun _ => K) w.1 w.2)-f u} ≤ ENNReal.ofReal p.δ := by
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hgrad : Measurable (gradient f) := hdiff.continuous.measurable
  by_cases hεΔ : p.Δ ≤ p.ε
  · have hempty : {w : Unit × (ℕ → p.Ω) |
        p.ε < f (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm p) (fun _ => K) w.1 w.2)-f u} = ∅ := by
      ext w
      rcases w with ⟨⟨⟩, ξ⟩
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      erw [execute_trivial p P g ξ hεΔ K]
      exact not_lt_of_ge (hgap.trans hεΔ)
    rw [hempty, measure_empty]
    exact bot_le
  · have hεΔ' := lt_of_not_ge hεΔ
    let s := initialIterate p.L0 p.R p.Δ p.ε p.x0
    let Z := accumulated (proofCost p f u) (proofNext p f u g) (proofNoise p f u g) (iterationLimit p) s
    let F := accumulated (proofCost p f u) (proofNext p f u g) (proofFailure p f u g) (iterationLimit p) s
    have hv := initial_valid p hp
    have hw := initial_weight_bound p hp hεΔ'
    have hZ := proofNoise_accumulated_measurable p hf hgrad u ho.measurable (iterationLimit p) s
    have hF := proofFailure_accumulated_measurable p hf hgrad u ho.measurable (iterationLimit p) s
    have ht := proofNoise_tail_iid p hp hf hgrad u hmin ho hIID (iterationLimit p) s hv.1 hv.2 hw
    have hft := (proofFailure_tail_iid p hp hf hgrad u ho hIID (iterationLimit p) s).trans
      (ENNReal.ofReal_le_ofReal (total_pilot_failure_le p hp))
    have hsnd : HasLaw (Prod.snd : Unit × (ℕ → p.Ω) → ℕ → p.Ω) (P : Measure _)
        ((Measure.dirac ()).prod (P : Measure _)) :=
      ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
    calc
      _ ≤ ((Measure.dirac ()).prod (P : Measure _))
          ({w : Unit × (ℕ → p.Ω) | 2*p.R^2 < Z w.2} ∪ {w | 1 ≤ F w.2}) := by
        apply measure_mono
        rintro ⟨⟨⟩, ξ⟩ hfail
        by_contra hn
        have hn' : ¬2*p.R^2 < Z ξ ∧ ¬1 ≤ F ξ := by simpa only [mem_union, mem_ofPred_eq, not_or] using hn
        have hacc := execute_accuracy_of_good p hp hεΔ' hc hg hdiff hH u hmin hdist hgap P g ξ K hK
          (le_of_not_gt hn'.1) (lt_of_not_ge hn'.2)
        exact not_lt_of_ge hacc hfail
      _ ≤ ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) | 2*p.R^2 < Z w.2}+
          ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) | 1 ≤ F w.2} := measure_union_le _ _
      _ = (P : Measure _) {ξ | 2*p.R^2 < Z ξ}+(P : Measure _) {ξ | 1 ≤ F ξ} := by
        rw [hsnd.measure_eq (measurableSet_lt measurable_const hZ),
          hsnd.measure_eq (measurableSet_le measurable_const hF)]
      _ ≤ ENNReal.ofReal (p.δ/2)+ENNReal.ofReal (p.δ/2) := add_le_add ht hft
      _ = ENNReal.ofReal p.δ := by
        rw [← ENNReal.ofReal_add (by have h := hp.2.2.2.2.2.2.1; positivity)
          (by have h := hp.2.2.2.2.2.2.1; positivity)]
        congr 1
        ring

end OracleTemplate.AdaptiveRobustGeneralized
