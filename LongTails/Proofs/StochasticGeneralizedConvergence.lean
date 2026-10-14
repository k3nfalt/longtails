import LongTails.Proofs.StochasticGeneralizedCap
import LongTails.Proofs.StochasticGeneralizedTrace
import LongTails.Proofs.StochasticGeneralizedTerminal
import LongTails.Proofs.StochasticGeneralizedCoupling

open MeasureTheory ProbabilityTheory Set

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate energy)

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

lemma execute_accuracy_of_noise (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    {f : p.E → ℝ} (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (hdist : ‖p.x0-u‖ ≤ p.R) (hgap : f p.x0-f u ≤ p.Δ)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) (N K : ℕ)
    (hN : 16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
      min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))) ≤ N)
    (hK : 2*N+⌈1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2⌉₊ ≤ K)
    (hnoise : accumulated (proofCost p f u) (proofNext p f u g) (proofNoise p f u g) N
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ ≤ 2*p.R^2) :
    f (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm p) (fun _ => K) () ξ)-f u ≤ p.ε := by
  have hT := proofTrace_reaches_target p hp hεΔ hc hg hdiff hH u hmin hdist hgap g ξ N hN hnoise
  have hv := initial_valid p hp
  have hw := initial_weight_bound p hp hεΔ
  have he := initial_energy_bound p hp u hdist hgap
  have hcalls := proofCalls_le p hp f u g _ hv.1 hv.2 hw ξ N
  have hceil := Nat.le_ceil (1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2)
  have hKreal : ((2*N+⌈1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2⌉₊ : ℕ) : ℝ) ≤ K :=
    Nat.cast_le.mpr hK
  push_cast at hKreal
  have hcallK : blockCalls (proofCost p f u) (proofNext p f u g)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ N ≤ K := by
    exact_mod_cast (show (blockCalls (proofCost p f u) (proofNext p f u g)
      (initialIterate p.L0 p.R p.Δ p.ε p.x0) ξ N : ℝ) ≤ K by linarith)
  erw [execute_after_target p P f u g ξ hεΔ N K hcallK hT]
  exact proofTrace_target_accuracy p hp hc hg hdiff hH u hmin g _ he ξ N hnoise hT

lemma execution_high_probability (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0+p.L1*‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f univ u) (hdist : ‖p.x0-u‖ ≤ p.R) (hgap : f p.x0-f u ≤ p.Δ)
    (μ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : IID (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (P : Measure _))
    {g : p.E → p.Ω → p.E} (ho : IsLightTailGradient p.E p.Ω (μ : Measure _) f g p.σ) (N K : ℕ)
    (hN : 16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
      min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))) ≤ N)
    (hK : 2*N+⌈1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2⌉₊ ≤ K) :
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
    let Z := accumulated (proofCost p f u) (proofNext p f u g) (proofNoise p f u g) N s
    have hv := initial_valid p hp
    have hw := initial_weight_bound p hp hεΔ'
    have hZ := proofNoise_accumulated_measurable p hf hgrad u ho.measurable N s
    have ht := proofNoise_tail_iid p hp hf hgrad u hmin ho hIID N s hv.1 hv.2 hw
    have hsnd : HasLaw (Prod.snd : Unit × (ℕ → p.Ω) → ℕ → p.Ω) (P : Measure _)
        ((Measure.dirac ()).prod (P : Measure _)) :=
      ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
    calc
      _ ≤ ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) | 2*p.R^2 < Z w.2} := by
        apply measure_mono
        rintro ⟨⟨⟩, ξ⟩ hfail
        change 2*p.R^2 < Z ξ
        by_contra hn
        have hacc := execute_accuracy_of_noise p hp hεΔ' hc hg hdiff hH u hmin hdist hgap P g ξ N K hN hK
          (le_of_not_gt hn)
        exact not_lt_of_ge hacc hfail
      _ = (P : Measure _) {ξ | 2*p.R^2 < Z ξ} := hsnd.measure_eq (measurableSet_lt measurable_const hZ)
      _ ≤ ENNReal.ofReal p.δ := ht

end OracleTemplate.StochasticGeneralized
