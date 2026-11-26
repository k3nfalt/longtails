import LongTails.Proofs.TwoPhaseGaussianVI
import LongTails.Proofs.TwoPhaseGaussianVIBudget

open MeasureTheory
namespace OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
open LongTails.Setups.GaussianVariationalInference

noncomputable def warmCount (q : Params) : ℕ :=
  ⌈offset q.L q.μ q.d / 2 * Real.log (max 1 (q.μ*q.R^2/q.ε))⌉₊

noncomputable def suffixCount (q : Params) : ℕ :=
  ⌈2 * offset q.L q.μ q.d * (1+q.d/q.ε)⌉₊

lemma twoPhase_convergence : Convergence spec (fun q _ => warmCount q + suffixCount q) := by
  refine ⟨fun q => twoPhaseSgd q.μ (offset q.L q.μ q.d) (warmCount q) (q.m0,q.C0), ?_,
    fun _ _ => trivial⟩
  intro q hq V O hadm
  obtain ⟨hm, hL, _, he, hz⟩ := hq
  obtain ⟨rfl, hg, hlip, hs, ms, Cs, hCs, hmin, hdist⟩ := hadm
  have h : Potential q.L q.μ V := ⟨hg,hlip,hs,hm,hL⟩
  have ho : IsOptimal V ms Cs := ⟨hCs,hmin⟩
  let a := offset q.L q.μ q.d
  let K := suffixCount q
  let T := warmCount q
  let z : Location q.d × Scale q.d := (q.m0,q.C0)
  have ha : 2 ≤ a := (constants h).offset_ge
  have hk : 2*a*(1+q.d/q.ε) ≤ K := Nat.le_ceil _
  have hkpos : 0 < K := by
    have hp : 0 < 2*a*(1+q.d/q.ε) := by positivity
    exact_mod_cast hp.trans_le hk
  let out := averaged V q.μ a K T z
  let F := fun ξ => gap V ms Cs (out ξ)
  have hf : Measurable out := (measurable_averaged h a K T).of_uncurry_left
  have hFm : Measurable F := (measurable_gap h ms Cs).comp hf
  have hr := averaged_bound h ho hkpos T z hz
  have hb := phase_budget h ho (z := z) hz he (R := q.R) hdist (T := T) (Nat.le_ceil _) hk
  let Ω := (ℕ → Fin q.d → ℝ) × (ℕ → Unit)
  let P := (Measure.infinitePi fun _ : ℕ => noiseLaw q.d).prod (Measure.dirac fun _ : ℕ => ())
  let draws := fun s : Ω => fun i : Fin (K+T) => s.1 i
  have mp : MeasurePreserving draws P (Measure.pi fun _ => noiseLaw q.d) :=
    (StochasticGradient.prefix_measurePreserving (noiseLaw q.d) (K+T)).comp
      (measurePreserving_fst (ν := Measure.dirac fun _ : ℕ => ()))
  intro A
  have eqout : (fun s : Ω => execute {answer := fun _ (_, x) _ => gradient V x}
      A (fun _ => T+K) s.1 s.2) = fun s => out (draws s) := by
    funext s
    have hu : s.2 = fun _ => () := funext fun _ => rfl
    rw [hu, Nat.add_comm T K]
    exact (execute_iterate (gradient V) A (K+T) s.1).trans (trace V q.μ a ha K hkpos T z s.1)
  change spec.successful q V (fun s : Ω => execute {answer := fun _ (_, x) _ => gradient V x}
    A (fun _ => T+K) s.1 s.2) ⟨P, inferInstance⟩
  rw [eqout]
  refine ⟨hf.comp mp.measurable, fun s => averaged_cholesky h ha hkpos T z hz _, ms,Cs,hCs,hmin,
    mp.integrable_comp_of_integrable hr.1, ?_⟩
  change (∫ s, F (draws s) ∂P) ≤ q.ε
  have heq := integral_map (μ := P) mp.measurable.aemeasurable (f := F) hFm.aestronglyMeasurable
  rw [mp.map_eq] at heq
  exact heq.ge.trans (hr.2.trans hb)

end OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
