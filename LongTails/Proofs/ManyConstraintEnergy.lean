import LongTails.Proofs.ManyConstraintRun
import LongTails.Proofs.ManyConstraintStream
import LongTails.Proofs.RecursiveGradientEnergy

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintEnergy

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintNoise
  LongTails.Proofs.ManyConstraintBall LongTails.Proofs.ManyConstraintCoupling
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintStream
  LongTails.Proofs.ManyConstraintRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ}

noncomputable def innerVal (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (s hs : E)
    (D : E → ℝ) : (n : ℕ) → (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → ℝ
  | 0, _, _, _ => 0
  | n + 1, yz, js, ξ =>
    let next := step grad P k s hs yz (js 0) (fun i => ξ i)
    D next.1 + k.θ * innerVal grad P k s hs D n next (fun i => js i.succ)
      (fun t => ξ (k.b + 2 + t))

variable {grad : Ξ → E → E} {K : Fin m → Set E} {P : Fin m → E → E}

omit [CompleteSpace E] in
lemma step_measurable (hgm : Measurable (Function.uncurry grad))
    (hP : ∀ j z, IsProj (K j) z (P j z)) (k : Knobs E) (s hs : E) (j : Fin m) :
    Measurable (fun p : (E × E) × (Fin k.b → Ξ) => step grad P k s hs p.1 j p.2) := by
  have hPc : Continuous (P j) := proj_continuous (hP j)
  have hx : Measurable (fun p : (E × E) × (Fin k.b → Ξ) => mix k.τ s p.1.1 p.1.2) := by
    unfold mix; fun_prop
  have hbatch : Measurable (fun p : (E × E) × (Fin k.b → Ξ) =>
      batch grad p.2 (mix k.τ s p.1.1 p.1.2)) := by
    unfold batch
    refine Measurable.const_smul ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hgm.comp ((measurable_pi_apply i).comp measurable_snd |>.prodMk hx)
  have hpen : Measurable (fun p : (E × E) × (Fin k.b → Ξ) =>
      penGrad k.β (P j) (mix k.τ s p.1.1 p.1.2)) := by
    unfold penGrad
    exact (hx.sub (hPc.measurable.comp hx)).const_smul _
  have hv : Measurable (fun p : (E × E) × (Fin k.b → Ξ) =>
      batch grad p.2 (mix k.τ s p.1.1 p.1.2) +
        (penGrad k.β (P j) (mix k.τ s p.1.1 p.1.2) - penGrad k.β (P j) s + hs)) :=
    hbatch.add ((hpen.sub measurable_const).add measurable_const)
  have hprox : ∀ a, Measurable (fun q : E × E => proxBall k.μ k.x0 k.ρ a q.1 q.2) := by
    intro a
    unfold proxBall ManyConstraintBall.center
    exact (projBall_measurable k.x0 k.ρ).comp (by fun_prop)
  unfold step
  exact ((hprox _).comp (hx.prodMk hv)).prodMk ((hprox _).comp
    ((measurable_snd.comp measurable_fst).prodMk hv))

omit [CompleteSpace E] in
lemma innerRun_measurable (hgm : Measurable (Function.uncurry grad))
    (hP : ∀ j z, IsProj (K j) z (P j z)) (k : Knobs E) (s hs : E)
    {D : E → ℝ} (hD : Measurable D) :
    ∀ (n : ℕ) (js : Fin n → Fin m),
      Measurable (fun p : (E × E) × (ℕ → Ξ) => innerRun grad P k s hs n p.1 js p.2) ∧
      Measurable (fun p : (E × E) × (ℕ → Ξ) => innerVal grad P k s hs D n p.1 js p.2) := by
  intro n
  induction n with
  | zero =>
    intro js
    have e1 : (fun p : (E × E) × (ℕ → Ξ) => innerRun grad P k s hs 0 p.1 js p.2) =
        fun p => (p.1, (0 : E)) := by funext p; rfl
    have e2 : (fun p : (E × E) × (ℕ → Ξ) => innerVal grad P k s hs D 0 p.1 js p.2) =
        fun _ => (0 : ℝ) := by funext p; rfl
    rw [e1, e2]
    exact ⟨measurable_fst.prodMk measurable_const, measurable_const⟩
  | succ n ih =>
    intro js
    have hst := step_measurable hgm hP k s hs (js 0)
    have hg : Measurable (fun p : (E × E) × (ℕ → Ξ) => (p.1, fun i : Fin k.b => p.2 i)) :=
      measurable_fst.prodMk (Measurable.of_eval fun i =>
        (measurable_pi_apply (i : ℕ)).comp measurable_snd)
    have hnext : Measurable (fun p : (E × E) × (ℕ → Ξ) =>
        step grad P k s hs p.1 (js 0) (fun i => p.2 i)) := by
      have := Measurable.comp hst hg
      exact this
    have htail : Measurable (fun p : (E × E) × (ℕ → Ξ) => (fun t => p.2 (k.b + 2 + t))) :=
      Measurable.of_eval fun t => (measurable_pi_apply (k.b + 2 + t)).comp measurable_snd
    obtain ⟨h1, h2⟩ := ih (fun i => js i.succ)
    constructor
    · simp only [innerRun]
      exact ((h1.comp (hnext.prodMk htail)).fst).prodMk
        ((measurable_fst.comp hnext).add ((h1.comp (hnext.prodMk htail)).snd.const_smul _))
    · simp only [innerVal]
      exact (hD.comp (measurable_fst.comp hnext)).add
        ((h2.comp (hnext.prodMk htail)).const_mul _)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma innerVal_abs_le (k : Knobs E) (hρ : 0 ≤ k.ρ) (hθ : 0 < k.θ) (s hs : E) {D : E → ℝ}
    {B : ℝ} (hB : ∀ x ∈ closedBall k.x0 k.ρ, |D x| ≤ B) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ : ℕ → Ξ),
      |innerVal grad P k s hs D n yz js ξ| ≤ weightSum k.θ n * B := by
  intro n
  induction n with
  | zero => intro yz js ξ; simp [innerVal, weightSum]
  | succ n ih =>
    intro yz js ξ
    simp only [innerVal]
    rw [weightSum_succ]
    have h1 := hB _ (step_mem grad P k hρ s hs yz (js 0) (fun i => ξ i)).1
    have h2 := ih (step grad P k s hs yz (js 0) (fun i => ξ i)) (fun i => js i.succ)
      (fun t => ξ (k.b + 2 + t))
    calc _ ≤ |D (step grad P k s hs yz (js 0) (fun i => ξ i)).1| +
          |k.θ * innerVal grad P k s hs D n (step grad P k s hs yz (js 0) (fun i => ξ i))
            (fun i => js i.succ) (fun t => ξ (k.b + 2 + t))| := abs_add_le _ _
      _ ≤ B + k.θ * (weightSum k.θ n * B) := by
          rw [abs_mul, abs_of_pos hθ]; gcongr
      _ = _ := by ring

end LongTails.Proofs.ManyConstraintEnergy
