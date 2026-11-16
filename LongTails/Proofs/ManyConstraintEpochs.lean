import LongTails.Proofs.ManyConstraintEnergy
import LongTails.Proofs.ManyConstraintInner
import LongTails.Proofs.ManyConstraintLower

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintEpochs

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintNoise
  LongTails.Proofs.ManyConstraintBall LongTails.Proofs.ManyConstraintCoupling
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintStream
  LongTails.Proofs.ManyConstraintRegularity LongTails.Proofs.ManyConstraintInner
  LongTails.Proofs.ManyConstraintStochastic LongTails.Proofs.ManyConstraintStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ}
variable {grad : Ξ → E → E} {K : Fin m → Set E} {P : Fin m → E → E}

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma innerRun_eq (k : Knobs E) (s hs : E) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ : ℕ → Ξ),
      innerRun grad P k s hs n yz js ξ =
        (runG (step grad P k s hs) n yz js ξ, sumG (step grad P k s hs) k.θ n yz js ξ) := by
  intro n
  induction n with
  | zero => intro yz js ξ; rfl
  | succ n ih =>
    intro yz js ξ
    simp only [innerRun, runG, sumG, ih]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma innerRun_congr (k : Knobs E) (s hs : E) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ ξ' : ℕ → Ξ),
      (∀ i, i < n * (k.b + 2) → ξ i = ξ' i) →
      innerRun grad P k s hs n yz js ξ = innerRun grad P k s hs n yz js ξ' := by
  intro n
  induction n with
  | zero => intro yz js ξ ξ' _; rfl
  | succ n ih =>
    intro yz js ξ ξ' h
    have hb : (fun i : Fin k.b => ξ i) = (fun i : Fin k.b => ξ' i) := by
      funext i; exact h i (by have := i.isLt; nlinarith)
    simp only [innerRun, hb]
    rw [ih _ _ (fun t => ξ (k.b + 2 + t)) (fun t => ξ' (k.b + 2 + t))
      (fun i hi => h _ (by nlinarith))]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma epoch_congr (k : Knobs E) (st : St E) (js : Fin k.M → Fin m) (ξ ξ' : ℕ → Ξ)
    (h : ∀ i, i < epochLen m k → ξ i = ξ' i) :
    epoch grad P k st js ξ = epoch grad P k st js ξ' := by
  unfold epoch
  rw [innerRun_congr k st.s _ k.M _ js (fun t => ξ (m + t)) (fun t => ξ' (m + t))
    (fun i hi => h _ (by unfold epochLen; omega))]

omit [CompleteSpace E] in
lemma step_measurable_joint (hgm : Measurable (Function.uncurry grad))
    (hP : ∀ j z, IsProj (K j) z (P j z)) (k : Knobs E) (j : Fin m) :
    Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) =>
      step grad P k p.1.1 (hgrad k.β P p.1.1) p.1.2 j p.2) := by
  have hPc : ∀ j, Continuous (P j) := fun j => proj_continuous (hP j)
  have hs : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) => p.1.1) := by fun_prop
  have hy : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) => p.1.2.1) := by fun_prop
  have hz : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) => p.1.2.2) := by fun_prop
  have hx : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) => mix k.τ p.1.1 p.1.2.1 p.1.2.2) := by
    unfold mix
    exact ((hz.const_smul _).add (hs.const_smul _)).add (hy.const_smul _)
  have hbatch : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) =>
      batch grad p.2 (mix k.τ p.1.1 p.1.2.1 p.1.2.2)) := by
    unfold batch
    refine Measurable.const_smul ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hgm.comp (((measurable_pi_apply i).comp measurable_snd).prodMk hx)
  have hpg : ∀ (f : (E × (E × E)) × (Fin k.b → Ξ) → E), Measurable f →
      Measurable (fun p => penGrad k.β (P j) (f p)) := by
    intro f hf
    unfold penGrad
    exact (hf.sub ((hPc j).measurable.comp hf)).const_smul _
  have hhg : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) => hgrad k.β P p.1.1) := by
    unfold hgrad penGrad
    refine Measurable.const_smul ?_ _
    exact Finset.measurable_sum _ fun i _ =>
      (hs.sub ((hPc i).measurable.comp hs)).const_smul _
  have hv : Measurable (fun p : (E × (E × E)) × (Fin k.b → Ξ) =>
      batch grad p.2 (mix k.τ p.1.1 p.1.2.1 p.1.2.2) +
        (penGrad k.β (P j) (mix k.τ p.1.1 p.1.2.1 p.1.2.2) - penGrad k.β (P j) p.1.1 +
          hgrad k.β P p.1.1)) :=
    hbatch.add (((hpg _ hx).sub (hpg _ hs)).add hhg)
  have hprox : ∀ a, Measurable (fun q : E × E => proxBall k.μ k.x0 k.ρ a q.1 q.2) := by
    intro a
    unfold proxBall ManyConstraintBall.center
    exact (projBall_measurable k.x0 k.ρ).comp (by fun_prop)
  unfold step
  exact ((hprox _).comp (hx.prodMk hv)).prodMk ((hprox _).comp (hz.prodMk hv))

omit [CompleteSpace E] in
lemma innerRun_measurable_joint (hgm : Measurable (Function.uncurry grad))
    (hP : ∀ j z, IsProj (K j) z (P j z)) (k : Knobs E) :
    ∀ (n : ℕ) (js : Fin n → Fin m),
      Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) =>
        innerRun grad P k p.1.1 (hgrad k.β P p.1.1) n p.1.2 js p.2) := by
  intro n
  induction n with
  | zero =>
    intro js
    have e1 : (fun p : (E × (E × E)) × (ℕ → Ξ) =>
        innerRun grad P k p.1.1 (hgrad k.β P p.1.1) 0 p.1.2 js p.2) =
        fun p => (p.1.2, (0 : E)) := by funext p; rfl
    rw [e1]
    exact (measurable_snd.comp measurable_fst).prodMk measurable_const
  | succ n ih =>
    intro js
    have hg : Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) => (p.1, fun i : Fin k.b => p.2 i)) :=
      measurable_fst.prodMk (Measurable.of_eval fun i =>
        (measurable_pi_apply (i : ℕ)).comp measurable_snd)
    have hnext : Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) =>
        step grad P k p.1.1 (hgrad k.β P p.1.1) p.1.2 (js 0) (fun i => p.2 i)) := by
      have := (step_measurable_joint hgm hP k (js 0)).comp hg
      exact this
    have htail : Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) => (fun t => p.2 (k.b + 2 + t))) :=
      Measurable.of_eval fun t => (measurable_pi_apply (k.b + 2 + t)).comp measurable_snd
    have hs : Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) => p.1.1) := by fun_prop
    have hrest := (ih (fun i => js i.succ)).comp ((hs.prodMk hnext).prodMk htail)
    simp only [innerRun]
    exact hrest.fst.prodMk ((measurable_fst.comp hnext).add (hrest.snd.const_smul _))

omit [CompleteSpace E] in
lemma epoch_measurable_joint (hgm : Measurable (Function.uncurry grad))
    (hP : ∀ j z, IsProj (K j) z (P j z)) (k : Knobs E) (js : Fin k.M → Fin m) :
    Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) =>
      let e := epoch grad P k ⟨p.1.1, p.1.2.1, p.1.2.2⟩ js p.2
      (e.s, (e.y, e.z))) := by
  have hshift : Measurable (fun p : (E × (E × E)) × (ℕ → Ξ) => (fun t => p.2 (m + t))) :=
    Measurable.of_eval fun t => (measurable_pi_apply (m + t)).comp measurable_snd
  have hin := (innerRun_measurable_joint hgm hP k k.M js).comp (measurable_fst.prodMk hshift)
  simp only [epoch]
  exact (hin.snd.const_smul _).prodMk (hin.fst.fst.prodMk hin.fst.snd)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma convexOn_of_support {f : E → ℝ} {g : E → E} (h : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) :
    ConvexOn ℝ univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set w := a • x + b • y
  have h1 := h w x
  have h2 := h w y
  have hzero : a • (x - w) + b • (y - w) = 0 := by
    simp only [w, smul_sub]
    have : a • x + b • y - (a + b) • (a • x + b • y) = 0 := by rw [hab, one_smul, sub_self]
    rw [← this]; module
  have hin : a * ⟪g w, x - w⟫ + b * ⟪g w, y - w⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hzero, inner_zero_right]
  simp only [smul_eq_mul]
  have hw : (a + b) * f w = f w := by rw [hab, one_mul]
  have e1 := mul_le_mul_of_nonneg_left h1 ha
  have e2 := mul_le_mul_of_nonneg_left h2 hb
  change f w ≤ a * f x + b * f y
  linarith

variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {L σ : ℝ} {xs : E}

lemma Phi_convex (h : Regular law loss grad L σ xs) (hL : 0 < L)
    (hP : ∀ j z, IsProj (K j) z (P j z)) {β : ℝ} (hβ : 0 ≤ β) (μ : ℝ) (hμ : 0 ≤ μ) (x0 : E) :
    ConvexOn ℝ univ (Phi law loss β P μ x0) := by
  have hf : ConvexOn ℝ univ (objective law loss) := convexOn_of_support (g := meanGrad law grad)
    fun x y => by
      have := h.support hL x y
      have : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ y - grad ξ x‖ ^ 2 ∂law := by
        have : 0 ≤ ∫ ξ, ‖grad ξ y - grad ξ x‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
        positivity
      linarith
  have hh : ConvexOn ℝ univ (hpen β P) := convexOn_of_support (g := hgrad β P)
    fun x y => hpen_support hP hβ x y
  have hr : ConvexOn ℝ univ (reg μ x0) :=
    (strongConvexOn_zero.mp ((reg_strong μ x0 univ convex_univ).mono hμ))
  unfold Phi Fsm
  exact (hf.add hh).add hr

end LongTails.Proofs.ManyConstraintEpochs
