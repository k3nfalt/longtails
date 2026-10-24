import LongTails.Proofs.MultiplicativeAccelerationEnergy
import LongTails.Algorithms.SplitRobustAcceleration
import LongTails.Proofs.AcceleratedStochastic

open Set MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Proofs.MultiplicativeAccelerationEnergy

namespace OracleTemplate.SplitRobustAcceleration

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [SecondCountableTopology E] in
lemma stochastic_coupling {f : E → ℝ} {L V α A a : ℝ}
    (hL : 0 < L) (hV : 0 < V) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hB : 0 < A+a) (hstep : a^2*V ≤ (A+a)/(16*L))
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z u y : E) (hm : IsMinOn f univ u)
    (hy : (A+a) • y = A • x+a • z)
    (d v : Ω → E) (hd : Measurable d) (hv : Measurable v)
    (hvi : Integrable v P)
    (hdi : Integrable (fun ω => ‖d ω-gradient f y‖^2) P)
    (hv2i : Integrable (fun ω => ‖v ω‖^2) P)
    (hdm : (∫ ω, ‖d ω-gradient f y‖^2 ∂P) ≤ ‖gradient f y‖^2/64)
    (hvm : (∫ ω, ‖v ω‖^2 ∂P) ≤ V*‖gradient f y‖^2)
    (hbias : ‖(∫ ω, v ω ∂P)-gradient f y‖ ≤ α*‖gradient f y‖) :
    let F := fun ω => (A+a)*(f (y-(1/L) • d ω)-f u)+‖z-a • v ω-u‖^2/2
    Integrable F P ∧ (∫ ω, F ω ∂P) ≤
      (1+α^2/(2*V))*(A*(f x-f u)+‖z-u‖^2/2) := by
  dsimp only
  let U := A*(f x-f u)+‖z-u‖^2/2
  let F := fun ω => (A+a)*(f (y-(1/L) • d ω)-f u)+‖z-a • v ω-u‖^2/2
  let G := gradient f y
  let H := fun ω => U-a*⟪v ω-G,z-u⟫-(A+a)/(2*L)*‖G‖^2+
    (A+a)/(2*L)*‖d ω-G‖^2+a^2/2*‖v ω‖^2
  have hHi : Integrable H P :=
    ((((integrable_const U).sub
      (((hvi.sub (integrable_const G)).inner_const (z-u)).const_mul a)).sub
        (integrable_const _)).add (hdi.const_mul _)).add (hv2i.const_mul _)
  have hbound (ω : Ω) : F ω ≤ H ω := by
    apply coupling_error hA ha hB hL hy
      (by dsimp [G]; linarith [Gradient.convex_support hc hg y x])
      (by dsimp [G]; linarith [Gradient.convex_support hc hg y u])
    have h := Gradient.smooth_upper_bound hg hlip y (y-(1/L) • d ω)
    rw [show y-(1/L) • d ω-y = -(1/L) • d ω by module] at h
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at h
    convert h using 1; ring
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hpos (ω : Ω) : 0 ≤ F ω := by
    have hh : 0 ≤ f (y-(1/L) • d ω)-f u := sub_nonneg.mpr (hm (by trivial))
    dsimp [F]
    positivity
  have hFi : Integrable F P := hHi.mono_nonneg hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall hpos) (Filter.Eventually.of_forall hbound)
  refine ⟨hFi, ?_⟩
  have hz : ‖z-u‖^2 ≤ 2*U := by
    have hh : 0 ≤ A*(f x-f u) := mul_nonneg hA (sub_nonneg.mpr (hm (by trivial)))
    dsimp [U]
    linarith
  exact expected_energy_growth hB hL ha hV hstep hz hvi hdi hv2i hFi hdm hvm hbias hbound

noncomputable def weight (L V : ℝ) (k : ℕ) : ℝ := (k : ℝ)*((k : ℝ)+1)/(64*L*V)

noncomputable def energy (f : E → ℝ) (L V : ℝ) (u : E) (k : ℕ) (s : E × E) : ℝ :=
  weight L V k*(f s.1-f u)+‖s.2-u‖^2/2

lemma weight_nonneg {L V : ℝ} (hL : 0 < L) (hV : 0 < V) (k : ℕ) :
    0 ≤ weight L V k := by unfold weight; positivity

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma energy_nonneg {f : E → ℝ} {L V : ℝ} {u : E}
    (hL : 0 < L) (hV : 0 < V) (hm : IsMinOn f univ u) (k : ℕ) (s : E × E) :
    0 ≤ energy f L V u k s := by
  unfold energy
  exact add_nonneg (mul_nonneg (weight_nonneg hL hV k)
    (sub_nonneg.mpr (hm (by trivial)))) (by positivity)

omit [CompleteSpace E] in
lemma measurable_run {g : E → Ω → E × E} (hg : Measurable (Function.uncurry g))
    (L V : ℝ) (K k : ℕ) :
    Measurable (fun w : (E × E) × (Fin K → Ω) => run g L V K k w.1.1 w.1.2 w.2) := by
  induction K generalizing k with
  | zero => exact measurable_fst
  | succ K ih =>
    let y := fun w : (E × E) × (Fin (K+1) → Ω) => Gradient.acceleratedQuery (k,w.1.1,w.1.2)
    have hy : Measurable y := by dsimp [y, Gradient.acceleratedQuery]; fun_prop
    have hr : Measurable (fun w : (E × E) × (Fin (K+1) → Ω) => g (y w) (w.2 0)) :=
      hg.comp (hy.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    exact (ih (k+1)).comp
      (((hy.sub (hr.fst.const_smul _)).prodMk
        (measurable_fst.snd.sub (hr.snd.const_smul _))).prodMk
          (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma measurable_energy {f : E → ℝ} (hf : Measurable f) (L V : ℝ) (u : E) (k : ℕ) :
    Measurable (energy f L V u k) := by unfold energy; fun_prop

lemma weight_step {L V : ℝ} (hL : 0 < L) (hV : 0 < V) (k : ℕ) :
    weight L V (k+1) = weight L V k+((k : ℝ)+1)/(32*L*V) ∧
    (((k : ℝ)+1)/(32*L*V))^2*V ≤ weight L V (k+1)/(16*L) := by
  constructor
  · unfold weight
    push_cast
    ring
  · apply (le_div_iff₀ (by positivity : 0 < 16*L)).mpr
    unfold weight
    apply (le_div_iff₀ (by positivity : 0 < 64*L*V)).mpr
    have he : (((k : ℝ)+1)/(32*L*V))^2*V*(16*L)*(64*L*V) = ((k : ℝ)+1)^2 := by
      field_simp
      ring
    rw [he]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma query_coupling {L V : ℝ} (hL : 0 < L) (hV : 0 < V) (k : ℕ) (x z : E) :
    (weight L V k+((k : ℝ)+1)/(32*L*V)) • Gradient.acceleratedQuery (k,x,z) =
      weight L V k • x+(((k : ℝ)+1)/(32*L*V)) • z := by
  have hden : (k : ℝ)*((k : ℝ)+1)/4+((k : ℝ)+1)/2 ≠ 0 := by positivity
  dsimp [weight, Gradient.acceleratedQuery]
  match_scalars
  all_goals (field_simp [hL.ne', hV.ne', hden]; ring)

omit [SecondCountableTopology E] in
lemma energy_step {f : E → ℝ} {G : E → Ω → E × E} {L V α : ℝ}
    (hL : 0 < L) (hV : 0 < V) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hG : Measurable (Function.uncurry G))
    (hvi : ∀ y, Integrable (fun ω => (G y ω).2) P)
    (hdi : ∀ y, Integrable (fun ω => ‖(G y ω).1-gradient f y‖^2) P)
    (hv2i : ∀ y, Integrable (fun ω => ‖(G y ω).2‖^2) P)
    (hdm : ∀ y, (∫ ω, ‖(G y ω).1-gradient f y‖^2 ∂P) ≤ ‖gradient f y‖^2/64)
    (hvm : ∀ y, (∫ ω, ‖(G y ω).2‖^2 ∂P) ≤ V*‖gradient f y‖^2)
    (hbias : ∀ y, ‖(∫ ω, (G y ω).2 ∂P)-gradient f y‖ ≤ α*‖gradient f y‖)
    (x z u : E) (hm : IsMinOn f univ u) (k : ℕ) :
    let y := Gradient.acceleratedQuery (k,x,z)
    let step := fun ω => (y-(1/L) • (G y ω).1,z-(((k : ℝ)+1)/(32*L*V)) • (G y ω).2)
    Integrable (fun ω => energy f L V u (k+1) (step ω)) P ∧
    (∫ ω, energy f L V u (k+1) (step ω) ∂P) ≤
      (1+α^2/(2*V))*energy f L V u k (x,z) := by
  let y := Gradient.acceleratedQuery (k,x,z)
  have hgm : Measurable (G y) := hG.comp (measurable_const.prodMk measurable_id)
  have hw := weight_step hL hV k
  have hB : 0 < weight L V k+((k : ℝ)+1)/(32*L*V) :=
    add_pos_of_nonneg_of_pos (weight_nonneg hL hV k) (by positivity)
  have hs := stochastic_coupling hL hV (weight_nonneg hL hV k) (by positivity)
    hB (by rw [← hw.1]; exact hw.2) hc hg hlip x z u y hm
    (query_coupling hL hV k x z) (fun ω => (G y ω).1) (fun ω => (G y ω).2)
    hgm.fst hgm.snd (hvi y) (hdi y) (hv2i y) (hdm y) (hvm y) (hbias y)
  simpa only [energy, hw.1] using hs

omit [CompleteSpace E] in
lemma integrate_energy_recursion {f : E → ℝ} {g : E → Ω → E × E} {L V c : ℝ}
    (hL : 0 < L) (hV : 0 < V) (hc : 0 ≤ c) (hf : Measurable f)
    (hg : Measurable (Function.uncurry g)) (u : E) (hm : IsMinOn f univ u)
    (hs : ∀ (k : ℕ) (x z : E),
      let y := Gradient.acceleratedQuery (k,x,z)
      let step := fun ω => (y-(1/L) • (g y ω).1, z-(((k : ℝ)+1)/(32*L*V)) • (g y ω).2)
      Integrable (fun ω => energy f L V u (k+1) (step ω)) P ∧
      (∫ ω, energy f L V u (k+1) (step ω) ∂P) ≤ c*energy f L V u k (x,z))
    (K k : ℕ) (x z : E) :
    Integrable (fun ξ => energy f L V u (k+K) (run g L V K k x z ξ))
      (Measure.pi fun _ : Fin K => P) ∧
    (∫ ξ, energy f L V u (k+K) (run g L V K k x z ξ)
      ∂Measure.pi fun _ : Fin K => P) ≤ c^K*energy f L V u k (x,z) := by
  induction K generalizing k x z with
  | zero => simp [run]
  | succ K ih =>
    let Q := Measure.pi (fun _ : Fin K => P)
    let y := Gradient.acceleratedQuery (k,x,z)
    let step := fun ω => (y-(1/L) • (g y ω).1, z-(((k : ℝ)+1)/(32*L*V)) • (g y ω).2)
    let B := fun ω => c^K*energy f L V u (k+1) (step ω)
    let F := fun w : Ω × (Fin K → Ω) =>
      energy f L V u (k+(K+1)) (run g L V (K+1) k x z (Fin.cons w.1 w.2))
    have hmp : Measurable (fun ξ : Fin (K+1) → Ω =>
        energy f L V u (k+(K+1)) (run g L V (K+1) k x z ξ)) :=
      (measurable_energy hf L V u _).comp
        ((measurable_run hg L V (K+1) k).comp
          (measurable_const.prodMk measurable_id :
            Measurable (fun ξ : Fin (K+1) → Ω => ((x,z),ξ))))
    have hcons := StochasticGradient.cons_measurePreserving P K
    have hFm : Measurable F := hmp.comp hcons.measurable
    have hFeq (ω : Ω) : (fun ξ => F (ω,ξ)) =
        fun ξ => energy f L V u (k+1+K) (run g L V K (k+1) (step ω).1 (step ω).2 ξ) := by
      funext ξ
      simp only [F, run, Fin.cons_zero, Fin.cons_succ, step, y]
      congr 1
      omega
    have hstep := hs k x z
    have hBi : Integrable B P := hstep.1.const_mul _
    have hsection : ∀ ω, Integrable (fun ξ => F (ω,ξ)) Q := by
      intro ω
      rw [hFeq]
      exact (ih (k+1) (step ω).1 (step ω).2).1
    have hbound (ω : Ω) : (∫ ξ, F (ω,ξ) ∂Q) ≤ B ω := by
      rw [hFeq]
      exact (ih (k+1) (step ω).1 (step ω).2).2
    have hnonneg (w : Ω × (Fin K → Ω)) : 0 ≤ F w := energy_nonneg hL hV hm _ _
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω,ξ)‖ ∂Q) P := by
      apply hBi.mono_nonneg hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · exact Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hbound ω)
    have hFi : Integrable F (P.prod Q) := (integrable_prod_iff hFm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hint⟩
    have hi : Integrable (fun ξ => energy f L V u (k+(K+1)) (run g L V (K+1) k x z ξ))
        (Measure.pi fun _ : Fin (K+1) => P) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp hFi
    refine ⟨hi, ?_⟩
    calc
      _ = ∫ w, F w ∂P.prod Q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
      _ = ∫ ω, ∫ ξ, F (ω,ξ) ∂Q ∂P := integral_prod F hFi
      _ ≤ ∫ ω, B ω ∂P := integral_mono hFi.integral_prod_left hBi hbound
      _ = c^K*(∫ ω, energy f L V u (k+1) (step ω) ∂P) := integral_const_mul _ _
      _ ≤ c^K*(c*energy f L V u k (x,z)) :=
        mul_le_mul_of_nonneg_left hstep.2 (pow_nonneg hc _)
      _ = _ := by rw [pow_succ]; ring

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma objective_from_energy {f : E → ℝ} {G : E → Ω → E × E} {L V c : ℝ}
    (hL : 0 < L) (hV : 0 < V) (hf : Measurable f)
    (hG : Measurable (Function.uncurry G)) (u x0 : E) (hm : IsMinOn f univ u)
    (K : ℕ) (hK : 0 < K)
    (hEi : Integrable (fun ξ => energy f L V u K (run G L V K 0 x0 x0 ξ))
      (Measure.pi fun _ : Fin K => P))
    (hE : (∫ ξ, energy f L V u K (run G L V K 0 x0 x0 ξ)
      ∂Measure.pi fun _ : Fin K => P) ≤ c*‖x0-u‖^2/2) :
    Integrable (fun ξ => f (run G L V K 0 x0 x0 ξ).1-f u)
      (Measure.pi fun _ : Fin K => P) ∧
    (∫ ξ, f (run G L V K 0 x0 x0 ξ).1-f u
      ∂Measure.pi fun _ : Fin K => P) ≤ c*‖x0-u‖^2/(2*weight L V K) := by
  have hw : 0 < weight L V K := by
    unfold weight
    have hk : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  have hgm : Measurable (fun ξ : Fin K → Ω => f (run G L V K 0 x0 x0 ξ).1-f u) :=
    (hf.comp (((measurable_run hG L V K 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun ξ : Fin K → Ω => ((x0,x0),ξ)))).fst)).sub measurable_const
  have hpos (ξ : Fin K → Ω) : 0 ≤ f (run G L V K 0 x0 x0 ξ).1-f u :=
    sub_nonneg.mpr (hm (by trivial))
  have hbound (ξ : Fin K → Ω) : f (run G L V K 0 x0 x0 ξ).1-f u ≤
      energy f L V u K (run G L V K 0 x0 x0 ξ)/weight L V K := by
    apply (le_div_iff₀ hw).mpr
    unfold energy
    nlinarith [sq_nonneg ‖(run G L V K 0 x0 x0 ξ).2-u‖]
  have hi := (hEi.div_const (weight L V K)).mono_nonneg hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall hpos) (Filter.Eventually.of_forall hbound)
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi (hEi.div_const (weight L V K)) hbound
  rw [integral_div] at hb
  exact hb.trans ((div_le_div_of_nonneg_right hE hw.le).trans_eq (by ring))

end OracleTemplate.SplitRobustAcceleration
