import LongTails.Proofs.GeneralizedLipschitzWarmStart
import LongTails.Proofs.StochasticEnvelopePilot
import LongTails.Proofs.HeterogeneousAdamDescent
open scoped RealInnerProductSpace
open MeasureTheory
namespace LongTails.Proofs.GeneralizedLipschitzWarmStartSampling
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
noncomputable def boundedPart (f : E → ℝ) (xstar : E) (G : ℝ) (oracle : E → Ω → E) (x : E) (ω : Ω) : E :=
  OracleTemplate.clip (G * (f x - f xstar)) (oracle x ω)
noncomputable def noisePart (f : E → ℝ) (xstar : E) (G : ℝ) (oracle : E → Ω → E) (x : E) (ω : Ω) : E :=
  oracle x ω - boundedPart f xstar G oracle x ω
lemma measurable_boundedPart {f : E → ℝ} (hf : Measurable f) (xstar : E) (G : ℝ)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle)) :
    Measurable (Function.uncurry (boundedPart f xstar G oracle)) :=
  LongTails.Proofs.StochasticEnvelopePilot.measurable_variable_clip
    (measurable_const.mul ((hf.comp measurable_fst).sub measurable_const)) ho
lemma measurable_noisePart {f : E → ℝ} (hf : Measurable f) (xstar : E) (G : ℝ)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle)) :
    Measurable (Function.uncurry (noisePart f xstar G oracle)) :=
  ho.sub (measurable_boundedPart hf xstar G ho)
omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma boundedPart_norm {f : E → ℝ} {xstar : E} {G : ℝ} (hG : 0 ≤ G)
    (hmin : ∀ x, f xstar ≤ f x) (oracle : E → Ω → E) (x : E) (ω : Ω) :
    ‖boundedPart f xstar G oracle x ω‖ ≤ G * (f x - f xstar) :=
  OracleTemplate.norm_clip_le (mul_nonneg hG (sub_nonneg.mpr (hmin x))) _
lemma noise_secondMoment (p : Measure Ω)
    {f : E → ℝ} {xstar : E} {oracle : E → Ω → E} {G0 G1 G : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG : 0 ≤ G) (hGG : G1 ≤ G)
    (hmin : ∀ x, f xstar ≤ f x) (x : E) :
    Integrable (fun ω => ‖noisePart f xstar G oracle x ω‖ ^ 2) p ∧
      (∫ ω, ‖noisePart f xstar G oracle x ω‖ ^ 2 ∂p) ≤ G0 ^ 2 := by
  obtain ⟨u, v, _, _, hsplit, hu2, hub, hv⟩ := ho.decomposition x
  have hB : 0 ≤ G * (f x - f xstar) := mul_nonneg hG (sub_nonneg.mpr (hmin x))
  have hX : Measurable (oracle x) := ho.measurable.comp (measurable_const.prodMk measurable_id)
  have hn : Measurable (noisePart f xstar G oracle x) := hX.sub ((OracleTemplate.measurable_clip _).comp hX)
  have hd : ∀ᵐ ω ∂p, ‖noisePart f xstar G oracle x ω‖ ^ 2 ≤ ‖u ω‖ ^ 2 := by
    filter_upwards [hsplit, hv] with ω he hvω
    have hvG : ‖v ω‖ ≤ G * (f x - f xstar) := hvω.trans (mul_le_mul_of_nonneg_right hGG (sub_nonneg.mpr (hmin x)))
    have hr := LongTails.Proofs.GeneralizedLipschitzPilot.residual_le_unbounded_part (u ω) (v ω) hB hvG
    dsimp [noisePart, boundedPart]
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hi : Integrable (fun ω => ‖noisePart f xstar G oracle x ω‖ ^ 2) p := by
    apply Integrable.mono' hu2 (hn.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hd] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖noisePart f xstar G oracle x ω‖))] using hω
  exact ⟨hi, (integral_mono_ae hi hu2 hd).trans hub⟩

lemma nonnegative_product_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hF : Measurable F) (hpos : ∀ z, 0 ≤ F z) {C : ℝ}
    (hi : ∀ a, Integrable (fun b => F (a, b)) ν)
    (hb : ∀ a, (∫ b, F (a, b) ∂ν) ≤ C) :
    Integrable F (μ.prod ν) ∧ (∫ z, F z ∂μ.prod ν) ≤ C := by
  have hs : StronglyMeasurable (Function.uncurry (fun a b => F (a, b))) := hF.stronglyMeasurable
  have hm : Measurable (fun a => ∫ b, F (a, b) ∂ν) :=
    hs.integral_prod_right.measurable
  have hj : Integrable (fun a => ∫ b, F (a, b) ∂ν) μ := by
    apply Integrable.mono' (integrable_const C) hm.aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun b => hpos (a, b)))]
    exact hb a
  have hip : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hj
  refine ⟨hip, ?_⟩
  rw [integral_prod F hip]
  calc (∫ a, ∫ b, F (a, b) ∂ν ∂μ) ≤ ∫ _, C ∂μ :=
        integral_mono hj (integrable_const C) hb
       _ = C := by simp

lemma fresh_noise_secondMoment {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (p : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure p]
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG : 0 ≤ G) (hGG : G1 ≤ G)
    (hmin : ∀ x, f xstar ≤ f x) {query : A → E} (hq : Measurable query) :
    Integrable (fun z : A × Ω => ‖noisePart f xstar G oracle (query z.1) z.2‖ ^ 2) (μ.prod p) ∧
      (∫ z : A × Ω, ‖noisePart f xstar G oracle (query z.1) z.2‖ ^ 2 ∂μ.prod p) ≤ G0 ^ 2 := by
  apply nonnegative_product_bound μ p
  · exact ((measurable_noisePart hf xstar G ho.measurable).comp
      ((hq.comp measurable_fst).prodMk measurable_snd)).norm.pow_const 2
  · intro z; positivity
  · intro a; exact (noise_secondMoment p ho hG hGG hmin (query a)).1
  · intro a; exact (noise_secondMoment p ho hG hGG hmin (query a)).2

section History
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStart
variable {Ω E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def finiteState (center : E) (D G0 α : ℝ) (oracle : E → Ω → E) :
    (n : ℕ) → (Fin n → Ω) → State E
  | 0, _ => initial center G0
  | n + 1, ξ =>
    let s := finiteState center D G0 α oracle n (fun i => ξ i.castSucc)
    update center D α s (oracle (point α s) (ξ (Fin.last n)))
lemma finiteState_eq (center : E) (D G0 α : ℝ) (oracle : E → Ω → E) (ξ : ℕ → Ω) (n : ℕ) :
    finiteState center D G0 α oracle n (fun i => ξ i) = trajectory center D G0 α oracle ξ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteState, trajectory, Fin.val_castSucc, Fin.val_last, ih]
variable [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma measurable_finiteState (center : E) (D G0 α : ℝ) {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (finiteState center D G0 α oracle n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs : Measurable (fun ξ : Fin (n + 1) → Ω => finiteState center D G0 α oracle n (fun i => ξ i.castSucc)) :=
      ih.comp (Measurable.of_eval (fun i => measurable_pi_apply i.castSucc))
    have hr := ho.comp (((measurable_point α).comp hs).prodMk (measurable_pi_apply (Fin.last n)))
    exact (measurable_update_family D α).comp (measurable_const.prodMk (hs.prodMk hr))
lemma independent_prefix {W : Type*} [MeasurableSpace W] (P : Measure W)
    {ξ : ℕ → W → Ω} (hi : ProbabilityTheory.iIndepFun ξ P)
    (hm : ∀ i, Measurable (ξ i)) (n : ℕ) :
    ProbabilityTheory.IndepFun (fun ω (i : Fin n) => ξ i ω) (ξ n) P := by
  have hd : Disjoint (Finset.range n) {n} := by simp
  have h := hi.indepFun_finset (Finset.range n) {n} hd hm
  have he := h.comp
    (Measurable.of_eval (fun i : Fin n => measurable_pi_apply ⟨i, Finset.mem_range.mpr i.isLt⟩))
    (measurable_pi_apply ⟨n, Finset.mem_singleton_self n⟩)
  exact he

lemma independent_noise_secondMoment {W : Type*} [MeasurableSpace W]
    (P : Measure W) (p : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G : ℝ}
    (ho : LongTails.Setups.StochasticGeneralizedLipschitzConvex.IsOracle p f xstar oracle G0 G1)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    {query : W → E} {sample : W → Ω} (hq : Measurable query) (hs : Measurable sample)
    (hind : ProbabilityTheory.IndepFun query sample P) (hlaw : P.map sample = p) :
    Integrable (fun ω => ‖noisePart f xstar G oracle (query ω) (sample ω)‖ ^ 2) P ∧
      (∫ ω, ‖noisePart f xstar G oracle (query ω) (sample ω)‖ ^ 2 ∂P) ≤ G0 ^ 2 := by
  let : IsProbabilityMeasure (P.map query) := (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  have hmap : P.map (fun ω => (query ω, sample ω)) = (P.map query).prod p := by
    rw [hind.map_prod_eq_prod_map_map hq.aemeasurable hs.aemeasurable, hlaw]
  have h := fresh_noise_secondMoment (P.map query) p hf ho hG hGG hmin measurable_id
  simp only [id_eq] at h
  rw [← hmap] at h
  have hm : Measurable (fun z : E × Ω => ‖noisePart f xstar G oracle z.1 z.2‖ ^ 2) :=
    (measurable_noisePart hf xstar G ho.measurable).norm.pow_const 2
  refine ⟨h.1.comp_measurable (hq.prodMk hs), ?_⟩
  rw [integral_map (hq.prodMk hs).aemeasurable hm.aestronglyMeasurable] at h
  exact h.2


lemma trajectory_query_independent {W : Type*} [MeasurableSpace W] (P : Measure W)
    {ξ : ℕ → W → Ω} (hi : ProbabilityTheory.iIndepFun ξ P) (hm : ∀ i, Measurable (ξ i))
    (center : E) (D G0 α : ℝ) {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω => point α (trajectory center D G0 α oracle (fun i => ξ i ω) n)) (ξ n) P := by
  have h := (independent_prefix P hi hm n).comp
    ((measurable_point α).comp (measurable_finiteState center D G0 α ho n)) measurable_id
  have he : (fun ω => point α (finiteState center D G0 α oracle n (fun i => ξ i ω))) =
      (fun ω => point α (trajectory center D G0 α oracle (fun i => ξ i ω) n)) := by
    funext ω
    rw [finiteState_eq center D G0 α oracle (fun i => ξ i ω)]
  simpa only [Function.comp_def, id_eq, he] using h
lemma trajectory_noise_secondMoment {W : Type*} [MeasurableSpace W]
    (P : Measure W) (p : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G : ℝ}
    (ho : LongTails.Setups.StochasticGeneralizedLipschitzConvex.IsOracle p f xstar oracle G0 G1)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (D α : ℝ) (n : ℕ) :
    let query := fun ω => point α (trajectory center D G0 α oracle (fun i => ξ i ω) n)
    Integrable (fun ω => ‖noisePart f xstar G oracle (query ω) (ξ n ω)‖ ^ 2) P ∧
      (∫ ω, ‖noisePart f xstar G oracle (query ω) (ξ n ω)‖ ^ 2 ∂P) ≤ G0 ^ 2 := by
  apply independent_noise_secondMoment P p hf ho hG hGG hmin
  · exact (measurable_point α).comp ((measurable_trajectory_family D G0 α ho.measurable n).comp
      (measurable_const.prodMk (Measurable.of_eval hξ.measurable)))
  · exact hξ.measurable n
  · exact trajectory_query_independent P hξ.independent hξ.measurable center D G0 α ho.measurable n
  · exact hξ.marginal n


end History

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma finite_vector_l2_triangle {ι : Type*} (s : Finset ι) (u v : ι → E) :
    Real.sqrt (∑ i ∈ s, ‖u i + v i‖ ^ 2) ≤
      Real.sqrt (∑ i ∈ s, ‖u i‖ ^ 2) + Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
  have hu : 0 ≤ ∑ i ∈ s, ‖u i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv : 0 ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have ht : (∑ i ∈ s, ‖u i + v i‖ ^ 2) ≤
      (∑ i ∈ s, ‖u i‖ ^ 2) + (∑ i ∈ s, ‖v i‖ ^ 2) +
        2 * (∑ i ∈ s, ‖u i‖ * ‖v i‖) := by
    calc (∑ i ∈ s, ‖u i + v i‖ ^ 2) ≤ ∑ i ∈ s, (‖u i‖ + ‖v i‖) ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
         _ = _ := by simp_rw [add_sq, mul_assoc]; rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have hc := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖u i‖) (fun i => ‖v i‖)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma integral_weighted_noise {W : Type*} [MeasurableSpace W] (P : Measure W)
    [IsProbabilityMeasure P] {u : ℕ → W → E} {G0 α : ℝ} (hG0 : 0 ≤ G0)
    (hα : 0 ≤ α) (hα1 : α < 1) (N : ℕ)
    (hi : ∀ i, Integrable (fun ω => ‖u i ω‖ ^ 2) P)
    (hb : ∀ i, (∫ ω, ‖u i ω‖ ^ 2 ∂P) ≤ G0 ^ 2) :
    let w := LongTails.Algorithms.GeneralizedLipschitzWarmStart.weight α
    Integrable (fun ω => Real.sqrt (∑ i ∈ Finset.range N, (w i) ^ 2 * ‖u i ω‖ ^ 2)) P ∧
      (∫ ω, Real.sqrt (∑ i ∈ Finset.range N, (w i) ^ 2 * ‖u i ω‖ ^ 2) ∂P) ≤
        G0 * Real.sqrt α * ((1 - α)⁻¹) ^ N := by
  dsimp only
  let w := LongTails.Algorithms.GeneralizedLipschitzWarmStart.weight α
  have hiS : Integrable (fun ω => ∑ i ∈ Finset.range N, (w i) ^ 2 * ‖u i ω‖ ^ 2) P :=
    integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hpS : ∀ ω, 0 ≤ ∑ i ∈ Finset.range N, (w i) ^ 2 * ‖u i ω‖ ^ 2 :=
    fun ω => Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hj := LongTails.Proofs.HeterogeneousAdamDescent.integral_sqrt_le_sqrt_integral hiS hpS
  refine ⟨hj.1, hj.2.trans ?_⟩
  have he : (∫ ω, ∑ i ∈ Finset.range N, (w i) ^ 2 * ‖u i ω‖ ^ 2 ∂P) ≤
      G0 ^ 2 * (α * (((1 - α)⁻¹) ^ N) ^ 2) := by
    rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
    simp_rw [integral_const_mul]
    calc (∑ i ∈ Finset.range N, w i ^ 2 * ∫ ω, ‖u i ω‖ ^ 2 ∂P) ≤
          ∑ i ∈ Finset.range N, w i ^ 2 * G0 ^ 2 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _))
         _ = G0 ^ 2 * ∑ i ∈ Finset.range N, w i ^ 2 := by rw [← Finset.sum_mul]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (LongTails.Proofs.GeneralizedLipschitzWarmStart.weight_square_sum hα hα1 N) (sq_nonneg G0)
  apply (Real.sqrt_le_sqrt he).trans_eq
  rw [Real.sqrt_mul (sq_nonneg G0), Real.sqrt_sq hG0, Real.sqrt_mul hα,
    Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hα1).le) N)]
  ring


omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma oracle_energy_split {ι : Type*} (s : Finset ι) (w : ι → ℝ) (x : ι → E) (ξ : ι → Ω)
    (f : E → ℝ) (xstar : E) (oracle : E → Ω → E) {G : ℝ}
    (hG : 0 ≤ G) (hmin : ∀ x, f xstar ≤ f x) :
    Real.sqrt (∑ i ∈ s, ‖w i • oracle (x i) (ξ i)‖ ^ 2) ≤
      Real.sqrt (∑ i ∈ s, (w i) ^ 2 * ‖noisePart f xstar G oracle (x i) (ξ i)‖ ^ 2) +
        G * Real.sqrt (∑ i ∈ s, (w i * (f (x i) - f xstar)) ^ 2) := by
  let u := fun i => w i • noisePart f xstar G oracle (x i) (ξ i)
  let v := fun i => w i • boundedPart f xstar G oracle (x i) (ξ i)
  have he : ∀ i, w i • oracle (x i) (ξ i) = u i + v i := by
    intro i
    dsimp [u, v, noisePart]
    rw [← smul_add, sub_add_cancel]
  simp_rw [he]
  apply (finite_vector_l2_triangle s u v).trans
  have hu : ∑ i ∈ s, ‖u i‖ ^ 2 =
      ∑ i ∈ s, (w i) ^ 2 * ‖noisePart f xstar G oracle (x i) (ξ i)‖ ^ 2 := by
    simp only [u, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hu]
  apply add_le_add le_rfl
  have hv : ∑ i ∈ s, ‖v i‖ ^ 2 ≤ G ^ 2 * ∑ i ∈ s, (w i * (f (x i) - f xstar)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := pow_le_pow_left₀ (norm_nonneg _) (boundedPart_norm hG hmin oracle (x i) (ξ i)) 2
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (w i))
    simp only [v, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [hh']
  apply (Real.sqrt_le_sqrt hv).trans_eq
  rw [Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG]

lemma independent_pair_integral {W A B : Type*} [MeasurableSpace W] [MeasurableSpace A]
    [MeasurableSpace B] (P : Measure W) (p : Measure B) [IsProbabilityMeasure P]
    {history : W → A} {sample : W → B} (hh : Measurable history) (hs : Measurable sample)
    (hind : ProbabilityTheory.IndepFun history sample P) (hlaw : P.map sample = p)
    {F : A × B → ℝ} (hi : Integrable F ((P.map history).prod p)) :
    Integrable (fun ω => F (history ω, sample ω)) P ∧
      (∫ ω, F (history ω, sample ω) ∂P) = ∫ z, F z ∂(P.map history).prod p := by
  have hm : P.map (fun ω => (history ω, sample ω)) = (P.map history).prod p := by
    rw [hind.map_prod_eq_prod_map_map hh.aemeasurable hs.aemeasurable, hlaw]
  rw [← hm] at hi ⊢
  exact ⟨hi.comp_measurable (hh.prodMk hs),
    (integral_map (hh.prodMk hs).aemeasurable hi.aestronglyMeasurable).symm⟩

section FreshInner
variable {Ω E A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [CompleteSpace E] in
lemma fresh_oracle_l2 (μ : Measure A) (p : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure p]
    {f : E → ℝ} {xstar : E} {oracle : E → Ω → E} {G0 G1 G D : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    {query : A → E} (hq : Measurable query) (hb : ∀ a, ‖query a - xstar‖ ≤ D)
    (N : ℕ) (hN : 0 < N) (hND : 2 * G * D ≤ N) :
    MemLp (fun z : A × Ω => oracle (query z.1) z.2) 2 (μ.prod p) := by
  have hm : Measurable (fun z : A × Ω => oracle (query z.1) z.2) :=
    ho.measurable.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (nonnegative_product_bound μ p (hm.norm.pow_const 2) (fun z => sq_nonneg _)
    (fun a => (LongTails.Proofs.GeneralizedLipschitzSampling.oracle_moment_bounds ho hG0 (query a)).2.1)
    (fun a => LongTails.Proofs.GeneralizedLipschitzSampling.oracle_ball_secondMoment ho hG0 hG1 hG hGG hmin N hN hND (query a) (hb a))).1
omit [CompleteSpace E] in
lemma fresh_inner_integrable (μ : Measure A) (p : Measure Ω)
    {oracle : E → Ω → E} {query direction : A → E}
    (ho : Measurable (Function.uncurry oracle)) (hq : Measurable query) (hd : Measurable direction)
    (hX : Integrable (fun z : A × Ω => oracle (query z.1) z.2) (μ.prod p))
    {B : ℝ} (hb : ∀ a, ‖direction a‖ ≤ B) :
    Integrable (fun z : A × Ω => ⟪oracle (query z.1) z.2, direction z.1⟫) (μ.prod p) := by
  have hm := ho.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  apply Integrable.mono' (hX.norm.mul_const B) (hm.inner (hd.comp measurable_fst)).aestronglyMeasurable
  filter_upwards [] with z
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb z.1) (norm_nonneg _))
omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma fresh_inner_identity (μ : Measure A) (p : Measure Ω) [SFinite μ] [SFinite p]
    {oracle : E → Ω → E} {query direction : A → E}
    (hoi : ∀ x, Integrable (oracle x) p)
    (hi : Integrable (fun z : A × Ω => ⟪oracle (query z.1) z.2, direction z.1⟫) (μ.prod p)) :
    (∫ z : A × Ω, ⟪oracle (query z.1) z.2, direction z.1⟫ ∂μ.prod p) =
      ∫ a, ⟪∫ ω, oracle (query a) ω ∂p, direction a⟫ ∂μ := by
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with a
  change (∫ ω, ⟪oracle (query a) ω, direction a⟫ ∂p) = ⟪∫ ω, oracle (query a) ω ∂p, direction a⟫
  calc (∫ ω, ⟪oracle (query a) ω, direction a⟫ ∂p) = ∫ ω, ⟪direction a, oracle (query a) ω⟫ ∂p :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
       _ = ⟪direction a, ∫ ω, oracle (query a) ω ∂p⟫ := integral_inner (hoi (query a)) (direction a)
       _ = _ := real_inner_comm _ _

end FreshInner

section AdaptiveInner
variable {Ω E A W : Type} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma independent_inner_identity (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {history : W → A} {sample : W → Ω} (hh : Measurable history) (hs : Measurable sample)
    (hind : ProbabilityTheory.IndepFun history sample P) (hlaw : P.map sample = p)
    {oracle : E → Ω → E} {query direction : A → E}
    (hoi : ∀ x, Integrable (oracle x) p)
    (hi : Integrable (fun z : A × Ω => ⟪oracle (query z.1) z.2, direction z.1⟫) ((P.map history).prod p)) :
    Integrable (fun ω => ⟪oracle (query (history ω)) (sample ω), direction (history ω)⟫) P ∧
    Integrable (fun ω => ⟪∫ v, oracle (query (history ω)) v ∂p, direction (history ω)⟫) P ∧
    (∫ ω, ⟪oracle (query (history ω)) (sample ω), direction (history ω)⟫ ∂P) =
      ∫ ω, ⟪∫ v, oracle (query (history ω)) v ∂p, direction (history ω)⟫ ∂P := by
  let : IsProbabilityMeasure (P.map history) := (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).mpr inferInstance
  have hmean : (fun a => ∫ v, ⟪oracle (query a) v, direction a⟫ ∂p) =
      (fun a => ⟪∫ v, oracle (query a) v ∂p, direction a⟫) := by
    funext a
    calc (∫ v, ⟪oracle (query a) v, direction a⟫ ∂p) = ∫ v, ⟪direction a, oracle (query a) v⟫ ∂p :=
          integral_congr_ae (Filter.Eventually.of_forall (fun v => real_inner_comm _ _))
         _ = ⟪direction a, ∫ v, oracle (query a) v ∂p⟫ := integral_inner (hoi (query a)) (direction a)
         _ = _ := real_inner_comm _ _
  have hm := hi.integral_prod_left
  change Integrable (fun a => ∫ v, ⟪oracle (query a) v, direction a⟫ ∂p) (P.map history) at hm
  rw [hmean] at hm
  have hp := independent_pair_integral P p hh hs hind hlaw hi
  refine ⟨hp.1, hm.comp_measurable hh, ?_⟩
  calc (∫ ω, ⟪oracle (query (history ω)) (sample ω), direction (history ω)⟫ ∂P) =
      ∫ z : A × Ω, ⟪oracle (query z.1) z.2, direction z.1⟫ ∂(P.map history).prod p := hp.2
       _ = ∫ a, ⟪∫ v, oracle (query a) v ∂p, direction a⟫ ∂P.map history := fresh_inner_identity _ _ hoi hi
       _ = _ := integral_map hh.aemeasurable hm.aestronglyMeasurable
omit [CompleteSpace E] [SecondCountableTopology E] in
lemma bounded_query_gap_integrable (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 ≤ G0)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    {query : W → E} (hq : Measurable query) (hb : ∀ ω, ‖query ω - xstar‖ ≤ D)
    (N : ℕ) (hN : 0 < N) (hND : 2 * G * D ≤ N) :
    Integrable (fun ω => f (query ω) - f xstar) P := by
  apply Integrable.mono' (integrable_const (((2 : ℝ) ^ N - 1) * (G0 / G)))
    ((hf.comp hq).sub measurable_const).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖f (query ω) - f xstar‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin _))]
  exact LongTails.Proofs.GeneralizedLipschitzSampling.oracle_gap_bound ho hG0 hG hGG hmin (query ω) N hN
    ((mul_le_mul_of_nonneg_left (hb ω) (by positivity)).trans hND)

end AdaptiveInner
section FiniteState
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStart
variable {Ω E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma finiteState_invariant (center : E) {D G0 α : ℝ} (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (oracle : E → Ω → E) (n : ℕ) (ξ : Fin n → Ω) :
    ‖(finiteState center D G0 α oracle n ξ).2.1 - center‖ ≤ D ∧
    ‖(finiteState center D G0 α oracle n ξ).2.2.1 - center‖ ≤ D ∧
    0 < (finiteState center D G0 α oracle n ξ).2.2.2 := by
  induction n with
  | zero => simpa only [finiteState, initial, sub_self, norm_zero] using And.intro hD (And.intro hD (sq_pos_of_pos hG0))
  | succ n ih =>
    have h := ih (fun i => ξ i.castSucc)
    exact update_invariant center _ _ hD hα hα1 h.1 h.2.1 h.2.2

end FiniteState
section TrajectoryInner
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStart
variable {Ω E W : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma trajectory_inner_identity (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 ≤ D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (n : ℕ) :
    let s := fun ω => trajectory center D G0 α oracle (fun i => ξ i ω) n
    Integrable (fun ω => ⟪oracle (point α (s ω)) (ξ n ω), (s ω).2.2.1 - xstar⟫) P ∧
    Integrable (fun ω => ⟪∫ v, oracle (point α (s ω)) v ∂p, (s ω).2.2.1 - xstar⟫) P ∧
    (∫ ω, ⟪oracle (point α (s ω)) (ξ n ω), (s ω).2.2.1 - xstar⟫ ∂P) =
      ∫ ω, ⟪∫ v, oracle (point α (s ω)) v ∂p, (s ω).2.2.1 - xstar⟫ ∂P := by
  let history := fun ω (i : Fin n) => ξ i ω
  have hh : Measurable history := Measurable.of_eval (fun i => hξ.measurable i)
  let μ := P.map history
  let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).mpr inferInstance
  let fs := finiteState center D G0 α oracle n
  let query := fun a => point α (fs a)
  let direction := fun a => (fs a).2.2.1 - xstar
  have hfs : Measurable fs := measurable_finiteState center D G0 α ho.measurable n
  have hq : Measurable query := (measurable_point α).comp hfs
  have hd : Measurable direction := hfs.snd.snd.fst.sub measurable_const
  have hinv a := finiteState_invariant center hD hG0 hα hα1 oracle n a
  have hcenter : ‖center - xstar‖ ≤ D := by simpa only [norm_sub_rev] using hstar
  have hqb (a) : ‖query a - xstar‖ ≤ 2 * D := by
    have hball := point_mem_ball center (fs a) hα hα1 (hinv a).1 (hinv a).2.1
    calc ‖query a - xstar‖ ≤ ‖query a - center‖ + ‖center - xstar‖ := by simpa only [dist_eq_norm] using dist_triangle _ center xstar
         _ ≤ D + D := add_le_add hball hcenter
         _ = _ := by ring
  have hdb (a) : ‖direction a‖ ≤ 2 * D := by
    calc ‖direction a‖ ≤ ‖(fs a).2.2.1 - center‖ + ‖center - xstar‖ := by simpa only [dist_eq_norm] using dist_triangle _ center xstar
         _ ≤ D + D := add_le_add (hinv a).2.1 hcenter
         _ = _ := by ring
  have hX := fresh_oracle_l2 μ p ho hG0.le hG1 hG hGG hmin hq hqb M hM (by nlinarith : 2 * G * (2 * D) ≤ M)
  have hprod := fresh_inner_integrable μ p ho.measurable hq hd (hX.integrable (by norm_num)) hdb
  have h := independent_inner_identity P p hh (hξ.measurable n)
    (independent_prefix P hξ.independent hξ.measurable n) (hξ.marginal n) ho.integrable hprod
  have he (ω) : fs (history ω) = trajectory center D G0 α oracle (fun i => ξ i ω) n :=
    finiteState_eq center D G0 α oracle (fun i => ξ i ω) n
  simpa only [query, direction, he] using h

omit [CompleteSpace E] in
lemma trajectory_gap_integrable (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : ∀ i, Measurable (ξ i))
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 ≤ D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (n : ℕ) :
    Integrable (fun ω => f ((trajectory center D G0 α oracle (fun i => ξ i ω) n).2.1) - f xstar) P := by
  have hstate : Measurable (fun ω => trajectory center D G0 α oracle (fun i => ξ i ω) n) :=
    (measurable_trajectory_family D G0 α ho.measurable n).comp
      (measurable_const.prodMk (Measurable.of_eval hξ))
  have hb (ω) : ‖(trajectory center D G0 α oracle (fun i => ξ i ω) n).2.1 - xstar‖ ≤ 2 * D := by
    have hi := (trajectory_invariant center hD hG0 hα hα1 oracle (fun i => ξ i ω) n).1
    have hc : ‖center - xstar‖ ≤ D := by simpa only [norm_sub_rev] using hstar
    have ht := dist_triangle (trajectory center D G0 α oracle (fun i => ξ i ω) n).2.1 center xstar
    simp only [dist_eq_norm] at ht
    linarith
  exact bounded_query_gap_integrable P p hf ho hG0.le hG hGG hmin hstate.snd.fst hb M hM (by nlinarith)

end TrajectoryInner
section ExpectedO2B
variable {W E : Type} [MeasurableSpace W] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma integral_online_to_batch_step (P : Measure W) (f : E → ℝ) (prev z g : W → E) (xstar : E)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hip : Integrable (fun ω => f (prev ω) - f xstar) P)
    (hiq : Integrable (fun ω => f ((1 - α) • prev ω + α • z ω) - f xstar) P)
    (hic : Integrable (fun ω => ⟪g ω, z ω - xstar⟫) P)
    (hsub : ∀ ω y, f ((1 - α) • prev ω + α • z ω) - f y ≤
      ⟪g ω, (1 - α) • prev ω + α • z ω - y⟫) :
    (∫ ω, f ((1 - α) • prev ω + α • z ω) - f xstar ∂P) ≤
      (1 - α) * (∫ ω, f (prev ω) - f xstar ∂P) + α * (∫ ω, ⟪g ω, z ω - xstar⟫ ∂P) := by
  have h := integral_mono hiq ((hip.const_mul (1 - α)).add (hic.const_mul α))
    (fun ω => by
      exact LongTails.Proofs.GeneralizedLipschitzWarmStart.online_to_batch_step f (prev ω) (z ω) xstar (g ω) hα hα1 (hsub ω))
  simp only [Pi.add_apply] at h
  rw [integral_add (hip.const_mul (1 - α)) (hic.const_mul α), integral_const_mul, integral_const_mul] at h
  exact h

end ExpectedO2B
section TrajectoryO2B
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStart
variable {Ω E W : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma trajectory_expected_gap_step (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 ≤ D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (n : ℕ) :
    let s := fun k ω => trajectory center D G0 α oracle (fun i => ξ i ω) k
    (∫ ω, f ((s (n + 1) ω).2.1) - f xstar ∂P) ≤
      (1 - α) * (∫ ω, f ((s n ω).2.1) - f xstar ∂P) +
        α * (∫ ω, ⟪oracle (point α (s n ω)) (ξ n ω), (s n ω).2.2.1 - xstar⟫ ∂P) := by
  let s := fun k ω => trajectory center D G0 α oracle (fun i => ξ i ω) k
  have hi := trajectory_inner_identity P p hξ ho hG0 hG1 hG hGG hmin center hD hstar hα hα1 M hM hMD n
  have hip := trajectory_gap_integrable P p hξ.measurable hf ho hG0 hG hGG hmin center hD hstar hα hα1 M hM hMD n
  have hiq := trajectory_gap_integrable P p hξ.measurable hf ho hG0 hG hGG hmin center hD hstar hα hα1 M hM hMD (n + 1)
  have h := integral_online_to_batch_step P f (fun ω => (s n ω).2.1) (fun ω => (s n ω).2.2.1)
    (fun ω => ∫ v, oracle (point α (s n ω)) v ∂p) xstar hα hα1 hip hiq hi.2.1
    (fun ω y => ho.subgradient (point α (s n ω)) y)
  rw [← hi.2.2] at h
  exact h
lemma trajectory_expected_telescope (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 ≤ D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α < 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (N : ℕ) :
    let s := fun k ω => trajectory center D G0 α oracle (fun i => ξ i ω) k
    ((1 - α)⁻¹) ^ N * (∫ ω, f ((s N ω).2.1) - f xstar ∂P) ≤
      f center - f xstar + ∫ ω, ∑ i ∈ Finset.range N,
        ⟪weight α i • oracle (point α (s i ω)) (ξ i ω), (s i ω).2.2.1 - xstar⟫ ∂P := by
  let s := fun k ω => trajectory center D G0 α oracle (fun i => ξ i ω) k
  let gap := fun k => ∫ ω, f ((s k ω).2.1) - f xstar ∂P
  let cost := fun k => ∫ ω, ⟪oracle (point α (s k ω)) (ξ k ω), (s k ω).2.2.1 - xstar⟫ ∂P
  have hstep k : gap (k + 1) ≤ (1 - α) * gap k + α * cost k :=
    trajectory_expected_gap_step P p hξ hf ho hG0 hG1 hG hGG hmin center hD hstar hα hα1.le M hM hMD k
  have ht := weighted_gap_telescope hα1 gap cost hstep N
  have hzero : gap 0 = f center - f xstar := by simp [gap, s, trajectory, initial]
  rw [hzero] at ht
  have hic k : Integrable (fun ω => ⟪oracle (point α (s k ω)) (ξ k ω), (s k ω).2.2.1 - xstar⟫) P :=
    (trajectory_inner_identity P p hξ ho hG0 hG1 hG hGG hmin center hD hstar hα hα1.le M hM hMD k).1
  have hs : (∑ i ∈ Finset.range N, weight α i * cost i) =
      ∫ ω, ∑ i ∈ Finset.range N, ⟪weight α i • oracle (point α (s i ω)) (ξ i ω), (s i ω).2.2.1 - xstar⟫ ∂P := by
    simp_rw [real_inner_smul_left]
    rw [integral_finsetSum _ (fun i _ => (hic i).const_mul (weight α i))]
    simp only [integral_const_mul, cost]
  rw [hs] at ht
  exact ht

end TrajectoryO2B
section RegretSplit
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStart
variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
lemma trajectory_regret_split (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {D G G0 G1 α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hD : 0 < D) (hG0 : 0 < G0)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α < 1)
    (T : ℕ) (hT : 0 < T) (hκ : 1 ≤ D * G) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (ξ : ℕ → Ω) (N : ℕ) (hN : T ≤ N) :
    let s := trajectory center D G0 α oracle ξ
    let gap := fun i => f (s (i + 1)).2.1 - f xstar
    (∑ i ∈ Finset.range N, ⟪weight α i • oracle (point α (s i)) (ξ i), (s i).2.2.1 - xstar⟫) ≤
      3 * D * G0 + 3 * D * Real.sqrt (∑ i ∈ Finset.range N,
        (weight α i) ^ 2 * ‖noisePart f xstar G oracle (point α (s i)) (ξ i)‖ ^ 2) +
      (15 * D * G / Real.sqrt T) * (∑ i ∈ Finset.range N, weight α i * gap i) +
      (69 * Real.sqrt T * α * D ^ 2 * G * G0) * (∑ i ∈ Finset.range N, weight α i) := by
  let s := trajectory center D G0 α oracle ξ
  have hr := trajectory_regret center xstar hD hG0 hα hα1.le hstar oracle ξ N
  have he := oracle_energy_split (Finset.range N) (weight α) (fun i => point α (s i)) ξ f xstar oracle hG hmin
  have hl := trajectory_weighted_l2 (center := center) p ho hD.le hG0 hG hGG hmin hα hα1 T hT hκ hsmall ξ N hN
  have hp (i) : point α (s i) = (s (i + 1)).2.1 := rfl
  simp only [hp] at he
  have hh := he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl hG))
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 3 * D)
  apply hr.trans
  apply (add_le_add le_rfl hh').trans_eq
  change 3 * D * G0 + 3 * D * (Real.sqrt (∑ i ∈ Finset.range N,
    (weight α i) ^ 2 * ‖noisePart f xstar G oracle (point α (s i)) (ξ i)‖ ^ 2) +
      G * ((5 / Real.sqrt T) * (∑ i ∈ Finset.range N, weight α i * (f (s (i + 1)).2.1 - f xstar)) +
        (23 * Real.sqrt T * α * D * G0) * (∑ i ∈ Finset.range N, weight α i))) = _
  ring

end RegretSplit
lemma probability_gt_of_small_integral {W : Type*} [MeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] {X : W → ℝ} {ε δ : ℝ}
    (hi : Integrable X P) (hn : ∀ ω, 0 ≤ X ω) (hε : 0 < ε)
    (hb : (∫ ω, X ω ∂P) ≤ ε * δ) :
    P {ω | ε < X ω} ≤ ENNReal.ofReal δ := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hi ε
  have hr : P.real {ω | ε ≤ X ω} ≤ δ := by nlinarith
  apply (measure_mono (show {ω | ε < X ω} ⊆ {ω | ε ≤ X ω} from fun ω hω => (show ε ≤ X ω from le_of_lt hω))).trans
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hr


section ExpectedRaw
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Proofs.GeneralizedLipschitzWarmStart
variable {Ω E W : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma trajectory_expected_raw_bound (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 < D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α < 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (T : ℕ) (hT : 0 < T) (hκ : 1 ≤ D * G) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (N : ℕ) (hN : T ≤ N) :
    let s := fun k ω => trajectory center D G0 α oracle (fun i => ξ i ω) k
    ((1 - α)⁻¹) ^ N * (∫ ω, f ((s N ω).2.1) - f xstar ∂P) ≤
      f center - f xstar + 3 * D * G0 + 3 * D * G0 * Real.sqrt α * ((1 - α)⁻¹) ^ N +
      (15 * D * G / Real.sqrt T) * (∑ i ∈ Finset.range N, weight α i * (∫ ω, f ((s (i + 1) ω).2.1) - f xstar ∂P)) +
      (69 * Real.sqrt T * α * D ^ 2 * G * G0) * (∑ i ∈ Finset.range N, weight α i) := by
  let s := fun k ω => trajectory center D G0 α oracle (fun i => ξ i ω) k
  let U := fun i ω => noisePart f xstar G oracle (point α (s i ω)) (ξ i ω)
  let A := fun ω => Real.sqrt (∑ i ∈ Finset.range N, (weight α i) ^ 2 * ‖U i ω‖ ^ 2)
  let B := fun ω => ∑ i ∈ Finset.range N, weight α i * (f ((s (i + 1) ω).2.1) - f xstar)
  let C := 69 * Real.sqrt T * α * D ^ 2 * G * G0 * (∑ i ∈ Finset.range N, weight α i)
  let c := 15 * D * G / Real.sqrt T
  have hu i := trajectory_noise_secondMoment P p hξ hf ho hG.le hGG hmin center D α i
  have hA := integral_weighted_noise P hG0.le hα hα1 N (fun i => (hu i).1) (fun i => (hu i).2)
  have hgap i := trajectory_gap_integrable P p hξ.measurable hf ho hG0 hG hGG hmin center hD.le hstar hα hα1.le M hM hMD i
  have hB : Integrable B P := integrable_finsetSum _ (fun i _ => (hgap (i + 1)).const_mul _)
  have hcost i := (trajectory_inner_identity P p hξ ho hG0 hG1 hG hGG hmin center hD.le hstar hα hα1.le M hM hMD i).1
  have hcostW i : Integrable (fun ω => ⟪weight α i • oracle (point α (s i ω)) (ξ i ω), (s i ω).2.2.1 - xstar⟫) P := by
    simpa only [real_inner_smul_left] using (hcost i).const_mul (weight α i)
  have hsum : Integrable (fun ω => ∑ i ∈ Finset.range N, ⟪weight α i • oracle (point α (s i ω)) (ξ i ω), (s i ω).2.2.1 - xstar⟫) P :=
    integrable_finsetSum _ (fun i _ => hcostW i)
  have hR : Integrable (fun ω => 3 * D * G0 + 3 * D * A ω + c * B ω + C) P :=
    (((integrable_const _).add (hA.1.const_mul _)).add (hB.const_mul _)).add (integrable_const _)
  have hr := integral_mono hsum hR (fun ω =>
    trajectory_regret_split p ho hD hG0 hG.le hGG hmin hstar hα hα1 T hT hκ hsmall (fun i => ξ i ω) N hN)
  have he : (∫ ω, 3 * D * G0 + 3 * D * A ω + c * B ω + C ∂P) =
      3 * D * G0 + 3 * D * (∫ ω, A ω ∂P) + c * (∫ ω, B ω ∂P) + C := by
    have hAi : Integrable A P := hA.1
    have h1 : Integrable (fun ω => 3 * D * G0 + 3 * D * A ω) P :=
      (integrable_const _).add (hAi.const_mul _)
    have h2 : Integrable (fun ω => 3 * D * G0 + 3 * D * A ω + c * B ω) P :=
      h1.add (hB.const_mul c)
    rw [integral_add h2 (integrable_const C), integral_add h1 (hB.const_mul c),
      integral_add (integrable_const (3 * D * G0)) (hAi.const_mul (3 * D))]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [he] at hr
  have hb : (∫ ω, B ω ∂P) = ∑ i ∈ Finset.range N, weight α i * (∫ ω, f ((s (i + 1) ω).2.1) - f xstar ∂P) := by
    rw [integral_finsetSum _ (fun i _ => (hgap (i + 1)).const_mul _)]
    simp only [integral_const_mul]
    rfl
  rw [hb] at hr
  have hnoise := mul_le_mul_of_nonneg_left hA.2 (by positivity : 0 ≤ 3 * D)
  have ht := trajectory_expected_telescope P p hξ hf ho hG0 hG1 hG hGG hmin center hD.le hstar hα hα1 M hM hMD N
  dsimp only [c, C] at hr
  nlinarith [hr, ht, hnoise]

lemma trajectory_expected_recurrence (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 < D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 ≤ α) (hα1 : α < 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (T : ℕ) (hT : 0 < T) (hκ : 1 ≤ D * G) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (hlarge : 60 * D * G ≤ Real.sqrt T) (hinit : f center - f xstar ≤ 64 * D * G0)
    (N : ℕ) :
    let z := fun k => ((1 - α)⁻¹) ^ k * (∫ ω,
      f ((trajectory center D G0 α oracle (fun i => ξ i ω) k).2.1) - f xstar ∂P)
    z N ≤ 512 * D * G0 + (D * G0 * (3 * Real.sqrt α + 192 * T * α)) * ((1 - α)⁻¹) ^ N +
      (α / 4) * (∑ i ∈ Finset.range N, z (i + 1)) := by
  let gap := fun k => ∫ ω, f ((trajectory center D G0 α oracle (fun i => ξ i ω) k).2.1) - f xstar ∂P
  let z := fun k => ((1 - α)⁻¹) ^ k * gap k
  have hz (k) : 0 ≤ z k := mul_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hα1).le) k)
    (integral_nonneg (fun ω => sub_nonneg.mpr (hmin _)))
  have hearly (k) (hk : k < T) : z k ≤ 200 * D * G0 := by
    have hi := trajectory_gap_integrable P p hξ.measurable hf ho hG0 hG hGG hmin center hD.le hstar hα hα1.le M hM hMD k
    have hb := integral_mono hi (integrable_const (100 * D * G0)) (fun ω =>
      trajectory_initial_gap (center := center) p ho hD.le hG0 hG.le hGG hmin hα hα1.le T hκ hsmall hinit (fun i => ξ i ω) k (by omega))
    simp only [integral_const, probReal_univ, one_smul] at hb
    have hαT : α * T ≤ 1 / 16 := by
      have hh := mul_le_mul_of_nonneg_left hκ (mul_nonneg hα (Nat.cast_nonneg T))
      nlinarith
    have hkT : (k : ℝ) ≤ T := by exact_mod_cast hk.le
    have hp := inverse_weight_power_bound hα1 k (by nlinarith [mul_le_mul_of_nonneg_left hkT hα])
    have hp' := mul_le_mul_of_nonneg_right hp (show 0 ≤ 100 * D * G0 by positivity)
    have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hα1).le) k)
    dsimp [z, gap]
    nlinarith
  have hraw (k) (hk : T ≤ k) := trajectory_expected_raw_bound P p hξ hf ho hG0 hG1 hG hGG hmin center hD hstar hα hα1 M hM hMD T hT hκ hsmall k hk
  have hsum (k) : (∑ i ∈ Finset.range k, weight α i * gap (i + 1)) = α * (∑ i ∈ Finset.range k, z (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [weight, z]
    ring
  apply warm_recurrence_from_raw hD.le hG.le hG0.le hα hα1 T hT hlarge hinit z hz hearly
  intro k hk
  have h := hraw k hk
  change z k ≤ f center - f xstar + 3 * D * G0 + 3 * D * G0 * Real.sqrt α * ((1 - α)⁻¹) ^ k +
    (15 * D * G / Real.sqrt T) * (∑ i ∈ Finset.range k, weight α i * gap (i + 1)) +
    (69 * Real.sqrt T * α * D ^ 2 * G * G0) * (∑ i ∈ Finset.range k, weight α i) at h
  rw [hsum] at h
  simpa only [mul_assoc] using h

lemma trajectory_expected_bound (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 < D) (hstar : ‖xstar - center‖ ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (M : ℕ) (hM : 0 < M) (hMD : 4 * G * D ≤ M) (T : ℕ) (hT : 0 < T) (hκ : 1 ≤ D * G) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (hlarge : 60 * D * G ≤ Real.sqrt T) (hinit : f center - f xstar ≤ 64 * D * G0)
    (N : ℕ) :
    (∫ ω, f ((trajectory center D G0 α oracle (fun i => ξ i ω) N).2.1) - f xstar ∂P) ≤
      (512 * D * G0) * Real.exp (-3 * α * N / 4) +
        4 * (D * G0 * (3 * Real.sqrt α + 192 * T * α)) / 3 := by
  let z := fun k => ((1 - α)⁻¹) ^ k * (∫ ω,
    f ((trajectory center D G0 α oracle (fun i => ξ i ω) k).2.1) - f xstar ∂P)
  have hrec k := trajectory_expected_recurrence P p hξ hf ho hG0 hG1 hG hGG hmin center hD hstar hα.le hα1 M hM hMD T hT hκ hsmall hlarge hinit k
  have h := recurrence_exponential hα hα1 (show 0 ≤ 512 * D * G0 by positivity)
    (show 0 ≤ D * G0 * (3 * Real.sqrt α + 192 * T * α) by positivity) z hrec N
  have hc : (1 - α) ^ N * ((1 - α)⁻¹) ^ N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (sub_pos.mpr hα1).ne', one_pow]
  dsimp only [z] at h
  rw [← mul_assoc, hc, one_mul] at h
  exact h

lemma trajectory_tuned_expected (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D ε : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 < D) (hstar : ‖xstar - center‖ ≤ D) (hκ : 1 ≤ D * G)
    (hinit : f center - f xstar ≤ 64 * D * G0) (hε : 0 < ε) :
    let T := ⌈(96 * D * G) ^ 2⌉₊
    let α := min (1 / (16 * T * (D * G))) (min ((ε / (24 * D * G0)) ^ 2) (ε / (1536 * T * D * G0)))
    let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / ε))⌉₊
    (∫ ω, f ((trajectory center D G0 α oracle (fun i => ξ i ω) K).2.1) - f xstar ∂P) ≤ ε := by
  let T := ⌈(96 * D * G) ^ 2⌉₊
  let α := min (1 / (16 * T * (D * G))) (min ((ε / (24 * D * G0)) ^ 2) (ε / (1536 * T * D * G0)))
  let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / ε))⌉₊
  have ht := warm_block_tuning hD hG
  have ha := warm_step_tuning hD hG hG0 hε T ht.1 hκ
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (4 * G * D))
  have hMp : 0 < M := by exact_mod_cast ((le_max_left 0 (4 * G * D)).trans_lt hM)
  have hMD : 4 * G * D ≤ M := (le_max_right 0 (4 * G * D)).trans hM.le
  have hb := trajectory_expected_bound P p hξ hf ho hG0 hG1 hG hGG hmin center hD hstar ha.1 ha.2.1 M hMp hMD T ht.1 hκ ha.2.2.1 ht.2 hinit K
  have hk := warm_horizon_bound ha.1 (show 0 ≤ 512 * D * G0 by positivity) hε ha.2.2.2
  have he : 2 * (512 * D * G0) = 1024 * D * G0 := by ring
  rw [he] at hk
  exact hb.trans hk

lemma trajectory_tuned_confidence (P : Measure W) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {ξ : ℕ → W → Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {f : E → ℝ} (hf : Measurable f) {xstar : E} {oracle : E → Ω → E} {G0 G1 G D ε : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hG0 : 0 < G0) (hG1 : 0 ≤ G1)
    (hG : 0 < G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (center : E) (hD : 0 < D) (hstar : ‖xstar - center‖ ≤ D) (hκ : 1 ≤ D * G)
    (hinit : f center - f xstar ≤ 64 * D * G0) (hε : 0 < ε) :
    let T := ⌈(96 * D * G) ^ 2⌉₊
    let α := min (1 / (16 * T * (D * G))) (min ((ε / (24 * D * G0)) ^ 2) (ε / (1536 * T * D * G0)))
    let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / ε))⌉₊
    P {ω | 20 * ε < f ((trajectory center D G0 α oracle (fun i => ξ i ω) K).2.1) - f xstar} ≤
      ENNReal.ofReal (1 / 20 : ℝ) := by
  let T := ⌈(96 * D * G) ^ 2⌉₊
  let α := min (1 / (16 * T * (D * G))) (min ((ε / (24 * D * G0)) ^ 2) (ε / (1536 * T * D * G0)))
  let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / ε))⌉₊
  have ht := warm_block_tuning hD hG
  have ha := warm_step_tuning hD hG hG0 hε T ht.1 hκ
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (4 * G * D))
  have hMp : 0 < M := by exact_mod_cast ((le_max_left 0 (4 * G * D)).trans_lt hM)
  have hMD : 4 * G * D ≤ M := (le_max_right 0 (4 * G * D)).trans hM.le
  have hi := trajectory_gap_integrable P p hξ.measurable hf ho hG0 hG hGG hmin center hD.le hstar ha.1.le ha.2.1.le M hMp hMD K
  have hm := trajectory_tuned_expected P p hξ hf ho hG0 hG1 hG hGG hmin center hD hstar hκ hinit hε
  apply probability_gt_of_small_integral P hi (fun ω => sub_nonneg.mpr (hmin _)) (show 0 < 20 * ε by positivity)
  convert hm using 1
  ring

end ExpectedRaw
end LongTails.Proofs.GeneralizedLipschitzWarmStartSampling
