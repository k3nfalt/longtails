import LongTails.Proofs.SpikedSoftCutEpochProcess
import LongTails.Proofs.SpikedSoftCutMeasurable
import LongTails.Proofs.SpikedSoftCutTuning

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LongTails.Proofs.SpikedSoftCutFreshness

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutEpochProcess
open SpikedSoftCutMeasurable
open CovarianceSoftCutProcess
open LongTails.Algorithms.CovarianceSoftCut

lemma measurable_innerSeedCuts (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun z : ℝ × (ℕ → q.Ω) =>
      sampleCuts (innerParams q c.α) c.α (2/c.α) c.b (innerOracle q z.1 g) n z.2) := by
  have hRp : 0 < (innerParams q c.α).R := by dsimp [innerParams]; positivity
  induction n with
  | zero => exact Measurable.of_eval fun i => Fin.elim0 i
  | succ n ih =>
    let point := fun z : ℝ × (ℕ → q.Ω) => centroid (innerParams q c.α) c.α (2/c.α)
      (List.ofFn (sampleCuts (innerParams q c.α) c.α (2/c.α) c.b (innerOracle q z.1 g) n z.2))
    have hx : Measurable point :=
      (CovarianceSoftCutDensity.continuous_centroid_ofFn (innerParams q c.α) hRp c.α (2/c.α) n).measurable.comp ih
    have hj : Measurable (fun z : ℝ × (ℕ → q.Ω) => join q z.1 (point z)) :=
      (SpikedSoftCutCoordinates.continuous_join q).measurable.comp (measurable_fst.prodMk hx)
    have hgi (i : Fin c.b) : Measurable (fun z : ℝ × (ℕ → q.Ω) =>
        innerOracle q z.1 g (point z) (z.2 (n*c.b+i))) :=
      (SpikedSoftCutCoordinates.continuous_tail q).measurable.comp
        (hg.comp (hj.prodMk ((measurable_pi_apply (n*c.b+i)).comp measurable_snd)))
    have hm : Measurable (fun z : ℝ × (ℕ → q.Ω) =>
        (1/(c.b : ℝ)) • ∑ i : Fin c.b, innerOracle q z.1 g (point z) (z.2 (n*c.b+i))) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [sampleCuts, Fin.append_left, Function.comp_def] using (measurable_pi_apply j).comp ih
    · simp only [sampleCuts, Fin.append_right]
      change Measurable (fun z : ℝ × (ℕ → q.Ω) =>
        ((1/(c.b : ℝ)) • ∑ i : Fin c.b, innerOracle q z.1 g (point z) (z.2 (n*c.b+i)), point z))
      exact hm.prodMk hx

lemma measurable_innerSeedPoint (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun z : ℝ × (ℕ → q.Ω) => innerSeedPoint q c z.1 g n z.2) :=
  (CovarianceSoftCutDensity.continuous_centroid_ofFn (innerParams q c.α)
    (by dsimp [innerParams]; positivity) c.α (2/c.α) n).measurable.comp
      (measurable_innerSeedCuts q c hR g hg n)

lemma measurable_innerSeedReplies (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : ℝ × (ℕ → q.Ω) => innerSeedReplies q c z.1 g z.2) := by
  apply Measurable.of_eval
  intro i
  exact hg.comp (((SpikedSoftCutCoordinates.continuous_join q).measurable.comp
    (measurable_fst.prodMk (measurable_innerSeedPoint q c hR g hg (i/c.b)))).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_epochReplies (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun z : OuterState q × (ℕ → q.Ω) => epochReplies q c k z.1 g z.2) := by
  have hi : Measurable (fun z : OuterState q × (ℕ → q.Ω) =>
      innerSeedReplies q c (center q z.1) g z.2) :=
    (measurable_innerSeedReplies q c hR g hg).comp (measurable_fst.fst.prodMk measurable_snd)
  apply Measurable.of_eval
  intro i
  by_cases h : i < c.T*c.b
  · simp only [epochReplies, h, ite_true]
    exact (measurable_pi_apply i).comp hi
  · simp only [epochReplies, h, ite_false]
    exact hg.comp (((measurable_scalarQuery q c hR k (i-c.T*c.b)).comp
      (measurable_fst.prodMk hi)).prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_seeded_nextState (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    @Measurable (OuterState q × (ℕ → q.Ω)) (OuterState q) _ _
      (fun z => nextState q c k z.1 (epochReplies q c k z.1 g z.2)) := by
  have hi : Measurable (fun z : OuterState q × (ℕ → q.Ω) =>
      (z.1, epochReplies q c k z.1 g z.2)) :=
    measurable_fst.prodMk (measurable_epochReplies q c hR g hg k)
  have hh := (measurable_nextState q c hR k).comp hi
  change Measurable (fun z : OuterState q × (ℕ → q.Ω) =>
    nextState q c k z.1 (epochReplies q c k z.1 g z.2)) at hh
  exact hh

lemma stratified_head_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (P : Measure Ξ)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (hTop : 0 ≤ q.vTop)
    (T N : ℕ) (hN : 0 < N) (w : Fin T → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (points : Fin T → Space q)
    (ξ : ((i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊) → Ξ → q.Ω)
    (hξ : ∀ j, Measurable (ξ j)) (hind : iIndepFun ξ P) (hlaw : ∀ j, P.map (ξ j) = p) :
    HasSubgaussianMGF (fun ω =>
      (∑ i, w i/(⌈(N : ℝ)*w i⌉₊ : ℝ) * ∑ j, head q (g (points i) (ξ ⟨i,j⟩ ω))) -
        ∑ i, w i*head q (v (points i))) ⟨q.vTop/N, by positivity⟩ P := by
  let X := fun j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊ =>
    fun ω => head q (g (points j.1) (ξ j ω)-v (points j.1))
  have hm (j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊) :
      Measurable (fun seed => head q (g (points j.1) seed-v (points j.1))) :=
    (SpikedSoftCutCoordinates.continuous_head q).measurable.comp
      ((hg.measurable.comp (measurable_const.prodMk measurable_id)).sub measurable_const)
  have hi : iIndepFun X P := hind.comp _ hm
  have hx (j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊) : HasSubgaussianMGF (X j) ⟨q.vTop, hTop⟩ P := by
    have hp : HasSubgaussianMGF (fun seed => head q (g (points j.1) seed-v (points j.1))) ⟨q.vTop, hTop⟩ p := by
      refine ⟨fun t => (SpikedSoftCutCoordinates.head_direction_exp q p f v g hg (points j.1) t).1, ?_⟩
      intro t
      apply (SpikedSoftCutCoordinates.head_direction_exp q p f v g hg (points j.1) t).2.trans_eq
      congr 1
      change t^2*q.vTop/2 = q.vTop*t^2/2
      ring
    exact HasSubgaussianMGF.of_map (hξ j).aemeasurable (by rw [hlaw j]; exact hp)
  have hh := StratifiedSubGaussianSampling.stratified_sum_mgf N hN w hw hsum X hi ⟨q.vTop, hTop⟩ hx
  have he (ω : Ξ) :
      (∑ i, w i/(⌈(N : ℝ)*w i⌉₊ : ℝ) * ∑ j, head q (g (points i) (ξ ⟨i,j⟩ ω))) -
        ∑ i, w i*head q (v (points i)) =
      ∑ j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊,
        (w j.1/(⌈(N : ℝ)*w j.1⌉₊ : ℝ))*X j ω := by
    exact StratifiedSubGaussianSampling.stratified_centered_identity N hN w hw
      (fun i => head q (v (points i))) (fun j => head q (g (points j.1) (ξ j ω)))
  simp_rw [he]
  exact hh

lemma fixed_reply_head_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (hN : 0 < c.N k) (a : ℝ) (r : ℕ → Space q)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ)
    (ξ : ℕ → Ξ → q.Ω) (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (hTop : 0 ≤ q.vTop) :
    HasSubgaussianMGF (fun ω =>
      (∑ i : Fin c.T, weights q c r i/(⌈(c.N k : ℝ)*weights q c r i⌉₊ : ℝ) *
        ∑ j : Fin ⌈(c.N k : ℝ)*weights q c r i⌉₊,
          head q (g (join q a (supportPoints q c r i)) (ξ (sampleStart q c k r i+j) ω))) -
      ∑ i : Fin c.T, weights q c r i*head q (v (join q a (supportPoints q c r i))))
      ⟨q.vTop/(c.N k), by positivity⟩ P := by
  have hw (i : Fin c.T) : 0 ≤ weights q c r i :=
    SpikedSoftCutSelection.certificateWeights_nonneg q c.α c.T c.n hn _ _ i
  have hs : ∑ i, weights q c r i = 1 :=
    SpikedSoftCutSelection.certificateWeights_sum q c.α c.T c.n hT _ _
  have hindex : Function.Injective (fun j : (i : Fin c.T) × Fin ⌈(c.N k : ℝ)*weights q c r i⌉₊ =>
      sampleStart q c k r j.1+j.2) := by
    have hh := SpikedSoftCutMethodExecution.scalarSampleIndex_injective q c k r
    change Function.Injective (fun j : (i : Fin c.T) × Fin (sampleCount q c k r i) =>
      sampleStart q c k r j.1+j.2) at hh
    have hc (i : Fin c.T) : sampleCount q c k r i = ⌈(c.N k : ℝ)*weights q c r i⌉₊ := by
      simp only [sampleCount, i.isLt, dite_true]
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have he : (⟨i, ⟨a, by rw [hc]; exact a.isLt⟩⟩ : (i : Fin c.T) × Fin (sampleCount q c k r i)) =
        ⟨j, ⟨b, by rw [hc]; exact b.isLt⟩⟩ := hh hab
    have hij : i = j := congrArg Sigma.fst he
    subst j
    have hab' := congrArg (fun x : (i : Fin c.T) × Fin (sampleCount q c k r i) => x.2.val) he
    have heq : a = b := Fin.ext hab'
    subst b
    rfl
  exact stratified_head_mgf q p P f v g hg hTop c.T (c.N k) hN (weights q c r) hw hs
    (fun i => join q a (supportPoints q c r i))
    (fun j => ξ (sampleStart q c k r j.1+j.2))
    (fun j => hξ.measurable _) (hξ.independent.precomp hindex) (fun j => hξ.marginal _)

lemma scalarEstimate_split (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (g : Space q → q.Ω → Space q) (z : q.Ω) (b : Fin (c.T*c.b) → q.Ω) (ξ : ℕ → q.Ω) :
    let pref := SoftCutPredictableBatches.prefixStream z (c.T*c.b) b
    let r := innerSeedReplies q c (center q state) g pref
    scalarEstimate q c k (epochReplies q c k state g
      ((OracleTemplate.StochasticGeneralized.splitStream (c.T*c.b)).symm (b,ξ))) =
      ∑ i : Fin c.T, weights q c r i/sampleCount q c k r i *
        ∑ j ∈ Finset.range (sampleCount q c k r i),
          head q (g (join q (center q state) (supportPoints q c r i)) (ξ (sampleStart q c k r i+j))) := by
  dsimp only
  let pref := SoftCutPredictableBatches.prefixStream z (c.T*c.b) b
  let seeds := (OracleTemplate.StochasticGeneralized.splitStream (c.T*c.b)).symm (b,ξ)
  let r := innerSeedReplies q c (center q state) g pref
  let s := innerSeedReplies q c (center q state) g seeds
  have hp : ∀ i, i < c.T*c.b → s i = r i := by
    intro i hi
    apply innerSeedReplies_seed_prefix q c (center q state) g (c.T*c.b) seeds pref _ i hi
    intro j hj
    change (if h : j < c.T*c.b then b ⟨j,h⟩ else ξ (j-c.T*c.b)) =
      (if h : j < c.T*c.b then b ⟨j,h⟩ else z)
    simp only [hj, dite_true]
  rw [scalarEstimate_epochReplies]
  change (∑ i : Fin c.T, weights q c s i/sampleCount q c k s i *
    ∑ j ∈ Finset.range (sampleCount q c k s i),
      head q (g (join q (center q state) (supportPoints q c s i))
        (seeds (c.T*c.b+sampleStart q c k s i+j)))) = _
  rw [SpikedSoftCutMethodExecution.weights_prefix q c s r hp,
    SpikedSoftCutMethodExecution.sampleCount_prefix q c k s r hp,
    SpikedSoftCutMethodExecution.sampleStart_prefix q c k s r hp,
    SpikedSoftCutMethodExecution.supportPoints_prefix q c s r hp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hn : ¬c.T*c.b+sampleStart q c k r i+j < c.T*c.b := by omega
  have he : c.T*c.b+sampleStart q c k r i+j-c.T*c.b = sampleStart q c k r i+j := by omega
  have hseed : seeds (c.T*c.b+sampleStart q c k r i+j) = ξ (sampleStart q c k r i+j) := by
    change (if h : c.T*c.b+sampleStart q c k r i+j < c.T*c.b then b ⟨_,h⟩
      else ξ (c.T*c.b+sampleStart q c k r i+j-c.T*c.b)) = _
    rw [dite_eq_right hn, he]
  rw [hseed]

lemma scalar_failure_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (X : Ξ → ℝ) (v : ℝ≥0)
    (hX : HasSubgaussianMGF X v P) (ε r K : ℝ) (hε : 0 < ε) (hr : 0 < r) (hK : 1 ≤ K)
    (hv : (v : ℝ) ≤ ε^2/(8192*K*r^2)) :
    P.real {ω | ε/(8*r) < |X ω|} ≤ 2*Real.exp (-64*K) := by
  have hKp : 0 < K := by linarith
  let ν : ℝ≥0 := ⟨ε^2/(8192*K*r^2), by positivity⟩
  have hm : HasSubgaussianMGF X ν P := StratifiedSubGaussianSampling.weaken_proxy hX hv
  have ht := SubGaussianNetProbability.abs_tail hm (ε/(8*r)) (by positivity)
  have he : -(ε/(8*r))^2/(2*(ν : ℝ)) = -64*K := by
    change -(ε/(8*r))^2/(2*(ε^2/(8192*K*r^2))) = -64*K
    field_simp
    ring
  rw [he] at ht
  exact ht

lemma product_event_probability {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (E : Set (A × B)) (hE : MeasurableSet E) (ρ : ℝ)
    (hsection : ∀ a, Q.real ((Prod.mk a) ⁻¹' E) ≤ ρ) : (P.prod Q).real E ≤ ρ := by
  let F : A × B → ℝ := E.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hFi : Integrable F (P.prod Q) := by
    apply (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ E <;> simp [F, hz]
  have hsect (a : A) : (∫ b, F (a,b) ∂Q) ≤ ρ := by
    have hm : MeasurableSet ((Prod.mk a) ⁻¹' E) := measurable_prodMk_left hE
    have he : (fun b => F (a,b)) = ((Prod.mk a) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
      funext b
      by_cases hb : (a,b) ∈ E <;> simp [F, hb]
    rw [he, integral_indicator_const 1 hm]
    simpa using hsection a
  have hh := integral_mono hFi.integral_prod_left (integrable_const ρ) hsect
  rw [← integral_prod _ hFi] at hh
  change (∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂P.prod Q) ≤ _ at hh
  rw [integral_indicator_const (1 : ℝ) hE] at hh
  simpa using hh

lemma split_event_probability {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) (E : Set (ℕ → Ω))
    (hE : MeasurableSet E) (ρ : ℝ)
    (hsection : ∀ b : Fin n → Ω, (Measure.infinitePi fun _ : ℕ => p).real
      {ξ | (OracleTemplate.StochasticGeneralized.splitStream n).symm (b,ξ) ∈ E} ≤ ρ) :
    (Measure.infinitePi fun _ : ℕ => p).real E ≤ ρ := by
  let e := OracleTemplate.StochasticGeneralized.splitStream (Ω := Ω) n
  have hp := product_event_probability (Measure.pi fun _ : Fin n => p)
    (Measure.infinitePi fun _ : ℕ => p) (e.symm ⁻¹' E) (e.symm.measurable hE) ρ hsection
  have he := MeasurePreserving.symm e (OracleTemplate.StochasticGeneralized.splitStream_preserving p n)
  rw [he.measureReal_preimage hE.nullMeasurableSet] at hp
  exact hp

noncomputable def headSlope (q : Params) (c : Config) (a : ℝ) (v : Space q → Space q)
    (r : ℕ → Space q) : ℝ := ∑ i : Fin c.T, weights q c r i*head q (v (join q a (supportPoints q c r i)))

lemma headSlope_prefix (q : Params) (c : Config) (a : ℝ) (v : Space q → Space q)
    (r s : ℕ → Space q) (h : ∀ i, i < c.T*c.b → r i = s i) :
    headSlope q c a v r = headSlope q c a v s := by
  unfold headSlope
  rw [SpikedSoftCutMethodExecution.weights_prefix q c r s h,
    SpikedSoftCutMethodExecution.supportPoints_prefix q c r s h]

lemma measurable_headSlope (q : Params) (c : Config) (hR : 0 < q.R)
    (v : Space q → Space q) (hv : Measurable v) :
    Measurable (fun z : ℝ × (ℕ → Space q) => headSlope q c z.1 v z.2) := by
  apply Finset.measurable_sum
  intro i _
  have hw : Measurable (fun z : ℝ × (ℕ → Space q) => weights q c z.2 i) :=
    ((measurable_pi_apply i).comp (measurable_weights q c hR)).comp measurable_snd
  have hx : Measurable (fun z : ℝ × (ℕ → Space q) => supportPoints q c z.2 i) :=
    ((measurable_pi_apply i).comp (measurable_supportPoints q c hR)).comp measurable_snd
  exact hw.mul ((SpikedSoftCutCoordinates.continuous_head q).measurable.comp
    (hv.comp ((SpikedSoftCutCoordinates.continuous_join q).measurable.comp (measurable_fst.prodMk hx))))

noncomputable def epochScalarError (q : Params) (c : Config) (k : ℕ) (s : OuterState q)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ : ℕ → q.Ω) : ℝ :=
  scalarEstimate q c k (epochReplies q c k s g ξ) -
    headSlope q c (center q s) v (innerSeedReplies q c (center q s) g ξ)

lemma measurable_epochScalarError (q : Params) (c : Config) (hR : 0 < q.R) (k : ℕ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    @Measurable (OuterState q × (ℕ → q.Ω)) ℝ _ _
      (fun z => epochScalarError q c k z.1 g v z.2) := by
  have harg : Measurable (fun z : OuterState q × (ℕ → q.Ω) => (center q z.1, z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hi : Measurable (fun z : OuterState q × (ℕ → q.Ω) =>
      innerSeedReplies q c (center q z.1) g z.2) :=
    (measurable_innerSeedReplies q c hR g hg).comp harg
  have he : Measurable (fun z : OuterState q × (ℕ → q.Ω) => scalarEstimate q c k (epochReplies q c k z.1 g z.2)) :=
    (measurable_scalarEstimate q c hR k).comp (measurable_epochReplies q c hR g hg k)
  have hp : Measurable (fun z : OuterState q × (ℕ → q.Ω) =>
      (center q z.1, innerSeedReplies q c (center q z.1) g z.2)) :=
    measurable_fst.fst.prodMk hi
  have hs := (measurable_headSlope q c hR v hv).comp hp
  convert! he.sub hs using 1

lemma split_scalar_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n) (k : ℕ) (hN : 0 < c.N k)
    (state : OuterState q) (z : q.Ω) (b : Fin (c.T*c.b) → q.Ω)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ)
    (ξ : ℕ → Ξ → q.Ω) (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (hTop : 0 ≤ q.vTop) :
    HasSubgaussianMGF (fun ω => epochScalarError q c k state g v
      ((OracleTemplate.StochasticGeneralized.splitStream (c.T*c.b)).symm (b,fun j => ξ j ω)))
      ⟨q.vTop/(c.N k), by positivity⟩ P := by
  let pref := SoftCutPredictableBatches.prefixStream z (c.T*c.b) b
  let r := innerSeedReplies q c (center q state) g pref
  have hh := fixed_reply_head_mgf q c hT hn k hN (center q state) r p P ξ hξ f v g hg hTop
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro ω
  let seeds := (OracleTemplate.StochasticGeneralized.splitStream (c.T*c.b)).symm (b,fun j => ξ j ω)
  have hp : ∀ i, i < c.T*c.b → innerSeedReplies q c (center q state) g seeds i = r i := by
    intro i hi
    apply innerSeedReplies_seed_prefix q c (center q state) g (c.T*c.b) seeds pref _ i hi
    intro j hj
    change (if h : j < c.T*c.b then b ⟨j,h⟩ else ξ (j-c.T*c.b) ω) =
      (if h : j < c.T*c.b then b ⟨j,h⟩ else z)
    simp only [hj, dite_true]
  change _ = scalarEstimate q c k (epochReplies q c k state g seeds) -
    headSlope q c (center q state) v (innerSeedReplies q c (center q state) g seeds)
  rw [headSlope_prefix q c (center q state) v _ r hp]
  have he := scalarEstimate_split q c k state g z b (fun j => ξ j ω)
  change scalarEstimate q c k (epochReplies q c k state g seeds) = _ at he
  rw [he]
  change _ - headSlope q c (center q state) v r = _ - headSlope q c (center q state) v r
  apply congrArg (fun x : ℝ => x-headSlope q c (center q state) v r)
  apply Finset.sum_congr rfl
  intro i _
  have hc : sampleCount q c k r i = ⌈(c.N k : ℝ)*weights q c r i⌉₊ := by
    simp only [sampleCount, i.isLt, dite_true]
  change weights q c r i/(⌈(c.N k : ℝ)*weights q c r i⌉₊ : ℝ) * _ =
    weights q c r i/(sampleCount q c k r i : ℝ) * _
  rw [hc]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => head q (g (join q (center q state) (supportPoints q c r i)) (ξ (sampleStart q c k r i+j) ω))) _

lemma epoch_scalar_probability (q : Params) (c : Config) (hR : 0 < q.R)
    (hT : 0 < c.T) (hn : 0 < c.n) (k : ℕ) (hN : 0 < c.N k) (state : OuterState q)
    (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (hTop : 0 ≤ q.vTop)
    (r K : ℝ) (hε : 0 < q.ε) (hr : 0 < r) (hK : 1 ≤ K)
    (hvariance : q.vTop/(c.N k : ℝ) ≤ q.ε^2/(8192*K*r^2)) :
    (Measure.infinitePi fun _ : ℕ => p).real
      {ξ | q.ε/(8*r) < |epochScalarError q c k state g v ξ|} ≤ 2*Real.exp (-64*K) := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => p))
  let z : q.Ω := Classical.choice (nonempty_of_isProbabilityMeasure p)
  have harg : Measurable (fun ξ : ℕ → q.Ω => (state, ξ)) := measurable_prodMk_left
  have hm := (measurable_epochScalarError q c hR k g v hg.measurable
      (SpikedSoftCutCoordinates.measurable_mean q p f v g hg)).comp harg
  have hE : MeasurableSet {ξ | q.ε/(8*r) < |epochScalarError q c k state g v ξ|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hm)
  apply split_event_probability p (c.T*c.b) _ hE (2*Real.exp (-64*K))
  intro b
  have hi := OracleTemplate.StochasticGeneralized.infinitePi_iid p
  have hh := split_scalar_mgf q c hT hn k hN state z b p P (fun j ξ => ξ j) hi f v g hg hTop
  exact scalar_failure_probability P _ _ hh q.ε r K hε hr hK hvariance

lemma measurable_innerBatchError (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (i : ℕ) :
    @Measurable (ℝ × (ℕ → q.Ω)) (InnerSpace q) _ _ (fun z =>
      SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
        (innerOracle q z.1 g) (fun x => tail q (v (join q z.1 x))) i z.2) := by
  have hx := measurable_innerSeedPoint q c hR g hg i
  have hj : Measurable (fun z : ℝ × (ℕ → q.Ω) => join q z.1 (innerSeedPoint q c z.1 g i z.2)) :=
    (SpikedSoftCutCoordinates.continuous_join q).measurable.comp (measurable_fst.prodMk hx)
  have hmean := (SpikedSoftCutCoordinates.continuous_tail q).measurable.comp (hv.comp hj)
  have herr (j : ℕ) : Measurable (fun z : ℝ × (ℕ → q.Ω) =>
      innerOracle q z.1 g (innerSeedPoint q c z.1 g i z.2) (z.2 (i*c.b+j)) -
        tail q (v (join q z.1 (innerSeedPoint q c z.1 g i z.2)))) := by
    have hsample := (SpikedSoftCutCoordinates.continuous_tail q).measurable.comp
      (hg.comp (hj.prodMk ((measurable_pi_apply (i*c.b+j)).comp measurable_snd)))
    exact hsample.sub hmean
  have hsum := Finset.measurable_sum (Finset.range c.b) (fun j _ => herr j)
  exact hsum.const_smul ((c.b : ℝ)⁻¹)

lemma measurable_innerErrorMatrix (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    Measurable (fun z : ℝ × (ℕ → q.Ω) => innerErrorMatrix q c z.1 g v z.2) := by
  unfold innerErrorMatrix SubGaussianNetProbability.columnOperator
  apply Finset.measurable_sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin c.T)) (InnerSpace q)
    (EuclideanSpace.proj i)).continuous.measurable.comp (measurable_innerBatchError q c hR g v hg hv i)

lemma measurable_innerErrorIntercept (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    Measurable (fun z : ℝ × (ℕ → q.Ω) => innerErrorIntercept q c z.1 g v z.2) := by
  have hh : Measurable (fun z : ℝ × (ℕ → q.Ω) => fun i : Fin c.T =>
      @inner ℝ (InnerSpace q) _
        (SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
          (innerOracle q z.1 g) (fun x => tail q (v (join q z.1 x))) i z.2)
        (innerSeedPoint q c z.1 g i z.2)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_innerBatchError q c hR g v hg hv i).inner (measurable_innerSeedPoint q c hR g hg i)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin c.T => ℝ)).measurable.comp hh

end LongTails.Proofs.SpikedSoftCutFreshness
