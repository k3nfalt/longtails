import LongTails.Proofs.ContaminatedParallelEstimator
import LongTails.Proofs.FixedBatchConfidenceProbability

namespace LongTails.Proofs.ContaminatedParallelSampling

open MeasureTheory ProbabilityTheory
open scoped Classical
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open OracleTemplate.RobustGradient
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

@[instance_reducible] def past (p : Params) (offset : Fin p.n → ℕ) : MeasurableSpace (Samples p) :=
  ⨆ v : Fin p.n × ℕ, ⨆ (_ : v.2 < offset v.1),
    MeasurableSpace.comap (fun s : Samples p => s v.1 v.2) p.measurableΩ

lemma past_eval (p : Params) (u : Fin p.n → ℕ) (i : Fin p.n) (k : ℕ) (h : k < u i) :
    Measurable[past p u] (fun s : Samples p => s i k) :=
  Measurable.of_comap_le (le_iSup_of_le (i,k) (le_iSup_of_le h le_rfl))

lemma past_mono (p : Params) {u v : Fin p.n → ℕ} (h : u ≤ v) : past p u ≤ past p v := by
  exact iSup_le (fun i => iSup_le (fun hi => (past_eval p v i.1 i.2 (hi.trans_le (h i.1))).comap_le))

lemma past_le (p : Params) (u : Fin p.n → ℕ) : past p u ≤ (inferInstance : MeasurableSpace (Samples p)) := by
  apply iSup_le
  intro i
  apply iSup_le
  intro _
  exact (show Measurable (fun s : Samples p => s i.1 i.2) by fun_prop).comap_le

lemma fresh {A : Type*} [MeasurableSpace A] (p : Params)
    (P : Measure (Samples p)) (u : Fin p.n → ℕ)
    (hi : iIndepFun (fun v : Fin p.n × ℕ => fun s : Samples p => s v.1 v.2) P)
    (x : Samples p → A) (hx : Measurable[past p u] x) :
    IndepFun x (LeonAdaptiveSampling.shifted (network p) u) P := by
  let m : Fin p.n × ℕ → MeasurableSpace (Samples p) := fun v =>
    MeasurableSpace.comap (fun s : Samples p => s v.1 v.2) p.measurableΩ
  let left : Set (Fin p.n × ℕ) := {v | v.2 < u v.1}
  let right : Set (Fin p.n × ℕ) := {v | u v.1 ≤ v.2}
  have hm (v) : m v ≤ (inferInstance : MeasurableSpace (Samples p)) :=
    (show Measurable (fun s : Samples p => s v.1 v.2) by fun_prop).comap_le
  have hd : Disjoint left right := Set.disjoint_left.mpr (fun _ h₁ h₂ => Nat.not_lt_of_ge h₂ h₁)
  have hind : iIndep m P := hi
  apply indep_of_indep_of_le (indep_iSup_of_disjoint hm hind hd) hx.comap_le
  change MeasurableSpace.comap (fun s : Samples p => fun (i : Fin p.n) (j : ℕ) => s i (u i+j))
    (inferInstance : MeasurableSpace (Fin p.n → ℕ → p.Ω)) ≤ ⨆ v ∈ right, m v
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def]
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  exact le_iSup_of_le (i, u i+j) (le_iSup_of_le (show (i,u i+j) ∈ right from Nat.le_add_right _ _) le_rfl)

lemma conditional_event {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Ω → A) (T : Ω → Ω) (hx : Measurable x)
    (hT : MeasurePreserving T P P) (hi : IndepFun x T P) (E : Set (A × Ω)) (hE : MeasurableSet E)
    (w : A → ℝ) (hw : Measurable w) (hw0 : ∀ a, 0 ≤ w a) (hwi : Integrable w (P.map x))
    (u : ℝ) (hu : ∀ a, P.real {ω | (a,ω) ∈ E} ≤ u) :
    (∫ ω, (if (x ω,T ω) ∈ E then w (x ω) else 0) ∂P) ≤ (∫ ω, w (x ω) ∂P) * u := by
  classical
  let F (z : A × Ω) := E.indicator (fun z => w z.1) z
  have hf : Measurable F := (hw.comp measurable_fst).indicator hE
  have hn (z) : 0 ≤ F z := Set.indicator_nonneg (fun a _ => hw0 a.1) _
  have he (a : A) (ω : Ω) : F (a,ω) = {s : Ω | (a,s) ∈ E}.indicator (fun _ => w a) ω := by
    rfl
  have hm (a : A) : MeasurableSet {s : Ω | (a,s) ∈ E} := measurable_prodMk_left hE
  have hfi (a : A) : Integrable (fun ω => F (a,ω)) P := by
    simp only [he]
    exact (integrable_const _).indicator (hm a)
  have hfb (a : A) : ∫ ω, F (a,ω) ∂P ≤ w a * u := by
    simp only [he, integral_indicator (hm a), setIntegral_const, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (hu a) (hw0 a)).trans_eq (mul_comm _ _)
  have hh := AdaptiveOracleConcentration.independent_nonnegative_fiber_bound hx hT.measurable hi
    hT.map_eq hf hn hfi (hwi.mul_const u) hfb
  rw [integral_mul_const, integral_map hx.aemeasurable hw.aestronglyMeasurable] at hh
  exact hh.2

noncomputable def centers (p : Params) (q : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (s : Samples p) (i : Fin p.n) : Point p :=
  pilotCenter (24 * p.σ i) (fun j : Fin (pilotCount p q) => g i x (s i j))

lemma measurable_centers {A : Type*} [MeasurableSpace A] (p : Params) (q : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (x : A → Point p) (hx : Measurable x) (s : A → Samples p)
    (hm : ∀ i k, k < pilotCount p q → Measurable (fun a => s a i k)) :
    Measurable (fun a => centers p q g (x a) (s a)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pilotCenter _).comp (measurable_const.prodMk (Measurable.of_eval
    (fun j => (hg i).comp (hx.prodMk (hm i j j.isLt)))))

lemma pilot_tuning (p : Params) (q : ℕ) :
    (p.n : ℝ) * (3/4 : ℝ) ^ pilotCount p q ≤ Real.exp (-(q : ℝ)) := by
  let k := 1 + Nat.log2 p.n
  have hh : (3/4 : ℝ)^8 ≤ (2:ℝ)⁻¹ := by norm_num
  have he : (3/4 : ℝ)^8 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  have hn : (p.n : ℝ) ≤ (2:ℝ)^k := by
    dsimp only [k]
    exact_mod_cast (Nat.lt_log2_self (n := p.n)).le.trans_eq (by rw [Nat.add_comm])
  have h1 : (p.n : ℝ) * ((3/4 : ℝ)^8)^k ≤ 1 := by
    have hx := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (3/4 : ℝ)^8) hh k
    apply (mul_le_mul hn hx (by positivity) (by positivity)).trans_eq
    rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (3/4 : ℝ)^8) he q
  rw [pilotCount, pow_mul, pow_add, ← mul_assoc]
  apply (mul_le_mul h1 h2 (by positivity) zero_le_one).trans_eq
  rw [one_mul, ← Real.exp_nat_mul]
  congr 1
  ring

lemma pilot_failure (p : Params) (hp : spec.valid p) (q : ℕ) (P : Measure (Samples p))
    (μ ν : Fin p.n → ProbabilityMeasure p.Ω)
    (hIID : ∀ i, IID (fun k (s : Samples p) => s i k) (mixture (p.η i) (μ i) (ν i)) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)) (x : Point p) :
    P.real {ω | ∃ i, 12 * p.σ i < ‖centers p q g x ω i - gradient (f i) x‖} ≤
      Real.exp (-(q : ℝ)) := by
  rcases hp with ⟨_, _, _, _, hpar, _, _, _⟩
  let A (i : Fin p.n) := {ω : Samples p | 12 * p.σ i < ‖centers p q g x ω i - gradient (f i) x‖}
  have hA (i) : P.real (A i) ≤ (3/4 : ℝ)^pilotCount p q := by
    let k := pilotCount p q
    let M := mixture (p.η i) (μ i : Measure p.Ω) (ν i)
    let Z (z : Fin k → p.Ω) := pilotCenter (24 * p.σ i) (fun j => g i x (z j))
    let E := {z | 12 * p.σ i < ‖Z z - gradient (f i) x‖}
    have hm : Measurable Z := (measurable_pilotCenter _).comp (measurable_const.prodMk (Measurable.of_eval
      (fun j => (hg i).measurable.comp (measurable_const.prodMk (measurable_pi_apply j)))))
    have he : MeasurableSet E := measurableSet_lt measurable_const (hm.sub_const _).norm
    have hh := DistributedContaminationMoments.contaminated_pilot (ν := (ν i : Measure p.Ω))
      ((hg i).measurable.comp (measurable_const.prodMk measurable_id))
      (hpar i).1 (hpar i).2.1 (hpar i).2.2 ((hg i).variance_integrable x) ((hg i).variance x) k
    have hpres : MeasurePreserving (fun ω (j : Fin k) => ω i j) P (Measure.pi fun _ : Fin k => M) := by
      simpa only [Nat.zero_add] using OracleTemplate.FixedBatchConfidence.iid_finite_block_law (hIID i) 0 k
    change P.real ((fun ω (j : Fin k) => ω i j) ⁻¹' E) ≤ _
    rw [hpres.measureReal_preimage he.nullMeasurableSet]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have he : {ω | ∃ i, 12 * p.σ i < ‖centers p q g x ω i - gradient (f i) x‖} = ⋃ i, A i := by
    ext ω; simp [A]
  rw [he]
  apply (measureReal_iUnion_fintype_le A).trans ((Finset.sum_le_sum (fun i _ => hA i)).trans ?_)
  simpa using pilot_tuning p q

open ContaminatedParallelEstimator
open LongTails.Algorithms.LeonTuning (resolution)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)

noncomputable def sampledError (p : Params) (q : ℕ) (g : Fin p.n → Point p → p.Ω → Point p)
    (f : Functions p) (x : Point p) (s : Samples p) : Point p :=
  centeredSum p q (centers p q g x s) (fun i => gradient (f i) x) (fun i => g i x)
    (LeonAdaptiveSampling.shifted (network p) (fun _ => pilotCount p q) s)

lemma measurable_centeredSum {A : Type*} [MeasurableSpace A] (p : Params) (q : ℕ)
    (c u : A → Fin p.n → Point p) (hc : Measurable c) (hu : Measurable u)
    (G : A → Fin p.n → p.Ω → Point p) (s : A → Samples p)
    (hG : ∀ z : BatchIndex p q, Measurable (fun a => G a z.1 (s a z.1 z.2))) :
    Measurable (fun a => centeredSum p q (c a) (u a) (G a) (s a)) := by
  apply Finset.measurable_fun_sum
  intro z _
  have hclip := measurable_centeredClip_joint.comp ((measurable_const (a := radius p q z.1)).prodMk
    (((measurable_pi_apply z.1).comp hc).prodMk (hG z)))
  exact (hclip.sub ((measurable_pi_apply z.1).comp hu)).fun_const_smul _

lemma one_batch (p : Params) (hp : spec.valid p) (q : ℕ) (hq : 1 ≤ q)
    (P : Measure (Samples p)) [IsProbabilityMeasure P] (μ ν : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun k (s : Samples p) => s i k) (mixture (p.η i) (μ i) (ν i)) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)) (x : Point p) :
    P.real {s | resolution (network p) < ‖sampledError p q g f x s‖} ≤ 2 * Real.exp (-(q : ℝ)) := by
  let u (i : Fin p.n) := gradient (f i) x
  let c := centers p q g x
  let T := LeonAdaptiveSampling.shifted (network p) (fun _ => pilotCount p q)
  let M (i : Fin p.n) : ProbabilityMeasure p.Ω := ⟨mixture (p.η i) (μ i) (ν i),
    DistributedContaminationMoments.mixture_probability (hp.2.2.2.2.1 i).2.1
      (by linarith [(hp.2.2.2.2.1 i).2.2])⟩
  let Good := {b : Fin p.n → Point p | ∀ i, ‖b i - u i‖ ≤ 12*p.σ i}
  let E := {z : (Fin p.n → Point p) × Samples p | z.1 ∈ Good ∧
    resolution (network p) < ‖centeredSum p q z.1 u (fun i => g i x) z.2‖}
  have hGood : MeasurableSet Good := by
    rw [show Good = ⋂ i, {b : Fin p.n → Point p | ‖b i - u i‖ ≤ 12*p.σ i} by ext b; simp [Good]]
    exact MeasurableSet.iInter (fun i => measurableSet_le ((measurable_pi_apply i).sub_const _).norm measurable_const)
  have hsum : Measurable (fun z : (Fin p.n → Point p) × Samples p =>
      centeredSum p q z.1 u (fun i => g i x) z.2) :=
    measurable_centeredSum _ _ _ _ measurable_fst measurable_const _ _ (fun z => (hg z.1).measurable.comp
      (measurable_const.prodMk (by change Measurable (fun a : (Fin p.n → Point p) × Samples p => a.2 z.1 z.2.val); fun_prop)))
  have hE : MeasurableSet E := (measurable_fst hGood).inter (measurableSet_lt measurable_const hsum.norm)
  have hind := DistributedSampling.independent_coordinates (network p) P M hw hIID
  have hc : Measurable[past p (fun _ => pilotCount p q)] c :=
    @measurable_centers (Samples p) (past p (fun _ => pilotCount p q)) p q g (fun i => (hg i).measurable) _ measurable_const id (fun i k h => past_eval _ _ i k h)
  have hcm : Measurable c := hc.mono (past_le p _) le_rfl
  have ht : MeasurePreserving T P P := LeonAdaptiveSampling.shift_law (network p) _ P M hw hIID
  have hpair := fresh p P _ hind c hc
  have hcond := conditional_event P c T hcm ht hpair E hE (fun _ => 1) measurable_const
    (fun _ => zero_le_one) (integrable_const _) (Real.exp (-(q:ℝ))) (fun b => by
      by_cases hb : b ∈ Good
      · have hsub : {ω : Samples p | (b,ω) ∈ E} ⊆ {ω | resolution (network p) < ‖centeredSum p q b u (fun i => g i x) ω‖} := fun _ h => h.2
        apply (measureReal_mono (μ := P) hsub).trans
        exact fixed_centers p hp q hq P μ ν hind (fun i k =>
          ⟨((hIID i).measurable k).aemeasurable, (hIID i).marginal k⟩) g f hg x b hb
      · have he : {ω : Samples p | (b,ω) ∈ E} = ∅ := by ext ω; simp [E,hb]
        rw [he, measureReal_empty]
        exact (Real.exp_pos _).le)
  let A := {ω : Samples p | (c ω,T ω) ∈ E}
  have ha : MeasurableSet A := (hcm.prodMk ht.measurable) hE
  have he : P.real A ≤ Real.exp (-(q:ℝ)) := by
    change (∫ ω, A.indicator 1 ω ∂P) ≤ _ at hcond
    simpa only [integral_indicator_one ha, integral_const, probReal_univ, one_smul, one_mul] using hcond
  let B := {ω : Samples p | ∃ i, 12 * p.σ i < ‖c ω i - u i‖}
  have hsub : {ω | resolution (network p) < ‖sampledError p q g f x ω‖} ⊆ A ∪ B := by
    intro ω hh
    by_cases h : ω ∈ B
    · exact Or.inr h
    · exact Or.inl ⟨fun i => le_of_not_gt (fun hi => h ⟨i,hi⟩), hh⟩
  have hb := pilot_failure p hp q P μ ν hIID g f hg x
  exact (measureReal_mono hsub).trans ((measureReal_union_le A B).trans
    ((add_le_add he hb).trans_eq (by ring)))

end LongTails.Proofs.ContaminatedParallelSampling
