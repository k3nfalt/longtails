import LongTails.Algorithms.LeonTrajectory
import LongTails.Proofs.DistributedSampling
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.LeonCalendar
import LongTails.Proofs.DashaQuantization
import LongTails.Proofs.SvrgConvex
import LongTails.Proofs.WeakGradientConvolution

namespace LongTails.Proofs.LeonSampling

open MeasureTheory ProbabilityTheory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.LeonTuning

abbrev Index (p : Params) (l : ℕ) := (i : Fin p.n) × Fin (batch p i l)

noncomputable def weight (p : Params) (l : ℕ) (i : Fin p.n) : ℝ :=
  ((p.n : ℝ) * (batch p i l : ℕ))⁻¹

noncomputable def errorSum (p : Params) (f : Functions p)
    (g : Fin p.n → Point p → p.Ω → Point p) (l : ℕ) (x : Point p) (s : Samples p) : Point p :=
  ∑ z : Index p l, weight p l z.1 • (g z.1 x (s z.1 z.2) - gradient (f z.1) x)

lemma fixed_second_moment (p : Params) (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε)
    (P : Measure (Samples p)) [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (f : Functions p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hworkers : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) p.σ)
    (l : ℕ) (x : Point p) :
    Integrable (fun s => ‖errorSum p f g l x s‖ ^ 2) P ∧
    (∫ s, ‖errorSum p f g l x s‖ ^ 2 ∂P) ≤ resolution p ^ 2 / 2 ^ l := by
  let N (z : Index p l) (y : p.Ω) := weight p l z.1 • (g z.1 x y - gradient (f z.1) x)
  let X (z : Index p l) (s : Samples p) := N z (s z.1 z.2)
  let idx (z : Index p l) : Fin p.n × ℕ := (z.1, z.2.val)
  have hinj : Function.Injective idx := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    obtain rfl : i = i' := congrArg Prod.fst h
    have he : j = j' := Fin.ext (congrArg Prod.snd h)
    cases he
    rfl
  have hm (z : Index p l) : Measurable (N z) :=
    (((hg z.1).measurable.comp (measurable_const.prodMk measurable_id)).sub_const _).fun_const_smul _
  have hind : iIndepFun X P :=
    ((DistributedSampling.independent_coordinates p P μ hworkers hIID).precomp hinj).comp N hm
  have law (z : Index p l) : HasLaw (fun s : Samples p => s z.1 z.2) (μ z.1 : Measure _) P :=
    ⟨((hIID z.1).measurable _).aemeasurable, (hIID z.1).marginal _⟩
  have hi (z : Index p l) : Integrable (N z) (μ z.1 : Measure _) :=
    (((hg z.1).integrable x).sub (integrable_const _)).fun_smul _
  have hsq (z : Index p l) : Integrable (fun y => ‖N z y‖ ^ 2) (μ z.1 : Measure _) := by
    simp only [N, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact ((hg z.1).variance_integrable x).const_mul _
  have hz (z : Index p l) : (∫ s, X z s ∂P) = 0 := by
    rw [show (∫ s, X z s ∂P) = ∫ y, N z y ∂(μ z.1 : Measure _) from
      (law z).integral_comp (hi z).aestronglyMeasurable]
    simp [N, integral_smul, integral_sub ((hg z.1).integrable x) (integrable_const _),
      (hg z.1).unbiased x]
  have hv := OracleTemplate.RobustGradient.independent_sum_second_moment X hind
    (fun z => (law z).integrable_comp (hi z)) (fun z => (law z).integrable_comp (hsq z)) hz
  refine ⟨hv.1, hv.2.trans_le ?_⟩
  calc
    _ ≤ ∑ z : Index p l, weight p l z.1 ^ 2 * p.σ ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      rw [show (∫ s, ‖X z s‖ ^ 2 ∂P) = ∫ y, ‖N z y‖ ^ 2 ∂(μ z.1 : Measure _) from
        (law z).integral_comp (hsq z).aestronglyMeasurable]
      simp only [N, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, integral_const_mul]
      exact mul_le_mul_of_nonneg_left ((hg z.1).variance x) (sq_nonneg _)
    _ = ∑ i, p.σ ^ 2 / ((p.n : ℝ) ^ 2 * (batch p i l : ℕ)) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      have hb : (0 : ℝ) < (batch p i l : ℕ) := by exact_mod_cast (batch p i l).pos
      have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
      simp only [weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ _ := LeonBatchTuning.batch_variance p hh hε l

end LongTails.Proofs.LeonSampling

namespace LongTails.Proofs.LeonAdaptiveSampling

open MeasureTheory ProbabilityTheory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonAggregate
open LeonSampling

lemma list_range_sum {E : Type*} [AddCommMonoid E] (n : ℕ) (f : ℕ → E) :
    ((List.range n).map f).sum = ∑ j : Fin n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, ih, Fin.sum_univ_castSucc]; rfl

lemma batch_mean_eq (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (used : Fin p.n → ℕ) (l : ℕ) (x : Point p) (i : Fin p.n) :
    mean p (samplesAt p g s used l x i) = ((batch p i l : ℕ) : ℝ)⁻¹ •
      ∑ j : Fin (batch p i l), g i x (s i (used i + j)) := by
  simp [mean, samplesAt, list_range_sum]

def shifted (p : Params) (offset : Fin p.n → ℕ) (s : Samples p) : Samples p :=
  fun i k => s i (offset i + k)

lemma error_eq (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Samples p)
    (used : Fin p.n → ℕ) (l : ℕ) (x : Point p) :
    (p.n : ℝ)⁻¹ • (∑ i, mean p (samplesAt p g s used l x i)) - gradient (objective p f) x =
      errorSum p f g l x (shifted p used s) := by
  have hg : gradient (objective p f) x = (p.n : ℝ)⁻¹ • ∑ i, gradient (f i) x := by
    apply HasGradientAt.gradient
    exact OracleTemplate.FiniteSum.objective_gradient (f := f)
      (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hf x
  rw [hg, ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum, errorSum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hb : ((batch p i l : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (batch p i l).pos.ne'
  simp only [batch_mean_eq, weight, mul_inv_rev, shifted, smul_sub, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [← Finset.smul_sum, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma shift_law (p : Params) (offset : Fin p.n → ℕ) (P : Measure (Samples p))
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P) :
    MeasurePreserving (shifted p offset) P P := by
  let cfg : LongTails.Algorithms.DistributedBatchedSgd.Config p := ⟨1, offset, 1, 0⟩
  have he : shifted p offset = DistributedSampling.tail p cfg 1 := by
    funext s i j
    simp [shifted, DistributedSampling.tail, cfg]
  rw [he]
  exact DistributedSampling.tail_preserving p cfg P μ hw hi 1

lemma bounded_fresh_error (p : Params) (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (x : Samples p → Point p) (tail : Samples p → Samples p) (hx : Measurable x)
    (ht : MeasurePreserving tail P P) (hi : IndepFun x tail P)
    (F : Point p × Samples p → ℝ) (c : ℝ) (hF : Measurable F) (hn : ∀ z, 0 ≤ F z)
    (hfi : ∀ v, Integrable (fun s => F (v, s)) P)
    (hb : ∀ v, (∫ s, F (v, s) ∂P) ≤ c) :
    Integrable (fun s => F (x s, tail s)) P ∧ (∫ s, F (x s, tail s) ∂P) ≤ c := by
  have : IsProbabilityMeasure (P.map x) :=
    (Measure.isProbabilityMeasure_map_iff hx.aemeasurable).mpr inferInstance
  obtain ⟨hFI, hFB⟩ := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := P.map x) hF.stronglyMeasurable hn (Filter.Eventually.of_forall hfi)
    (integrable_const c) (Filter.Eventually.of_forall hb)
  have law : HasLaw (fun s => (x s, tail s)) ((P.map x).prod P) P :=
    ⟨(hx.prodMk ht.measurable).aemeasurable, by
      rw [hi.map_prod_eq_prod_map_map hx.aemeasurable ht.measurable.aemeasurable, ht.map_eq]⟩
  exact ⟨law.integrable_comp hFI, by
    simpa using (law.integral_comp hFI.aestronglyMeasurable).trans_le hFB⟩

end LongTails.Proofs.LeonAdaptiveSampling

namespace LongTails.Proofs.LeonMeasurability

open MeasureTheory ProbabilityTheory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonAggregate
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

lemma measurable_decode {Z : Type*} [MeasurableSpace Z] (p : Params) (l : ℕ)
    (a : Z → Point p) (r : Z → Fin p.d → ℤ) (ha : Measurable a) (hr : Measurable r) :
    Measurable (fun z => decode p.n (width p l) (spacing p) (radius p l) (a z) (r z)) := by
  let v : (Fin p.d → ℤ) → Point p := fun b =>
    displacement p.n (spacing p) (fun j => LongTails.Algorithms.DashaModular.restore (width p l) (b j))
  have hv := (measurable_of_countable v).comp hr
  exact Measurable.ite (measurableSet_le hv.norm measurable_const) (ha.add hv) ha

lemma measurable_estimate {Z : Type*} [MeasurableSpace Z] (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (s : Z → Samples p) (u : Fin p.n → ℕ) (l : ℕ) (current : Z → Model p)
    (hx : Measurable (fun z => (current z).point))
    (ha : ∀ k, Measurable (fun z => (current z).anchors k))
    (hs : ∀ i j, j < (batch p i l : ℕ) → Measurable (fun z => s z i (u i + j))) :
    Measurable (fun z => decode p.n (width p l) (spacing p) (radius p l)
      ((current z).anchors (l + 1)) (totalCodes p (current z) l
        (samplesAt p g (s z) u l (current z).point))) := by
  have hm (i : Fin p.n) : Measurable (fun z => mean p (samplesAt p g (s z) u l (current z).point i)) := by
    simp only [LeonAdaptiveSampling.batch_mean_eq]
    apply Measurable.fun_const_smul
    apply Finset.measurable_sum
    intro j _
    exact (hg i).comp (hx.prodMk (hs i j j.isLt))
  have hz : Measurable (fun z => totalCodes p (current z) l (samplesAt p g (s z) u l (current z).point)) := by
    apply Measurable.of_eval
    intro j
    apply Finset.measurable_sum
    intro i _
    have hc := (DashaQuantization.measurable_indices p.d false (spacing p)).comp
      (((hm i).sub (ha (l + 1))).prodMk (measurable_const (a := fun _ : Fin p.d => (0 : ℝ))))
    exact (measurable_pi_apply j).comp hc
  exact measurable_decode p l _ _ (ha _) hz

lemma measurable_state {Z : Type*} [MeasurableSpace Z] (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (s : Z → Samples p) (ls : List ℕ) (t : ℕ) (hlen : t ≤ ls.length)
    (hs : ∀ i j, j < spent p (ls.take t) i → Measurable (fun z => s z i j)) :
    Measurable (fun z => (trajectory p g (s z) ls t).point) ∧
      ∀ l, Measurable (fun z => (trajectory p g (s z) ls t).anchors l) := by
  induction t with
  | zero => exact ⟨measurable_const, fun _ => measurable_const⟩
  | succ t ih =>
    let l := ls[t]?.getD 0
    let current := fun z => trajectory p g (s z) ls t
    have ht : t < ls.length := by omega
    have hused (i : Fin p.n) : spent p (ls.take (t + 1)) i =
        spent p (ls.take t) i + (batch p i l : ℕ) := by
      rw [List.take_succ_eq_append_getElem ht]
      simp only [spent, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        l, List.getElem?_eq_getElem ht, Option.getD_some]
    obtain ⟨hx, ha⟩ := ih (Nat.le_of_lt ht)
      (fun i j hj => hs i j (by rw [hused]; omega))
    let vs := fun z => samplesAt p g (s z) (spent p (ls.take t)) l (current z).point
    let estimate := fun z => decode p.n (width p l) (spacing p) (radius p l)
      ((current z).anchors (l + 1)) (totalCodes p (current z) l (vs z))
    have hv : Measurable estimate := measurable_estimate p g hg s _ l current hx ha
      (fun i j hj => hs i _ (by rw [hused]; exact Nat.add_lt_add_left hj _))
    change Measurable (fun z => (applyEstimate p (current z) l (estimate z)).point) ∧ _
    by_cases hl : l = 0
    · constructor
      · simp only [applyEstimate, hl, ite_true]
        exact hx.sub ((measurable_const.div hv.norm).smul hv)
      · intro k
        change Measurable (fun z => (applyEstimate p (current z) l (estimate z)).anchors k)
        simpa only [applyEstimate, hl, ite_true] using ha k
    · constructor
      · simpa only [applyEstimate, ite_eq_right hl] using hx
      · intro k
        change Measurable (fun z => (applyEstimate p (current z) l (estimate z)).anchors k)
        by_cases hk : k = l
        · subst k; simpa [applyEstimate, hl] using hv
        · simpa [applyEstimate, hl, Function.update_of_ne hk] using ha k

end LongTails.Proofs.LeonMeasurability

namespace LongTails.Proofs.LeonFreshError

open MeasureTheory ProbabilityTheory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LeonSampling LeonAdaptiveSampling

lemma fresh_independent (p : Params) (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (ls : List ℕ) (t : ℕ) (ht : t ≤ ls.length) :
    IndepFun (fun s => (trajectory p g s ls t).point) (shifted p (spent p (ls.take t))) P := by
  let u := spent p (ls.take t)
  let m : Fin p.n × ℕ → MeasurableSpace (Samples p) := fun v =>
    MeasurableSpace.comap (fun s : Samples p => s v.1 v.2) p.measurableΩ
  let past : Set (Fin p.n × ℕ) := {v | v.2 < u v.1}
  let future : Set (Fin p.n × ℕ) := {v | u v.1 ≤ v.2}
  have hm (v) : m v ≤ (inferInstance : MeasurableSpace (Samples p)) := by
    have hv : Measurable (fun s : Samples p => s v.1 v.2) := by fun_prop
    exact hv.comap_le
  have hind : iIndep m P := DistributedSampling.independent_coordinates p P μ hw hi
  have hd : Disjoint past future := Set.disjoint_left.mpr (fun _ h₁ h₂ => Nat.not_lt_of_ge h₂ h₁)
  have hpair := indep_iSup_of_disjoint hm hind hd
  have hx := @LeonMeasurability.measurable_state (Samples p) (⨆ v ∈ past, m v) p g hg id ls t ht
    (fun i j hj => Measurable.of_comap_le (le_iSup_of_le (i, j) (le_iSup_of_le hj le_rfl)))
  apply indep_of_indep_of_le hpair hx.1.comap_le
  change MeasurableSpace.comap (shifted p u) (inferInstance : MeasurableSpace (Samples p)) ≤ _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def, shifted]
  exact iSup_le (fun i => iSup_le (fun j => le_iSup_of_le (i, u i + j)
    (le_iSup_of_le (Nat.le_add_right _ _) le_rfl)))

lemma measurable_noise (p : Params) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (f : Functions p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) p.σ) (l : ℕ) :
    Measurable (fun z : Point p × Samples p => ‖errorSum p f g l z.1 z.2‖) := by
  have hgrad (i : Fin p.n) : Measurable (gradient (f i)) := by
    have hf := (hg i).measurable.stronglyMeasurable.integral_prod_right' (ν := (μ i : Measure _))
    simpa only [Function.uncurry_apply_pair, (hg i).unbiased] using hf.measurable
  apply Measurable.norm
  apply Finset.measurable_sum
  intro z _
  apply Measurable.fun_const_smul
  apply Measurable.sub
  · exact (hg z.1).measurable.comp (measurable_fst.prodMk
      ((measurable_pi_apply z.2.val).comp ((measurable_pi_apply z.1).comp measurable_snd)))
  · exact (hgrad z.1).comp measurable_fst

lemma adaptive_second_moment (p : Params) (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε)
    (P : Measure (Samples p)) [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (f : Functions p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) p.σ)
    (ls : List ℕ) (t : ℕ) (ht : t ≤ ls.length) (l : ℕ) :
    let err := fun s => ‖errorSum p f g l (trajectory p g s ls t).point
      (shifted p (spent p (ls.take t)) s)‖ ^ 2
    Integrable err P ∧ (∫ s, err s ∂P) ≤ resolution p ^ 2 / 2 ^ l := by
  let x := fun s => (trajectory p g s ls t).point
  have hx := (LeonMeasurability.measurable_state p g (fun i => (hg i).measurable) id ls t ht
    (fun i j _ => (hi i).measurable j)).1
  let F := fun z : Point p × Samples p => ‖errorSum p f g l z.1 z.2‖ ^ 2
  have hm : Measurable F := (measurable_noise p μ f g hg l).pow_const 2
  exact bounded_fresh_error p P x _ hx (shift_law p _ P μ hw hi)
    (fresh_independent p P μ hw hi g (fun i => (hg i).measurable) ls t ht) F _ hm
    (fun _ => sq_nonneg _) (fun v => (fixed_second_moment p hh hε P μ f g hw hi hg l v).1)
    (fun v => (fixed_second_moment p hh hε P μ f g hw hi hg l v).2)

end LongTails.Proofs.LeonFreshError
