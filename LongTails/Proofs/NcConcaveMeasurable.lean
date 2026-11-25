import LongTails.Proofs.NcConcaveSecret

open MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveMeasurable

open LongTails.Proofs.NcConcaveTransitions LongTails.Proofs.NcConcaveTransitionBounds
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveModel
open LongTails.Proofs.NcConcaveLocality LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveReply
open LongTails.Proofs.NcConcaveOracle LongTails.Proofs.NcConcaveSecret
open LongTails.Proofs.AbcHardOracle (coin unif coin_integrable coin_integral coin_sq_integral setOf_le_measurable coin_measurable)
open LongTails.Setups.StochasticNonconvexConcaveMinimax

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace

variable {d n m : ℕ}

lemma norm_le_sqrt_chainSq (v : CS n m) : ‖v‖ ≤ Real.sqrt (chainSq v) := by
  have hc : 0 ≤ chainSq v := nsq_nonneg _ _ _ _
  have hcoord : ∀ t : ℝ, t ^ 2 ≤ chainSq v → ‖t‖ ≤ Real.sqrt (chainSq v) := by
    intro t ht
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt ht
  have h1 : sq1 v.1 ≤ chainSq v := by unfold chainSq nsq; linarith [sq2_nonneg v.2.1, sq2_nonneg v.2.2.1, sqY_nonneg v.2.2.2]
  have h2 : sq2 v.2.1 ≤ chainSq v := by unfold chainSq nsq; linarith [sq1_nonneg v.1, sq2_nonneg v.2.2.1, sqY_nonneg v.2.2.2]
  have h3 : sq2 v.2.2.1 ≤ chainSq v := by unfold chainSq nsq; linarith [sq1_nonneg v.1, sq2_nonneg v.2.1, sqY_nonneg v.2.2.2]
  have h4 : sqY v.2.2.2 ≤ chainSq v := by unfold chainSq nsq; linarith [sq1_nonneg v.1, sq2_nonneg v.2.1, sq2_nonneg v.2.2.1]
  have hs := Real.sqrt_nonneg (chainSq v)
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩⟩
  · refine (pi_norm_le_iff_of_nonneg hs).mpr fun j => hcoord _ (le_trans ?_ h1)
    exact Finset.single_le_sum (f := fun j => v.1 j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  · refine (pi_norm_le_iff_of_nonneg hs).mpr fun j => hcoord _ (le_trans ?_ h2)
    exact Finset.single_le_sum (f := fun j => v.2.1 j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  · refine (pi_norm_le_iff_of_nonneg hs).mpr fun j => hcoord _ (le_trans ?_ h3)
    exact Finset.single_le_sum (f := fun j => v.2.2.1 j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  · refine (pi_norm_le_iff_of_nonneg hs).mpr fun i => (pi_norm_le_iff_of_nonneg hs).mpr fun k =>
      hcoord _ (le_trans ?_ h4)
    calc v.2.2.2 i k ^ 2 ≤ ∑ k', v.2.2.2 i k' ^ 2 :=
          Finset.single_le_sum (f := fun k' => v.2.2.2 i k' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ sqY v.2.2.2 :=
          Finset.single_le_sum (f := fun i' => ∑ k', v.2.2.2 i' k' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

lemma bounds_near (c c' : CS n m) (h : ‖c' - c‖ < 1) :
    sq2 c'.2.1 ≤ ((n + 1) * (‖c‖ + 1)) ^ 2 ∧ ∀ i, |c'.2.2.1 i| ≤ (n + 1) * (‖c‖ + 1) := by
  have hn : ‖c'‖ ≤ ‖c‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c' c
    linarith [norm_sub_rev c' c]
  have hc' := base_a c'
  have hb' := base_b c'
  unfold baseB at hc' hb'
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · refine hc'.trans ?_
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hn (by positivity)
  · intro i
    exact (hb' i).trans (mul_le_mul_of_nonneg_left hn (by positivity))

theorem gradC_continuous {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) :
    Continuous (gradC (n := n) (m := m) θ τ) := by
  rw [continuous_iff_continuousAt]
  intro c
  rw [Metric.continuousAt_iff]
  intro ε hε
  set B := (n + 1) * (‖c‖ + 1)
  have hB : 0 ≤ B := by positivity
  set M := 6 * cF B * Real.sqrt (NC n m)
  have hM : 0 ≤ M := by
    have : 0 ≤ cF B := by unfold cF cP; linarith
    positivity
  refine ⟨min 1 (ε / (M + 1)), by positivity, fun c' hc' => ?_⟩
  rw [dist_eq_norm] at hc' ⊢
  have h1 : ‖c' - c‖ < 1 := lt_of_lt_of_le hc' (min_le_left _ _)
  have h2 : ‖c' - c‖ < ε / (M + 1) := lt_of_lt_of_le hc' (min_le_right _ _)
  obtain ⟨ha', hb'⟩ := bounds_near c c' h1
  obtain ⟨ha, hb⟩ := bounds_near c c (by simp)
  have hl := gradC_lip hθ hθ1 hτ B hB c' c ha' hb' ha hb
  have hn := nsq_le (c' - c)
  have hcs : chainSq (c' - c) ≤ NC n m * ‖c' - c‖ ^ 2 := hn
  have hNC : 0 ≤ NC n m := by unfold NC; positivity
  have hcF : 0 ≤ cF B := by unfold cF cP; linarith
  have h3 : Real.sqrt (chainSq (gradC θ τ c' - gradC θ τ c)) ≤ M * ‖c' - c‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    calc _ ≤ (6 * cF B) ^ 2 * chainSq (c' - c) := hl
      _ ≤ (6 * cF B) ^ 2 * (NC n m * ‖c' - c‖ ^ 2) := mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (M * ‖c' - c‖) ^ 2 := by
          simp only [M]
          rw [show (6 * cF B * Real.sqrt (NC n m) * ‖c' - c‖) ^ 2 =
            (6 * cF B) ^ 2 * Real.sqrt (NC n m) ^ 2 * ‖c' - c‖ ^ 2 by ring, Real.sq_sqrt hNC]
          ring
  have h4 := norm_le_sqrt_chainSq (gradC θ τ c' - gradC θ τ c)
  have h5 : M * ‖c' - c‖ < ε := by
    calc M * ‖c' - c‖ ≤ (M + 1) * ‖c' - c‖ := by nlinarith [norm_nonneg (c' - c)]
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left h2 (by linarith)
      _ = ε := by field_simp
  linarith

noncomputable def selCL (W : Word d n m) (s : ℝ) : (Prim d × Dual d) →ₗ[ℝ] CS n m where
  toFun z := selC W s z.1 z.2
  map_add' z w := by
    simp only [selC, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> funext j <;>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply] <;> try (funext k; simp only [Pi.add_apply])
    all_goals ring
  map_smul' a z := by
    simp only [selC, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> funext j <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul] <;>
      try (funext k; simp only [Pi.smul_apply, smul_eq_mul])
    all_goals ring

lemma selC_continuous (W : Word d n m) (s : ℝ) :
    Continuous (fun z : Prim d × Dual d => selC W s z.1 z.2) :=
  (selCL W s).continuous_of_finiteDimensional

noncomputable def embXL (W : Word d n m) : CS n m →ₗ[ℝ] Prim d where
  toFun := embX W
  map_add' := embX_add W
  map_smul' a g := by rw [embX_smul]; rfl

noncomputable def embYL (W : Word d n m) : CS n m →ₗ[ℝ] Dual d where
  toFun := embY W
  map_add' := embY_add W
  map_smul' a g := by rw [embY_smul]; rfl

lemma embX_continuous (W : Word d n m) : Continuous (embX W) := (embXL W).continuous_of_finiteDimensional

lemma embY_continuous (W : Word d n m) : Continuous (embY W) := (embYL W).continuous_of_finiteDimensional

lemma knownC_continuous {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (r : ℕ) :
    Continuous (knownC (n := n) (m := m) θ τ r) := by
  unfold knownC
  exact (prC r).continuous.comp ((gradC_continuous hθ hθ1 hτ).comp (prC r).continuous)

lemma measurable_max_nat {Z : Type*} [MeasurableSpace Z] {f g : Z → ℕ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun z => max (f z) (g z)) := by
  have e : (fun z => max (f z) (g z)) = (fun q : ℕ × ℕ => max q.1 q.2) ∘ (fun z => (f z, g z)) := rfl
  rw [e]
  exact (measurable_of_countable _).comp (hf.prodMk hg)

lemma measurable_univ_sup {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] (f : ι → Z → ℕ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun z => Finset.univ.sup fun i => f i z) := by
  classical
  have key : ∀ t : Finset ι, Measurable (fun z => t.sup fun i => f i z) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp only [Finset.sup_empty]; exact measurable_const
    | insert a t ha ih =>
      simp only [Finset.sup_insert]
      exact measurable_max_nat (hf a) ih
  exact key Finset.univ

lemma measurable_famSup {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] (θ' : ℝ) (r : ℕ)
    (pos : ι → ℕ) (val : Z → ι → ℝ) (hv : ∀ i, Measurable fun z => val z i) :
    Measurable (fun z => famSup θ' r pos (val z)) := by
  unfold famSup
  apply measurable_univ_sup
  intro i
  apply Measurable.ite _ measurable_const measurable_const
  have : {z : Z | pos i < r ∧ θ' < |val z i|} = {z | pos i < r} ∩ {z | θ' < |val z i|} := by
    ext z; simp
  rw [this]
  exact (MeasurableSet.const _).inter
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hv i)))

lemma stage_measurable_CS (θ' : ℝ) : Measurable (fun c : CS n m => stage θ' c) := by
  have h1 : Measurable (fun c : CS n m => famSup θ' (K n m) (fun j : Fin (n + 1) => pU m j) c.1) :=
    measurable_famSup θ' (K n m) _ (fun c : CS n m => c.1)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
  have h2 : Measurable (fun c : CS n m => famSup θ' (K n m) (fun i : Fin n => pA m i) c.2.1) :=
    measurable_famSup θ' (K n m) _ (fun c : CS n m => c.2.1)
      (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have h3 : Measurable (fun c : CS n m => famSup θ' (K n m) (fun i : Fin n => pB m i) c.2.2.1) :=
    measurable_famSup θ' (K n m) _ (fun c : CS n m => c.2.2.1)
      (fun i => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have h4 : Measurable (fun c : CS n m => famSup θ' (K n m)
      (fun p : Fin n × Fin (m + 1) => pY m p.1 p.2) (fun p => c.2.2.2 p.1 p.2)) :=
    measurable_famSup θ' (K n m) _ (fun (c : CS n m) (p : Fin n × Fin (m + 1)) => c.2.2.2 p.1 p.2)
      (fun p => (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  unfold stage stageUpTo
  exact measurable_max_nat (measurable_max_nat h1 h2) (measurable_max_nat h3 h4)

lemma stage_measurable (θ' : ℝ) (W : Word d n m) (s : ℝ) :
    Measurable (fun z : Prim d × Dual d => stage θ' (selC W s z.1 z.2)) :=
  (stage_measurable_CS θ').comp (selC_continuous W s).measurable

theorem oracleG_measurable {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (p : ℝ)
    (W : Word d n m) (s ℓ : ℝ) :
    Measurable (fun w : (Prim d × Dual d) × ℝ => oracleG θ τ p W s ℓ w.1.1 w.1.2 w.2) := by
  let sec : ℕ → CS n m → CS n m := fun r c =>
    if maskedPos m n r then gradC θ τ c - knownC θ τ r c else 0
  let H : ((Prim d × Dual d) × ℝ) × ℕ → Prim d × Dual d := fun q =>
    ((ℓ * s) • embX W (gradC θ τ (selC W s q.1.1.1 q.1.1.2) +
        (coin p q.1.2 - 1) • sec q.2 (selC W s q.1.1.1 q.1.1.2)),
      (ℓ * s) • embY W (gradC θ τ (selC W s q.1.1.1 q.1.1.2) +
        (coin p q.1.2 - 1) • sec q.2 (selC W s q.1.1.1 q.1.1.2)))
  have hH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro r
    have hsel : Continuous (fun q : (Prim d × Dual d) × ℝ => selC W s q.1.1 q.1.2) :=
      (selC_continuous W s).comp continuous_fst
    have hg : Continuous (fun q : (Prim d × Dual d) × ℝ => gradC θ τ (selC W s q.1.1 q.1.2)) :=
      (gradC_continuous hθ hθ1 hτ).comp hsel
    have hk : Continuous (fun q : (Prim d × Dual d) × ℝ => knownC θ τ r (selC W s q.1.1 q.1.2)) :=
      (knownC_continuous hθ hθ1 hτ r).comp hsel
    have hsec : Measurable (fun q : (Prim d × Dual d) × ℝ => sec r (selC W s q.1.1 q.1.2)) := by
      simp only [sec]
      split_ifs
      · exact (hg.sub hk).measurable
      · exact measurable_const
    have hcoin : Measurable (fun q : (Prim d × Dual d) × ℝ => coin p q.2 - 1) :=
      ((coin_measurable p).comp measurable_snd).sub measurable_const
    have hinner : Measurable (fun q : (Prim d × Dual d) × ℝ => gradC θ τ (selC W s q.1.1 q.1.2) +
        (coin p q.2 - 1) • sec r (selC W s q.1.1 q.1.2)) :=
      continuous_add.measurable2 hg.measurable (continuous_smul.measurable2 hcoin hsec)
    exact ((continuous_const_smul (ℓ * s)).measurable.comp ((embX_continuous W).measurable.comp hinner)).prodMk
      ((continuous_const_smul (ℓ * s)).measurable.comp ((embY_continuous W).measurable.comp hinner))
  have he : (fun w : (Prim d × Dual d) × ℝ => oracleG θ τ p W s ℓ w.1.1 w.1.2 w.2) =
      H ∘ (fun w => (w, stage (θ / 2) (selC W s w.1.1 w.1.2))) := by
    funext w
    simp only [Function.comp, H, sec, oracleG, replyC_split, secretC]
  rw [he]
  exact hH.comp (measurable_id.prodMk ((stage_measurable (θ / 2) W s).comp measurable_fst))

end LongTails.Proofs.NcConcaveMeasurable
