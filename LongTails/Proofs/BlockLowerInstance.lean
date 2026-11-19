import LongTails.Proofs.BlockEmbedding
import LongTails.Proofs.AbcLowerBound
import LongTails.Proofs.GdConvex
import LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.BlockLowerInstance

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution LongTails.Proofs.AbcHardCounting
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcLowerAssembly LongTails.Proofs.FiniteSumNondualLowerAveraging
open LongTails.Proofs.FiniteSumNondualLowerBound LongTails.Proofs.BlockEmbedding
open LongTails.Proofs.AbcLowerBound LongTails.Proofs.AbcHardContinuity
open LongTails.Setups.BlockHeterogeneousNonconvex (blockProj)

abbrev BParams := LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params
abbrev BSpec := LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec
abbrev QParams := LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex.Params
abbrev QSpec := LongTails.Setups.HighDimensionalBlockHeterogeneousNonconvex.spec

section Single

lemma block_sum_bound (qj : BParams) (hv : BSpec.valid qj) (N : ℕ) (hN : N ≤ lowerBudget qj)
    {St : Type*} (query output : St → Space qj.d) (update : St → Space qj.d → St)
    (initial : St) (ω : ℕ → ℝ) (hz : coinCount (revealBar qj) ω N ≤ chainDim qj / 2) :
    3 * qj.ε * (7 / 8) * Fintype.card (CoordinateWords qj.d (chainDim qj)) ≤
      ∑ w : CoordinateWords qj.d (chainDim qj),
        ‖objGrad (scaleOf qj hv.1 hv.2.2.2.2.1) (coordinateEmbedding w) qj.x0
          (output (trueState (scaleOf qj hv.1 hv.2.2.2.2.1) (revealProb qj (chainDim qj))
            (coordinateEmbedding w) qj.x0 query update initial ω N))‖ := by
  have hε := hv.2.2.2.2.1
  set S := scaleOf qj hv.1 hε
  set n := chainDim qj
  set qf := revealProb qj n
  set qbar := revealBar qj
  set Mh := n / 2
  have hratio : S.a / S.lam = 60 * qj.ε := amplitude_ratio qj hv.1 hε
  have hlev : level n qbar ω N < n + 1 := by
    have := min_le_right (n + 1) (coinCount qbar ω N)
    unfold level
    omega
  have hq : ∀ m, m ≤ level n qbar ω N → qf m ≤ qbar := by
    intro m hm
    have hm' : m ≤ (chainLength qj - 1) / 2 := by
      have := min_le_right (n + 1) (coinCount qbar ω N)
      have h2 : m ≤ Mh := by unfold level at hm; omega
      simpa [Mh, n, chainDim] using h2
    exact revealProb_le_bar qj hε n m (half_le_level qj hv m hm')
  have hbad := bad_fraction qj hv N hN S query output update initial ω
  have hgood (w : CoordinateWords qj.d n) : ¬ coordinateBad S qf qj.x0 query output update
      initial qbar ω N (coordinateEmbedding w) →
      3 * qj.ε ≤ ‖objGrad S (coordinateEmbedding w) qj.x0
        (output (trueState S qf (coordinateEmbedding w) qj.x0 query update initial ω N))‖ := by
    intro hw
    have h := good_gradient S qf qj.x0 query output update initial qbar ω N
      (coordinateEmbedding w) hw hlev hq
    rw [hratio] at h
    linarith
  have hterm (w : CoordinateWords qj.d n) : 3 * qj.ε * (1 - if coordinateBad S qf qj.x0 query
      output update initial qbar ω N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      ‖objGrad S (coordinateEmbedding w) qj.x0
        (output (trueState S qf (coordinateEmbedding w) qj.x0 query update initial ω N))‖ := by
    by_cases hw : coordinateBad S qf qj.x0 query output update initial qbar ω N
        (coordinateEmbedding w)
    · simp only [hw, ↓reduceIte, sub_self, mul_zero]; exact norm_nonneg _
    · simp only [hw, ↓reduceIte, sub_zero, mul_one]; exact hgood w hw
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords qj.d n))) =>
    hterm w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  have hεp : 0 ≤ 3 * qj.ε := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hbad hεp]

lemma block_variance (qj : BParams) (hv : BSpec.valid qj) (hA : qj.A = 0) (hB : qj.B = 0)
    (π : Fin (chainDim qj + 1) ↪ Fin qj.d) (x0 x : Space qj.d) :
    ∫ ω, ‖reply (scaleOf qj hv.1 hv.2.2.2.2.1) (revealProb qj (chainDim qj)) π x0 x ω -
      objGrad (scaleOf qj hv.1 hv.2.2.2.2.1) π x0 x‖ ^ 2 ∂unif ≤ qj.C := by
  have hε := hv.2.2.2.2.1
  have hC := hv.2.2.2.1
  set S := scaleOf qj hv.1 hε
  rw [reply_variance S _ (revealProb_pos qj hε (chainDim qj)) (revealProb_le qj hε (chainDim qj))]
  set w := toUnit S x0 x
  set m := stage (sel π w)
  have hratio : S.a / S.lam = 60 * qj.ε := amplitude_ratio qj hv.1 hε
  have hsec := secret_norm S π x0 x
  rw [hratio] at hsec
  have hlev : levelBudget qj (chainDim qj) m = qj.C := by
    unfold levelBudget; rw [hA, hB]; ring
  have hvar := variance_le_budget qj hε (chainDim qj) m _ (norm_nonneg _)
    (le_of_le_of_eq hsec (by ring)) (by rw [hlev]; exact hC)
  rw [hlev] at hvar
  exact hvar

lemma two_sided (S : Scale) {d n : ℕ} (π : Fin (n + 1) ↪ Fin d) (x0 u v : Space d) :
    |objective S π x0 v - objective S π x0 u - ⟪objGrad S π x0 u, v - u⟫| ≤
      1024 * S.a / S.lam ^ 2 / 2 * ‖v - u‖ ^ 2 := by
  have hup := OracleTemplate.Gradient.smooth_upper_bound
    (fun x => objective_hasGradientAt S π x0 x) (fun x y => objGrad_lipschitz S π x0 x y) u v
  have hlo := OracleTemplate.Gradient.smooth_upper_bound (f := fun x => -objective S π x0 x)
    (oracle := fun x => -objGrad S π x0 x)
    (fun x => by
      have h := (objective_hasGradientAt S π x0 x).hasFDerivAt.neg
      rw [hasGradientAt_iff_hasFDerivAt, map_neg]
      exact h)
    (fun x y => by rw [neg_sub_neg, norm_sub_rev x y]; exact objGrad_lipschitz S π x0 y x) u v
  simp only [inner_neg_left] at hlo
  rw [abs_le]
  constructor <;> linarith

end Single

section Composite

structure Alloc (B : ℕ) where
  Δ : Fin B → ℝ
  ε : Fin B → ℝ
  C : Fin B → ℝ

noncomputable abbrev blockParams (q : QParams) (a : Alloc q.B) (j : Fin q.B) : BParams where
  d := blockSize q.blk j
  L := q.L j
  A := 0
  B := 0
  C := a.C j
  Δ := a.Δ j
  ε := a.ε j
  x0 := restrict q.blk j q.x0

structure AllocValid (q : QParams) (a : Alloc q.B) (N : ℕ) : Prop where
  valid : ∀ j, BSpec.valid (blockParams q a j)
  budget : ∀ j, N ≤ lowerBudget (blockParams q a j)
  noise : ∀ j, a.C j ≤ q.σ j ^ 2
  gap : ∑ j, a.Δ j ≤ q.Δ
  acc : q.ε ≤ 2 * ∑ j, a.ε j

variable {q : QParams} {a : Alloc q.B} {N : ℕ} (hav : AllocValid q a N)

abbrev Word (q : QParams) (a : Alloc q.B) (j : Fin q.B) : Type :=
  CoordinateWords (blockSize q.blk j) (chainDim (blockParams q a j))

noncomputable abbrev sc (j : Fin q.B) : Scale :=
  scaleOf (blockParams q a j) (hav.valid j).1 (hav.valid j).2.2.2.2.1

noncomputable abbrev rate (q : QParams) (a : Alloc q.B) (j : Fin q.B) : ℕ → ℝ :=
  revealProb (blockParams q a j) (chainDim (blockParams q a j))

noncomputable def hardF (w : ∀ j, Word q a j) (x : Space q.d) : ℝ :=
  ∑ j, objective (sc hav j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
    (restrict q.blk j x)

noncomputable def hardGrad (w : ∀ j, Word q a j) (x : Space q.d) : Space q.d :=
  ∑ j, extend q.blk j (objGrad (sc hav j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
    (restrict q.blk j x))

noncomputable def hardG (w : ∀ j, Word q a j) (x : Space q.d) (ω : ℝ) : Space q.d :=
  ∑ j, extend q.blk j (reply (sc hav j) (rate q a j) (coordinateEmbedding (w j))
    (restrict q.blk j q.x0) (restrict q.blk j x) ω)

noncomputable def hardO (w : ∀ j, Word q a j) : Oracle (Space q.d) (Space q.d) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => hardG hav w x ω

lemma blockProj_sum_extend (j : Fin q.B) (v : ∀ k, Space (blockSize q.blk k)) :
    blockProj q.blk j (∑ k, extend q.blk k (v k)) = extend q.blk j (v j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · exact blockProj_extend_self q.blk j (v j)
  · intro k _ hk
    exact blockProj_extend_ne q.blk (Ne.symm hk) (v k)
  · intro h; exact absurd (Finset.mem_univ j) h

lemma hasGradientAt_restrict {j : Fin q.B} {h : Space (blockSize q.blk j) → ℝ}
    {g : Space (blockSize q.blk j)} {x : Space q.d} (hh : HasGradientAt h g (restrict q.blk j x)) :
    HasGradientAt (fun y => h (restrict q.blk j y)) (extend q.blk j g) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hh ⊢
  have hc := hh.comp x (restrict q.blk j).hasFDerivAt
  have key : InnerProductSpace.toDual ℝ (Space q.d) (extend q.blk j g) =
      (InnerProductSpace.toDual ℝ (Space (blockSize q.blk j)) g).comp (restrict q.blk j) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    change ⟪extend q.blk j g, v⟫ = ⟪g, restrict q.blk j v⟫
    rw [← real_inner_comm g, inner_restrict]
    exact real_inner_comm _ _
  rw [key]
  exact hc

lemma hardF_hasGradientAt (w : ∀ j, Word q a j) (x : Space q.d) :
    HasGradientAt (hardF hav w) (hardGrad hav w x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hs : ∀ j ∈ (Finset.univ : Finset (Fin q.B)),
      HasFDerivAt (fun y => objective (sc hav j) (coordinateEmbedding (w j))
        (restrict q.blk j q.x0) (restrict q.blk j y))
        (InnerProductSpace.toDual ℝ (Space q.d) (extend q.blk j (objGrad (sc hav j)
          (coordinateEmbedding (w j)) (restrict q.blk j q.x0) (restrict q.blk j x)))) x := by
    intro j _
    exact (hasGradientAt_restrict (objective_hasGradientAt _ _ _ _)).hasFDerivAt
  have h := HasFDerivAt.fun_sum hs
  unfold hardGrad
  rw [map_sum]
  exact h

lemma hardF_gradient (w : ∀ j, Word q a j) (x : Space q.d) :
    gradient (hardF hav w) x = hardGrad hav w x :=
  (hardF_hasGradientAt hav w x).gradient

lemma blockProj_hardGrad (w : ∀ j, Word q a j) (j : Fin q.B) (x : Space q.d) :
    blockProj q.blk j (hardGrad hav w x) = extend q.blk j (objGrad (sc hav j)
      (coordinateEmbedding (w j)) (restrict q.blk j q.x0) (restrict q.blk j x)) :=
  blockProj_sum_extend j _

lemma norm_blockProj_hardGrad (w : ∀ j, Word q a j) (j : Fin q.B) (x : Space q.d) :
    ‖blockProj q.blk j (hardGrad hav w x)‖ = ‖objGrad (sc hav j)
      (coordinateEmbedding (w j)) (restrict q.blk j q.x0) (restrict q.blk j x)‖ := by
  rw [blockProj_hardGrad, norm_extend]

lemma smooth_coeff (j : Fin q.B) : 1024 * (sc hav j).a / (sc hav j).lam ^ 2 = q.L j :=
  smoothness_eq (blockParams q a j) (hav.valid j).1 (hav.valid j).2.2.2.2.1

lemma hardF_smooth (w : ∀ j, Word q a j) (x y : Space q.d) :
    |hardF hav w y - hardF hav w x - ⟪hardGrad hav w x, y - x⟫| ≤
      (1 / 2) * ∑ j, q.L j * ‖blockProj q.blk j (y - x)‖ ^ 2 := by
  have hin : ⟪hardGrad hav w x, y - x⟫ = ∑ j, ⟪objGrad (sc hav j) (coordinateEmbedding (w j))
      (restrict q.blk j q.x0) (restrict q.blk j x), restrict q.blk j y - restrict q.blk j x⟫ := by
    unfold hardGrad
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_comm, ← inner_restrict, real_inner_comm, map_sub]
  rw [hin]
  unfold hardF
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  have h := two_sided (sc hav j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
    (restrict q.blk j x) (restrict q.blk j y)
  have hn : ‖restrict q.blk j y - restrict q.blk j x‖ = ‖blockProj q.blk j (y - x)‖ := by
    rw [← map_sub, norm_restrict]
  rw [smooth_coeff, hn] at h
  linarith

lemma hardG_term_measurable (w : ∀ j, Word q a j) (j : Fin q.B) :
    Measurable (fun z : Space q.d × ℝ => extend q.blk j (reply (sc hav j) (rate q a j)
      (coordinateEmbedding (w j)) (restrict q.blk j q.x0) (restrict q.blk j z.1) z.2)) := by
  have hr := reply_measurable (sc hav j) (rate q a j) (coordinateEmbedding (w j))
    (restrict q.blk j q.x0)
  have hp : Measurable (fun z : Space q.d × ℝ => (restrict q.blk j z.1, z.2)) :=
    ((restrict q.blk j).continuous.measurable.comp measurable_fst).prodMk measurable_snd
  have h := (extend q.blk j).continuous.measurable.comp (hr.comp hp)
  simp only [Function.comp_def, Function.uncurry_apply_pair] at h
  exact h

lemma hardG_measurable (w : ∀ j, Word q a j) : Measurable (Function.uncurry (hardG hav w)) := by
  have h := Finset.measurable_sum (Finset.univ : Finset (Fin q.B))
    (fun j _ => hardG_term_measurable hav w j)
  have he : Function.uncurry (hardG hav w) = fun z : Space q.d × ℝ => ∑ j, extend q.blk j
      (reply (sc hav j) (rate q a j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
        (restrict q.blk j z.1) z.2) := by
    funext z
    rfl
  rw [he]
  exact h

lemma hardG_integrable (w : ∀ j, Word q a j) (x : Space q.d) :
    Integrable (hardG hav w x) unif := by
  unfold hardG
  exact integrable_finsetSum _ (fun j _ => (extend q.blk j).integrable_comp
    (reply_integrable _ _ _ _ _))

lemma hardG_mean (w : ∀ j, Word q a j) (x : Space q.d) :
    ∫ ω, hardG hav w x ω ∂unif = hardGrad hav w x := by
  unfold hardG hardGrad
  rw [integral_finsetSum _ (fun j _ => (extend q.blk j).integrable_comp
    (reply_integrable _ _ _ _ _))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(extend q.blk j).integral_comp_comm (reply_integrable _ _ _ _ _)]
  rw [reply_integral _ _ (revealProb_pos _ (hav.valid j).2.2.2.2.1 _)
    (revealProb_le _ (hav.valid j).2.2.2.2.1 _)]

lemma hardG_block (w : ∀ j, Word q a j) (j : Fin q.B) (x : Space q.d) (ω : ℝ) :
    ‖blockProj q.blk j (hardG hav w x ω - hardGrad hav w x)‖ =
      ‖reply (sc hav j) (rate q a j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
        (restrict q.blk j x) ω - objGrad (sc hav j) (coordinateEmbedding (w j))
          (restrict q.blk j q.x0) (restrict q.blk j x)‖ := by
  unfold hardG hardGrad
  rw [← Finset.sum_sub_distrib]
  simp only [← map_sub]
  rw [blockProj_sum_extend, norm_extend]

lemma hardF_smooth' (w : ∀ j, Word q a j) (x y : Space q.d) :
    |hardF hav w y - hardF hav w x - ⟪gradient (hardF hav w) x, y - x⟫| ≤
      (1 / 2) * ∑ j, q.L j * ‖blockProj q.blk j (y - x)‖ ^ 2 := by
  rw [hardF_gradient]
  exact hardF_smooth hav w x y

lemma hardG_mean' (w : ∀ j, Word q a j) (x : Space q.d) :
    ∫ ω, hardG hav w x ω ∂unif = gradient (hardF hav w) x := by
  rw [hardF_gradient]
  exact hardG_mean hav w x

lemma hardG_block' (w : ∀ j, Word q a j) (j : Fin q.B) (x : Space q.d) (ω : ℝ) :
    ‖blockProj q.blk j (hardG hav w x ω - gradient (hardF hav w) x)‖ =
      ‖reply (sc hav j) (rate q a j) (coordinateEmbedding (w j)) (restrict q.blk j q.x0)
        (restrict q.blk j x) ω - objGrad (sc hav j) (coordinateEmbedding (w j))
          (restrict q.blk j q.x0) (restrict q.blk j x)‖ := by
  rw [hardF_gradient]
  exact hardG_block hav w j x ω

lemma hardF_lower (w : ∀ j, Word q a j) (x : Space q.d) :
    ∑ j, (sc hav j).a * (-3 * ((chainDim (blockParams q a j) : ℝ) + 1)) ≤ hardF hav w x := by
  unfold hardF
  refine Finset.sum_le_sum (fun j _ => ?_)
  exact mul_le_mul_of_nonneg_left (hardValue_lower _ _) (sc hav j).ha.le

lemma hardF_gap (w : ∀ j, Word q a j) :
    hardF hav w q.x0 - ∑ j, (sc hav j).a * (-3 * ((chainDim (blockParams q a j) : ℝ) + 1)) ≤
      q.Δ := by
  unfold hardF
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) hav.gap
  have hv := hav.valid j
  have hn1 := chainDim_succ (blockParams q a j) hv
  have ht : toUnit (sc hav j) (restrict q.blk j q.x0) (restrict q.blk j q.x0) = 0 := by
    simp [toUnit]
  simp only [objective, ht, hardValue_zero]
  have h := amplitude_chain_le (blockParams q a j) hv
  have hc : (((chainDim (blockParams q a j)) : ℝ) + 1) = chainLength (blockParams q a j) := by
    rw [← hn1]; push_cast; ring
  rw [hc]
  have : (sc hav j).a = amplitude (blockParams q a j) := rfl
  rw [this]
  have ha : 0 < amplitude (blockParams q a j) := (sc hav j).ha
  change _ ≤ (blockParams q a j).Δ
  nlinarith

theorem hard_admissible (w : ∀ j, Word q a j) :
    QSpec.admissible q (hardF hav w) (hardO hav w) := by
  refine ⟨hardG hav w, ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hardF_hasGradientAt hav w x).differentiableAt.hasGradientAt
  · intro x y
    exact hardF_smooth' hav w x y
  · exact hardG_measurable hav w
  · intro x
    exact hardG_integrable hav w x
  · intro x
    exact hardG_mean' hav w x
  · intro x j
    have h := (reply_variance_integrable (sc hav j) (rate q a j) (coordinateEmbedding (w j))
      (restrict q.blk j q.x0) (restrict q.blk j x)).congr
      (ae_of_all _ (fun ω => (congrArg (· ^ 2) (hardG_block' hav w j x ω)).symm))
    exact h
  · intro x j
    have h := (integral_congr_ae (μ := unif)
      (ae_of_all _ (fun ω => congrArg (· ^ 2) (hardG_block' hav w j x ω)))).trans_le
      ((block_variance (blockParams q a j) (hav.valid j) rfl rfl _ _ _).trans (hav.noise j))
    exact h
  · exact ⟨_, hardF_lower hav w, hardF_gap hav w⟩

end Composite

end LongTails.Proofs.BlockLowerInstance
