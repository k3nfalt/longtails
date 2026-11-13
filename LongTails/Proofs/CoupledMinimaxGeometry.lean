import LongTails.Algorithms.CoupledMinimax
import Mathlib.Analysis.Calculus.MeanValue
import LongTails.Proofs.PLMinimaxOracleGeometry
import LongTails.Proofs.FrankWolfeDescent

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxGeometry

open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax

lemma domain_convex {p : Params} (hv : Valid p) : Convex ℝ (domain p) := by
  intro x hx y hy a b ha hb hab
  exact ⟨hv.convexX hx.1 hy.1 ha hb hab, hv.convexY hx.2 hy.2 ha hb hab⟩

lemma constraints_lipschitz {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {z w : Joint p} (hz : z ∈ domain p) (hw : w ∈ domain p) :
    ‖I.c z - I.c w‖ ≤ p.J * ‖z - w‖ := by
  exact (domain_convex hv).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v hv => (H.derivative v hv).hasFDerivWithinAt) H.jacobian_bound hw hz

noncomputable def lagrangian {p : Params} (I : Instance p) (w : Weights p) (z : Joint p) : ℝ :=
  I.f z - ⟪w, I.c z⟫

lemma lagrangian_gradient {p : Params} {I : Instance p} (H : Assumptions p I)
    (w : Weights p) {z : Joint p} (hz : z ∈ domain p) :
    HasGradientAt (lagrangian I w) (I.g z - (I.jac z).adjoint w) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hi := ((innerSL ℝ w).hasFDerivAt).comp z (H.derivative z hz)
  have hf := (H.gradient z hz).hasFDerivAt.sub hi
  convert hf using 1
  · rfl
  · ext v
    simp [ContinuousLinearMap.adjoint_inner_left]

lemma lagrangian_gradient_lipschitz {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {w : Weights p} {M : ℝ} (hM : ‖w‖ ≤ M)
    {z z' : Joint p} (hz : z ∈ domain p) (hz' : z' ∈ domain p) :
    ‖(I.g z - (I.jac z).adjoint w) - (I.g z' - (I.jac z').adjoint w)‖ ≤
      (p.Lf + M * p.LJ) * ‖z - z'‖ := by
  have he : (I.g z - (I.jac z).adjoint w) - (I.g z' - (I.jac z').adjoint w) =
      (I.g z - I.g z') - (I.jac z - I.jac z').adjoint w := by
    simp only [map_sub, sub_apply]
    abel
  have ha := (I.jac z - I.jac z').adjoint.le_opNorm w
  rw [ContinuousLinearMap.adjoint.norm_map] at ha
  have hb : ‖I.jac z - I.jac z'‖ * ‖w‖ ≤ p.LJ * ‖z - z'‖ * M :=
    mul_le_mul (H.jacobian_lipschitz z hz z' hz') hM (norm_nonneg _)
      (mul_nonneg hv.LJ_nonneg (norm_nonneg _))
  rw [he]
  calc
    _ ≤ ‖I.g z - I.g z'‖ + ‖(I.jac z - I.jac z').adjoint w‖ := norm_sub_le _ _
    _ ≤ p.Lf * ‖z - z'‖ + p.LJ * ‖z - z'‖ * M :=
      add_le_add (H.gradient_lipschitz z hz z' hz') (ha.trans hb)
    _ = (p.Lf + M * p.LJ) * ‖z - z'‖ := by ring

lemma weights_norm_le_sum {p : Params} {w : Weights p} (hw : ∀ i, 0 ≤ w i) :
    ‖w‖ ≤ ∑ i, w i := by
  have he : (∑ i, (PiLp.single 2 i (w i) : Weights p)) = w := by ext j; simp
  calc
    ‖w‖ = ‖∑ i, (PiLp.single 2 i (w i) : Weights p)‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖(PiLp.single 2 i (w i) : Weights p)‖ := norm_sum_le _ _
    _ = ∑ i, w i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (hw i)]

lemma cap_pos {p : Params} (hv : Valid p) : 0 < cap p := by
  unfold cap
  have hδ := hv.δ_pos
  have hZ := hv.Z_pos
  have hG := hv.Gy_nonneg
  positivity

lemma start_mem {p : Params} (hv : Valid p) : start p ∈ minDomain p := by
  refine ⟨hv.startX, ?_, ?_⟩
  · simp [start]
  · simpa [start] using (cap_pos hv).le

lemma minDomain_convex {p : Params} (hv : Valid p) : Convex ℝ (minDomain p) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hv.convexX hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · intro i
    change 0 ≤ a * x.snd i + b * y.snd i
    exact add_nonneg (mul_nonneg ha (hx.2.1 i)) (mul_nonneg hb (hy.2.1 i))
  · change (∑ i, (a * x.snd i + b * y.snd i)) ≤ cap p
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left hx.2.2 ha
    have h2 := mul_le_mul_of_nonneg_left hy.2.2 hb
    have he := congrArg (fun r : ℝ => r * cap p) hab
    nlinarith

lemma minDomain_closed {p : Params} (hv : Valid p) : IsClosed (minDomain p) := by
  have hX : IsClosed {q : MinSpace p | q.fst ∈ p.X} :=
    hv.compactX.isClosed.preimage (by fun_prop)
  have hW : IsClosed {q : MinSpace p | ∀ i, 0 ≤ q.snd i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have hM : IsClosed {q : MinSpace p | (∑ i, q.snd i) ≤ cap p} :=
    isClosed_le (by fun_prop) continuous_const
  exact hX.inter (hW.inter hM)

lemma pairing_eq_sum {p : Params} (w v : Weights p) : ⟪w, v⟫ = ∑ i, w i * v i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma pairing_convex {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {x : XSpace p} (hx : x ∈ p.X) {w : Weights p}
    (hw : ∀ i, 0 ≤ w i) :
    ConvexOn ℝ p.Y (fun y => ⟪w, I.c (WithLp.toLp 2 (x, y))⟫) := by
  refine ⟨hv.convexY, ?_⟩
  intro y hy z hz a b ha hb hab
  simp only [smul_eq_mul, pairing_eq_sum]
  calc
    _ ≤ ∑ i, w i * (a * I.c (WithLp.toLp 2 (x, y)) i +
        b * I.c (WithLp.toLp 2 (x, z)) i) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (H.convex_constraints x hx i).2 hy hz ha hb hab
      exact mul_le_mul_of_nonneg_left hh (hw i)
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma pairing_gradient {p : Params} {I : Instance p} (H : Assumptions p I)
    (w : Weights p) {z : Joint p} (hz : z ∈ domain p) :
    HasGradientAt (fun v => ⟪w, I.c v⟫) ((I.jac z).adjoint w) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hi := ((innerSL ℝ w).hasFDerivAt).comp z (H.derivative z hz)
  convert hi using 1
  · rfl
  · ext v
    simp [ContinuousLinearMap.adjoint_inner_left]

lemma inner_strong_model {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y v : YSpace p} (hy : y ∈ p.Y) (hv' : v ∈ p.Y) :
    -lagrangian I q.snd (query p q y) +
      ⟪-(I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd).snd, v - y⟫ +
      p.μ / 2 * ‖v - y‖ ^ 2 ≤ -lagrangian I q.snd (query p q v) := by
  have hg := OracleTemplate.PLMinimax.joint_gradient_snd
    (pairing_gradient H q.snd (show query p q y ∈ domain p from ⟨hq.1, hy⟩))
  have hc := OracleTemplate.FrankWolfe.convex_support_on
    (pairing_convex hv H hq.1 hq.2.1) hy hv' hg
  have hf := H.strongly_concave q.fst hq.1 y hy v hv'
  have hs : (I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd).snd =
      (I.g (query p q y)).snd - ((I.jac (query p q y)).adjoint q.snd).snd := rfl
  rw [hs]
  simp only [lagrangian, query, inner_neg_left, inner_sub_left]
  linarith

noncomputable def innerObjective {p : Params} (I : Instance p) (q : MinSpace p)
    (y : YSpace p) : ℝ := -lagrangian I q.snd (query p q y)

noncomputable def innerGradient {p : Params} (I : Instance p) (q : MinSpace p)
    (y : YSpace p) : YSpace p :=
  -(I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd).snd

lemma inner_hasGradient {p : Params} {I : Instance p} (H : Assumptions p I)
    {q : MinSpace p} (hq : q ∈ minDomain p) {y : YSpace p} (hy : y ∈ p.Y) :
    HasGradientAt (innerObjective I q) (innerGradient I q y) y := by
  have hh := OracleTemplate.PLMinimax.joint_gradient_snd
    (lagrangian_gradient H q.snd (show query p q y ∈ domain p from ⟨hq.1, hy⟩))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh.hasFDerivAt.neg using 1
  · rfl
  · simp [innerGradient, query]

lemma inner_support {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y v : YSpace p} (hy : y ∈ p.Y) (hv' : v ∈ p.Y) :
    innerObjective I q y + ⟪innerGradient I q y, v - y⟫ ≤ innerObjective I q v := by
  have hh := inner_strong_model hv H hq hy hv'
  have hp : 0 ≤ p.μ / 2 * ‖v - y‖ ^ 2 := mul_nonneg (by linarith [hv.μ_pos]) (sq_nonneg _)
  change -lagrangian I q.snd (query p q y) +
    ⟪-(I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd).snd, v - y⟫ ≤ _
  change -lagrangian I q.snd (query p q y) +
    ⟪-(I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd).snd, v - y⟫ ≤
      -lagrangian I q.snd (query p q v)
  linarith

lemma inner_gradient_lipschitz {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y v : YSpace p} (hy : y ∈ p.Y) (hv' : v ∈ p.Y) :
    ‖innerGradient I q y - innerGradient I q v‖ ≤ smoothness p * ‖y - v‖ := by
  have hw : ‖q.snd‖ ≤ cap p := (weights_norm_le_sum hq.2.1).trans hq.2.2
  have hh := lagrangian_gradient_lipschitz hv H hw
    (show query p q y ∈ domain p from ⟨hq.1, hy⟩)
    (show query p q v ∈ domain p from ⟨hq.1, hv'⟩)
  have he : ‖query p q y - query p q v‖ = ‖y - v‖ := by
    unfold query
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_snd]
  rw [he] at hh
  let a := I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd
  let b := I.g (query p q v) - (I.jac (query p q v)).adjoint q.snd
  have hp := WithLp.norm_snd_le (XSpace p) (a - b)
  have hn : ‖innerGradient I q y - innerGradient I q v‖ = ‖(a - b).snd‖ := by
    change ‖-a.snd - -b.snd‖ = ‖a.snd - b.snd‖
    rw [neg_sub_neg, norm_sub_rev]
  rw [hn]
  have hl : p.Lf + cap p * p.LJ ≤ smoothness p := by
    unfold smoothness
    linarith [hv.μ_pos, hv.J_nonneg]
  exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right hl (norm_nonneg _))

lemma inner_smooth_upper {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y v : YSpace p} (hy : y ∈ p.Y) (hv' : v ∈ p.Y) :
    innerObjective I q v ≤ innerObjective I q y + ⟪innerGradient I q y, v - y⟫ +
      smoothness p / 2 * ‖v - y‖ ^ 2 := by
  exact OracleTemplate.FrankWolfe.smooth_upper_bound_on hv.convexY
    (fun z hz => inner_hasGradient H hq hz)
    (fun z hz w hw => inner_gradient_lipschitz hv H hq hz hw) hy hv'

lemma inner_attain {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p) :
    ∃ u ∈ p.Y, IsMinOn (innerObjective I q) p.Y u := by
  exact hv.compactY.exists_isMinOn ⟨p.y0, hv.startY⟩
    (fun y hy => (inner_hasGradient H hq hy).continuousAt.continuousWithinAt)

lemma inner_minimizer_growth {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {u : YSpace p} (hu : u ∈ p.Y) (hm : IsMinOn (innerObjective I q) p.Y u)
    {v : YSpace p} (hv' : v ∈ p.Y) :
    p.μ / 2 * ‖v - u‖ ^ 2 ≤ innerObjective I q v - innerObjective I q u := by
  have hi : 0 ≤ ⟪innerGradient I q u, v - u⟫ :=
    hm.isLocalMinOn.hasFDerivWithinAt_nonneg
      (inner_hasGradient H hq hu).hasFDerivAt.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hv.convexY.segment_subset hu hv'))
  have hh := inner_strong_model hv H hq hu hv'
  change innerObjective I q u + ⟪innerGradient I q u, v - u⟫ +
    p.μ / 2 * ‖v - u‖ ^ 2 ≤ innerObjective I q v at hh
  linarith

lemma product_norm_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (v : WithLp 2 (E × F)) :
    ‖v‖ ≤ ‖v.fst‖ + ‖v.snd‖ := by
  have hh := WithLp.prod_norm_sq_eq_of_L2 v
  nlinarith [norm_nonneg v, norm_nonneg v.fst, norm_nonneg v.snd,
    mul_nonneg (norm_nonneg v.fst) (norm_nonneg v.snd)]

lemma min_gradient_inner_lipschitz {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y v : YSpace p} (hy : y ∈ p.Y) (hv' : v ∈ p.Y) :
    ‖minGradient p (exactReply p I (query p q y)) q.snd -
      minGradient p (exactReply p I (query p q v)) q.snd‖ ≤ smoothness p * ‖y - v‖ := by
  have hz : query p q y ∈ domain p := ⟨hq.1, hy⟩
  have hz' : query p q v ∈ domain p := ⟨hq.1, hv'⟩
  have hw : ‖q.snd‖ ≤ cap p := (weights_norm_le_sum hq.2.1).trans hq.2.2
  have hg := lagrangian_gradient_lipschitz hv H hw hz hz'
  have hc := constraints_lipschitz hv H hz hz'
  have he : ‖query p q y - query p q v‖ = ‖y - v‖ := by
    unfold query
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_snd]
  rw [he] at hg hc
  let a := I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd
  let b := I.g (query p q v) - (I.jac (query p q v)).adjoint q.snd
  have hf := WithLp.norm_fst_le (XSpace p) (a - b)
  have hp := product_norm_le (minGradient p (exactReply p I (query p q y)) q.snd -
    minGradient p (exactReply p I (query p q v)) q.snd)
  change _ ≤ ‖a.fst - b.fst‖ + ‖-I.c (query p q y) - -I.c (query p q v)‖ at hp
  rw [neg_sub_neg, norm_sub_rev (I.c (query p q v)) (I.c (query p q y))] at hp
  have hf' : ‖a.fst - b.fst‖ ≤ (p.Lf + cap p * p.LJ) * ‖y - v‖ := hf.trans hg
  have hl : p.Lf + cap p * p.LJ + p.J ≤ smoothness p := by
    unfold smoothness
    linarith [hv.μ_pos, hv.J_nonneg]
  have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg (y - v))
  nlinarith

lemma lagrangian_upper {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {w : Weights p} {M : ℝ} (hw : ‖w‖ ≤ M)
    {z z' : Joint p} (hz : z ∈ domain p) (hz' : z' ∈ domain p) :
    lagrangian I w z' ≤ lagrangian I w z +
      ⟪I.g z - (I.jac z).adjoint w, z' - z⟫ +
      (p.Lf + M * p.LJ) / 2 * ‖z' - z‖ ^ 2 := by
  exact OracleTemplate.FrankWolfe.smooth_upper_bound_on (domain_convex hv)
    (fun v hv' => lagrangian_gradient H w hv')
    (fun v hv' u hu => lagrangian_gradient_lipschitz hv H hw hv' hu) hz hz'

lemma min_block_upper {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q q' : MinSpace p}
    (hq : q ∈ minDomain p) (hq' : q' ∈ minDomain p)
    {y : YSpace p} (hy : y ∈ p.Y) :
    lagrangian I q'.snd (query p q' y) ≤ lagrangian I q.snd (query p q y) +
      ⟪minGradient p (exactReply p I (query p q y)) q.snd, q' - q⟫ +
      smoothness p / 2 * ‖q' - q‖ ^ 2 := by
  have hz : query p q y ∈ domain p := ⟨hq.1, hy⟩
  have hz' : query p q' y ∈ domain p := ⟨hq'.1, hy⟩
  have hw : ‖q.snd‖ ≤ cap p := (weights_norm_le_sum hq.2.1).trans hq.2.2
  have hu := lagrangian_upper hv H hw hz hz'
  have hc := constraints_lipschitz hv H hz' hz
  have he : query p q' y - query p q y = WithLp.toLp 2 (q'.fst - q.fst, 0) := by
    unfold query
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
  rw [he, WithLp.norm_toLp_fst] at hc
  rw [he, WithLp.norm_toLp_fst, WithLp.prod_inner_apply] at hu
  simp only [inner_zero_right, add_zero] at hu
  have hi := real_inner_le_norm (-(q'.snd - q.snd))
    (I.c (query p q' y) - I.c (query p q y))
  rw [inner_neg_left, norm_neg] at hi
  have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg (q'.snd - q.snd))
  have hn := WithLp.prod_norm_sq_eq_of_L2 (q' - q)
  change ‖q' - q‖ ^ 2 = ‖q'.fst - q.fst‖ ^ 2 + ‖q'.snd - q.snd‖ ^ 2 at hn
  have hJ := hv.J_nonneg
  have hK : 0 ≤ p.Lf + cap p * p.LJ :=
    add_nonneg hv.Lf_nonneg (mul_nonneg (cap_pos hv).le hv.LJ_nonneg)
  have hL : p.Lf + cap p * p.LJ + p.J ≤ smoothness p := by
    unfold smoothness
    linarith [hv.μ_pos]
  have hsq := mul_nonneg hJ (sq_nonneg (‖q'.fst - q.fst‖ - ‖q'.snd - q.snd‖))
  have hmul := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖q' - q‖)
  rw [hn] at hmul
  have hk := mul_nonneg hK (sq_nonneg ‖q'.snd - q.snd‖)
  simp only [inner_sub_left, inner_sub_right] at hi
  simp only [lagrangian] at hu ⊢
  change _ ≤ _ + (⟪(I.g (query p q y) - (I.jac (query p q y)).adjoint q.snd).fst,
    q'.fst - q.fst⟫ + ⟪-I.c (query p q y), q'.snd - q.snd⟫) + _
  rw [inner_neg_left, real_inner_comm (q'.snd - q.snd) (I.c (query p q y)), inner_sub_left]
  rw [hn]
  simp only [WithLp.fst] at *
  nlinarith

lemma objective_x_difference {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {x x' : XSpace p} (hx : x ∈ p.X) (hx' : x' ∈ p.X)
    {y : YSpace p} (hy : y ∈ p.Y) :
    ‖I.f (WithLp.toLp 2 (x, y)) - I.f (WithLp.toLp 2 (x', y))‖ ≤ p.Gx * ‖x - x'‖ := by
  apply hv.convexX.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (OracleTemplate.PLMinimax.joint_gradient_fst
      (H.gradient _ (show WithLp.toLp 2 (z, y) ∈ domain p from ⟨hz, hy⟩))).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => ?_) hx' hx
  simpa using H.gradientX_bound (WithLp.toLp 2 (z, y)) ⟨hz, hy⟩

lemma objective_y_difference {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {x : XSpace p} (hx : x ∈ p.X)
    {y y' : YSpace p} (hy : y ∈ p.Y) (hy' : y' ∈ p.Y) :
    ‖I.f (WithLp.toLp 2 (x, y)) - I.f (WithLp.toLp 2 (x, y'))‖ ≤ p.Gy * ‖y - y'‖ := by
  apply hv.convexY.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (OracleTemplate.PLMinimax.joint_gradient_snd
      (H.gradient _ (show WithLp.toLp 2 (x, z) ∈ domain p from ⟨hx, hz⟩))).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => ?_) hy' hy
  simpa using H.gradientY_bound (WithLp.toLp 2 (x, z)) ⟨hx, hz⟩

end LongTails.Proofs.CoupledMinimaxGeometry
