import LongTails.Proofs.CoupledMinimaxOuter
import LongTails.Proofs.CoupledMinimaxMultipliers

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxCertificate

open OracleTemplate
open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxGeometry
open LongTails.Proofs.CoupledMinimaxTuning
open LongTails.Proofs.CoupledMinimaxInner
open LongTails.Proofs.CoupledMinimaxOuter
open LongTails.Proofs.CoupledMinimaxValue

lemma min_normal_components {p : Params} {q n : MinSpace p}
    (hq : q ∈ minDomain p) (hn : Normal (minDomain p) q n) :
    Normal p.X q.fst n.fst ∧
      ∀ w : Weights p, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ cap p →
        ⟪n.snd, w - q.snd⟫ ≤ 0 := by
  constructor
  · intro x hx
    have hh := hn (WithLp.toLp 2 (x, q.snd)) ⟨hx, hq.2⟩
    have he : WithLp.toLp 2 (x, q.snd) - q = WithLp.toLp 2 (x - q.fst, 0) := by
      change WithLp.toLp 2 (x, q.snd) - WithLp.toLp 2 (q.fst, q.snd) = _
      rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
    rw [he, WithLp.prod_inner_apply] at hh
    simpa using hh
  · intro w hw hs
    have hh := hn (WithLp.toLp 2 (q.fst, w)) ⟨hq.1, hw, hs⟩
    have he : WithLp.toLp 2 (q.fst, w) - q = WithLp.toLp 2 (0, w - q.snd) := by
      change WithLp.toLp 2 (q.fst, w) - WithLp.toLp 2 (q.fst, q.snd) = _
      rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
    rw [he, WithLp.prod_inner_apply] at hh
    simpa using hh

lemma projected_normal {p : Params} (hv : Valid p) (q g : MinSpace p) :
    let q' := SaddlePoint.project (minDomain p)
      (q - (1 / (2 * valueSmoothness p)) • g)
    Normal (minDomain p) q' ((2 * valueSmoothness p) • (q - q') - g) := by
  let L := 2 * valueSmoothness p
  have hL : 0 < L := mul_pos (by norm_num) (valueSmoothness_pos hv)
  let q' := SaddlePoint.project (minDomain p) (q - (1 / L) • g)
  have hp := (projectMin_spec hv (q - (1 / L) • g)).2
  have he : L • (q - (1 / L) • g - q') = L • (q - q') - g := by
    simp only [smul_sub, smul_smul, one_div, mul_inv_cancel₀ hL.ne', one_smul]
    abel
  change Normal (minDomain p) q' (L • (q - q') - g)
  intro v hv'
  change ⟪L • (q - q') - g, v - q'⟫ ≤ 0
  rw [← he, real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos hL.le (hp v hv')

lemma lagrangian_mixed_lipschitz {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {z z' : Joint p} (hz : z ∈ domain p) (hz' : z' ∈ domain p)
    {w w' : Weights p} (hw : ‖w‖ ≤ cap p) :
    ‖(I.g z - (I.jac z).adjoint w) - (I.g z' - (I.jac z').adjoint w')‖ ≤
      (p.Lf + cap p * p.LJ) * ‖z - z'‖ + p.J * ‖w - w'‖ := by
  have hl := lagrangian_gradient_lipschitz hv H hw hz hz'
  have ha := (I.jac z').adjoint.le_opNorm (w - w')
  rw [ContinuousLinearMap.adjoint.norm_map] at ha
  have hb := ha.trans (mul_le_mul_of_nonneg_right (H.jacobian_bound z' hz')
    (norm_nonneg (w - w')))
  have he : (I.g z - (I.jac z).adjoint w) - (I.g z' - (I.jac z').adjoint w') =
      ((I.g z - (I.jac z).adjoint w) - (I.g z' - (I.jac z').adjoint w)) -
        (I.jac z').adjoint (w - w') := by
    rw [map_sub]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hl hb)

lemma joint_transport {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q q' : MinSpace p}
    (hq : q ∈ minDomain p) (hq' : q' ∈ minDomain p) {y : YSpace p} (hy : y ∈ p.Y) :
    ‖lagrangianGradient p (exactReply p I (query p q y)) q.snd -
      lagrangianGradient p (exactReply p I (query p q' y)) q'.snd‖ +
      ‖I.c (query p q y) - I.c (query p q' y)‖ ≤ smoothness p * ‖q - q'‖ := by
  have hz : query p q y ∈ domain p := ⟨hq.1, hy⟩
  have hz' : query p q' y ∈ domain p := ⟨hq'.1, hy⟩
  have hw : ‖q.snd‖ ≤ cap p := (weights_norm_le_sum hq.2.1).trans hq.2.2
  have hg := lagrangian_mixed_lipschitz (w' := q'.snd) hv H hz hz' hw
  have hc := constraints_lipschitz hv H hz hz'
  have he : ‖query p q y - query p q' y‖ = ‖q.fst - q'.fst‖ := by
    unfold query
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_fst]
  rw [he] at hg hc
  have hx : ‖q.fst - q'.fst‖ ≤ ‖q - q'‖ := WithLp.norm_fst_le (XSpace p) (q - q')
  have hw' : ‖q.snd - q'.snd‖ ≤ ‖q - q'‖ := WithLp.norm_snd_le (XSpace p) (q - q')
  have hK : 0 ≤ p.Lf + cap p * p.LJ + p.J := by
    have hh := mul_nonneg (cap_pos hv).le hv.LJ_nonneg
    linarith [hv.Lf_nonneg, hv.J_nonneg]
  have hm := mul_le_mul_of_nonneg_left hx hK
  have hm' := mul_le_mul_of_nonneg_left hw' hv.J_nonneg
  have hL : p.Lf + cap p * p.LJ + 2 * p.J ≤ smoothness p := by
    unfold smoothness
    linarith [hv.μ_pos]
  have hm'' := mul_le_mul_of_nonneg_right hL (norm_nonneg (q - q'))
  simp only [lagrangianGradient, exactReply]
  nlinarith

lemma min_gradient_transport {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q q' : MinSpace p}
    (hq : q ∈ minDomain p) (hq' : q' ∈ minDomain p) {y : YSpace p} (hy : y ∈ p.Y) :
    ‖minGradient p (exactReply p I (query p q y)) q.snd -
      minGradient p (exactReply p I (query p q' y)) q'.snd‖ ≤ smoothness p * ‖q - q'‖ := by
  let a := lagrangianGradient p (exactReply p I (query p q y)) q.snd
  let b := lagrangianGradient p (exactReply p I (query p q' y)) q'.snd
  have ht := joint_transport hv H hq hq' hy
  have hf := WithLp.norm_fst_le (XSpace p) (a - b)
  have hp := product_norm_le (minGradient p (exactReply p I (query p q y)) q.snd -
    minGradient p (exactReply p I (query p q' y)) q'.snd)
  change _ ≤ ‖a.fst - b.fst‖ + ‖-I.c (query p q y) - -I.c (query p q' y)‖ at hp
  rw [neg_sub_neg, norm_sub_rev (I.c (query p q' y)) (I.c (query p q y))] at hp
  exact hp.trans ((add_le_add hf le_rfl).trans ht)

lemma inner_gradient_transport {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q q' : MinSpace p}
    (hq : q ∈ minDomain p) (hq' : q' ∈ minDomain p) {y : YSpace p} (hy : y ∈ p.Y) :
    ‖innerGradient I q y - innerGradient I q' y‖ ≤ smoothness p * ‖q - q'‖ := by
  let a := lagrangianGradient p (exactReply p I (query p q y)) q.snd
  let b := lagrangianGradient p (exactReply p I (query p q' y)) q'.snd
  have ht := joint_transport hv H hq hq' hy
  have hf := WithLp.norm_snd_le (XSpace p) (a - b)
  have he : ‖innerGradient I q y - innerGradient I q' y‖ = ‖a.snd - b.snd‖ := by
    simp only [innerGradient, a, b, lagrangianGradient, exactReply, neg_sub_neg]
    exact norm_sub_rev _ _
  rw [he]
  exact hf.trans ((le_add_of_nonneg_right (norm_nonneg _)).trans ht)

lemma projected_residual {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y : YSpace p} (hy : y ∈ p.Y) :
    let g := minGradient p (exactReply p I (query p q y)) q.snd
    let q' := SaddlePoint.project (minDomain p)
      (q - (1 / (2 * valueSmoothness p)) • g)
    ∃ n, Normal (minDomain p) q' n ∧
      ‖minGradient p (exactReply p I (query p q' y)) q'.snd + n‖ ≤
        (2 * valueSmoothness p + smoothness p) * ‖q' - q‖ := by
  let g := minGradient p (exactReply p I (query p q y)) q.snd
  let L := 2 * valueSmoothness p
  let q' := SaddlePoint.project (minDomain p) (q - (1 / L) • g)
  have hL : 0 < L := mul_pos (by norm_num) (valueSmoothness_pos hv)
  have hq' := (projectMin_spec hv (q - (1 / L) • g)).1
  have hg := min_gradient_transport hv H hq' hq hy
  refine ⟨L • (q - q') - g, projected_normal hv q g, ?_⟩
  have he : minGradient p (exactReply p I (query p q' y)) q'.snd +
      (L • (q - q') - g) =
      (minGradient p (exactReply p I (query p q' y)) q'.snd - g) + L • (q - q') := by
    abel
  rw [he]
  have hn := norm_add_le (minGradient p (exactReply p I (query p q' y)) q'.snd - g)
    (L • (q - q'))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_sub_rev q q'] at hn
  change _ ≤ (L + smoothness p) * ‖q' - q‖
  change ‖minGradient p (exactReply p I (query p q' y)) q'.snd - g‖ ≤
    smoothness p * ‖q' - q‖ at hg
  nlinarith

lemma cleanup_residual_at_next {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q q' : MinSpace p}
    (hq : q ∈ minDomain p) (hq' : q' ∈ minDomain p) {y : YSpace p} (hy : y ∈ p.Y) :
    let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
    ∃ n, Normal p.Y b n ∧ ‖innerGradient I q' b + n‖ ≤
      2 * smoothness p * ‖b - y‖ + smoothness p * ‖q' - q‖ := by
  let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
  have hb := (projectY_spec hv (y - (1 / smoothness p) • innerGradient I q y)).1
  obtain ⟨n, hn, hr⟩ := cleanup_residual hv H hq hy
  refine ⟨n, hn, ?_⟩
  have ht := inner_gradient_transport hv H hq' hq hb
  have he : innerGradient I q' b + n =
      (innerGradient I q' b - innerGradient I q b) + (innerGradient I q b + n) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

lemma smoothness_le_valueSmoothness {p : Params} (hv : Valid p) :
    smoothness p ≤ valueSmoothness p := by
  have hL := (smoothness_pos hv).le
  have hh := mul_nonneg hL (div_nonneg hL hv.μ_pos.le)
  unfold valueSmoothness
  nlinarith

lemma cleanup_step_bound {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y : YSpace p} (hy : y ∈ p.Y)
    (herr : ‖y - optimizer I q‖ ≤ tolerance p / (12 * smoothness p)) :
    let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
    ‖b - y‖ ≤ tolerance p / (6 * smoothness p) := by
  let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
  obtain ⟨hu, hm⟩ := optimizer_spec hv H hq
  have hb := cleanup_distance hv H hq hu hy hm
  have ht : ‖b - y‖ ≤ ‖b - optimizer I q‖ + ‖optimizer I q - y‖ := by
    calc
      ‖b - y‖ = ‖(b - optimizer I q) + (optimizer I q - y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev (optimizer I q) y] at ht
  change ‖b - optimizer I q‖ ≤ ‖y - optimizer I q‖ at hb
  change ‖b - y‖ ≤ tolerance p / (6 * smoothness p)
  calc
    ‖b - y‖ ≤ tolerance p / (12 * smoothness p) +
        tolerance p / (12 * smoothness p) := ht.trans (add_le_add (hb.trans herr) herr)
    _ = tolerance p / (6 * smoothness p) := by ring

def CandidateBound (p : Params) (I : Instance p) (c : Candidate p) : Prop :=
  let q : MinSpace p := WithLp.toLp 2 (c.point.x, c.point.multiplier)
  q ∈ minDomain p ∧ c.point.y ∈ p.Y ∧
    ∃ n ny, Normal (minDomain p) q n ∧ Normal p.Y c.point.y ny ∧
      ‖minGradient p (exactReply p I (query p q c.point.y)) q.snd + n‖ ≤
        3 * valueSmoothness p * c.displacement ∧
      ‖innerGradient I q c.point.y + ny‖ ≤
        tolerance p / 3 + smoothness p * c.displacement

lemma candidate_bound_mk {p : Params} {I : Instance p} (q : MinSpace p)
    (y : YSpace p) (d : ℝ) (hq : q ∈ minDomain p) (hy : y ∈ p.Y)
    (n : MinSpace p) (ny : YSpace p) (hn : Normal (minDomain p) q n)
    (hny : Normal p.Y y ny)
    (hxres : ‖minGradient p (exactReply p I (query p q y)) q.snd + n‖ ≤
      3 * valueSmoothness p * d)
    (hyres : ‖innerGradient I q y + ny‖ ≤ tolerance p / 3 + smoothness p * d) :
    CandidateBound p I ⟨⟨q.fst, y, q.snd⟩, d⟩ := by
  exact ⟨hq, hy, n, ny, hn, hny, hxres, hyres⟩

set_option maxHeartbeats 800000 in
lemma step_certificate {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p) :
    CandidateBound p I (QueryPlan.eval (exactReply p I) (step p q)).2 := by
  let y := QueryPlan.eval (exactReply p I)
    (Algorithms.CoupledMinimaxInner.restart (query p q)
      (fun r => -(lagrangianGradient p r q.snd).snd) (SaddlePoint.project p.Y)
      (smoothness p) (innerIterations p) (innerRestarts p) p.y0)
  obtain ⟨hu, hm⟩ := optimizer_spec hv H hq
  have hy := mapped_accuracy hv H hq hu hm
  let b := SaddlePoint.project p.Y (y + (1 / smoothness p) •
    (lagrangianGradient p (exactReply p I (query p q y)) q.snd).snd)
  have he : b = SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y) := by
    simp only [b, innerGradient, lagrangianGradient, exactReply]
    rw [smul_neg, sub_neg_eq_add]
  have hb : b ∈ p.Y := by rw [he]; exact (projectY_spec hv _).1
  let g := minGradient p (exactReply p I (query p q b)) q.snd
  let q' := SaddlePoint.project (minDomain p) (q - (1 / (2 * valueSmoothness p)) • g)
  have hq' : q' ∈ minDomain p := (projectMin_spec hv _).1
  obtain ⟨n, hn, hr⟩ := projected_residual hv H hq hb
  obtain ⟨ny, hny, hry⟩ := cleanup_residual_at_next hv H hq hq' hy.1
  have hs := cleanup_step_bound hv H hq hy.1 hy.2
  rw [← he] at hny hry hs
  have hL := smoothness_pos hv
  have hLv := smoothness_le_valueSmoothness hv
  have hprod := mul_le_mul_of_nonneg_right hLv (norm_nonneg (q' - q))
  have hxres : ‖minGradient p (exactReply p I (query p q' b)) q'.snd + n‖ ≤
      3 * valueSmoothness p * ‖q' - q‖ := by
    change _ ≤ (2 * valueSmoothness p + smoothness p) * ‖q' - q‖ at hr
    nlinarith
  have hyres : ‖innerGradient I q' b + ny‖ ≤
      tolerance p / 3 + smoothness p * ‖q' - q‖ := by
    have hk : 2 * smoothness p * (tolerance p / (6 * smoothness p)) = tolerance p / 3 := by
      field_simp
      ring
    calc
      _ ≤ 2 * smoothness p * ‖b - y‖ + smoothness p * ‖q' - q‖ := hry
      _ ≤ 2 * smoothness p * (tolerance p / (6 * smoothness p)) +
          smoothness p * ‖q' - q‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hs (by positivity)) le_rfl
      _ = tolerance p / 3 + smoothness p * ‖q' - q‖ := by rw [hk]
  unfold step stepCalls
  rw [QueryPlan.eval_bind]
  simp only [QueryPlan.eval]
  exact candidate_bound_mk q' b ‖q' - q‖ hq' hb n ny hn hny hxres hyres

lemma outer_certificate {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) (N : ℕ) {q : MinSpace p} (hq : q ∈ minDomain p) :
    ∀ c ∈ QueryPlan.eval (exactReply p I) (outer p N q), CandidateBound p I c := by
  induction N generalizing q with
  | zero => simp [outer, QueryPlan.eval]
  | succ N ih =>
      simp only [outer, QueryPlan.eval_bind, QueryPlan.eval_map, List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · exact step_certificate hv H hq
      · exact ih (step_min_mem (I := I) hv q) c hc

def ResidualBound (p : Params) (I : Instance p) (o : Output p) : Prop :=
  let q : MinSpace p := WithLp.toLp 2 (o.x, o.multiplier)
  q ∈ minDomain p ∧ o.y ∈ p.Y ∧
    ∃ n ny, Normal (minDomain p) q n ∧ Normal p.Y o.y ny ∧
      ‖minGradient p (exactReply p I (query p q o.y)) q.snd + n‖ ≤ tolerance p ∧
      ‖innerGradient I q o.y + ny‖ ≤ tolerance p

lemma candidate_small_residual {p : Params} {I : Instance p} (hv : Valid p)
    {c : Candidate p} (hc : CandidateBound p I c) (hd0 : 0 ≤ c.displacement)
    (hd : c.displacement ≤ tolerance p / (6 * valueSmoothness p)) :
    ResidualBound p I c.point := by
  obtain ⟨hq, hy, n, ny, hn, hny, hxres, hyres⟩ := hc
  refine ⟨hq, hy, n, ny, hn, hny, ?_, ?_⟩
  · have hh := (le_div_iff₀ (mul_pos (by norm_num) (valueSmoothness_pos hv))).mp hd
    have ht := tolerance_pos hv
    linarith
  · have hh := (le_div_iff₀ (mul_pos (by norm_num) (valueSmoothness_pos hv))).mp hd
    have hm := mul_le_mul_of_nonneg_right (smoothness_le_valueSmoothness hv) hd0
    have ht := tolerance_pos hv
    linarith

lemma selected_residual {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) :
    ResidualBound p I (select p (QueryPlan.eval (exactReply p I)
      (outer p (outerIterations p) (start p)))) := by
  obtain ⟨c, hc, hout, hd⟩ := selected_displacement hv H
  rw [hout]
  exact candidate_small_residual hv
    (outer_certificate hv H (outerIterations p) (start_mem hv) c hc)
    (outer_displacement_nonneg I _ _ c hc) hd

end LongTails.Proofs.CoupledMinimaxCertificate
