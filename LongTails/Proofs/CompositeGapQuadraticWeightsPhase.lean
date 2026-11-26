import LongTails.Proofs.CompositeGapQuadraticWeightsLocal
import LongTails.Proofs.CompositeGeneralizedRun

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapQuadraticWeights

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate OracleTemplate.CompositeGapQuadraticWeights
open CompositeGapGeometry CompositeGapModel

variable {p : Params} {I : Instance p} {s c : p.E}

structure Invariant (I : Instance p) (s c : p.E) (M r d : ℝ) (n : ℕ) (q : State p.E) : Prop where
  fx : q.x ∈ I.Q
  fz : q.z ∈ I.Q
  gap : objective I q.x - objective I s ≤ d
  radius : ‖q.x - s‖ ≤ p.R
  cx : ‖q.x - c‖ ≤ (n + 1 : ℝ) * r / 8
  cz : ‖q.z - c‖ ≤ (n + 1 : ℝ) * r / 8
  grad : ‖q.v - mass M n • I.grad s‖ ≤ mass M n * (12 * M * r)
  reg : regularizerShift I s q.z ≤ d + ((n + 1 : ℝ) * r / 8) * (12 * M * r)
  cert : ∃ b, let W := model (regularizerShift I s) c (mass M n) (q.v - mass M n • I.grad s) b
              IsMinOn W I.Q q.z ∧ mass M n * (objective I q.x - objective I s) ≤ W q.z ∧
              ∀ u ∈ I.Q, W u ≤ ‖u - c‖ ^ 2 / 2 + mass M n * (objective I u - objective I s)

set_option maxHeartbeats 1200000 in
lemma advance (h : Conditions p I s) {M r d : ℝ}
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hM : 0 < M) (hr : 0 < r)
    (hd : M * r ^ 2 = d) (hcoef : p.H0 + p.H1 * d ≤ M)
    (hloc : Real.sqrt p.H1 * r ≤ 1) (hc : c ∈ I.Q) (hR : 0 < p.R)
    (hcs : ‖c - s‖ ≤ p.R) (hcg : objective I c - objective I s ≤ d)
    (n : ℕ) (q : State p.E) (hq : Invariant I s c M r d n q) :
    Invariant I s c M r d (n + 1)
      (QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) (step p M c n q)) := by
  let A := mass M n
  let a := increment M n
  let B := A + a
  let θ := a / B
  let K := (n + 1 : ℝ) * r / 8
  let K' := ((n : ℝ) + 2) * r / 8
  let G := 12 * M * r
  let y := CompositeGeneralized.mixPoint A a q.x q.z
  let g := I.grad y - I.grad s
  let z := I.prox B c ((1 / B) • (q.v + a • I.grad y))
  let w := CompositeGeneralized.mixPoint A a q.x z
  let v := q.v - A • I.grad s
  have hA : 0 ≤ A := by dsimp [A, mass]; positivity
  have ha : 0 < a := by dsimp [a, increment]; positivity
  have hB : 0 < B := add_pos_of_nonneg_of_pos hA ha
  have hθ : 0 ≤ θ := div_nonneg ha.le hB.le
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  have hsum : A / B + θ = 1 := by dsimp [θ, B]; field_simp [hB.ne']
  have hα : 0 ≤ A / B := div_nonneg hA hB.le
  have hθ1 : θ ≤ 1 := by linarith
  have hfrac : θ = 2 / ((n : ℝ) + 2) := fraction_eq hM n
  have htK : θ * K ≤ r / 4 := by
    rw [hfrac]; dsimp [K]; field_simp; nlinarith
  have hsmall : 64 * (θ * a) * M ≤ 1 := by
    rw [hfrac]; dsimp [a, increment]; field_simp; linarith
  have hmix (u : p.E) : CompositeGeneralized.mixPoint A a q.x u - q.x = θ • (u - q.x) := by
    have he : A / B = 1 - θ := by linarith
    change (A / B) • q.x + θ • u - q.x = _
    rw [he]; module
  have hyx : ‖y - q.x‖ ≤ r / 2 := by
    rw [show y - q.x = _ from hmix q.z, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    have ht : ‖q.z - q.x‖ ≤ K + K :=
      (norm_sub_le_norm_sub_add_norm_sub q.z c q.x).trans
        (add_le_add hq.cz (by rw [norm_sub_rev]; exact hq.cx))
    linarith [mul_le_mul_of_nonneg_left ht hθ]
  have hb := upper_ball h h0 h1 hM hr hd hcoef hloc hq.fx hq.gap
  have hg : ‖g‖ ≤ G := probe h hr hd hyx hb hM
  have hy : y ∈ I.Q := h.convex_domain hq.fx hq.fz hα hθ hsum
  have hjx := (regularizerShift_le_gap h q.x).trans hq.gap
  have hJ : θ * regularizerShift I s q.z ≤ θ * d + 3 * d := by
    have ht := mul_le_mul_of_nonneg_left hq.reg hθ
    change θ * regularizerShift I s q.z ≤ θ * (d + K * G) at ht
    have hm := mul_le_mul_of_nonneg_right htK hG
    dsimp [G] at ht hm
    nlinarith only [ht, hm, hd]
  have hyg : objective I y - objective I s ≤ 10 * d := by
    have hj := (shifted_regularizer_convex h).2 hq.fx hq.fz hα hθ hsum
    change regularizerShift I s y ≤ A / B * regularizerShift I s q.x + θ * regularizerShift I s q.z at hj
    rw [← shift_sum]
    have hh := hb y (by linarith only [hyx, hr])
    nlinarith only [hh, hj, hJ, mul_le_mul_of_nonneg_left hjx hα, congrArg (· * d) hsum]
  obtain ⟨b, hm, hl, hu⟩ := hq.cert
  let b' := b + a * (smoothShift I s y - ⟪g, y - c⟫)
  let W := model (regularizerShift I s) c A v b
  let W' := model (regularizerShift I s) c B (v + a • g) b'
  have hvnew : q.v + a • I.grad y - B • I.grad s = v + a • g := by dsimp [v, g, B]; module
  have hp := prox_is_model_min h hB c (q.v + a • I.grad y) b'
  have hm' : IsMinOn W' I.Q z := by
    have ht := shifted_model_min (s := s) hp.2
    rwa [hvnew] at ht
  have hgr : W q.z + ‖z - q.z‖ ^ 2 / 2 ≤ W z :=
    model_growth h.convex_domain (shifted_regularizer_convex h) hA hq.fz hp.1 hm
  have happ (u : p.E) : W' u = W u +
      a * (smoothShift I s y + ⟪g, u - y⟫ + regularizerShift I s u) :=
    model_append _ c v g y u A a b _
  have hdisp : θ * ‖z - q.z‖ ≤ r := by
    have happ' (u : p.E) : W' u = W u + a * ((smoothShift I s y - ⟪g, y⟫) +
        ⟪g, u⟫ + regularizerShift I s u) := by rw [happ, inner_sub_right]; ring
    apply scaled_displacement ha.le hθ hr hd (norm_nonneg _) hsmall
      (hJ.trans (by nlinarith [mul_le_mul_of_nonneg_right hθ1 (show 0 ≤ d by rw [← hd]; positivity)]))
    exact cumulative_displacement_sq ha.le hgr (hm' hq.fz) happ'
      (regularizerShift_nonneg h hp.1) le_rfl hg
  have hwy : w - y = θ • (z - q.z) := by dsimp [w, y, CompositeGeneralized.mixPoint, θ, B]; module
  have hlocal : Real.sqrt p.H1 * ‖w - y‖ ≤ 1 := by
    rw [hwy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left hdisp (Real.sqrt_nonneg _)).trans hloc
  have hdesc : smoothShift I s w ≤ smoothShift I s y + ⟪g, w - y⟫ + (10 * M) * ‖w - y‖ ^ 2 := by
    have hcf : p.H0 + p.H1 * (objective I y - objective I s) ≤ 10 * M := by
      nlinarith only [mul_le_mul_of_nonneg_left hyg h1, hcoef, h0]
    exact (shifted_upper h hy hlocal).trans (by linarith [mul_le_mul_of_nonneg_right hcf (sq_nonneg ‖w - y‖)])
  have hw : w ∈ I.Q := h.convex_domain hq.fx hp.1 hα hθ hsum
  have hid (u : p.E) : B • CompositeGeneralized.mixPoint A a q.x u = A • q.x + a • u := by
    unfold CompositeGeneralized.mixPoint
    rw [smul_add, smul_smul, smul_smul]
    change (B * (A / B)) • q.x + (B * (a / B)) • u = _
    field_simp
  have hjmix : B * regularizerShift I s w ≤ A * regularizerShift I s q.x + a * regularizerShift I s z := by
    have ht := (shifted_regularizer_convex h).2 hq.fx hp.1 hα hθ hsum
    change regularizerShift I s w ≤ A / B * _ + (a / B) * _ at ht
    field_simp at ht
    linarith only [ht]
  have hlow : B * (objective I w - objective I s) ≤ W' z := by
    rw [← shift_sum]
    apply cumulative_step hA hB (hid q.z) (hid z) (shifted_support h q.x y) hjmix hdesc
      (by rw [shift_sum]; exact hl) hgr (happ z)
    have ht := mul_le_mul_of_nonneg_right hsmall hB.le
    have he : θ * B = a := by dsimp [θ]; field_simp
    have he' := congrArg (· * (64 * a * M)) he
    nlinarith only [ht, he', mul_nonneg hM.le (sq_nonneg a)]
  have hupp (u : p.E) (hf : u ∈ I.Q) : W' u ≤ ‖u - c‖ ^ 2 / 2 + B * (objective I u - objective I s) := by
    rw [happ]
    have ht := hu u hf
    change W u ≤ _ at ht
    rw [← shift_sum] at ht ⊢
    dsimp only [B]
    nlinarith only [ht, mul_le_mul_of_nonneg_left (shifted_support h u y) ha.le]
  have he (u : p.E) (hf : u ∈ I.Q) := model_energy h hB.le hp.1 hf hm' hlow (hupp u hf)
  have hes := he s h.minimizer_feasible
  rw [norm_sub_rev s c] at hes
  have hec := he c hc
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hec
  have hnon : 0 ≤ objective I w - objective I s := sub_nonneg.mpr (h.minimizer hw)
  have hzs : ‖z - s‖ ≤ p.R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    nlinarith only [hes, mul_nonneg hB.le hnon, (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hcs]
  have hzc : ‖z - c‖ ≤ K' := by
    apply (sq_le_sq₀ (norm_nonneg _) hK').mp
    have hh : ‖z - c‖ ^ 2 ≤ 2 * B * d := by
      nlinarith only [hec, mul_nonneg hB.le hnon, mul_le_mul_of_nonneg_left hcg hB.le]
    apply hh.trans
    change 2 * (mass M n + increment M n) * d ≤ _
    rw [← mass_succ, ← hd]
    have eq : 2 * mass M (n + 1) * (M * r ^ 2) = ((n : ℝ) + 1) * ((n : ℝ) + 2) * r ^ 2 / 128 := by
      dsimp [mass]; push_cast; field_simp; ring
    rw [eq]; dsimp [K']
    have hprod := mul_nonneg (sq_nonneg ((n : ℝ) + 2)) (sq_nonneg r)
    have hlin := mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity) (sq_nonneg r)
    nlinarith only [hprod, hlin]
  have hvg : ‖v + a • g‖ ≤ B * G := by
    have hv := hq.grad
    change ‖v‖ ≤ A * G at hv
    calc
      _ ≤ ‖v‖ + ‖a • g‖ := norm_add_le _ _
      _ ≤ B * G := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]; dsimp [B]; linarith [mul_le_mul_of_nonneg_left hg ha.le]
  have hreg := nonsmooth_bound (R := K' / 2) hB hG hc hm'
    ((regularizerShift_le_gap h c).trans hcg) hvg (by linarith only [hzc])
  change Invariant I s c M r d (n + 1) ⟨w, z, q.v + a • I.grad y⟩
  have hmB : mass M (n + 1) = B := mass_succ M n
  have hidx : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  constructor
  · exact hw
  · exact hp.1
  · have ht : objective I w ≤ objective I c := by
      by_contra! hh
      nlinarith only [hec, mul_pos hB (sub_pos.mpr hh), sq_nonneg ‖z - c‖]
    linarith
  · exact CompositeGeneralized.mix_dist hA ha.le hB q.x z s hq.radius hzs
  · rw [hidx]
    exact CompositeGeneralized.mix_dist hA ha.le hB q.x z c (hq.cx.trans (by linarith only [hr])) hzc
  · rw [hidx]; exact hzc
  · rw [hmB, hvnew]; exact hvg
  · rw [hidx]; change regularizerShift I s z ≤ d + K' * G
    linarith only [hreg]
  · rw [hmB, hvnew]; exact ⟨b', hm', hlow, hupp⟩

end LongTails.Proofs.CompositeGapQuadraticWeights
