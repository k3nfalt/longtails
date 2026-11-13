import LongTails.Proofs.CoupledMinimaxGeometry
import LongTails.Proofs.CoupledMinimaxDescent

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxValue

open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxGeometry

noncomputable def optimizer {p : Params} (I : Instance p) (q : MinSpace p) : YSpace p := by
  classical
  exact if h : ∃ u ∈ p.Y, IsMinOn (innerObjective I q) p.Y u then h.choose else p.y0

noncomputable def value {p : Params} (I : Instance p) (q : MinSpace p) : ℝ :=
  -innerObjective I q (optimizer I q)

lemma optimizer_spec {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p) :
    optimizer I q ∈ p.Y ∧ IsMinOn (innerObjective I q) p.Y (optimizer I q) := by
  have hh := inner_attain hv H hq
  unfold optimizer
  rw [dite_eq_left hh]
  exact hh.choose_spec

lemma value_eq {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {u : YSpace p} (hu : u ∈ p.Y) (hm : IsMinOn (innerObjective I q) p.Y u) :
    value I q = -innerObjective I q u := by
  obtain ⟨hy, hh⟩ := optimizer_spec hv H hq
  have h1 : innerObjective I q (optimizer I q) ≤ innerObjective I q u := hh hu
  have h2 : innerObjective I q u ≤ innerObjective I q (optimizer I q) := hm hy
  unfold value
  linarith

lemma value_growth {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y : YSpace p} (hy : y ∈ p.Y) :
    lagrangian I q.snd (query p q y) +
      p.μ / 2 * ‖y - optimizer I q‖ ^ 2 ≤ value I q := by
  obtain ⟨hu, hm⟩ := optimizer_spec hv H hq
  have hh := inner_minimizer_growth hv H hq hu hm hy
  unfold value innerObjective at *
  linarith

lemma value_upper {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q q' : MinSpace p}
    (hq : q ∈ minDomain p) (hq' : q' ∈ minDomain p) :
    value I q' ≤ value I q +
      ⟪minGradient p (exactReply p I (query p q (optimizer I q))) q.snd, q' - q⟫ +
      valueSmoothness p / 2 * ‖q' - q‖ ^ 2 := by
  have hu := (optimizer_spec hv H hq).1
  have hu' := (optimizer_spec hv H hq').1
  have hg := value_growth hv H hq hu'
  have hs := min_block_upper hv H hq hq' hu'
  have he : value I q' = lagrangian I q'.snd (query p q' (optimizer I q')) := by
    simp only [value, innerObjective, neg_neg]
  rw [← he] at hs
  have hupper : value I q' ≤ value I q +
      ⟪minGradient p (exactReply p I (query p q (optimizer I q'))) q.snd, q' - q⟫ +
      smoothness p / 2 * ‖q' - q‖ ^ 2 -
      p.μ / 2 * ‖optimizer I q' - optimizer I q‖ ^ 2 := by linarith
  have herr := min_gradient_inner_lipschitz hv H hq hu' hu
  have hh := CoupledMinimaxDescent.envelope_upper hv.μ_pos herr hupper
  have hc : smoothness p + smoothness p ^ 2 / p.μ = valueSmoothness p := by
    unfold valueSmoothness
    ring
  rwa [hc] at hh

lemma initial_gap {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p) :
    value I (start p) - value I q ≤ gapBound p := by
  let u := optimizer I (start p)
  have hu : u ∈ p.Y := (optimizer_spec hv H (start_mem hv)).1
  have hx := objective_x_difference hv H hv.startX hq.1 hu
  have hy := objective_y_difference hv H hq.1 hu hv.startY
  have hxd := mul_le_mul_of_nonneg_left (hv.diameterX p.x0 hv.startX q.fst hq.1) hv.Gx_nonneg
  have hyd := mul_le_mul_of_nonneg_left (hv.diameterY u hu p.y0 hv.startY) hv.Gy_nonneg
  have hx' := (le_abs_self (I.f (WithLp.toLp 2 (p.x0, u)) -
    I.f (WithLp.toLp 2 (q.fst, u)))).trans (hx.trans hxd)
  have hy' := (le_abs_self (I.f (WithLp.toLp 2 (q.fst, u)) -
    I.f (WithLp.toLp 2 (q.fst, p.y0)))).trans (hy.trans hyd)
  have hg := value_growth hv H hq hv.startY
  have hw : ‖q.snd‖ ≤ cap p := (weights_norm_le_sum hq.2.1).trans hq.2.2
  have hc := H.constraint_bound (query p q p.y0) ⟨hq.1, hv.startY⟩
  have hi := (real_inner_le_norm q.snd (I.c (query p q p.y0))).trans
    (mul_le_mul hw hc (norm_nonneg _) (cap_pos hv).le)
  have he : value I (start p) = I.f (WithLp.toLp 2 (p.x0, u)) := by
    simp [value, innerObjective, lagrangian, start, query, u]
  have hp : 0 ≤ p.μ / 2 * ‖p.y0 - optimizer I q‖ ^ 2 :=
    mul_nonneg (by linarith [hv.μ_pos]) (sq_nonneg _)
  rw [he]
  unfold lagrangian query at hg hi
  unfold gapBound
  linarith

end LongTails.Proofs.CoupledMinimaxValue
