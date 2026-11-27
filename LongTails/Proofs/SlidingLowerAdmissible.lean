import LongTails.Setups.HighDimensionalSlidingStochasticComposite
import LongTails.Proofs.SlidingLowerGap
import LongTails.Proofs.SlidingLowerHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SlidingLowerAdmissible

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingLowerChain SlidingLowerInstance SlidingLowerOracle SlidingLowerGap SlidingLowerHiding
open SoftRadialProjection QuasarCoinLaw QuasarHardAdmissible

variable {T : ℕ}

noncomputable def hardInstance (q : Params) (Q : Scale) (π : Fin (2 * T + 1) ↪ Fin q.d) :
    spec.Instance q :=
  ⟨fS Q.a Q.s Q.R π q.x0, hS Q.a Q.s Q.R π q.x0⟩

noncomputable def hardOracle (q : Params) (Q : Scale) (hp0 : 0 ≤ Q.p) (hp1 : Q.p ≤ 1)
    (π : Fin (2 * T + 1) ↪ Fin q.d) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) 2 where
  Seed := fun _ => Bool
  law := coinPath Q.p hp0 hp1
  answer := fun _ qq ω => if qq.1 = 0 then gradient (fS Q.a Q.s Q.R π q.x0) qq.2
    else hO Q.p Q.a Q.s Q.R π q.x0 qq.2 ω

structure Valid (q : Params) (T : ℕ) (Q : Scale) : Prop where
  p_pos : 0 < Q.p
  p_le : Q.p ≤ 1
  a_nonneg : 0 ≤ Q.a
  s_pos : 0 < Q.s
  radius : 5280 * (1 + Real.sqrt T) ≤ Q.R
  smooth : Q.a / Q.s ^ 2 * 2200 = q.ℓ
  ell_le : q.ℓ ≤ q.L
  gap : Q.a * (4 + 4 * T) ≤ q.Δ
  noise : 576 * (Q.a / Q.s) ^ 2 * (1 / Q.p - 1) ≤ q.σ ^ 2

lemma fS_grad_eq {Q : Scale} (hR : 0 < Q.R) {d : ℕ} (π : Fin (2 * T + 1) ↪ Fin d)
    (x0 x : Point d) :
    gradient (fS Q.a Q.s Q.R π x0) x = (Q.a / Q.s) • fgrad Q.R π (rescale Q.s x0 x) :=
  (fS_gradient hR π x0 x).gradient

lemma hS_grad_eq {Q : Scale} (hR : 0 < Q.R) {d : ℕ} (π : Fin (2 * T + 1) ↪ Fin d)
    (x0 x : Point d) :
    gradient (hS Q.a Q.s Q.R π x0) x = (Q.a / Q.s) • hgrad Q.R π (rescale Q.s x0 x) :=
  (hS_gradient hR π x0 x).gradient

lemma rescale_self {d : ℕ} (s : ℝ) (x0 : Point d) : rescale s x0 x0 = 0 := by
  simp [rescale]

lemma objective_lower (q : Params) (Q : Scale) (hV : Valid q T Q) (π : Fin (2 * T + 1) ↪ Fin q.d)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    fS Q.a Q.s Q.R π q.x0 q.x0 + hS Q.a Q.s Q.R π q.x0 q.x0 - Q.a * (4 + 4 * T) ≤
      fS Q.a Q.s Q.R π q.x0 x + hS Q.a Q.s Q.R π q.x0 x := by
  have h := gap_bound Q.R π (rescale Q.s q.x0 x)
  unfold fS hS
  rw [rescale_self]
  have := mul_le_mul_of_nonneg_left h hV.a_nonneg
  nlinarith

lemma hard_admissible (q : Params) (Q : Scale) (hV : Valid q T Q)
    (π : Fin (2 * T + 1) ↪ Fin q.d) :
    spec.admissible q (hardInstance q Q π) (hardOracle q Q hV.p_pos.le hV.p_le π) := by
  have hR0 := (radius_facts hV.radius).1
  refine ⟨hO Q.p Q.a Q.s Q.R π q.x0, coinLaw Q.p hV.p_pos.le hV.p_le,
    coinPath Q.p hV.p_pos.le hV.p_le, coinPath_iid hV.p_pos.le hV.p_le, rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (fS_gradient hR0 π q.x0 x).differentiableAt.hasGradientAt
  · intro x y
    change ‖gradient (fS Q.a Q.s Q.R π q.x0) x - gradient (fS Q.a Q.s Q.R π q.x0) y‖ ≤ q.ℓ * ‖x - y‖
    rw [fS_grad_eq hR0, fS_grad_eq hR0, ← hV.smooth]
    exact scaled_lipschitz hV.a_nonneg hV.s_pos (fgrad_lipschitz hV.radius π) q.x0 x y
  · exact hS_convex hV.a_nonneg hR0 π q.x0
  · intro x
    exact (hS_gradient hR0 π q.x0 x).differentiableAt.hasGradientAt
  · intro x y
    change ‖gradient (hS Q.a Q.s Q.R π q.x0) x - gradient (hS Q.a Q.s Q.R π q.x0) y‖ ≤ q.L * ‖x - y‖
    rw [hS_grad_eq hR0, hS_grad_eq hR0]
    refine (scaled_lipschitz hV.a_nonneg hV.s_pos (hgrad_lipschitz hV.radius π) q.x0 x y).trans ?_
    rw [hV.smooth]
    exact mul_le_mul_of_nonneg_right hV.ell_le (norm_nonneg _)
  · refine ⟨fS Q.a Q.s Q.R π q.x0 q.x0 + hS Q.a Q.s Q.R π q.x0 q.x0 - Q.a * (4 + 4 * T),
      fun x => objective_lower q Q hV π x, ?_⟩
    change fS Q.a Q.s Q.R π q.x0 q.x0 + hS Q.a Q.s Q.R π q.x0 q.x0 -
      (fS Q.a Q.s Q.R π q.x0 q.x0 + hS Q.a Q.s Q.R π q.x0 q.x0 - Q.a * (4 + 4 * T)) ≤ q.Δ
    linarith [hV.gap]
  · have e1 : (toGeneral q).measurableE =
        LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace q.d :=
      (toGeneral q).borelE.measurable_eq.trans
        (LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace q.d).measurable_eq.symm
    refine (hO_measurable Q.p Q.a Q.s hR0 π q.x0).mono ?_ e1.le
    rw [e1]
  · intro x
    exact coin_integrable hV.p_pos.le hV.p_le _
  · intro x
    change ∫ ω, hO Q.p Q.a Q.s Q.R π q.x0 x ω ∂_ = gradient (hS Q.a Q.s Q.R π q.x0) x
    rw [hO_mean hV.p_pos hV.p_le, hS_grad_eq hR0]
  · intro x
    exact coin_integrable hV.p_pos.le hV.p_le _
  · intro x
    change ∫ ω, ‖hO Q.p Q.a Q.s Q.R π q.x0 x ω - gradient (hS Q.a Q.s Q.R π q.x0) x‖ ^ 2 ∂_ ≤ q.σ ^ 2
    rw [hS_grad_eq hR0]
    exact (hO_variance hV.p_pos hV.p_le hR0 π q.x0 x).trans hV.noise

lemma answer_eq (q : Params) (Q : Scale) (hV : Valid q T Q) (π : Fin (2 * T + 1) ↪ Fin q.d)
    (β : ℕ → Bool) :
    ∀ history qq, (hardOracle q Q hV.p_pos.le hV.p_le π).answer history qq (β history.length) =
      trueReply Q q.x0 π (β history.length) qq := by
  intro history qq
  have hR0 := (radius_facts hV.radius).1
  unfold trueReply
  change (if qq.1 = 0 then gradient (fS Q.a Q.s Q.R π q.x0) qq.2
    else hO Q.p Q.a Q.s Q.R π q.x0 qq.2 (β history.length)) = _
  rw [fS_grad_eq hR0]

lemma moreauGap_nonneg_of_lower (q : Params) (I : spec.Instance q) (c : ℝ) (hℓ : 0 ≤ q.ℓ)
    (hc : ∀ y, c ≤ LongTails.Setups.SlidingStochasticComposite.objective I y)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    0 ≤ LongTails.Setups.SlidingStochasticComposite.moreauGap I x := by
  unfold LongTails.Setups.SlidingStochasticComposite.moreauGap
  have hb : BddBelow (Set.range fun y : EuclideanSpace ℝ (Fin q.d) =>
      LongTails.Setups.SlidingStochasticComposite.objective I y + q.ℓ * ‖y - x‖ ^ 2) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := hc y
    have : 0 ≤ q.ℓ * ‖y - x‖ ^ 2 := by positivity
    linarith
  have h : (⨅ y, (LongTails.Setups.SlidingStochasticComposite.objective I y + q.ℓ * ‖y - x‖ ^ 2)) ≤
      LongTails.Setups.SlidingStochasticComposite.objective I x + q.ℓ * ‖x - x‖ ^ 2 := ciInf_le hb x
  rw [sub_self, norm_zero] at h
  have : q.ℓ * (0 : ℝ) ^ 2 = 0 := by ring
  linarith

lemma moreauGap_nonneg (q : Params) (Q : Scale) (hV : Valid q T Q) (π : Fin (2 * T + 1) ↪ Fin q.d)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    0 ≤ LongTails.Setups.SlidingStochasticComposite.moreauGap (hardInstance q Q π) x := by
  have hℓ : 0 ≤ q.ℓ := by
    rw [← hV.smooth]; have := hV.a_nonneg; have := hV.s_pos; positivity
  exact moreauGap_nonneg_of_lower q _ _ hℓ (fun y => objective_lower q Q hV π y) x

end LongTails.Proofs.SlidingLowerAdmissible
