import LongTails.Algorithms.DashaDistributedNormalization
import LongTails.Proofs.DashaDistributedConfigured

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedNormalization

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributedNormalization

variable {p : Params}

lemma single_gradient (hn : p.n = 1) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (i : Fin p.n) (x : Point p) :
    gradient (objective p f) x = gradient (f i) x := by
  have hval : (p.n : ℕ) = 1 := congrArg PNat.val hn
  have he (j : Fin p.n) : j = i := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [DashaScalingDescent.objective_gradient_eq f hg]
  have hs : (∑ j, gradient (f j) x) = ∑ _ : Fin p.n, gradient (f i) x :=
    Finset.sum_congr rfl (fun j _ => by rw [he j])
  rw [hs]
  simp [hn]

lemma normalized_valid (hp : spec.valid p) : spec.valid (normalize p) := by
  obtain ⟨hh, hL, hH, hΔ, hG, hε⟩ := hp
  change (∀ i, 0 < p.h i) ∧ 0 < min p.L p.Lhat ∧
    0 < (if p.n = 1 then min p.L p.Lhat else p.Lhat) ∧ 0 ≤ p.Δ ∧
    0 ≤ (if p.n = 1 then min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ)) else p.G) ∧ 0 < p.ε
  refine ⟨hh, lt_min hL hH, ?_, hΔ, ?_, hε⟩
  · split_ifs <;> positivity
  · split_ifs <;> positivity

lemma normalized_admissible (hp : spec.valid p) (f : Functions p)
    (O : Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1))
    (hO : spec.admissible p f O) : spec.admissible (normalize p) f O := by
  obtain ⟨_, hL, hH, hΔ, hG0, _⟩ := hp
  obtain ⟨rfl, hg, hlip, hs, hG, lower, hlower, hgap⟩ := hO
  have heff := DashaScalingDescent.objective_lipschitz_effective f hg hH.le hlip hs
  have hgapgrad := DashaScalingDescent.initial_gradient_gap f hg hL hH hlip hs lower hlower hgap
  refine ⟨rfl, hg, heff, ?_, ?_, lower, hlower, hgap⟩
  · change ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      (if p.n = 1 then min p.L p.Lhat else p.Lhat) ^ 2 * ‖x - y‖ ^ 2
    intro x y
    by_cases hn : p.n = 1
    · rw [ite_eq_left hn]
      have he (i : Fin p.n) : ‖gradient (f i) x - gradient (f i) y‖ ^ 2 =
          ‖gradient (objective p f) x - gradient (objective p f) y‖ ^ 2 := by
        rw [← single_gradient hn f hg i x, ← single_gradient hn f hg i y]
      simp_rw [he]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn0 : (p.n : ℝ) ≠ 0 := by positivity
      rw [← mul_assoc, one_div_mul_cancel hn0, one_mul]
      have hb := sq_le_sq₀ (norm_nonneg (gradient (objective p f) x - gradient (objective p f) y))
        (show 0 ≤ min p.L p.Lhat * ‖x - y‖ by positivity) |>.mpr (heff x y)
      simpa only [mul_pow] using hb
    · rw [ite_eq_right hn]
      exact hs x y
  · change ∀ i, ‖gradient (f i) p.x0‖ ≤
      if p.n = 1 then min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ)) else p.G
    intro i
    by_cases hn : p.n = 1
    · rw [ite_eq_left hn]
      refine le_min (hG i) ?_
      rw [← single_gradient hn f hg i p.x0]
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hgapgrad
    · simpa only [ite_eq_right hn] using hG i

end LongTails.Proofs.DashaDistributedNormalization
