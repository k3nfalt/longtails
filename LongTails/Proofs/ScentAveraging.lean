import LongTails.Proofs.ScentSystem


namespace OracleTemplate.Scent

open MeasureTheory Real
open LongTails.Setups.CompositionalEntropicRisk
open scoped RealInnerProductSpace BigOperators

variable {q : Params} {I : Instance q} {projection : q.E → q.E} {wstar : q.E}
  (h : SysHyp I projection wstar)

namespace SysHyp
include h

lemma spmd_virtual_int {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : ℝ}
    (hν : ν ∈ Set.Icc q.c0 q.c1) (i : Fin q.n) :
    Integrable (fun ζ => spmd α ν (I.score i w ζ)) (I.law i : Measure q.Ξ) := by
  refine (h.anchor i).spmd_int hw hα hν (fun r => r) measurable_id (|q.c0| + |q.c1|) ?_
  intro r hr
  rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;> linarith [hr.1, hr.2]

lemma anchor_average {ι : Type*} (s : Finset ι) (hs : 0 < s.card) (w : ι → q.E)
    (hw : ∀ k ∈ s, w k ∈ I.domain) (ν : ι → Fin q.n → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hν : ∀ k ∈ s, ∀ i, ν k i ∈ Set.Icc q.c0 q.c1) (i : Fin q.n) :
    1 + log (mass (I.law i : Measure q.Ξ) (I.score i) ((s.card : ℝ)⁻¹ • ∑ k ∈ s, w k)) ≤
      (s.card : ℝ)⁻¹ * ∑ k ∈ s, ∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) (w k)
        (spmd α (ν k i) (I.score i (w k) ζ)) ∂(I.law i : Measure q.Ξ) := by
  have hA := h.anchor i
  set N : ℝ := (s.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hs
  set wbar : q.E := N⁻¹ • ∑ k ∈ s, w k with hwbar
  have hwbar_mem : wbar ∈ I.domain := by
    rw [hwbar, Finset.smul_sum]
    refine h.convex.sum_mem (fun k _ => inv_nonneg.mpr hNpos.le) ?_ hw
    rw [Finset.sum_const, nsmul_eq_mul, hN]
    exact mul_inv_cancel₀ hNpos.ne'
  set νhat : ℝ := N⁻¹ * ∑ k ∈ s, ∫ ζ, spmd α (ν k i) (I.score i (w k) ζ) ∂(I.law i : Measure q.Ξ) with hνhat
  have hper : ∀ k ∈ s, dualObj (I.law i : Measure q.Ξ) (I.score i) wbar νhat +
      ⟪gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) wbar νhat, w k - wbar⟫ +
      (1 - mass (I.law i : Measure q.Ξ) (I.score i) wbar * exp (-νhat)) *
        ((∫ ζ, spmd α (ν k i) (I.score i (w k) ζ) ∂(I.law i : Measure q.Ξ)) - νhat) ≤
      ∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) (w k) (spmd α (ν k i) (I.score i (w k) ζ))
        ∂(I.law i : Measure q.Ξ) := by
    intro k hk
    have hpt : ∀ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) wbar νhat +
        ⟪gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) wbar νhat, w k - wbar⟫ +
        (1 - mass (I.law i : Measure q.Ξ) (I.score i) wbar * exp (-νhat)) *
          (spmd α (ν k i) (I.score i (w k) ζ) - νhat) ≤
        dualObj (I.law i : Measure q.Ξ) (I.score i) (w k) (spmd α (ν k i) (I.score i (w k) ζ)) :=
      fun ζ => hA.joint_convex hwbar_mem (hw k hk) νhat (spmd α (ν k i) (I.score i (w k) ζ))
    have hi_sp := h.spmd_virtual_int (hw k hk) hα (hν k hk i) i
    have hi_obj := h.dualObj_int (hw k hk) hα (hν k hk) i
    have hi_sub : Integrable (fun ζ => spmd α (ν k i) (I.score i (w k) ζ) - νhat) (I.law i : Measure q.Ξ) :=
      hi_sp.sub (integrable_const _)
    have hi2 : Integrable (fun ζ => (1 - mass (I.law i : Measure q.Ξ) (I.score i) wbar * exp (-νhat)) *
        (spmd α (ν k i) (I.score i (w k) ζ) - νhat)) (I.law i : Measure q.Ξ) := hi_sub.const_mul _
    have hi_lhs : Integrable (fun ζ => dualObj (I.law i : Measure q.Ξ) (I.score i) wbar νhat +
        ⟪gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) wbar νhat, w k - wbar⟫ +
        (1 - mass (I.law i : Measure q.Ξ) (I.score i) wbar * exp (-νhat)) *
          (spmd α (ν k i) (I.score i (w k) ζ) - νhat)) (I.law i : Measure q.Ξ) :=
      (integrable_const _).add hi2
    have := integral_mono hi_lhs hi_obj hpt
    rw [integral_add (integrable_const _) hi2, integral_const_mul, integral_sub hi_sp (integrable_const _),
      integral_const, integral_const, probReal_univ, one_smul, one_smul] at this
    exact this
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← inner_sum,
    ← Finset.mul_sum] at hsum
  have hcancel1 : ∑ k ∈ s, (w k - wbar) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, hwbar, smul_smul, ← hN,
      mul_inv_cancel₀ hNpos.ne', one_smul, sub_self]
  have hcancel2 : ∑ k ∈ s, ((∫ ζ, spmd α (ν k i) (I.score i (w k) ζ) ∂(I.law i : Measure q.Ξ)) - νhat) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hN, hνhat, ← mul_assoc,
      mul_inv_cancel₀ hNpos.ne', one_mul, sub_self]
  rw [hcancel1, inner_zero_right, add_zero, hcancel2, mul_zero, add_zero, ← hN] at hsum
  have hgap : 1 + log (mass (I.law i : Measure q.Ξ) (I.score i) wbar) ≤
      dualObj (I.law i : Measure q.Ξ) (I.score i) wbar νhat := by
    have := hA.gap_eq hwbar_mem νhat
    have hnn : 0 ≤ anchorGap (I.law i : Measure q.Ξ) (I.score i) wbar νhat :=
      AnchorHyp.gap_nonneg wbar νhat
    have h1 : dualObj (I.law i : Measure q.Ξ) (I.score i) wbar (log (mass (I.law i : Measure q.Ξ) (I.score i) wbar)) =
        1 + log (mass (I.law i : Measure q.Ξ) (I.score i) wbar) := by
      unfold dualObj
      rw [exp_neg, exp_log (hA.mass_pos hwbar_mem), mul_inv_cancel₀ (hA.mass_pos hwbar_mem).ne']
    linarith
  calc 1 + log (mass (I.law i : Measure q.Ξ) (I.score i) wbar)
      ≤ dualObj (I.law i : Measure q.Ξ) (I.score i) wbar νhat := hgap
    _ = N⁻¹ * (N * dualObj (I.law i : Measure q.Ξ) (I.score i) wbar νhat) := by
        rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
    _ ≤ N⁻¹ * ∑ k ∈ s, ∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) (w k)
        (spmd α (ν k i) (I.score i (w k) ζ)) ∂(I.law i : Measure q.Ξ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)

lemma average_bound {ι : Type*} (s : Finset ι) (hs : 0 < s.card) (w : ι → q.E)
    (hw : ∀ k ∈ s, w k ∈ I.domain) (ν : ι → Fin q.n → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hν : ∀ k ∈ s, ∀ i, ν k i ∈ Set.Icc q.c0 q.c1) :
    1 + objective I ((s.card : ℝ)⁻¹ • ∑ k ∈ s, w k) ≤
      (s.card : ℝ)⁻¹ * ∑ k ∈ s, virtualObj I α (w k) (ν k) := by
  have hper := fun i => h.anchor_average s hs w hw ν hα hν i
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hsum
  unfold objective virtualObj
  have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have := mul_le_mul_of_nonneg_left hsum hn
  rw [mul_add, inv_mul_cancel₀ (SysHyp.n_pos (q := q)).ne'] at this
  calc 1 + (q.n : ℝ)⁻¹ * ∑ i, log (normalizer I i ((s.card : ℝ)⁻¹ • ∑ k ∈ s, w k))
      ≤ (q.n : ℝ)⁻¹ * ∑ i, (s.card : ℝ)⁻¹ * ∑ k ∈ s, ∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) (w k)
        (spmd α (ν k i) (I.score i (w k) ζ)) ∂(I.law i : Measure q.Ξ) := this
    _ = (s.card : ℝ)⁻¹ * ∑ k ∈ s, (q.n : ℝ)⁻¹ * ∑ i, ∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) (w k)
        (spmd α (ν k i) (I.score i (w k) ζ)) ∂(I.law i : Measure q.Ξ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro i _
        ring

end SysHyp

end OracleTemplate.Scent
