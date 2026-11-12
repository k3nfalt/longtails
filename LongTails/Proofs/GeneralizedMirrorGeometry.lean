import LongTails.Setups.StochasticGeneralizedMirror
import LongTails.Proofs.GeneralizedMirrorPotential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set

namespace LongTails.Proofs.GeneralizedMirrorGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma composite_optimality {h ψ : E → ℝ} {Q : Set E} {x : E}
    {g : E →L[ℝ] ℝ} (hψ : ConvexOn ℝ Q ψ) (hx : x ∈ Q)
    (hg : HasFDerivAt h g x)
    (hm : ∀ u ∈ Q, h x + ψ x ≤ h u + ψ u) {u : E} (hu : u ∈ Q) :
    0 ≤ g (u - x) + ψ u - ψ x := by
  let d := u - x
  let F : ℝ → ℝ := fun t => h (x + t • d) + ψ x + t * (ψ u - ψ x)
  have hline : HasDerivAt (fun t : ℝ => h (x + t • d)) (g d) 0 := by
    have hg' : HasFDerivAt h g (x + (0 : ℝ) • d) := by simpa using hg
    have hh := hg'.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).smul_const d |>.const_add x)
    convert hh using 1 <;> simp [Function.comp_def]
  have hd : HasDerivAt F (g d + (ψ u - ψ x)) 0 := by
    convert (hline.add_const (ψ x)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (ψ u - ψ x)) using 1
    · funext t
      rfl
    · simp
  have hmin : IsMinOn F (Icc 0 1) 0 := by
    intro t ht
    have he : x + t • d = (1 - t) • x + t • u := by dsimp [d]; module
    have hmem : x + t • d ∈ Q := by
      rw [he]
      exact hψ.1 hx hu (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hupper := hψ.2 hx hu (sub_nonneg.mpr ht.2) ht.1
      (show 1 - t + t = 1 by ring)
    simp only [smul_eq_mul, ← he] at hupper
    have hlow := hm _ hmem
    dsimp [F]
    simp only [zero_smul, add_zero, zero_mul]
    nlinarith
  have htangent : (1 : ℝ) - 0 ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) 1).segment_subset (by constructor <;> norm_num)
        (by constructor <;> norm_num))
  have hh := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  have hh' : 0 ≤ g d + (ψ u - ψ x) := by simpa using hh
  dsimp [d] at hh'
  linarith

lemma divergence_three_point
    {q : LongTails.Setups.StochasticGeneralizedMirror.Public}
    (I : LongTails.Setups.StochasticGeneralizedMirror.Instance q) (u p z : q.E) :
    LongTails.Setups.StochasticGeneralizedMirror.divergence I u z -
      LongTails.Setups.StochasticGeneralizedMirror.divergence I u p -
      LongTails.Setups.StochasticGeneralizedMirror.divergence I p z =
        (I.dh p - I.dh z) (u - p) := by
  simp only [LongTails.Setups.StochasticGeneralizedMirror.divergence,
    sub_apply, map_sub]
  ring

open LongTails.Setups.StochasticGeneralizedMirror

lemma prox_three_point {q : Public} (I : Instance q) {a : ℝ} (ha : 0 < a)
    {z p u : q.E} {v : Dual q} (hψ : ConvexOn ℝ I.Q I.ψ)
    (hp : p ∈ I.Q) (hu : u ∈ I.Q) (hd : HasFDerivAt I.h (I.dh p) p)
    (hm : IsMinOn (proxObjective I a z v) I.Q p) :
    a * (v (p - u) + I.ψ p - I.ψ u) ≤
      divergence I u z - divergence I u p - divergence I p z := by
  let H : q.E → ℝ := fun w => I.h w + a * v (w - z) - I.dh z (w - z)
  have hv : HasFDerivAt (fun w => v (w - z)) v p := by
    simpa only [map_sub] using v.hasFDerivAt.sub_const (v z)
  have hz : HasFDerivAt (fun w => I.dh z (w - z)) (I.dh z) p := by
    simpa only [map_sub] using (I.dh z).hasFDerivAt.sub_const (I.dh z z)
  have hH : HasFDerivAt H (I.dh p + a • v - I.dh z) p :=
    (hd.add (hv.const_mul a)).sub hz
  have hc : ConvexOn ℝ I.Q (fun w => a * I.ψ w) := by
    simpa only [smul_eq_mul] using ConvexOn.smul ha.le hψ
  have hmin : ∀ w ∈ I.Q, H p + a * I.ψ p ≤ H w + a * I.ψ w := by
    intro w hw
    have hh := hm hw
    change proxObjective I a z v p ≤ proxObjective I a z v w at hh
    dsimp [proxObjective, divergence, H] at hh ⊢
    nlinarith
  have hh := composite_optimality hc hp hH hmin hu
  rw [divergence_three_point I u p z]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul,
    map_sub] at hh ⊢
  nlinarith

lemma prox_comparator {q : Public} (I : Instance q) {a : ℝ} (ha : 0 < a)
    {z p u : q.E} {v : Dual q} (hψ : ConvexOn ℝ I.Q I.ψ)
    (hp : p ∈ I.Q) (hu : u ∈ I.Q) (hd : HasFDerivAt I.h (I.dh p) p)
    (hm : IsMinOn (proxObjective I a z v) I.Q p)
    (hf : HasFDerivAt I.f (I.df u) u) (hopt : IsMinOn (objective I) I.Q u)
    (hD : 0 ≤ divergence I p z) :
    divergence I u p ≤ divergence I u z + a * (v - I.df u) (u - p) := by
  have hthree := prox_three_point I ha hψ hp hu hd hm
  have hop := composite_optimality hψ hu hf hopt hp
  have hmul := mul_nonneg ha.le hop
  simp only [sub_apply, map_sub] at hthree hmul ⊢
  nlinarith

lemma prox_localization {q : Public} (I : Instance q) {a R : ℝ}
    (ha : 0 < a) (hR : 0 < R) {z p u : q.E} {v : Dual q}
    (hψ : ConvexOn ℝ I.Q I.ψ) (hp : p ∈ I.Q) (hu : u ∈ I.Q)
    (hd : HasFDerivAt I.h (I.dh p) p)
    (hm : IsMinOn (proxObjective I a z v) I.Q p)
    (hf : HasFDerivAt I.f (I.df u) u) (hopt : IsMinOn (objective I) I.Q u)
    (hD : 0 ≤ divergence I p z)
    (hstrong : ‖u - p‖ ^ 2 / 2 ≤ divergence I u p)
    (hinit : divergence I u z ≤ R ^ 2 / 2)
    (hstep : a * ‖v - I.df u‖ ≤ R / 4) : ‖u - p‖ ≤ 3 * R / 2 := by
  have hc := prox_comparator I ha hψ hp hu hd hm hf hopt hD
  have he : (v - I.df u) (u - p) ≤ ‖v - I.df u‖ * ‖u - p‖ :=
    (le_abs_self _).trans ((v - I.df u).le_opNorm _)
  have hm := mul_le_mul_of_nonneg_left he ha.le
  apply GeneralizedMirrorPotential.prox_radius (divergence I) u z p hR hstrong hinit
    (e := ‖v - I.df u‖) (a := a) ?_ hstep
  nlinarith

end LongTails.Proofs.GeneralizedMirrorGeometry
