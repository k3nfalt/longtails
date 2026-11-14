import LongTails.Proofs.CoupledMinimaxCertificate
import LongTails.Proofs.CoupledMinimaxGeometry
import LongTails.Proofs.CoupledMinimaxTuning
import LongTails.Proofs.CoupledMinimaxMultipliers

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxKkt

open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxGeometry
open LongTails.Proofs.CoupledMinimaxTuning
open LongTails.Proofs.CoupledMinimaxCertificate

noncomputable def constraintGradient {p : Params} (I : Instance p) (z : Joint p)
    (i : Fin p.constraints) : YSpace p :=
  ((I.jac z).adjoint (PiLp.single 2 i 1)).snd

lemma adjoint_y_inner {p : Params} (I : Instance p) (z : Joint p)
    (w : Weights p) (d : YSpace p) :
    ⟪((I.jac z).adjoint w).snd, d⟫ = ⟪w, I.jac z (WithLp.toLp 2 (0, d))⟫ := by
  have hh := ContinuousLinearMap.adjoint_inner_left (I.jac z) (WithLp.toLp 2 (0, d)) w
  rw [WithLp.prod_inner_apply] at hh
  simpa using hh

lemma constraint_gradient_inner {p : Params} (I : Instance p) (z : Joint p)
    (i : Fin p.constraints) (d : YSpace p) :
    ⟪constraintGradient I z i, d⟫ = (I.jac z (WithLp.toLp 2 (0, d))) i := by
  unfold constraintGradient
  rw [adjoint_y_inner]
  simpa using EuclideanSpace.inner_single_left i (1 : ℝ)
    (I.jac z (WithLp.toLp 2 (0, d)))

lemma weighted_constraint_gradient {p : Params} (I : Instance p) (z : Joint p)
    (w : Weights p) :
    (∑ i, w i • constraintGradient I z i) = ((I.jac z).adjoint w).snd := by
  apply ext_inner_right ℝ
  intro d
  simp only [sum_inner, real_inner_smul_left, constraint_gradient_inner, adjoint_y_inner]
  simp [PiLp.inner_apply, mul_comm]

lemma norm_of_coordinate_bound {m : ℕ} {v : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hr : 0 ≤ r) (hv : ∀ i, |v i| ≤ r) : ‖v‖ ≤ Real.sqrt m * r := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  calc
    ∑ i, (v i) ^ 2 ≤ ∑ _ : Fin m, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (sq_le_sq₀ (abs_nonneg (v i)) hr).mpr (hv i)
      simpa only [sq_abs] using hh
    _ = (m : ℝ) * r ^ 2 := by simp

lemma tolerance_total {p : Params} (hv : Valid p) :
    2 * (1 + Real.sqrt p.constraints + cap p) * tolerance p ≤ p.ε := by
  have he := hv.ε_pos
  have hc := cap_pos hv
  have hs := Real.sqrt_nonneg (p.constraints : ℝ)
  have ht := tolerance_pos hv
  have hid : 2 * (1 + p.ε) * (1 + Real.sqrt p.constraints + cap p) * tolerance p = p.ε := by
    unfold tolerance
    field_simp
  have hh := mul_nonneg he.le (show 0 ≤ 2 * (1 + Real.sqrt p.constraints + cap p) * tolerance p by positivity)
  nlinarith

lemma capped_feasibility {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {z : Joint p} (hz : z ∈ domain p)
    {w v : Weights p} {ny : YSpace p} (hw : ∀ i, 0 ≤ w i)
    (hsum : (∑ i, w i) ≤ cap p)
    (hvn : ∀ u : Weights p, (∀ i, 0 ≤ u i) → (∑ i, u i) ≤ cap p →
      ⟪v, u - w⟫ ≤ 0)
    (hvr : ‖v - I.c z‖ ≤ tolerance p) (hny : Normal p.Y z.snd ny)
    (hyr : ‖(I.g z).snd - ((I.jac z).adjoint w).snd - ny‖ ≤ tolerance p) :
    (∀ i, max (I.c z i) 0 ≤ 2 * tolerance p) ∧
      (∑ i, |w i * I.c z i|) ≤ 2 * cap p * tolerance p := by
  classical
  obtain ⟨d, hd, hnd, hdir⟩ := H.qualification z hz
  have hcap : p.Z * (p.Gy + tolerance p) < p.δ * cap p := by
    have he : p.δ * cap p = p.δ + 2 * p.Z * (p.Gy + 1) := by
      unfold cap
      field_simp [hv.δ_pos.ne']
    rw [he]
    have ht := tolerance_le_one hv
    have hm := mul_le_mul_of_nonneg_left ht hv.Z_pos.le
    nlinarith [hv.δ_pos, hv.Z_pos, hv.Gy_nonneg]
  apply CoupledMinimaxMultipliers.transfer (a := constraintGradient I z)
    (d := d) (g := (I.g z).snd) (n := ny) (v := fun i => v i)
    (cap_pos hv) hw (tolerance_pos hv).le hcap hsum
  · intro u hu hs
    have hh := hvn (WithLp.toLp 2 u) hu hs
    simpa [PiLp.inner_apply, mul_comm] using hh
  · intro i
    have hh := (PiLp.norm_apply_le (v - I.c z) i).trans hvr
    simpa [Real.norm_eq_abs] using hh
  · exact H.gradientY_bound z hz
  · exact hd
  · rw [weighted_constraint_gradient]
    exact hyr
  · exact hnd ny hny
  · intro i hi
    rw [constraint_gradient_inner]
    exact hdir i hi

lemma tolerance_accuracy {p : Params} (hv : Valid p) :
    tolerance p ≤ p.ε ∧ 2 * Real.sqrt p.constraints * tolerance p ≤ p.ε ∧
      2 * cap p * tolerance p ≤ p.ε := by
  have hh := tolerance_total hv
  have ht := tolerance_pos hv
  have hc := mul_nonneg (cap_pos hv).le ht.le
  have hs := mul_nonneg (Real.sqrt_nonneg (p.constraints : ℝ)) ht.le
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma residual_kkt {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {o : Output p} (hr : ResidualBound p I o) : KKT p I o := by
  let q : MinSpace p := WithLp.toLp 2 (o.x, o.multiplier)
  let z := query p q o.y
  obtain ⟨hq, hy, n, ny, hn, hny, hres, hyres⟩ := hr
  have hz : z ∈ domain p := ⟨hq.1, hy⟩
  obtain ⟨hnx, hnw⟩ := min_normal_components hq hn
  have hxres := (WithLp.norm_fst_le (XSpace p)
    (minGradient p (exactReply p I z) q.snd + n)).trans hres
  have hwres := (WithLp.norm_snd_le (XSpace p)
    (minGradient p (exactReply p I z) q.snd + n)).trans hres
  have hwres' : ‖n.snd - I.c z‖ ≤ tolerance p := by
    change ‖-I.c z + n.snd‖ ≤ tolerance p at hwres
    simpa only [sub_eq_add_neg, add_comm] using hwres
  have hyres' : ‖(I.g z).snd - ((I.jac z).adjoint q.snd).snd - ny‖ ≤ tolerance p := by
    have he : (I.g z).snd - ((I.jac z).adjoint q.snd).snd - ny =
        -(innerGradient I q o.y + ny) := by
      simp only [innerGradient]
      change _ = -(-((I.g z).snd - ((I.jac z).adjoint q.snd).snd) + ny)
      abel
    rw [he, norm_neg]
    exact hyres
  obtain ⟨hfeas, hcomp⟩ := capped_feasibility hv H hz hq.2.1 hq.2.2 hnw hwres' hny hyres'
  obtain ⟨ht, hf, hc⟩ := tolerance_accuracy hv
  have hfnorm : ‖WithLp.toLp 2 (fun i => max (I.c z i) 0)‖ ≤
      Real.sqrt p.constraints * (2 * tolerance p) := by
    apply norm_of_coordinate_bound (mul_nonneg (by norm_num) (tolerance_pos hv).le)
    intro i
    change |max (I.c z i) 0| ≤ 2 * tolerance p
    rw [abs_of_nonneg (le_max_right (I.c z i) 0)]
    exact hfeas i
  change q.fst ∈ p.X ∧ o.y ∈ p.Y ∧ (∀ i, 0 ≤ q.snd i) ∧ _
  refine ⟨hq.1, hy, hq.2.1, ?_, hcomp.trans hc, n.fst, ny, hnx, hny, ?_, ?_⟩
  · exact hfnorm.trans (by nlinarith [hf])
  · exact hxres.trans ht
  · exact hyres'.trans ht

lemma selected_kkt {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) :
    KKT p I (select p (OracleTemplate.QueryPlan.eval (exactReply p I)
      (outer p (outerIterations p) (start p)))) :=
  residual_kkt hv H (selected_residual hv H)

lemma execute_kkt {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) (O : OracleTemplate.Oracle (Joint p) (Reply p))
    (hans : ∀ history seed z, z ∈ domain p → O.answer history (0, z) seed = exactReply p I z)
    {K : ℕ} (hK : calls p ≤ K) (ξ : (k : ℕ) → O.Seed k) :
    KKT p I (OracleTemplate.execute O (algorithm p) (fun _ => K) () ξ) := by
  rw [CoupledMinimaxInner.execute_eq hv H O hans hK ξ]
  exact selected_kkt hv H

end LongTails.Proofs.CoupledMinimaxKkt
