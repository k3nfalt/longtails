import LongTails.Proofs.BFGSComposite
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

open Set Filter Topology
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BFGSWolfe

open OracleTemplate LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSComposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma line_deriv {f : E → ℝ} {grad : E → E} (hg : ∀ z, HasGradientAt f (grad z) z) (x v : E)
    (t : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • v)) ⟪grad (x + t • v), v⟫ t := by
  have hp : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h := (hasGradientAt_iff_hasFDerivAt.mp (hg (x + t • v))).comp_hasDerivAt t hp
  exact h

theorem wolfe_exists {f : E → ℝ} {grad : E → E} (hg : ∀ z, HasGradientAt f (grad z) z)
    {m : ℝ} (hlow : ∀ z, m ≤ f z) {c1 c2 : ℝ} (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (x v : E) (hv : ⟪grad x, v⟫ < 0) :
    ∃ α, 0 < α ∧ f (x + α • v) ≤ f x + c1 * α * ⟪grad x, v⟫ ∧
      c2 * ⟪grad x, v⟫ ≤ ⟪grad (x + α • v), v⟫ := by
  set s := ⟪grad x, v⟫
  set ψ : ℝ → ℝ := fun t => f (x + t • v) - f x - c1 * t * s
  have hψd : ∀ t, HasDerivAt ψ (⟪grad (x + t • v), v⟫ - c1 * s) t := by
    intro t
    have h1 := line_deriv hg x v t
    have h2 : HasDerivAt (fun t : ℝ => c1 * t * s) (c1 * s) t := by
      simpa using ((hasDerivAt_id t).const_mul c1).mul_const s
    exact (h1.sub_const (f x)).sub h2
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun t => (hψd t).continuousAt
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  set T := (f x - m + 1) / (-(c1 * s))
  have hcs : 0 < -(c1 * s) := by nlinarith
  have hT : 0 < T := div_pos (by linarith [hlow x]) hcs
  have hψT : 0 ≤ ψ T := by
    have hs0 : s ≠ 0 := hv.ne
    have hc0 : c1 ≠ 0 := hc1.ne'
    have h1 : -(c1 * T * s) = f x - m + 1 := by
      simp only [T]
      field_simp
    have := hlow (x + T • v)
    simp only [ψ]
    linarith
  have hslope : Tendsto (slope ψ 0) (𝓝[>] 0) (𝓝 (⟪grad (x + (0 : ℝ) • v), v⟫ - c1 * s)) :=
    (hasDerivAt_iff_tendsto_slope.mp (hψd 0)).mono_left (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  have hlim : ⟪grad (x + (0 : ℝ) • v), v⟫ - c1 * s < 0 := by
    have hgs : ⟪grad (x + (0 : ℝ) • v), v⟫ = s := by simp [s]
    rw [hgs]
    nlinarith
  obtain ⟨t1, ht1s, ht1⟩ := ((hslope.eventually (gt_mem_nhds hlim)).and
    (Ioo_mem_nhdsGT hT)).exists
  have ht1pos : 0 < t1 := ht1.1
  have ht1T : t1 < T := ht1.2
  have hψt1 : ψ t1 < 0 := by
    have : slope ψ 0 t1 < 0 := ht1s
    rw [slope_def_field, hψ0, sub_zero, sub_zero] at this
    exact (div_neg_iff.mp this).elim (fun h => absurd h.2 (not_lt.mpr ht1pos.le)) (fun h => h.1)
  set S := {t ∈ Icc t1 T | 0 ≤ ψ t}
  have hSne : S.Nonempty := ⟨T, ⟨⟨ht1T.le, le_rfl⟩, hψT⟩⟩
  have hSbdd : BddBelow S := ⟨t1, fun t ht => ht.1.1⟩
  have hSclosed : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hψc)
  set tb := sInf S
  have htbS : tb ∈ S := hSclosed.csInf_mem hSne hSbdd
  have htb1 : t1 < tb := by
    rcases lt_or_eq_of_le htbS.1.1 with h | h
    · exact h
    · exfalso
      have := htbS.2
      rw [← h] at this
      linarith
  obtain ⟨τ, hτ, hτd⟩ := exists_hasDerivAt_eq_slope ψ (fun t => ⟪grad (x + t • v), v⟫ - c1 * s)
    htb1 hψc.continuousOn (fun t _ => hψd t)
  have hpos : 0 < (ψ tb - ψ t1) / (tb - t1) := div_pos (by linarith [htbS.2]) (by linarith)
  have hτneg : ψ τ < 0 := by
    by_contra hcon
    push Not at hcon
    have hmem : τ ∈ S := ⟨⟨hτ.1.le, (hτ.2.trans_le htbS.1.2).le⟩, hcon⟩
    have := csInf_le hSbdd hmem
    linarith [hτ.2]
  refine ⟨τ, ht1pos.trans hτ.1, ?_, ?_⟩
  · simp only [ψ] at hτneg
    linarith
  · rw [← hτd] at hpos
    nlinarith

theorem admissible_exists (q : Params) (I : Instance q.toPublic) (hc1 : 0 < q.c1)
    (hc12 : q.c1 < q.c2) (hc2 : q.c2 < 1) {gradH : Space q.m → Space q.m}
    (hgH : ∀ z, HasGradientAt I.h (gradH z) z) {xs : Space q.d}
    (hmin : IsMinOn (objective I) univ xs) :
    ∃ O : Oracle (Space q.d × Space q.d) (ℝ × Space q.d) 1,
      (∀ k seed x v, HasGradientAt (objective I) (O.answer k (0, (x, v)) seed).2
        (x + (O.answer k (0, (x, v)) seed).1 • v)) ∧
      (∀ k seed x v, ⟪gradient (objective I) x, v⟫ < 0 →
        0 < (O.answer k (0, (x, v)) seed).1 ∧
        objective I (x + (O.answer k (0, (x, v)) seed).1 • v) ≤
          objective I x + q.c1 * (O.answer k (0, (x, v)) seed).1 *
            ⟪gradient (objective I) x, v⟫ ∧
        q.c2 * ⟪gradient (objective I) x, v⟫ ≤ ⟪(O.answer k (0, (x, v)) seed).2, v⟫) := by
  set gf : Space q.d → Space q.d := fun x => ContinuousLinearMap.adjoint I.A (gradH (I.A x))
  have hgf : ∀ x, HasGradientAt (objective I) (gf x) x :=
    fun x => hasGradientAt_comp I.A (hgH (I.A x))
  have hgr : ∀ x, gradient (objective I) x = gf x := fun x => (hgf x).gradient
  have hlow : ∀ z, objective I xs ≤ objective I z := fun z => hmin (mem_univ z)
  let step : Space q.d → Space q.d → ℝ := fun x v =>
    if h : ⟪gf x, v⟫ < 0 then Classical.choose (wolfe_exists hgf hlow hc1 hc12 hc2 x v h) else 0
  refine ⟨{ answer := fun _ query _ => (step query.2.1 query.2.2,
      gf (query.2.1 + step query.2.1 query.2.2 • query.2.2)) }, ?_, ?_⟩
  · intro k seed x v
    exact hgf _
  · intro k seed x v hv
    rw [hgr] at hv ⊢
    have hs : step x v = Classical.choose (wolfe_exists hgf hlow hc1 hc12 hc2 x v hv) := by
      simp only [step, hv, ↓reduceDIte]
    have hspec := Classical.choose_spec (wolfe_exists hgf hlow hc1 hc12 hc2 x v hv)
    simp only
    rw [hs]
    exact hspec

end LongTails.Proofs.BFGSWolfe
