import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import LongTails.Proofs.RipmProxGeometry
import LongTails.Proofs.RipmSmoothGeometry
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmRegularity

noncomputable section

lemma component_measurable {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ)
    (xs : Core.Vec d) (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) :
    Measurable (fun z : I.Sample × Core.Vec d => I.component z.1 z.2) := by
  have hm := MeasureTheory.measurable_uncurry_of_continuous_of_measurable
    (fun s => continuous_iff_continuousAt.mpr
      (fun x => (hS.componentGradient s x).differentiableAt.continuousAt))
    hS.componentMeasurable
  exact hm.comp measurable_swap


lemma trajectory_measurable {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (L Lg eta : ℝ) (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hi : ∀ t, Measurable (i t)) (hj : ∀ t, Measurable (j t)) (t : ℕ) :
    Measurable (Core.trajectory I eta x0 i j t) := by
  have hscale : 0 < eta * (m : ℝ) := mul_pos heta (Nat.cast_pos.mpr hS.countPos)
  have hprox : Measurable (fun z : Fin m × Core.Vec d =>
      Core.prox (I.regularizers z.1) (eta * m) z.2) := by
    apply measurable_from_prod_countable_right
    intro k
    have hp : LipschitzWith 1 (Core.prox (I.regularizers k) (eta * m)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
        LongTails.Proofs.RipmProxGeometry.prox_nonexpansive
          (I.regularizers k) (eta * m) Lg hscale hS.regularizerNonneg
          (hS.regularizerConvex k) (hS.regularizerLipschitz k) x y
    exact hp.continuous.measurable
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun omega =>
      Core.prox (I.regularizers (j t omega)) (eta * m)
        (Core.trajectory I eta x0 i j t omega -
          eta • I.grad (i t omega) (Core.trajectory I eta x0 i j t omega)))
    exact hprox.comp ((hj t).prodMk
      (Measurable.fun_sub ih
        ((measurable_const_smul eta).comp
          (hS.gradientMeasurable.comp ((hi t).prodMk ih)))))


lemma trajectory_adapted {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (t : ℕ) :
    Core.iterateHistory I eta x0 i j t ≤ mΩ ∧ @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _ (Core.trajectory I eta x0 i j t) := by
  let H := fun omega => (fun s : Fin (t + 1) => Core.trajectory I eta x0 i j s.val omega)
  have hHm : Measurable H := measurable_pi_iff.mpr (fun s =>
    trajectory_measurable I L Lg eta x0 xs sigmaSq i j hS heta
      hSamples.1.measurable (fun k => (hSamples.2 k).1) s.val)
  have hH : @Measurable Ω (Fin (t + 1) → Core.Vec d)
      (MeasurableSpace.comap H inferInstance) _ H :=
    measurable_iff_comap_le.mpr le_rfl
  refine ⟨hHm.comap_le, ?_⟩
  exact (measurable_pi_apply (⟨t, by omega⟩ : Fin (t + 1))).comp hH


lemma trajectory_memLp {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (t : ℕ) : MemLp (Core.trajectory I eta x0 i j t) 2 P.toMeasure := by
  have hgrad (k : ℕ) (z : Ω → Core.Vec d) (hz : Measurable z)
      (hz2 : MemLp z 2 P.toMeasure) :
      MemLp (fun omega => I.grad (i k omega) (z omega)) 2 P.toMeasure := by
    have hbase := (LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp
      I L Lg xs sigmaSq hS 0).comp_measurePreserving
        (show MeasurePreserving (i k) P.toMeasure I.law.toMeasure from
          ⟨hSamples.1.measurable k, hSamples.1.marginal k⟩)
    have hbound := (hz2.norm.const_mul L).add hbase.norm
    apply hbound.mono'
      (hS.gradientMeasurable.comp ((hSamples.1.measurable k).prodMk hz)).aestronglyMeasurable
    filter_upwards [] with omega
    have hn := norm_add_le
      (I.grad (i k omega) (z omega) - I.grad (i k omega) 0) (I.grad (i k omega) 0)
    rw [sub_add_cancel] at hn
    have hs := hS.componentSmooth (i k omega) (z omega) 0
    rw [sub_zero] at hs
    exact hn.trans (add_le_add hs le_rfl)
  have hmeas (k : ℕ) := trajectory_measurable I L Lg eta x0 xs sigmaSq i j hS heta
    hSamples.1.measurable (fun n => (hSamples.2 n).1) k
  have hscale : 0 < eta * (m : ℝ) := mul_pos heta (Nat.cast_pos.mpr hS.countPos)
  induction t with
  | zero => exact memLp_const _
  | succ t ih =>
    let v := fun omega => Core.trajectory I eta x0 i j t omega -
      eta • I.grad (i t omega) (Core.trajectory I eta x0 i j t omega)
    have hv : MemLp v 2 P.toMeasure :=
      ih.sub ((hgrad t _ (hmeas t) ih).const_smul eta)
    have hb := hv.norm.add (memLp_const (eta * (m : ℝ) * Lg) (p := 2) (μ := P.toMeasure))
    apply hb.mono' (hmeas (t + 1)).aestronglyMeasurable
    filter_upwards [] with omega
    change ‖Core.prox (I.regularizers (j t omega)) (eta * m) (v omega)‖ ≤
      ‖v omega‖ + eta * m * Lg
    have hp := LongTails.Proofs.RipmProxGeometry.prox_displacement
      (I.regularizers (j t omega)) (eta * m) Lg hscale hS.regularizerNonneg
      (hS.regularizerConvex _) (hS.regularizerLipschitz _) (v omega)
    have hn := norm_add_le
      (Core.prox (I.regularizers (j t omega)) (eta * m) (v omega) - v omega) (v omega)
    rw [sub_add_cancel] at hn
    linarith


lemma gradient_memLp {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (t : ℕ) :
    MemLp (fun omega => I.grad (i t omega) (Core.trajectory I eta x0 i j t omega)) 2 P.toMeasure := by
  have hgrad (k : ℕ) (z : Ω → Core.Vec d) (hz : Measurable z)
      (hz2 : MemLp z 2 P.toMeasure) :
      MemLp (fun omega => I.grad (i k omega) (z omega)) 2 P.toMeasure := by
    have hbase := (LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp
      I L Lg xs sigmaSq hS 0).comp_measurePreserving
        (show MeasurePreserving (i k) P.toMeasure I.law.toMeasure from
          ⟨hSamples.1.measurable k, hSamples.1.marginal k⟩)
    have hbound := (hz2.norm.const_mul L).add hbase.norm
    apply hbound.mono'
      (hS.gradientMeasurable.comp ((hSamples.1.measurable k).prodMk hz)).aestronglyMeasurable
    filter_upwards [] with omega
    have hn := norm_add_le
      (I.grad (i k omega) (z omega) - I.grad (i k omega) 0) (I.grad (i k omega) 0)
    rw [sub_add_cancel] at hn
    have hs := hS.componentSmooth (i k omega) (z omega) 0
    rw [sub_zero] at hs
    exact hn.trans (add_le_add hs le_rfl)
  exact hgrad t _ (trajectory_measurable I L Lg eta x0 xs sigmaSq i j hS heta
    hSamples.1.measurable (fun k => (hSamples.2 k).1) t)
    (trajectory_memLp I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t)


lemma objective_integrable {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (t : ℕ) :
    Integrable (fun omega => Core.objective I (Core.trajectory I eta x0 i j t omega)) P.toMeasure := by
  have hobjL1 (z : Ω → Core.Vec d) (hz : Measurable z)
      (hz2 : MemLp z 2 P.toMeasure) :
      Integrable (fun omega => Core.objective I (z omega)) P.toMeasure := by
    classical
    let F := Core.meanGradient I 0
    let A := |I.average 0| + ∑ k, |I.regularizers k 0|
    let B := ‖F‖ + (m : ℝ) * Lg
    have hf : Continuous I.average := continuous_iff_continuousAt.mpr
      (fun x => (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient
        I L Lg xs sigmaSq hS x).differentiableAt.continuousAt)
    have hg : Continuous (Core.regularizer I) := by
      change Continuous (fun x => ∑ k, I.regularizers k x)
      apply continuous_finsetSum
      intro k hk
      exact continuousOn_univ.mp
        (ConvexOn.continuousOn isOpen_univ (hS.regularizerConvex k))
    have hbound (x : Core.Vec d) :
        ‖Core.objective I x‖ ≤ A + B * ‖x‖ + (L / 2) * ‖x‖ ^ 2 := by
      have hu := LongTails.Proofs.RipmSmoothGeometry.smooth_upper
        I.average (Core.meanGradient I) L hS.smoothPos
        (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient I L Lg xs sigmaSq hS)
        (LongTails.Proofs.RipmSmoothGeometry.mean_lipschitz I L Lg xs sigmaSq hS) 0 x
      have hl := LongTails.Proofs.RipmSmoothGeometry.convex_lower
        I.average (Core.meanGradient I)
        (LongTails.Proofs.RipmSmoothGeometry.mean_convex I L Lg xs sigmaSq hS)
        (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient I L Lg xs sigmaSq hS) 0 x
      rw [sub_zero] at hu hl
      have hi : |inner ℝ F x| ≤ ‖F‖ * ‖x‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) F x
      have hfabs : |I.average x| ≤ |I.average 0| + ‖F‖ * ‖x‖ +
          L / 2 * ‖x‖ ^ 2 := by
        have hi1 := (abs_le.mp hi).1
        have hi2 := (abs_le.mp hi).2
        have hL := hS.smoothPos
        have hquad : 0 ≤ L / 2 * ‖x‖ ^ 2 := by positivity
        apply abs_le.mpr
        constructor <;> dsimp [F] at * <;>
          nlinarith [le_abs_self (I.average 0), neg_abs_le (I.average 0), sq_nonneg ‖x‖]
      have hgabs : |Core.regularizer I x| ≤
          (∑ k, |I.regularizers k 0|) + (m : ℝ) * Lg * ‖x‖ := by
        change |∑ k, I.regularizers k x| ≤ _
        calc
          _ ≤ ∑ k, |I.regularizers k x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k, (|I.regularizers k 0| + Lg * ‖x‖) := by
            apply Finset.sum_le_sum
            intro k hk
            have h := hS.regularizerLipschitz k x 0
            rw [sub_zero] at h
            have ht := abs_add_le (I.regularizers k x - I.regularizers k 0)
              (I.regularizers k 0)
            rw [sub_add_cancel] at ht
            linarith
          _ = _ := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
      have hh := abs_add_le (I.average x) (Core.regularizer I x)
      change |I.average x + Core.regularizer I x| ≤ _
      dsimp [A, B]
      nlinarith
    have hn := (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hz2).norm
    have hs := (memLp_two_iff_integrable_sq_norm hz2.aestronglyMeasurable).mp hz2
    have hb := ((integrable_const A).fun_add (hn.const_mul B)).fun_add (hs.const_mul (L / 2))
    apply hb.mono' ((hf.add hg).measurable.comp hz).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun omega => hbound (z omega))
  exact hobjL1 _ (trajectory_measurable I L Lg eta x0 xs sigmaSq i j hS heta
    hSamples.1.measurable (fun k => (hSamples.2 k).1) t)
    (trajectory_memLp I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t)


lemma reference_integrable {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (t : ℕ) (z : Ω → Core.Vec d)
    (hz : @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _ z)
    (hz2 : MemLp z 2 P.toMeasure) :
    Integrable (fun omega => Core.objective I (z omega)) P.toMeasure ∧
    Integrable (fun omega => ‖Core.trajectory I eta x0 i j t omega - z omega‖ ^ 2) P.toMeasure ∧
    Integrable (fun omega => ‖Core.trajectory I eta x0 i j (t + 1) omega - z omega‖ ^ 2) P.toMeasure ∧
    Integrable (fun omega => I.component (i t omega) (z omega)) P.toMeasure ∧
    Integrable (fun omega => I.regularizers (j t omega) (z omega)) P.toMeasure ∧
    Integrable (fun omega => I.regularizers (j t omega) (Core.trajectory I eta x0 i j (t + 1) omega)) P.toMeasure := by
  have hobjL1 (z : Ω → Core.Vec d) (hz : Measurable z)
      (hz2 : MemLp z 2 P.toMeasure) :
      Integrable (fun omega => Core.objective I (z omega)) P.toMeasure := by
    classical
    let F := Core.meanGradient I 0
    let A := |I.average 0| + ∑ k, |I.regularizers k 0|
    let B := ‖F‖ + (m : ℝ) * Lg
    have hf : Continuous I.average := continuous_iff_continuousAt.mpr
      (fun x => (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient
        I L Lg xs sigmaSq hS x).differentiableAt.continuousAt)
    have hg : Continuous (Core.regularizer I) := by
      change Continuous (fun x => ∑ k, I.regularizers k x)
      apply continuous_finsetSum
      intro k hk
      exact continuousOn_univ.mp
        (ConvexOn.continuousOn isOpen_univ (hS.regularizerConvex k))
    have hbound (x : Core.Vec d) :
        ‖Core.objective I x‖ ≤ A + B * ‖x‖ + (L / 2) * ‖x‖ ^ 2 := by
      have hu := LongTails.Proofs.RipmSmoothGeometry.smooth_upper
        I.average (Core.meanGradient I) L hS.smoothPos
        (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient I L Lg xs sigmaSq hS)
        (LongTails.Proofs.RipmSmoothGeometry.mean_lipschitz I L Lg xs sigmaSq hS) 0 x
      have hl := LongTails.Proofs.RipmSmoothGeometry.convex_lower
        I.average (Core.meanGradient I)
        (LongTails.Proofs.RipmSmoothGeometry.mean_convex I L Lg xs sigmaSq hS)
        (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient I L Lg xs sigmaSq hS) 0 x
      rw [sub_zero] at hu hl
      have hi : |inner ℝ F x| ≤ ‖F‖ * ‖x‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) F x
      have hfabs : |I.average x| ≤ |I.average 0| + ‖F‖ * ‖x‖ +
          L / 2 * ‖x‖ ^ 2 := by
        have hi1 := (abs_le.mp hi).1
        have hi2 := (abs_le.mp hi).2
        have hL := hS.smoothPos
        have hquad : 0 ≤ L / 2 * ‖x‖ ^ 2 := by positivity
        apply abs_le.mpr
        constructor <;> dsimp [F] at * <;>
          nlinarith [le_abs_self (I.average 0), neg_abs_le (I.average 0), sq_nonneg ‖x‖]
      have hgabs : |Core.regularizer I x| ≤
          (∑ k, |I.regularizers k 0|) + (m : ℝ) * Lg * ‖x‖ := by
        change |∑ k, I.regularizers k x| ≤ _
        calc
          _ ≤ ∑ k, |I.regularizers k x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k, (|I.regularizers k 0| + Lg * ‖x‖) := by
            apply Finset.sum_le_sum
            intro k hk
            have h := hS.regularizerLipschitz k x 0
            rw [sub_zero] at h
            have ht := abs_add_le (I.regularizers k x - I.regularizers k 0)
              (I.regularizers k 0)
            rw [sub_add_cancel] at ht
            linarith
          _ = _ := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
      have hh := abs_add_le (I.average x) (Core.regularizer I x)
      change |I.average x + Core.regularizer I x| ≤ _
      dsimp [A, B]
      nlinarith
    have hn := (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hz2).norm
    have hs := (memLp_two_iff_integrable_sq_norm hz2.aestronglyMeasurable).mp hz2
    have hb := ((integrable_const A).fun_add (hn.const_mul B)).fun_add (hs.const_mul (L / 2))
    apply hb.mono' ((hf.add hg).measurable.comp hz).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun omega => hbound (z omega))
  classical
  have hzM : Measurable z := hz.mono
    (trajectory_adapted I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t).1 le_rfl
  have hmp : MeasurePreserving (i t) P.toMeasure I.law.toMeasure :=
    ⟨hSamples.1.measurable t, hSamples.1.marginal t⟩
  have hphi0 := hmp.integrable_comp_of_integrable (hS.componentIntegrable 0)
  have hg0 := (LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp
    I L Lg xs sigmaSq hS 0).comp_measurePreserving hmp
  have hzSq := (memLp_two_iff_integrable_sq_norm hz2.aestronglyMeasurable).mp hz2
  have hphi : Integrable (fun omega => I.component (i t omega) (z omega)) P.toMeasure := by
    have hb := (hphi0.norm.fun_add (hg0.norm.integrable_mul hz2.norm)).fun_add
      (hzSq.const_mul (L / 2))
    apply hb.mono'
      ((component_measurable I L Lg xs sigmaSq hS).comp
        ((hSamples.1.measurable t).prodMk hzM)).aestronglyMeasurable
    filter_upwards [] with omega
    let s := i t omega
    let x := z omega
    have hu := LongTails.Proofs.RipmSmoothGeometry.smooth_upper
      (I.component s) (I.grad s) L hS.smoothPos (hS.componentGradient s)
      (hS.componentSmooth s) 0 x
    have hl := LongTails.Proofs.RipmSmoothGeometry.convex_lower
      (I.component s) (I.grad s) (hS.componentConvex s)
      (hS.componentGradient s) 0 x
    rw [sub_zero] at hu hl
    have hi : |inner ℝ (I.grad s 0) x| ≤ ‖I.grad s 0‖ * ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (I.grad s 0) x
    have hi1 := (abs_le.mp hi).1
    have hi2 := (abs_le.mp hi).2
    have hL := hS.smoothPos
    have hquad : 0 ≤ L / 2 * ‖x‖ ^ 2 := by positivity
    change |I.component s x| ≤ |I.component s 0| +
      ‖I.grad s 0‖ * ‖x‖ + L / 2 * ‖x‖ ^ 2
    apply abs_le.mpr
    constructor <;> nlinarith [le_abs_self (I.component s 0), neg_abs_le (I.component s 0)]
  have hreg (v : Ω → Core.Vec d) (hv : Measurable v) (hv2 : MemLp v 2 P.toMeasure) :
      Integrable (fun omega => I.regularizers (j t omega) (v omega)) P.toMeasure := by
    have hm : Measurable (fun p : Fin m × Core.Vec d => I.regularizers p.1 p.2) := by
      apply measurable_from_prod_countable_right
      intro k
      exact (continuousOn_univ.mp
        (ConvexOn.continuousOn isOpen_univ (hS.regularizerConvex k))).measurable
    have hb := (integrable_const (∑ k, |I.regularizers k 0|)).fun_add
      ((MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hv2).norm.const_mul Lg)
    apply hb.mono' (hm.comp (((hSamples.2 t).1).prodMk hv)).aestronglyMeasurable
    filter_upwards [] with omega
    have h := hS.regularizerLipschitz (j t omega) (v omega) 0
    rw [sub_zero] at h
    have ht := abs_add_le
      (I.regularizers (j t omega) (v omega) - I.regularizers (j t omega) 0)
      (I.regularizers (j t omega) 0)
    rw [sub_add_cancel] at ht
    have hs : |I.regularizers (j t omega) 0| ≤ ∑ k, |I.regularizers k 0| :=
      Finset.single_le_sum (f := fun k : Fin m => |I.regularizers k 0|)
        (fun k _hk => abs_nonneg (I.regularizers k 0)) (Finset.mem_univ (j t omega))
    change |I.regularizers (j t omega) (v omega)| ≤ _
    linarith
  have hx := trajectory_memLp I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t
  have hx1 := trajectory_memLp I P L Lg eta x0 xs sigmaSq i j hS heta hSamples (t + 1)
  have hd0 := hx.sub hz2
  have hd1 := hx1.sub hz2
  exact ⟨hobjL1 z hzM hz2,
    (memLp_two_iff_integrable_sq_norm hd0.aestronglyMeasurable).mp hd0,
    (memLp_two_iff_integrable_sq_norm hd1.aestronglyMeasurable).mp hd1,
    hphi, hreg z hzM hz2,
    hreg _ (trajectory_measurable I L Lg eta x0 xs sigmaSq i j hS heta
      hSamples.1.measurable (fun k => (hSamples.2 k).1) (t + 1)) hx1⟩


lemma anchor_memLp {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (T t : ℕ) (mu : ℝ)
    (hmu : 0 ≤ mu) (hmu1 : mu < 1) (ht : t ≤ T) :
    MemLp (Core.anchor T mu xs (Core.trajectory I eta x0 i j) t) 2 P.toMeasure := by
  have hall : ∀ k, k ≤ T →
      MemLp (Core.anchor T mu xs (Core.trajectory I eta x0 i j) k) 2 P.toMeasure := by
    intro k
    induction k with
    | zero =>
      intro _
      exact memLp_const _
    | succ k ih =>
      intro hk
      have hp := trajectory_memLp I P L Lg eta x0 xs sigmaSq i j hS heta hSamples (k + 1)
      have hprev := ih (Nat.le_trans (Nat.le_succ k) hk)
      let c := Core.mixing T mu (k + 1)
      have hc0 : 0 ≤ c := by
        change 0 ≤ if k + 1 = 0 then 1 else
          ((T - (k + 1) : ℕ) + 1 + mu) / ((T - (k + 1) : ℕ) + 2)
        rw [ite_eq_right (Nat.succ_ne_zero k)]
        positivity
      have hc1 : c ≤ 1 := by
        change (if k + 1 = 0 then 1 else
          ((T - (k + 1) : ℕ) + 1 + mu) / ((T - (k + 1) : ℕ) + 2)) ≤ 1
        rw [ite_eq_right (Nat.succ_ne_zero k)]
        apply (div_le_one (by positivity)).mpr
        linarith
      change MemLp (fun omega =>
        (1 - c) • Core.trajectory I eta x0 i j (k + 1) omega +
          c • Core.anchor T mu xs (Core.trajectory I eta x0 i j) k omega) 2 P.toMeasure
      apply (hp.norm.add hprev.norm).mono'
        ((hp.aestronglyMeasurable.fun_const_smul (1 - c)).fun_add
          (hprev.aestronglyMeasurable.fun_const_smul c))
      filter_upwards [] with omega
      have hn := norm_add_le
        ((1 - c) • Core.trajectory I eta x0 i j (k + 1) omega)
        (c • Core.anchor T mu xs (Core.trajectory I eta x0 i j) k omega)
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hc1), abs_of_nonneg hc0] at hn
      have h1 := mul_le_mul_of_nonneg_right (show 1 - c ≤ 1 by linarith)
        (norm_nonneg (Core.trajectory I eta x0 i j (k + 1) omega))
      have h2 := mul_le_mul_of_nonneg_right hc1
        (norm_nonneg (Core.anchor T mu xs (Core.trajectory I eta x0 i j) k omega))
      simp only [Pi.add_apply]
      linarith
  exact hall t ht


lemma anchor_regular {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (T t : ℕ) (mu : ℝ)
    (hmu : 0 ≤ mu) (hmu1 : mu < 1) (ht : t ≤ T) :
    let z := Core.anchor T mu xs (Core.trajectory I eta x0 i j) t
    @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _ z ∧
      Integrable (fun omega => Core.objective I (z omega)) P.toMeasure ∧
      Integrable (fun omega => ‖Core.trajectory I eta x0 i j t omega - z omega‖ ^ 2) P.toMeasure ∧
      Integrable (fun omega => ‖Core.trajectory I eta x0 i j (t + 1) omega - z omega‖ ^ 2) P.toMeasure := by
  let H := fun omega => (fun s : Fin (t + 1) => Core.trajectory I eta x0 i j s.val omega)
  have hH : @Measurable Ω (Fin (t + 1) → Core.Vec d)
      (Core.iterateHistory I eta x0 i j t) _ H :=
    measurable_iff_comap_le.mpr le_rfl
  have hX (k : ℕ) (hk : k ≤ t) :
      @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _
        (Core.trajectory I eta x0 i j k) :=
    (measurable_pi_apply (⟨k, by omega⟩ : Fin (t + 1))).comp hH
  have hA : ∀ k, k ≤ t →
      @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _
        (Core.anchor T mu xs (Core.trajectory I eta x0 i j) k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact measurable_const
    | succ k ih =>
      intro hk
      change @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _
        (fun omega => (1 - Core.mixing T mu (k + 1)) •
          Core.trajectory I eta x0 i j (k + 1) omega +
          Core.mixing T mu (k + 1) •
            Core.anchor T mu xs (Core.trajectory I eta x0 i j) k omega)
      exact Measurable.fun_add
        ((measurable_const_smul (1 - Core.mixing T mu (k + 1))).comp (hX (k + 1) hk))
        ((measurable_const_smul (Core.mixing T mu (k + 1))).comp (ih (by omega)))
  have hz := hA t le_rfl
  have hr := reference_integrable I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t
    (Core.anchor T mu xs (Core.trajectory I eta x0 i j) t) hz
    (anchor_memLp I P L Lg eta x0 xs sigmaSq i j hS heta hSamples T t mu hmu hmu1 ht)
  exact ⟨hz, hr.1, hr.2.1, hr.2.2.1⟩


end

end LongTails.Proofs.RipmRegularity
