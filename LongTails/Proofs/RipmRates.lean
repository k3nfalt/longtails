import LongTails.Setups.RipmGeneral
import LongTails.Proofs.RipmWeights
import Mathlib.Analysis.Complex.ExponentialBounds

import LongTails.Proofs.RipmSmoothGeometry
import LongTails.Proofs.RipmRegularity
import LongTails.Proofs.RipmDescent
import LongTails.Proofs.RipmLastIterate
import LongTails.Algorithms.RipmOutput
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmRates

noncomputable section

def generalBound (T m : ℕ) (C L Lg D2 Delta sigmaSq : ℝ) : ℝ :=
  Real.exp (8 / (Real.exp 1 * C)) *
    (C * L * D2 / Real.sqrt T + 2 * Delta / T +
      4 * sigmaSq / ((C - 2) * L * (T * Real.sqrt T)) +
      16 * sigmaSq * Real.log ((T : ℝ) + 1) / ((C - 2) * L * Real.sqrt T) +
      16 * (m : ℝ) ^ 2 * Lg ^ 2 / (C * L * (T * Real.sqrt T)) +
      64 * (m : ℝ) ^ 2 * Lg ^ 2 * Real.log ((T : ℝ) + 1) / (C * L * Real.sqrt T))

def targetBound (T m : ℕ) (L Lg D2 Delta sigmaSq : ℝ) : ℝ :=
  10 / Real.sqrt T *
    (L * D2 + Delta / Real.sqrt T +
      (sigmaSq + 4 * (m : ℝ) ^ 2 * Lg ^ 2) / L * (1 / T + 4 * Real.log ((T : ℝ) + 1)))

lemma scalar_general (T m : ℕ) (C L Lg D2 Delta sigmaSq R : ℝ)
    (hT : 1 ≤ T) (hC : 4 < C) (hL : 0 < L) (hLg : 0 ≤ Lg)
    (hD : 0 ≤ D2) (hDelta : 0 ≤ Delta) (hSigma : 0 ≤ sigmaSq)
    (hbound :
      let tau := 1 / (C * L * Real.sqrt T)
      let gamma := (1 - 2 * tau * L) / (1 + 2 * tau * L)
      let mu := 2 * tau * L * (1 + gamma)
      let v := (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2
      R ≤ D2 / (2 * tau * Core.weight T mu T) + Delta / Core.weight T mu T +
        (v / Core.weight T mu T) * ∑ t ∈ Finset.range (T + 1), Core.weight T mu t) :
    R ≤ generalBound T m C L Lg D2 Delta sigmaSq := by
  let s := Real.sqrt T
  let tau := 1 / (C * L * s)
  let gamma := (1 - 2 * tau * L) / (1 + 2 * tau * L)
  let mu := 2 * tau * L * (1 + gamma)
  let a := Core.weight T mu T
  let q := (T : ℝ) ^ mu
  let N := (2 * sigmaSq / (C - 2) + 8 * (m : ℝ) ^ 2 * Lg ^ 2 / C) / (L * s)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTr
  have hs : 0 < s := Real.sqrt_pos.mpr hTp
  have hs1 : 1 ≤ s := (Real.le_sqrt (by norm_num) hTp.le).mpr (by simpa using hTr)
  have hs2 : s ^ 2 = (T : ℝ) := Real.sq_sqrt hTp.le
  have hC0 : 0 < C := by linarith
  have hC2 : 0 < C - 2 := by linarith
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hp := LongTails.Proofs.RipmWeights.power_bound L C T hL (by linarith) hT
  change 0 < gamma ∧ 0 < mu ∧ mu < 1 ∧ tau * L = 1 / (C * s) ∧
    tau * L ≤ 1 / C ∧ 1 / C < 1 / 2 ∧ q ≤ Real.exp (8 / (Real.exp 1 * C)) at hp
  obtain ⟨hg, hm, hm1, htl, htlC, hChalf, hpower⟩ := hp
  have ha : 0 < a := LongTails.Proofs.RipmWeights.weight_positive T T mu hm.le le_rfl
  have hq : 0 < q := Real.rpow_pos_of_pos hTp mu
  have hb : 0 < 1 - mu := by linarith
  have htwo : (2 : ℝ) ^ (1 - mu) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 - mu ≤ 1 by linarith)
    simpa only [Real.rpow_one] using h
  have hterminal := LongTails.Proofs.RipmWeights.weight_lower T mu hT hm hm1
  have hbase : (T : ℝ) ^ (1 - mu) ≤ 2 * a := by
    have hmon := Real.rpow_le_rpow hTp.le (show (T : ℝ) ≤ T + 1 by linarith) hb.le
    have hden := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 - mu)
    have hmul := (div_le_iff₀ hden).mp hterminal
    have hupper := mul_le_mul_of_nonneg_left htwo ha.le
    change ((T : ℝ) + 1) ^ (1 - mu) ≤ a * (2 : ℝ) ^ (1 - mu) at hmul
    exact (hmon.trans (hmul.trans hupper)).trans_eq (mul_comm a 2)
  have hprod : (T : ℝ) ^ (1 - mu) * q = (T : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_add hTp, sub_add_cancel, Real.rpow_one]
  have hinv : 1 / a ≤ 2 * q / T := by
    apply (div_le_div_iff₀ ha hTp).mpr
    have h := mul_le_mul_of_nonneg_right hbase hq.le
    rw [hprod] at h
    calc
      1 * (T : ℝ) = T := one_mul _
      _ ≤ (2 * a) * q := h
      _ = 2 * q * a := by ring
  have hsum := LongTails.Proofs.RipmWeights.weight_sum T mu hT hm hm1
  have hsumall : (∑ t ∈ Finset.range (T + 1), Core.weight T mu t) / a ≤
      q * (2 / T + 8 * Real.log ((T : ℝ) + 1)) := by
    have hzero : Core.weight T mu 0 = 1 := rfl
    rw [Finset.sum_range_succ', hzero, add_div]
    change _ / a + 1 / a ≤ _
    change _ / a ≤ 8 * q * Real.log ((T : ℝ) + 1) at hsum
    exact (add_le_add hsum hinv).trans_eq (by ring)
  have hCsLower : C ≤ C * s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hC0.le
  have hCs : 0 < C * s - 2 := by linarith
  have hCsplus : 0 < C * s + 2 := by positivity
  have hgam : gamma = (C * s - 2) / (C * s + 2) := by
    dsimp [gamma]
    rw [show 2 * tau * L = 2 * (tau * L) by ring, htl]
    field_simp [hC0.ne', hs.ne', hCsplus.ne']
  have hcoef : (1 + 1 / gamma) * tau = 2 / (L * (C * s - 2)) := by
    rw [hgam]
    dsimp [tau]
    field_simp [hC0.ne', hL.ne', hs.ne', hCs.ne', hCsplus.ne']
    ring
  have hcoefle : (1 + 1 / gamma) * tau ≤ 2 / ((C - 2) * L * s) := by
    rw [hcoef]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hLs := mul_nonneg hL.le (sub_nonneg.mpr hs1)
    nlinarith only [hLs]
  have hLg2 : 0 ≤ Lg ^ 2 := pow_nonneg hLg 2
  have hnoise : 0 ≤ (m : ℝ) ^ 2 * Lg ^ 2 := mul_nonneg (sq_nonneg _) hLg2
  have hv0 : 0 ≤ (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2 := by
    positivity
  have hv : (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2 ≤ N := by
    have h := mul_le_mul_of_nonneg_right hcoefle hSigma
    have heq : 2 / ((C - 2) * L * s) * sigmaSq +
        8 * tau * (m : ℝ) ^ 2 * Lg ^ 2 = N := by
      dsimp [tau, N]
      field_simp
    rw [← heq]
    calc
      _ = ((1 + 1 / gamma) * tau) * sigmaSq + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2 := by ring
      _ ≤ _ := add_le_add h le_rfl
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hS0 : 0 ≤ q * (2 / T + 8 * Real.log ((T : ℝ) + 1)) := by positivity
  let G := C * L * D2 / s + 2 * Delta / T +
    4 * sigmaSq / ((C - 2) * L * (T * s)) +
    16 * sigmaSq * Real.log ((T : ℝ) + 1) / ((C - 2) * L * s) +
    16 * (m : ℝ) ^ 2 * Lg ^ 2 / (C * L * (T * s)) +
    64 * (m : ℝ) ^ 2 * Lg ^ 2 * Real.log ((T : ℝ) + 1) / (C * L * s)
  have hG : 0 ≤ G := by
    have hreg : 0 ≤ 16 * (m : ℝ) ^ 2 * Lg ^ 2 := by nlinarith only [hnoise]
    have hreglog : 0 ≤ 64 * (m : ℝ) ^ 2 * Lg ^ 2 * Real.log ((T : ℝ) + 1) := by
      have h := mul_nonneg hnoise hlog
      nlinarith only [h]
    dsimp [G]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (by positivity) (by positivity))
            (by positivity))
          (by positivity))
        (div_nonneg hreg (by positivity)))
      (div_nonneg hreglog (by positivity))
  have hDterm : D2 / (2 * tau * a) ≤ D2 / (2 * tau) * (2 * q / T) := by
    have h := mul_le_mul_of_nonneg_left hinv (show 0 ≤ D2 / (2 * tau) by positivity)
    have heq : D2 / (2 * tau * a) = D2 / (2 * tau) * (1 / a) := by ring
    rw [heq]
    exact h
  have hDelterm : Delta / a ≤ Delta * (2 * q / T) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv hDelta
  have hvterm : (((1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2) / a) *
        (∑ t ∈ Finset.range (T + 1), Core.weight T mu t) ≤
        N * (q * (2 / T + 8 * Real.log ((T : ℝ) + 1))) := by
    have h := mul_le_mul_of_nonneg_left hsumall hv0
    have h' := mul_le_mul_of_nonneg_right hv hS0
    have heq : (((1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2) / a) *
        (∑ t ∈ Finset.range (T + 1), Core.weight T mu t) =
        ((1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2) *
          ((∑ t ∈ Finset.range (T + 1), Core.weight T mu t) / a) := by ring
    rw [heq]
    exact h.trans h'
  have halgebra : D2 / (2 * tau) * (2 * q / T) + Delta * (2 * q / T) +
      N * (q * (2 / T + 8 * Real.log ((T : ℝ) + 1))) = q * G := by
    dsimp [tau, N, G]
    rw [← hs2]
    field_simp [hC0.ne', hC2.ne', hL.ne', hs.ne']
    ring
  have hR : R ≤ q * G := by
    change R ≤ D2 / (2 * tau * a) + Delta / a +
      (((1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2) / a) *
        (∑ t ∈ Finset.range (T + 1), Core.weight T mu t) at hbound
    rw [← halgebra]
    exact hbound.trans (add_le_add (add_le_add hDterm hDelterm) hvterm)
  exact hR.trans (mul_le_mul_of_nonneg_right hpower hG)


lemma scalar_five (T m : ℕ) (L Lg D2 Delta sigmaSq R : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hLg : 0 ≤ Lg)
    (hD : 0 ≤ D2) (hDelta : 0 ≤ Delta) (hSigma : 0 ≤ sigmaSq)
    (hbound : R ≤ generalBound T m 5 L Lg D2 Delta sigmaSq) :
    R ≤ targetBound T m L Lg D2 Delta sigmaSq := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTr
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTp
  have hs2 : (Real.sqrt T) ^ 2 = (T : ℝ) := Real.sq_sqrt hTp.le
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLg2 : 0 ≤ Lg ^ 2 := pow_nonneg hLg 2
  have hnoise : 0 ≤ (m : ℝ) ^ 2 * Lg ^ 2 := mul_nonneg (sq_nonneg _) hLg2
  have he : (8 : ℝ) / 3 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hl : (3 : ℝ) / 5 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have harg : 8 / (Real.exp 1 * 5) ≤ Real.log 2 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.exp 1 * 5)).mpr
    have hprod := mul_pos (sub_pos.mpr he) (sub_pos.mpr hl)
    nlinarith
  have hexp : Real.exp (8 / (Real.exp 1 * 5)) ≤ 2 := by
    have h := Real.exp_le_exp.mpr harg
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  let G := 5 * L * D2 / Real.sqrt T + 2 * Delta / T +
    4 * sigmaSq / ((5 - 2) * L * (T * Real.sqrt T)) +
    16 * sigmaSq * Real.log ((T : ℝ) + 1) / ((5 - 2) * L * Real.sqrt T) +
    16 * (m : ℝ) ^ 2 * Lg ^ 2 / (5 * L * (T * Real.sqrt T)) +
    64 * (m : ℝ) ^ 2 * Lg ^ 2 * Real.log ((T : ℝ) + 1) / (5 * L * Real.sqrt T)
  have hG : 0 ≤ G := by
    have hreg : 0 ≤ 16 * (m : ℝ) ^ 2 * Lg ^ 2 := by nlinarith only [hnoise]
    have hreglog : 0 ≤ 64 * (m : ℝ) ^ 2 * Lg ^ 2 * Real.log ((T : ℝ) + 1) := by
      have h := mul_nonneg hnoise hlog
      nlinarith only [h]
    dsimp [G]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (by positivity) (by positivity))
            (by positivity))
          (by positivity))
        (div_nonneg hreg (by positivity)))
      (div_nonneg hreglog (by positivity))
  have hmajor : 2 * G ≤ targetBound T m L Lg D2 Delta sigmaSq := by
    have heq : targetBound T m L Lg D2 Delta sigmaSq - 2 * G =
        6 * Delta / T + (22 / 3 : ℝ) * sigmaSq / (L * (T * Real.sqrt T)) +
        (88 / 3 : ℝ) * sigmaSq * Real.log ((T : ℝ) + 1) / (L * Real.sqrt T) +
        (168 / 5 : ℝ) * (m : ℝ) ^ 2 * Lg ^ 2 / (L * (T * Real.sqrt T)) +
        (672 / 5 : ℝ) * (m : ℝ) ^ 2 * Lg ^ 2 * Real.log ((T : ℝ) + 1) /
          (L * Real.sqrt T) := by
      delta targetBound
      dsimp [G]
      generalize Real.sqrt T = s at hs hs2 ⊢
      rw [← hs2]
      field_simp [hL.ne', hs.ne']
      ring
    have hnonneg : 0 ≤ targetBound T m L Lg D2 Delta sigmaSq - 2 * G := by
      rw [heq]
      positivity
    linarith
  exact hbound.trans ((mul_le_mul_of_nonneg_right hexp hG).trans hmajor)



lemma general_rate {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (T : ℕ) (hT : 1 ≤ T) (C : ℝ) (hC : 4 < C)
    (hSamples : Core.Sampling I P (1 / (C * L * Real.sqrt T)) x0 i j) :
    (∫ omega, Core.objective I (LongTails.Algorithms.RipmOutput.lastIterate I (1 / (C * L * Real.sqrt T)) x0 i j T omega) - Core.objective I xs ∂P.toMeasure) ≤
      generalBound T m C L Lg (‖x0 - xs‖ ^ 2)
        (Core.objective I x0 - Core.objective I xs) sigmaSq := by
  classical
  let tau := 1 / (C * L * Real.sqrt T)
  let gamma := (1 - 2 * tau * L) / (1 + 2 * tau * L)
  let mu := 2 * tau * L * (1 + gamma)
  let v := (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2
  have hCpos : 0 < C := by linarith
  have hL := hS.smoothPos
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨hgamma, hmu, hmu1, htauL, htauC, hC2, hpow⟩ :=
    LongTails.Proofs.RipmWeights.power_bound L C T hL (by linarith) hT
  change 0 < gamma at hgamma
  change 0 < mu at hmu
  change mu < 1 at hmu1
  change tau * L ≤ 1 / C at htauC
  have hstep : tau * L < 1 / 4 :=
    lt_of_le_of_lt htauC (one_div_lt_one_div_of_lt (by norm_num) hC)
  have hsigma : 0 ≤ sigmaSq := by
    obtain ⟨z, hz, hi, he⟩ := hS.solutionMoment
    rw [← he]
    exact integral_nonneg (fun i => sq_nonneg _)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hgconv : ConvexOn ℝ Set.univ (Core.regularizer I) := by
    refine ⟨convex_univ, fun u hu z hz a b ha hb hab => ?_⟩
    change (∑ j, I.regularizers j (a • u + b • z)) ≤
      a * (∑ j, I.regularizers j u) + b * (∑ j, I.regularizers j z)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [smul_eq_mul] using (hS.regularizerConvex j).2 hu hz ha hb hab
  have hhconv : ConvexOn ℝ Set.univ (Core.objective I) :=
    (LongTails.Proofs.RipmSmoothGeometry.mean_convex I L Lg xs sigmaSq hS).add hgconv
  have hA (t : ℕ) (ht : t ≤ T) := LongTails.Proofs.RipmRegularity.anchor_regular
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples T t mu hmu.le hmu1 ht
  have hl := LongTails.Proofs.RipmLastIterate.last_iterate_nonnegative P (Core.objective I)
    (Core.trajectory I tau x0 i j) x0 xs T tau mu v hT htau hmu.le hmu1 hv
    hhconv hS.minimizer (Filter.Eventually.of_forall (fun omega => rfl))
    (fun t ht => LongTails.Proofs.RipmRegularity.trajectory_measurable
      I L Lg tau x0 xs sigmaSq i j hS htau hSamples.1.measurable
        (fun k => (hSamples.2 k).1) t)
    (fun t ht => LongTails.Proofs.RipmRegularity.objective_integrable
      I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t)
    (fun t ht => (hA t ht).2.1)
    (fun t ht => ⟨(hA t ht).2.2.1, (hA t ht).2.2.2⟩)
    (fun t ht => by
      have hd := LongTails.Proofs.RipmDescent.descent I P L Lg tau x0 xs sigmaSq i j
        hS htau hSamples t (Core.anchor T mu xs (Core.trajectory I tau x0 i j) t)
        (hA t ht).1 hstep gamma hgamma (hA t ht).2.1
        (hA t ht).2.2.1 (hA t ht).2.2.2
      simpa only [mu, v, div_eq_mul_inv, one_mul, mul_comm, add_assoc] using hd)
  apply scalar_general T m C L Lg (‖x0 - xs‖ ^ 2)
    (Core.objective I x0 - Core.objective I xs) sigmaSq _ hT hC hL
    hS.regularizerNonneg (sq_nonneg _)
    (sub_nonneg.mpr (hS.minimizer (Set.mem_univ x0))) hsigma
  have hw := LongTails.Proofs.RipmWeights.weight_positive T T mu hmu.le le_rfl
  change (∫ omega, Core.objective I (Core.trajectory I tau x0 i j (T + 1) omega) -
      Core.objective I xs ∂P.toMeasure) ≤
    ‖x0 - xs‖ ^ 2 / (2 * tau * Core.weight T mu T) +
      (Core.objective I x0 - Core.objective I xs) / Core.weight T mu T +
      (v / Core.weight T mu T) * ∑ t ∈ Finset.range (T + 1), Core.weight T mu t
  calc
    _ ≤ (‖x0 - xs‖ ^ 2 / (2 * tau) +
        (Core.objective I x0 - Core.objective I xs) +
        v * ∑ t ∈ Finset.range (T + 1), Core.weight T mu t) / Core.weight T mu T := by
      apply (le_div_iff₀ hw).mpr
      nlinarith [hl]
    _ = _ := by
      field_simp [hw.ne', htau.ne']


lemma theorem41 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (T : ℕ) (hT : 1 ≤ T)
    (hSamples : Core.Sampling I P (1 / (5 * L * Real.sqrt T)) x0 i j) :
    (∫ omega, Core.objective I (LongTails.Algorithms.RipmOutput.lastIterate I (1 / (5 * L * Real.sqrt T)) x0 i j T omega) - Core.objective I xs ∂P.toMeasure) ≤
      targetBound T m L Lg (Core.distanceSq I x0)
        (Core.objective I x0 - Core.objective I xs) sigmaSq := by
  obtain ⟨hne, hclosed, y, hy, hdist⟩ :=
    LongTails.Proofs.RipmSmoothGeometry.nearest_minimizer I L Lg xs sigmaSq hS x0
  have hSy : Core.SourceAssumptions I L Lg y sigmaSq := { hS with minimizer := hy }
  have hval : Core.objective I y = Core.objective I xs :=
    le_antisymm (hy (Set.mem_univ xs)) (hS.minimizer (Set.mem_univ y))
  have hraw := general_rate I P L Lg x0 y sigmaSq i j hSy T hT 5 (by norm_num) hSamples
  rw [hval, hdist] at hraw
  have hsigma : 0 ≤ sigmaSq := by
    obtain ⟨z, hz, hi, he⟩ := hS.solutionMoment
    rw [← he]
    exact integral_nonneg (fun i => sq_nonneg _)
  exact scalar_five T m L Lg (Core.distanceSq I x0)
    (Core.objective I x0 - Core.objective I xs) sigmaSq _ hT hS.smoothPos
    hS.regularizerNonneg (sq_nonneg _)
    (sub_nonneg.mpr (hS.minimizer (Set.mem_univ x0))) hsigma hraw


end

end LongTails.Proofs.RipmRates
