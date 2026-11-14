import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Intervals

open MeasureTheory
open scoped BigOperators
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmLastIterate

noncomputable section

lemma last_iterate_positive
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (h : Core.Vec d → ℝ) (x : ℕ → Ω → Core.Vec d) (x0 xs : Core.Vec d)
    (T : ℕ) (tau mu v : ℝ) (hT : 1 ≤ T) (htau : 0 < tau)
    (hmu : 0 ≤ mu) (hmu1 : mu < 1) (hv : 0 < v)
    (hconvex : ConvexOn ℝ Set.univ h) (hmin : IsMinOn h Set.univ xs)
    (hx0 : ∀ᵐ omega ∂(P : Measure Ω), x 0 omega = x0)
    (hxmeas : ∀ t, t ≤ T + 1 → Measurable (x t))
    (hxint : ∀ t, t ≤ T + 1 → Integrable (fun omega => h (x t omega)) (P : Measure Ω))
    (hzint : ∀ t, t ≤ T →
      Integrable (fun omega => h (Core.anchor T mu xs x t omega)) (P : Measure Ω))
    (hdist : ∀ t, t ≤ T →
      Integrable (fun omega => ‖x t omega - Core.anchor T mu xs x t omega‖ ^ 2)
        (P : Measure Ω) ∧
      Integrable (fun omega => ‖x (t + 1) omega - Core.anchor T mu xs x t omega‖ ^ 2)
        (P : Measure Ω))
    (hstep : ∀ t, t ≤ T →
      (∫ omega, h (x (t + 1) omega) - h (Core.anchor T mu xs x t omega) -
          mu * h (x t omega) + mu * h xs ∂(P : Measure Ω)) ≤
        (∫ omega, ‖x t omega - Core.anchor T mu xs x t omega‖ ^ 2 -
          ‖x (t + 1) omega - Core.anchor T mu xs x t omega‖ ^ 2 ∂(P : Measure Ω)) /
            (2 * tau) + v) :
    Core.weight T mu T * (∫ omega, h (x (T + 1) omega) - h xs ∂(P : Measure Ω)) ≤
      ‖x0 - xs‖ ^ 2 / (2 * tau) + (h x0 - h xs) +
        v * ∑ t ∈ Finset.range (T + 1), Core.weight T mu t := by
  let a : ℕ → ℝ := Core.weight T mu
  let p : ℕ → ℝ := Core.mixing T mu
  let z : ℕ → Ω → Core.Vec d := Core.anchor T mu xs x
  let R : ℕ → ℝ := fun t => (∫ omega, h (x t omega) ∂P.toMeasure) - h xs
  let Z : ℕ → ℝ := fun t => (∫ omega, h (z t omega) ∂P.toMeasure) - h xs
  let D : ℕ → ℝ := fun t => ∫ omega, ‖x t omega - z t omega‖ ^ 2 ∂P.toMeasure
  let E : ℕ → ℝ := fun t => ∫ omega, ‖x (t + 1) omega - z t omega‖ ^ 2 ∂P.toMeasure
  let Y : ℕ → ℝ := fun t => a t * R (t + 1) + ((T - t : ℕ) : ℝ) * a t * Z t +
    (a t * E t) / (2 * tau)
  have ha0 : a 0 = 1 := rfl
  have ha : ∀ t : ℕ, t ≤ T → 0 < a t := by
    intro t
    induction t with
    | zero =>
        intro ht
        change (0 : ℝ) < 1
        norm_num
    | succ k ih =>
        intro hk
        have hsub : 0 < ((T - k : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < T - k by omega)
        change 0 < a k * ((T - k : ℕ) + 1) / ((T - k : ℕ) + mu)
        exact div_pos (mul_pos (ih (by omega)) (by positivity))
          (add_pos_of_pos_of_nonneg hsub hmu)
  have hcoef : ∀ k : ℕ, k + 1 ≤ T →
      0 ≤ p (k + 1) ∧ p (k + 1) ≤ 1 ∧ a (k + 1) * p (k + 1) = a k ∧
      (((T - (k + 1) : ℕ) : ℝ) + 1) * (a (k + 1) - a k) + mu * a (k + 1) = a k := by
    intro k hk
    let n : ℕ := T - (k + 1)
    have hsub : T - k = n + 1 := by dsimp [n]; omega
    have hp : p (k + 1) = ((n : ℝ) + 1 + mu) / ((n : ℝ) + 2) := by
      change Core.mixing T mu (k + 1) = _
      delta Core.mixing
      rw [ite_eq_right (show k + 1 ≠ 0 by omega)]
    have hnum : 0 < (n : ℝ) + 1 + mu := by positivity
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hp0 : 0 ≤ p (k + 1) := by rw [hp]; exact (div_pos hnum hden).le
    have hp1 : p (k + 1) ≤ 1 := by rw [hp, div_le_iff₀ hden]; linarith
    have hw : a (k + 1) = a k * ((n : ℝ) + 2) / ((n : ℝ) + 1 + mu) := by
      change a k * ((T - k : ℕ) + 1) / ((T - k : ℕ) + mu) = _
      rw [hsub]
      push_cast
      ring
    have heq : a (k + 1) * p (k + 1) = a k := by
      rw [hw, hp]
      field_simp [hnum.ne', hden.ne']
    have hcross : a (k + 1) * ((n : ℝ) + 1 + mu) = a k * ((n : ℝ) + 2) := by
      rw [hw]
      field_simp [hnum.ne']
    refine ⟨hp0, hp1, heq, ?_⟩
    change ((n : ℝ) + 1) * (a (k + 1) - a k) + mu * a (k + 1) = a k
    nlinarith only [hcross]
  have hconst : Integrable (fun _ : Ω => h xs) P.toMeasure := integrable_const _
  have hconstval : (∫ _omega : Ω, h xs ∂P.toMeasure) = h xs := by simp
  have hstep' : ∀ t : ℕ, t ≤ T →
      R (t + 1) - Z t - mu * R t ≤ (D t - E t) / (2 * tau) + v := by
    intro t ht
    have hn := hxint (t + 1) (by omega)
    have hc := hxint t (by omega)
    have hz := hzint t ht
    have hm := hc.const_mul mu
    have hcm : Integrable (fun _ : Ω => mu * h xs) P.toMeasure := integrable_const _
    have hcmval : (∫ _omega : Ω, mu * h xs ∂P.toMeasure) = mu * h xs := by simp
    have hs := hstep t ht
    have hadd := integral_add ((hn.sub hz).sub hm) hcm
    have hsub1 := integral_sub (hn.sub hz) hm
    have hsub2 := integral_sub hn hz
    simp only [Pi.sub_apply] at hadd hsub1
    rw [hadd, hsub1, hsub2, integral_const_mul, hcmval,
      integral_sub (hdist t ht).1 (hdist t ht).2] at hs
    dsimp only [R, Z, D, E, z]
    nlinarith only [hs]
  have hR0 : R 0 = h x0 - h xs := by
    have hi : (∫ omega, h (x 0 omega) ∂P.toMeasure) = h x0 := by
      calc
        (∫ omega, h (x 0 omega) ∂P.toMeasure) = ∫ _omega : Ω, h x0 ∂P.toMeasure :=
          integral_congr_ae (hx0.mono fun omega heq => congrArg h heq)
        _ = h x0 := by simp
    exact congrArg (fun b : ℝ => b - h xs) hi
  have hZ0 : Z 0 = 0 := by
    change (∫ _omega : Ω, h xs ∂P.toMeasure) - h xs = 0
    rw [hconstval]
    ring
  have hD0 : D 0 = ‖x0 - xs‖ ^ 2 := by
    calc
      D 0 = ∫ _omega : Ω, ‖x0 - xs‖ ^ 2 ∂P.toMeasure := by
        apply integral_congr_ae
        filter_upwards [hx0] with omega heq
        change ‖x 0 omega - xs‖ ^ 2 = ‖x0 - xs‖ ^ 2
        rw [heq]
      _ = ‖x0 - xs‖ ^ 2 := by simp
  have hR0nonneg : 0 ≤ R 0 := by
    rw [hR0]
    exact sub_nonneg.mpr (hmin (Set.mem_univ x0))
  have hbase : Y 0 ≤ D 0 / (2 * tau) + R 0 + v := by
    have hs := hstep' 0 (Nat.zero_le T)
    have hm := mul_le_mul_of_nonneg_right hmu1.le hR0nonneg
    rw [hZ0, sub_div] at hs
    dsimp only [Y]
    rw [ha0, hZ0]
    simp only [one_mul, mul_zero, add_zero]
    nlinarith only [hs, hm]
  have hYstep : ∀ k : ℕ, k + 1 ≤ T → Y (k + 1) ≤ Y k + a (k + 1) * v := by
    intro k hk
    have hk0 : k ≤ T := by omega
    rcases hcoef k hk with ⟨hp0, hp1, heq, hid⟩
    have hJ : a (k + 1) * Z (k + 1) ≤
        (a (k + 1) - a k) * R (k + 1) + a k * Z k := by
      have hcpoint : ∀ omega,
          h (z (k + 1) omega) ≤
            (1 - p (k + 1)) * h (x (k + 1) omega) + p (k + 1) * h (z k omega) := by
        intro omega
        have hc := hconvex.2 (Set.mem_univ (x (k + 1) omega))
          (Set.mem_univ (z k omega)) (sub_nonneg.mpr hp1) hp0
          (show (1 - p (k + 1)) + p (k + 1) = 1 by ring)
        change h ((1 - p (k + 1)) • x (k + 1) omega + p (k + 1) • z k omega) ≤ _
        simpa only [smul_eq_mul] using hc
      have hi1 := (hxint (k + 1) (by omega)).const_mul (1 - p (k + 1))
      have hi2 := (hzint k hk0).const_mul (p (k + 1))
      have hci := integral_mono (hzint (k + 1) hk) (hi1.add hi2) hcpoint
      simp only [Pi.add_apply] at hci
      rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at hci
      have hcenter : Z (k + 1) ≤ (1 - p (k + 1)) * R (k + 1) + p (k + 1) * Z k := by
        dsimp only [R, Z]
        nlinarith only [hci]
      calc
        a (k + 1) * Z (k + 1) ≤
            a (k + 1) * ((1 - p (k + 1)) * R (k + 1) + p (k + 1) * Z k) :=
          mul_le_mul_of_nonneg_left hcenter (ha (k + 1) hk).le
        _ = (a (k + 1) - a (k + 1) * p (k + 1)) * R (k + 1) +
            (a (k + 1) * p (k + 1)) * Z k := by ring
        _ = (a (k + 1) - a k) * R (k + 1) + a k * Z k := by rw [heq]
    have hD : a (k + 1) * D (k + 1) ≤ a k * E k := by
      have hpnt : ∀ omega,
          a (k + 1) * ‖x (k + 1) omega - z (k + 1) omega‖ ^ 2 ≤
            a k * ‖x (k + 1) omega - z k omega‖ ^ 2 := by
        intro omega
        have hvect : x (k + 1) omega - z (k + 1) omega =
            p (k + 1) • (x (k + 1) omega - z k omega) := by
          change x (k + 1) omega -
            ((1 - p (k + 1)) • x (k + 1) omega + p (k + 1) • z k omega) = _
          module
        rw [hvect, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0, mul_pow]
        calc
          a (k + 1) * (p (k + 1) ^ 2 * ‖x (k + 1) omega - z k omega‖ ^ 2) =
              (a (k + 1) * p (k + 1)) * p (k + 1) *
                ‖x (k + 1) omega - z k omega‖ ^ 2 := by ring
          _ = p (k + 1) * (a k * ‖x (k + 1) omega - z k omega‖ ^ 2) := by rw [heq]; ring
          _ ≤ 1 * (a k * ‖x (k + 1) omega - z k omega‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hp1 (mul_nonneg (ha k hk0).le (sq_nonneg _))
          _ = a k * ‖x (k + 1) omega - z k omega‖ ^ 2 := one_mul _
      have hi := integral_mono ((hdist (k + 1) hk).1.const_mul (a (k + 1)))
        ((hdist k hk0).2.const_mul (a k)) hpnt
      rw [integral_const_mul, integral_const_mul] at hi
      exact hi
    have hs := mul_le_mul_of_nonneg_left (hstep' (k + 1) hk) (ha (k + 1) hk).le
    have hj := mul_le_mul_of_nonneg_left hJ
      (show 0 ≤ (((T - (k + 1) : ℕ) : ℝ) + 1) by positivity)
    have hd := div_le_div_of_nonneg_right hD (show 0 ≤ 2 * tau by positivity)
    have hidentity := congrArg (fun b : ℝ => b * R (k + 1)) hid
    have hidx : ((T - k : ℕ) : ℝ) = ((T - (k + 1) : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show T - k = (T - (k + 1)) + 1 by omega)
    dsimp only [Y]
    rw [hidx]
    simp only [sub_div, mul_div_assoc] at hs hd ⊢
    nlinarith only [hs, hj, hd, hidentity]
  have htotal : ∀ t : ℕ, t ≤ T →
      Y t / v ≤ (D 0 / (2 * tau) + R 0) / v + ∑ k ∈ Finset.range (t + 1), a k := by
    intro t
    induction t with
    | zero =>
        intro ht
        have h := div_le_div_of_nonneg_right hbase hv.le
        simpa only [add_div, div_self hv.ne', Nat.zero_add, Finset.sum_range_one, ha0] using h
    | succ k ih =>
        intro hk
        have hi := ih (show k ≤ T by omega)
        have hs := div_le_div_of_nonneg_right (hYstep k hk) hv.le
        simp only [add_div, mul_div_cancel_right₀ _ hv.ne'] at hs
        rw [Finset.sum_range_succ]
        linarith
  have hzmeas : ∀ k : ℕ, k ≤ T → Measurable (z k) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact measurable_const
    | succ k ih =>
        intro hk
        change Measurable (fun omega =>
          (1 - p (k + 1)) • x (k + 1) omega + p (k + 1) • z k omega)
        exact Measurable.fun_add
          ((measurable_const_smul (1 - p (k + 1))).comp (hxmeas (k + 1) (by omega)))
          ((measurable_const_smul (p (k + 1))).comp (ih (by omega)))
  have hE : 0 ≤ E T := by
    have hmeas : Measurable (fun omega => ‖x (T + 1) omega - z T omega‖ ^ 2) := by
      simpa only [Pi.sub_apply] using
        ((hxmeas (T + 1) le_rfl).sub (hzmeas T le_rfl)).norm.pow_const 2
    change 0 ≤ ∫ omega, ‖x (T + 1) omega - z T omega‖ ^ 2 ∂P.toMeasure
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun omega => sq_nonneg _)) hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_nonneg
  have hterminal : a T * R (T + 1) ≤ Y T := by
    dsimp only [Y]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (ha T (le_refl T)).le hE)
      (by positivity))
  have hprev := htotal (T - 1) (by omega)
  have hlast := div_le_div_of_nonneg_right (hYstep (T - 1) (by omega)) hv.le
  rw [Nat.sub_add_cancel hT] at hprev hlast
  simp only [add_div, mul_div_cancel_right₀ _ hv.ne'] at hlast
  have hend : Y T / v ≤ (D 0 / (2 * tau) + R 0) / v +
      ∑ k ∈ Finset.range (T + 1), a k := by
    rw [Finset.sum_range_succ]
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hend hv.le
  simp only [div_mul_cancel₀ _ hv.ne', add_mul] at hscaled
  have hfinal : a T * R (T + 1) ≤ D 0 / (2 * tau) + R 0 +
      v * ∑ k ∈ Finset.range (T + 1), a k := by
    nlinarith only [hterminal, hscaled]
  rw [hD0, hR0] at hfinal
  have hgap : (∫ omega, h (x (T + 1) omega) - h xs ∂P.toMeasure) = R (T + 1) := by
    rw [integral_sub (hxint (T + 1) (le_refl (T + 1))) hconst, hconstval]
  rw [hgap]
  exact hfinal

lemma last_iterate_nonnegative
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (h : Core.Vec d → ℝ) (x : ℕ → Ω → Core.Vec d) (x0 xs : Core.Vec d)
    (T : ℕ) (tau mu v : ℝ) (hT : 1 ≤ T) (htau : 0 < tau)
    (hmu : 0 ≤ mu) (hmu1 : mu < 1) (hv : 0 ≤ v)
    (hconvex : ConvexOn ℝ Set.univ h) (hmin : IsMinOn h Set.univ xs)
    (hx0 : ∀ᵐ omega ∂(P : Measure Ω), x 0 omega = x0)
    (hxmeas : ∀ t, t ≤ T + 1 → Measurable (x t))
    (hxint : ∀ t, t ≤ T + 1 → Integrable (fun omega => h (x t omega)) (P : Measure Ω))
    (hzint : ∀ t, t ≤ T →
      Integrable (fun omega => h (Core.anchor T mu xs x t omega)) (P : Measure Ω))
    (hdist : ∀ t, t ≤ T →
      Integrable (fun omega => ‖x t omega - Core.anchor T mu xs x t omega‖ ^ 2)
        (P : Measure Ω) ∧
      Integrable (fun omega => ‖x (t + 1) omega - Core.anchor T mu xs x t omega‖ ^ 2)
        (P : Measure Ω))
    (hstep : ∀ t, t ≤ T →
      (∫ omega, h (x (t + 1) omega) - h (Core.anchor T mu xs x t omega) -
          mu * h (x t omega) + mu * h xs ∂(P : Measure Ω)) ≤
        (∫ omega, ‖x t omega - Core.anchor T mu xs x t omega‖ ^ 2 -
          ‖x (t + 1) omega - Core.anchor T mu xs x t omega‖ ^ 2 ∂(P : Measure Ω)) /
            (2 * tau) + v) :
    Core.weight T mu T * (∫ omega, h (x (T + 1) omega) - h xs ∂(P : Measure Ω)) ≤
      ‖x0 - xs‖ ^ 2 / (2 * tau) + (h x0 - h xs) +
        v * ∑ t ∈ Finset.range (T + 1), Core.weight T mu t := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let S : ℝ := ∑ t ∈ Finset.range (T + 1), Core.weight T mu t
  let delta : ℝ := epsilon / (|S| + 1)
  have hden : 0 < |S| + 1 := by positivity
  have hdelta : 0 < delta := div_pos hepsilon hden
  have hnew := last_iterate_positive P h x x0 xs T tau mu (v + delta)
    hT htau hmu hmu1 (add_pos_of_nonneg_of_pos hv hdelta)
    hconvex hmin hx0 hxmeas hxint hzint hdist
    (fun t ht => (hstep t ht).trans (by linarith only [hdelta]))
  have hS : S ≤ |S| + 1 := by linarith only [le_abs_self S]
  have hperturb : delta * S ≤ epsilon := by
    calc
      delta * S ≤ delta * (|S| + 1) := mul_le_mul_of_nonneg_left hS hdelta.le
      _ = epsilon := div_mul_cancel₀ epsilon hden.ne'
  dsimp only [S] at hperturb
  nlinarith only [hnew, hperturb]

end

end LongTails.Proofs.RipmLastIterate
