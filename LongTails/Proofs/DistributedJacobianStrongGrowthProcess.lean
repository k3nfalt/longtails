import LongTails.Algorithms.DistributedLocalExtragradientProcess
import LongTails.Proofs.DistributedJacobianStrongGrowthRoundedHistory

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthProcess

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientProcess

lemma measurable_projectedBlockOutput (p : Params) (T N : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (fun z : (Point p × Point p) × (ℕ → p.Ω) =>
      projectedBlockOutput p T N H width spacing z.1.1 r g z.1.2 z.2) := by
  have hinput : Measurable (fun z : (Point p × Point p) × (ℕ → p.Ω) => (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm := (DistributedJacobianStrongGrowthRounding.measurable_roundedBlockOutput
    p T N H width spacing g hg).comp hinput
  have hpair := (show Measurable (fun z : (Point p × Point p) × (ℕ → p.Ω) => z.1.1) from
    measurable_fst.comp measurable_fst).prodMk hm
  convert! (DistributedJacobianStrongGrowthProjection.measurable_localizedOutput p r).comp hpair using 1


lemma measurable_refineRun (p : Params) (s T : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (fun z : Point p × (ℕ → p.Ω) =>
      refineRun p s T H width spacing r g z.1 z.2 k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      change Measurable (fun z : Point p × (ℕ → p.Ω) =>
        projectedBlockOutput p T (p.n * (s + 2 * T * k)) H width spacing z.1 r g
          (refineRun p s T H width spacing r g z.1 z.2 k) z.2)
      have hinput := (show Measurable (fun z : Point p × (ℕ → p.Ω) => z.1) from
        measurable_fst).prodMk ih
      convert! (measurable_projectedBlockOutput p T (p.n * (s + 2 * T * k)) H width spacing r g hg).comp
        (hinput.prodMk measurable_snd) using 1

lemma roundedBlockOutput_prefix (p : Params) (T N : ℕ) (H : ℝ)
    (width : ℕ) (spacing : ℝ) (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p)
    (samples other : ℕ → p.Ω)
    (heq : ∀ j < N + p.n * (2 * T), samples j = other j) :
    roundedBlockOutput p T N H width spacing g x samples =
      roundedBlockOutput p T N H width spacing g x other := by
  have he (i : Fin p.n) :
      LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
        (fun k => samples (N + (p.n * k + i.val))) T =
      LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
        (fun k => other (N + (p.n * k + i.val))) T := by
    apply LocalNonlinearExtragradientSampling.run_prefix
    intro k hk
    apply heq
    apply Nat.add_lt_add_left
    calc
      p.n * k + i.val < p.n * k + p.n := Nat.add_lt_add_left i.isLt _
      _ = p.n * (k + 1) := by ring
      _ ≤ p.n * (2 * T) := Nat.mul_le_mul_left _ (by omega)
  simp only [roundedBlockOutput]
  simp_rw [he]

lemma refineRun_prefix (p : Params) (s T : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (center : Point p) (samples other : ℕ → p.Ω) (k : ℕ)
    (heq : ∀ j < p.n * (s + 2 * T * k), samples j = other j) :
    refineRun p s T H width spacing r g center samples k =
      refineRun p s T H width spacing r g center other k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hcut : p.n * (s + 2 * T * (k + 1)) =
          p.n * (s + 2 * T * k) + p.n * (2 * T) := by ring
      have hpast := ih (fun j hj => heq j (by rw [hcut]; omega))
      simp only [refineRun, hpast, projectedBlockOutput]
      rw [roundedBlockOutput_prefix p T (p.n * (s + 2 * T * k)) H width spacing g _
        samples other (fun j hj => heq j (by rwa [hcut]))]

lemma refineRun_local (p : Params) (s T : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (center y : Point p) (samples : ℕ → p.Ω) (k : ℕ)
    (hR : 0 ≤ p.R) (hr : 0 ≤ r) (hc : ‖center - p.x0‖ ≤ p.R)
    (hcy : ‖center - y‖ ≤ 3 * r / 8) :
    ‖refineRun p s T H width spacing r g center samples k - y‖ ≤ r := by
  cases k with
  | zero => exact hcy.trans (by linarith)
  | succ k => exact DistributedJacobianStrongGrowthProjection.localized_root_bound p center _ y hR hr hc hcy

lemma refineRun_global (p : Params) (s T : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (center : Point p) (samples : ℕ → p.Ω) (k : ℕ)
    (hR : 0 ≤ p.R) (hc : ‖center - p.x0‖ ≤ p.R) :
    ‖refineRun p s T H width spacing r g center samples k - p.x0‖ ≤ p.R := by
  cases k with
  | zero => exact hc
  | succ k => exact DistributedJacobianStrongGrowthProjection.localized_mem_global p center _ hR

lemma refineRun_shift (p : Params) (s T : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (center : Point p) (samples : ℕ → p.Ω) (k : ℕ) :
    refineRun p s T H width spacing r g center samples k =
      refineRun p 0 T H width spacing r g center (fun j => samples (p.n * s + j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [refineRun, refineRun, ih]
      simp only [projectedBlockOutput, roundedBlockOutput, Nat.zero_add, Nat.mul_add, Nat.add_assoc]

lemma refineRun_global_root_bound (p : Params) (s T : ℕ) (H : ℝ)
    (width : ℕ) (spacing r : ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (center y : Point p) (samples : ℕ → p.Ω) (k : ℕ)
    (hR : 0 ≤ p.R) (hc : ‖center - p.x0‖ ≤ p.R) (hy : ‖p.x0 - y‖ ≤ p.R) :
    ‖refineRun p s T H width spacing r g center samples k - y‖ ≤ 2 * p.R := by
  have ht := dist_triangle (refineRun p s T H width spacing r g center samples k) p.x0 y
  simp only [dist_eq_norm] at ht
  linarith [refineRun_global p s T H width spacing r g center samples k hR hc]

end LongTails.Proofs.DistributedJacobianStrongGrowthProcess
