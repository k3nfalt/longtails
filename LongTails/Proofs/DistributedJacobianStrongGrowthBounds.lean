import LongTails.Proofs.DistributedJacobianStrongGrowthProcess
import LongTails.Proofs.SymmetricReverseFisherGeometry

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthBounds

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientProcess

lemma refineRun_step_bound (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (s T : ℕ) {r : ℝ} (hr : 0 < r)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T ≤ (p.n : ℝ))
    (hguard : p.M * r ≤ p.L /
      (16 * (p.L / p.μ) * p.ρ * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T))
    (width : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (hrange : 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T ≤
      spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (center : Point p) (hcR : ‖center - p.x0‖ ≤ p.R)
    (hcenter : ‖center - I.solution‖ ≤ 3 * r / 8) (k : ℕ) :
    let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
    let c := (T : ℝ) / (64 * (p.L / p.μ))
    let output := fun j ω => refineRun p s T H width spacing r g center (fun t => S.sample t ω) j
    Integrable (fun ω => ‖output (k + 1) ω - I.solution‖ ^ 2) (S.law : Measure S.Seed) ∧
      (∫ ω, ‖output (k + 1) ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)) ≤
        (1 - c / 2) * (∫ ω, ‖output k ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)) +
          (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2 := by
  classical
  let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
  let N := p.n * (s + 2 * T * k)
  let default : p.Ω := Classical.choice (nonempty_of_isProbabilityMeasure (S.marginal : Measure p.Ω))
  let extend : (Fin N → p.Ω) → ℕ → p.Ω :=
    fun z j => if hj : j < N then z ⟨j, hj⟩ else default
  have hExt : Measurable extend := by
    apply Measurable.of_eval
    intro j
    by_cases hj : j < N
    · simpa only [extend, dite_eq_left hj] using (measurable_pi_apply (⟨j, hj⟩ : Fin N))
    · simpa only [extend, dite_eq_right hj] using
        (measurable_const : Measurable (fun _ : Fin N → p.Ω => default))
  let current : (Fin N → p.Ω) → Point p :=
    fun z => refineRun p s T H width spacing r g center (extend z) k
  have hx : Measurable current := by
    convert! (DistributedJacobianStrongGrowthProcess.measurable_refineRun
      p s T H width spacing r g hg.1 k).comp (measurable_const.prodMk hExt) using 1
  have hR : 0 ≤ p.R := le_of_lt hp.2.2.2.2.2.2.2.2.2.2.1
  have hlocal (z : Fin N → p.Ω) (_ : z ∈ Set.univ) : ‖current z - I.solution‖ ≤ r :=
    DistributedJacobianStrongGrowthProcess.refineRun_local
      p s T H width spacing r g center I.solution (extend z) k hR hr.le hcR hcenter
  have hanchor (z : Fin N → p.Ω) (_ : z ∈ Set.univ) : ‖I.solution - center‖ ≤ r / 2 := by
    rw [norm_sub_rev]
    linarith
  have hb := DistributedJacobianStrongGrowthRoundedHistory.history_projected_block_contraction
    p hp I hI g S hg T N hr hT hTκ hn hguard width spacing hs hrange
    current (fun _ => center) hx measurable_const Set.univ MeasurableSet.univ hlocal hanchor
  have he (ω : S.Seed) : current (fun i : Fin N => S.sample i.val ω) =
      refineRun p s T H width spacing r g center (fun j => S.sample j ω) k := by
    apply DistributedJacobianStrongGrowthProcess.refineRun_prefix
    intro j hj
    have hj' : j < N := hj
    simp only [extend, dite_eq_left hj']
  simp only [Set.preimage_univ, Set.indicator_univ] at hb
  simp_rw [he] at hb
  exact hb

lemma affine_recursion_bound (u : ℕ → ℝ) {q b : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 ≤ b)
    (hstep : ∀ k, u (k + 1) ≤ q * u k + b) (k : ℕ) :
    u k ≤ q ^ k * u 0 + b / (1 - q) := by
  let D := b / (1 - q)
  have hD : 0 ≤ D := div_nonneg hb (by linarith)
  have he : D * (1 - q) = b := div_mul_cancel₀ _ (by linarith)
  have hs (j : ℕ) : u (j + 1) - D ≤ q * (u j - D) := by
    nlinarith [hstep j]
  have hh := SymmetricReverseFisherGeometry.geometric_recurrence (fun j => u j - D) hq hs k
  nlinarith [mul_nonneg (pow_nonneg hq k) hD]

lemma refineRun_bound (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (s T : ℕ) {r : ℝ} (hr : 0 < r)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T ≤ (p.n : ℝ))
    (hguard : p.M * r ≤ p.L /
      (16 * (p.L / p.μ) * p.ρ * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T))
    (width : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (hrange : 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T ≤
      spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (center : Point p) (hcR : ‖center - p.x0‖ ≤ p.R)
    (hcenter : ‖center - I.solution‖ ≤ 3 * r / 8) (k : ℕ) :
    let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
    let c := (T : ℝ) / (64 * (p.L / p.μ))
    let output := fun j ω => refineRun p s T H width spacing r g center (fun t => S.sample t ω) j
    Integrable (fun ω => ‖output k ω - I.solution‖ ^ 2) (S.law : Measure S.Seed) ∧
      (∫ ω, ‖output k ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)) ≤
        (1 - c / 2) ^ k * ‖center - I.solution‖ ^ 2 +
          (2 / c) * (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2 := by
  let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
  let c := (T : ℝ) / (64 * (p.L / p.μ))
  let output := fun j ω => refineRun p s T H width spacing r g center (fun t => S.sample t ω) j
  let u := fun j => ∫ ω, ‖output j ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)
  have hmup : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hL : 0 < p.L := lt_of_lt_of_le hmup hp.2.2.2.2.2.2.2.1
  have hκ : 0 < p.L / p.μ := div_pos hL hmup
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 64 * (p.L / p.μ))).mpr
    nlinarith
  have hb (j : ℕ) := refineRun_step_bound p hp I hI g S hg s T hr hT hTκ hn hguard
    width spacing hs hrange center hcR hcenter j
  have hstep (j : ℕ) : u (j + 1) ≤ (1 - c / 2) * u j +
      (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2 := (hb j).2
  have hu0 : u 0 = ‖center - I.solution‖ ^ 2 := by simp [u, output, refineRun]
  have hbound := affine_recursion_bound u (by linarith : 0 ≤ 1 - c / 2)
    (by linarith : 1 - c / 2 < 1) (by positivity) hstep k
  refine ⟨?_, ?_⟩
  · cases k with
    | zero => simp [refineRun]
    | succ j => exact (hb j).1
  · change u k ≤ (1 - c / 2) ^ k * ‖center - I.solution‖ ^ 2 +
        (2 / c) * (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2
    rw [hu0] at hbound
    calc
      _ ≤ _ := hbound
      _ = _ := by
        congr 1
        field_simp [hc.ne']
        ring

end LongTails.Proofs.DistributedJacobianStrongGrowthBounds
