import LongTails.Proofs.BirchAveragingExecution

open MeasureTheory

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

/-- Success in the original standalone setup for zero-variance worker oracles.
The algorithm is public and uses exactly K R calls per worker. -/
theorem correctedAveraging_successful {workers K R : ℕ} (p : Params workers)
    (hp : Valid p) (hK : 0 < K) (hR : 0 < R) (η : ℝ) (hη : 0 < η)
    (hσ : ∀ i, p.σ i = 0) (hδ : 0 < p.δ)
    (hmode : p.similarity = .secondOrder ∨ p.similarity = .firstAndSecondOrder)
    (hstep : η * p.L ≤ 1 / 4)
    (hh : η * p.L * (K : ℝ) ≤ Real.log (1 + p.L / p.δ) / 8)
    (haccuracy : 2 * p.Δ / (η * (K : ℝ) * (R : ℝ)) ≤ p.ε)
    (I : Instance workers p.d) (O : Oracle (Point p.d) (Point p.d) workers)
    (ho : Admissible p I O) :
    let A := correctedAveraging workers p.d K R hp.1 hK hR p.x0 η
    (spec workers).successful p I
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K * R) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases ho with ⟨hobj, Ω, m, horacle⟩
  let := m
  rcases horacle with ⟨μ, P, g, hiid, hg, rfl⟩
  rcases hobj with ⟨hf, hs, hlower, hgap, hsim⟩
  have hsecond : SecondOrderSimilarity I p.δ := by
    rcases hmode with hmode | hmode
    · simpa only [hmode, Similarity.Holds] using hsim
    · exact (show FirstOrderSimilarity I p.ζ ∧ SecondOrderSimilarity I p.δ by
        simpa only [hmode, Similarity.Holds] using hsim).2
  have hd := gradientDifferenceSimilarity_of_secondOrderSimilarity hsecond
  have hg0 (i : Fin workers) :
      LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
        (μ : Measure Ω) (I.localObjective i) (g i) 0 := by
    simpa only [hσ i] using hg i
  have hm := measurable_correctedAveraging_execute hp.1 hK hR p.x0 η P g
    (fun i => (hg i).measurable)
  have hout := correctedAveraging_output_moments hp.1 hK hR I hf g hiid hg0 p.x0 η
  have hb := referencePoint_average_bound hp.1 hK hR hη hp.2.2.1 hδ hs hd p.x0
    hstep hh hlower hgap
  have hacc := hout.2.le.trans (hb.trans haccuracy)
  set_option backward.isDefEq.respectTransparency false in
    exact ⟨hm, hout.1, hacc⟩

end LongTails.Setups.BirchNonIID

open MeasureTheory

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

theorem rounded_round_accuracy {η ε Δ : ℝ} {K : ℕ}
    (hη : 0 < η) (hε : 0 < ε) (hK : 0 < K) :
    2 * Δ / (η * (K : ℝ) * (max 1 ⌈2 * Δ / (η * (K : ℝ) * ε)⌉₊ : ℕ)) ≤ ε := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hR : 0 < max 1 ⌈2 * Δ / (η * (K : ℝ) * ε)⌉₊ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hR' : (0 : ℝ) < (max 1 ⌈2 * Δ / (η * (K : ℝ) * ε)⌉₊ : ℕ) := by exact_mod_cast hR
  have hr : 2 * Δ / (η * (K : ℝ) * ε) ≤ (max 1 ⌈2 * Δ / (η * (K : ℝ) * ε)⌉₊ : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈2 * Δ / (η * (K : ℝ) * ε)⌉₊)
  have hb := (div_le_iff₀ (show 0 < η * (K : ℝ) * ε by positivity)).mp hr
  apply (div_le_iff₀ (show 0 < η * (K : ℝ) *
    (max 1 ⌈2 * Δ / (η * (K : ℝ) * ε)⌉₊ : ℕ) by positivity)).mpr
  nlinarith

/-- Explicit finite budget for logarithmically safe deterministic corrected averaging.
The call count is per worker; the setup and its admissible oracles are unchanged. -/
theorem logarithmic_correctedAveraging_complexity {workers K : ℕ} (p : Params workers)
    (hp : Valid p) (hK : 0 < K) (hσ : ∀ i, p.σ i = 0) (hδ : 0 < p.δ)
    (hmode : p.similarity = .secondOrder ∨ p.similarity = .firstAndSecondOrder) :
    let η := min (1 / (4 * p.L)) (Real.log (1 + p.L / p.δ) / (8 * p.L * (K : ℝ)))
    let R := max 1 ⌈2 * p.Δ / (η * (K : ℝ) * p.ε)⌉₊
    ∃ A : Algorithm (Point p.d) (Point p.d) (Point p.d) workers,
      ∀ I O, Admissible p I O →
        (spec workers).successful p I
          (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K * R) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let η := logarithmicStep p.L p.δ K
  let R := max 1 ⌈2 * p.Δ / (η * (K : ℝ) * p.ε)⌉₊
  have hR : 0 < R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hb := logarithmicStep_bounds hp.2.2.1 hδ hK
  refine ⟨correctedAveraging workers p.d K R hp.1 hK hR p.x0 η, ?_⟩
  intro I O ho
  exact correctedAveraging_successful p hp hK hR η hb.1 hσ hδ hmode hb.2.1 hb.2.2
    (rounded_round_accuracy hb.1 hp.2.2.2.2.1 hK) I O ho

end LongTails.Setups.BirchNonIID

open MeasureTheory

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

theorem nonnegative_div_min_mul {n a b c : ℝ} (hn : 0 ≤ n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    n / (min a b * c) = max (n / (a * c)) (n / (b * c)) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_left]
    exact div_le_div_of_nonneg_left hn (mul_pos ha hc) (mul_le_mul_of_nonneg_right hab hc.le)
  · rw [min_eq_right hba, max_eq_right]
    exact div_le_div_of_nonneg_left hn (mul_pos hb hc) (mul_le_mul_of_nonneg_right hba hc.le)

theorem logarithmic_round_ratio {L δ Δ ε : ℝ} {K : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hK : 0 < K) :
    2 * Δ / (logarithmicStep L δ K * (K : ℝ) * ε) =
      max (8 * L * Δ / ((K : ℝ) * ε))
        (16 * L * Δ / (ε * Real.log (1 + L / δ))) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : 0 < Real.log (1 + L / δ) := Real.log_pos (by linarith [div_pos hL hδ])
  unfold logarithmicStep
  rw [mul_assoc, nonnegative_div_min_mul (by positivity) (by positivity) (by positivity) (by positivity)]
  congr 1 <;> field_simp <;> ring

/-- Explicit per-worker oracle budget with the step size eliminated from the formula. -/
theorem logarithmic_public_budget {workers K : ℕ} (p : Params workers)
    (hp : Valid p) (hK : 0 < K) (hσ : ∀ i, p.σ i = 0) (hδ : 0 < p.δ)
    (hmode : p.similarity = .secondOrder ∨ p.similarity = .firstAndSecondOrder) :
    let R := max 1 ⌈max (8 * p.L * p.Δ / ((K : ℝ) * p.ε))
      (16 * p.L * p.Δ / (p.ε * Real.log (1 + p.L / p.δ)))⌉₊
    ∃ A : Algorithm (Point p.d) (Point p.d) (Point p.d) workers,
      ∀ I O, Admissible p I O →
        (spec workers).successful p I
          (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K * R) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have h := logarithmic_correctedAveraging_complexity p hp hK hσ hδ hmode
  dsimp only at h ⊢
  have he := logarithmic_round_ratio hp.2.2.1 hδ hp.2.2.2.2.2.1 hp.2.2.2.2.1 hK
  unfold logarithmicStep at he
  simp only [he] at h
  exact h

end LongTails.Setups.BirchNonIID

open MeasureTheory

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

/-- Method-specific public complexity theorem: the algorithm is explicitly corrected averaging. -/
theorem correctedAveraging_public_budget {workers K : ℕ} (p : Params workers)
    (hp : Valid p) (hK : 0 < K) (hσ : ∀ i, p.σ i = 0) (hδ : 0 < p.δ)
    (hmode : p.similarity = .secondOrder ∨ p.similarity = .firstAndSecondOrder)
    (I : Instance workers p.d) (O : Oracle (Point p.d) (Point p.d) workers)
    (ho : Admissible p I O) :
    let η := logarithmicStep p.L p.δ K
    let R := max 1 ⌈max (8 * p.L * p.Δ / ((K : ℝ) * p.ε))
      (16 * p.L * p.Δ / (p.ε * Real.log (1 + p.L / p.δ)))⌉₊
    let hR : 0 < R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    let A := correctedAveraging workers p.d K R hp.1 hK hR p.x0 η
    (spec workers).successful p I
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K * R) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let η := logarithmicStep p.L p.δ K
  let R := max 1 ⌈max (8 * p.L * p.Δ / ((K : ℝ) * p.ε))
    (16 * p.L * p.Δ / (p.ε * Real.log (1 + p.L / p.δ)))⌉₊
  have hR : 0 < R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hb := logarithmicStep_bounds hp.2.2.1 hδ hK
  have he := logarithmic_round_ratio hp.2.2.1 hδ hp.2.2.2.2.2.1 hp.2.2.2.2.1 hK
  have ha : 2 * p.Δ / (η * (K : ℝ) * (R : ℝ)) ≤ p.ε := by
    have h := rounded_round_accuracy (Δ := p.Δ) hb.1 hp.2.2.2.2.1 hK
    rw [he] at h
    exact h
  exact correctedAveraging_successful p hp hK hR η hb.1 hσ hδ hmode hb.2.1 hb.2.2 ha I O ho

end LongTails.Setups.BirchNonIID

open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

theorem zeroSimilarity_round_descent {workers d : ℕ} {I : Instance workers d} {L η : ℝ}
    (hw : 0 < workers) (hη : 0 ≤ η) (hL : 0 < L)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I 0) (anchor : Point d) (K : ℕ)
    (hstep : η * L ≤ 1) :
    (workers : ℝ) * objective I (pointMean (fun i => localPath I i anchor η K)) ≤
      (workers : ℝ) * objective I anchor - η / 2 * roundGradientEnergy I anchor η K := by
  have hb := localPath_round_descent hw hη hL (le_refl 0) hs hd anchor K
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, mul_zero, sub_zero] at hb
  have hn : 0 ≤ (η / 2 * (1 - L * η)) *
      (∑ i, ∑ k ∈ Finset.range K, ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) := by
    apply mul_nonneg
    · apply mul_nonneg (by positivity)
      nlinarith
    · positivity
  dsimp [roundGradientEnergy]
  linarith

theorem zeroSimilarity_gradient_energy {workers d : ℕ} {I : Instance workers d} {L η Δ : ℝ}
    (hw : 0 < workers) (hη : 0 < η) (hL : 0 < L)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I 0) (x0 : Point d) (K R : ℕ)
    (hstep : η * L ≤ 1) (hlower : ∀ x, I.lower ≤ objective I x)
    (hgap : objective I x0 - I.lower ≤ Δ) :
    (∑ r ∈ Finset.range R, roundGradientEnergy I (serverPath I x0 η K r) η K) ≤
      2 * (workers : ℝ) * Δ / η := by
  have hb : (workers : ℝ) * objective I (serverPath I x0 η K R) ≤
      (workers : ℝ) * objective I x0 - η / 2 *
        ∑ r ∈ Finset.range R, roundGradientEnergy I (serverPath I x0 η K r) η K := by
    induction R with
    | zero => simp [serverPath]
    | succ R ih =>
      have hr := zeroSimilarity_round_descent hw hη.le hL hs hd (serverPath I x0 η K R) K hstep
      simp only [serverPath, Finset.sum_range_succ]
      linarith
  have hl := mul_le_mul_of_nonneg_left (hlower (serverPath I x0 η K R)) (Nat.cast_nonneg workers)
  have hg := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg workers)
  apply (le_div_iff₀ hη).mpr
  nlinarith

theorem zeroSimilarity_average_bound {workers d K R : ℕ} {I : Instance workers d} {L η Δ : ℝ}
    (hw : 0 < workers) (hK : 0 < K) (hR : 0 < R) (hη : 0 < η) (hL : 0 < L)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I 0) (x0 : Point d) (hstep : η * L ≤ 1)
    (hlower : ∀ x, I.lower ≤ objective I x) (hgap : objective I x0 - I.lower ≤ Δ) :
    (1 / ((workers * K * R : ℕ) : ℝ)) *
      (∑ j : Fin (workers * K * R), ‖gradient (objective I) (referencePoint hw I x0 η K j.val)‖ ^ 2) ≤
      2 * Δ / (η * (K : ℝ) * (R : ℝ)) := by
  rw [referencePoint_energy_sum hw hK]
  have he := zeroSimilarity_gradient_energy hw hη hL hs hd x0 K R hstep hlower hgap
  have hw' : (workers : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  calc
    _ ≤ (1 / ((workers * K * R : ℕ) : ℝ)) * (2 * (workers : ℝ) * Δ / η) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by push_cast; field_simp

end LongTails.Setups.BirchNonIID

open MeasureTheory

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

/-- Success in the original standalone setup for zero-variance worker oracles.
The algorithm is public and uses exactly K R calls per worker. -/
theorem zeroSimilarity_correctedAveraging_successful {workers K R : ℕ} (p : Params workers)
    (hp : Valid p) (hK : 0 < K) (hR : 0 < R) (η : ℝ) (hη : 0 < η)
    (hσ : ∀ i, p.σ i = 0) (hδ : p.δ = 0)
    (hmode : p.similarity = .secondOrder ∨ p.similarity = .firstAndSecondOrder)
    (hstep : η * p.L ≤ 1)
    (haccuracy : 2 * p.Δ / (η * (K : ℝ) * (R : ℝ)) ≤ p.ε)
    (I : Instance workers p.d) (O : Oracle (Point p.d) (Point p.d) workers)
    (ho : Admissible p I O) :
    let A := correctedAveraging workers p.d K R hp.1 hK hR p.x0 η
    (spec workers).successful p I
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K * R) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases ho with ⟨hobj, Ω, m, horacle⟩
  let := m
  rcases horacle with ⟨μ, P, g, hiid, hg, rfl⟩
  rcases hobj with ⟨hf, hs, hlower, hgap, hsim⟩
  have hsecond : SecondOrderSimilarity I p.δ := by
    rcases hmode with hmode | hmode
    · simpa only [hmode, Similarity.Holds] using hsim
    · exact (show FirstOrderSimilarity I p.ζ ∧ SecondOrderSimilarity I p.δ by
        simpa only [hmode, Similarity.Holds] using hsim).2
  have hd : GradientDifferenceSimilarity I 0 := by
    simpa only [hδ] using gradientDifferenceSimilarity_of_secondOrderSimilarity hsecond
  have hg0 (i : Fin workers) :
      LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
        (μ : Measure Ω) (I.localObjective i) (g i) 0 := by
    simpa only [hσ i] using hg i
  have hm := measurable_correctedAveraging_execute hp.1 hK hR p.x0 η P g
    (fun i => (hg i).measurable)
  have hout := correctedAveraging_output_moments hp.1 hK hR I hf g hiid hg0 p.x0 η
  have hb := zeroSimilarity_average_bound hp.1 hK hR hη hp.2.2.1 hs hd p.x0
    hstep hlower hgap
  have hacc := hout.2.le.trans (hb.trans haccuracy)
  set_option backward.isDefEq.respectTransparency false in
    exact ⟨hm, hout.1, hacc⟩

/-- At zero similarity the same method allows every local horizon. -/
theorem zeroSimilarity_public_budget {workers K : ℕ} (p : Params workers)
    (hp : Valid p) (hK : 0 < K) (hσ : ∀ i, p.σ i = 0) (hδ : p.δ = 0)
    (hmode : p.similarity = .secondOrder ∨ p.similarity = .firstAndSecondOrder)
    (I : Instance workers p.d) (O : Oracle (Point p.d) (Point p.d) workers)
    (ho : Admissible p I O) :
    let η := 1 / (4 * p.L)
    let R := max 1 ⌈8 * p.L * p.Δ / ((K : ℝ) * p.ε)⌉₊
    let hR : 0 < R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    let A := correctedAveraging workers p.d K R hp.1 hK hR p.x0 η
    (spec workers).successful p I
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K * R) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hL := hp.2.2.1
  have hε := hp.2.2.2.2.1
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hη : 0 < 1 / (4 * p.L) := by positivity
  have he : 2 * p.Δ / ((1 / (4 * p.L)) * (K : ℝ) * p.ε) =
      8 * p.L * p.Δ / ((K : ℝ) * p.ε) := by field_simp; ring
  have ha := rounded_round_accuracy (Δ := p.Δ) hη hε hK
  rw [he] at ha
  have hstep : (1 / (4 * p.L)) * p.L ≤ 1 := by
    have he' : (1 / (4 * p.L)) * p.L = 1 / 4 := by field_simp
    rw [he']; norm_num
  exact zeroSimilarity_correctedAveraging_successful p hp hK
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) _ hη hσ hδ hmode hstep ha I O ho

end LongTails.Setups.BirchNonIID
