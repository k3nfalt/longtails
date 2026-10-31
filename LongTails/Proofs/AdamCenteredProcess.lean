import LongTails.Proofs.AdamExponentialProcess
import LongTails.Proofs.MatrixOracleMoments

open MeasureTheory

namespace LongTails.Proofs.AdamCenteredProcess

open AdamHeavyTailedProcess AdamExponentialProcess

lemma state_integral_zero {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S) (s : S) (ω0 : Ω)
    (n : ℕ) (U : S → Ω → ℝ)
    (hi : Integrable (fun ξ => U (stateAt next s ξ n) (ξ n)) (Measure.infinitePi (fun _ : ℕ => P)))
    (hUi : ∀ s, Integrable (U s) P) (hzero : ∀ s, (∫ ω, U s ω ∂P) = 0) :
    (∫ ξ, U (stateAt next s ξ n) (ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) = 0 := by
  have hp := stateAt_sample_integral_le P next s ω0 n U (fun _ => 0) hi (integrable_const 0)
    (fun b => hUi _) (fun b => by rw [hzero])
  have hn := stateAt_sample_integral_le P next s ω0 n (fun s ω => -U s ω) (fun _ => 0)
    hi.neg (integrable_const 0) (fun b => (hUi _).neg) (fun b => by rw [integral_neg, hzero]; simp)
  simp only [integral_neg, integral_zero] at hp hn
  linarith

noncomputable def sumNext {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (z : S × ℝ) (ω : Ω) : S × ℝ := (next z.1 ω, z.2 + U z.1 ω)

lemma sum_state {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    stateAt (sumNext next U) (s, 0) ξ n = (stateAt next s ξ n, partialSum next U s ξ n) := by
  induction n with
  | zero => simp [stateAt_zero, partialSum]
  | succ n ih =>
      rw [stateAt_succ, ih, stateAt_succ]
      simp only [sumNext, partialSum, Finset.sum_range_succ]

lemma partialSum_cross_zero {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ω0 : Ω) (n : ℕ)
    (hi : Integrable (fun ξ => partialSum next U s ξ n * U (stateAt next s ξ n) (ξ n))
      (Measure.infinitePi (fun _ : ℕ => P)))
    (hUi : ∀ s, Integrable (U s) P) (hzero : ∀ s, (∫ ω, U s ω ∂P) = 0) :
    (∫ ξ, partialSum next U s ξ n * U (stateAt next s ξ n) (ξ n)
      ∂Measure.infinitePi (fun _ : ℕ => P)) = 0 := by
  have hh := state_integral_zero P (sumNext next U) (s, 0) ω0 n (fun z ω => z.2 * U z.1 ω)
    (by simpa only [sum_state] using hi) (fun z => (hUi z.1).const_mul z.2)
    (fun z => by rw [integral_const_mul, hzero, mul_zero])
  simpa only [sum_state] using hh

lemma partialSum_second_moment {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (s : S) (ω0 : Ω) (n : ℕ)
    (hUi : ∀ s, Integrable (U s) P) (hzero : ∀ s, (∫ ω, U s ω ∂P) = 0)
    (hU2 : ∀ t < n, Integrable (fun ξ => (U (stateAt next s ξ t) (ξ t)) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P))) :
    Integrable (fun ξ => (partialSum next U s ξ n) ^ 2) (Measure.infinitePi (fun _ : ℕ => P)) ∧
      (∫ ξ, (partialSum next U s ξ n) ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) =
        ∑ t ∈ Finset.range n, ∫ ξ, (U (stateAt next s ξ t) (ξ t)) ^ 2
          ∂Measure.infinitePi (fun _ : ℕ => P) := by
  have hUm (t) : Measurable (fun ξ => U (stateAt next s ξ t) (ξ t)) :=
    hU.comp ((measurable_stateAt hn s t).prodMk (measurable_pi_apply t))
  have hmem (t : ℕ) (ht : t < n) := (memLp_two_iff_integrable_sq (hUm t).aestronglyMeasurable).2 (hU2 t ht)
  have hs (k : ℕ) (hk : k ≤ n) : MemLp (partialSum next U s · k) 2 (Measure.infinitePi (fun _ : ℕ => P)) :=
    memLp_finsetSum _ (fun t ht => hmem t (Nat.lt_of_lt_of_le (Finset.mem_range.1 ht) hk))
  have he (k : ℕ) (hk : k ≤ n) :
      (∫ ξ, (partialSum next U s ξ k) ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) =
        ∑ t ∈ Finset.range k, ∫ ξ, (U (stateAt next s ξ t) (ξ t)) ^ 2
          ∂Measure.infinitePi (fun _ : ℕ => P) := by
    induction k with
    | zero => simp [partialSum]
    | succ k ih =>
        have hk' : k < n := by omega
        have hsk := hs k (by omega)
        have huk := hmem k hk'
        have hcross := partialSum_cross_zero P next U s ω0 k (hsk.integrable_mul huk) hUi hzero
        have hh := MatrixOracleMoments.second_moment_add_of_orthogonal hsk huk hcross
        have hstep (ξ) : partialSum next U s ξ (k + 1) =
            partialSum next U s ξ k + U (stateAt next s ξ k) (ξ k) := by
          simp only [partialSum, Finset.sum_range_succ]
        simp only [hstep]
        rw [hh, ih (by omega), Finset.sum_range_succ]
  exact ⟨(hs n le_rfl).integrable_sq, he n le_rfl⟩

end LongTails.Proofs.AdamCenteredProcess
