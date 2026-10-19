import LongTails.Proofs.AdamHeavyTailedHistory
import LongTails.Proofs.AdamHeavyTailedTuning

open MeasureTheory OracleTemplate.Adam

namespace LongTails.Proofs.AdamHeavyTailedRate

lemma trajectory_signal_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {f : Point d → ℝ} {grad : Point d → Point d} {L Δ p M : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x) (hL : 0 < L) (hΔ : 0 ≤ Δ)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M) (hM : 0 ≤ M)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1000000000000) (hτ : 0 < τ)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : Point d) (hgap : ∀ x, f x0 - f x ≤ Δ) (ω0 : Ω) (T : ℕ) (hT : 0 < T) :
    let η := τ * ρ / (100000 * L)
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    (∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g (9 / 10) ρ η τ x0 ξ s).2.2
      (grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1) ∂Q) / T ≤
      20 * Δ / (η * T) + 4000000 * τ * ρ := by
  dsimp only
  let η := τ * ρ / (100000 * L)
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let S := ∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g (9 / 10) ρ η τ x0 ξ s).2.2
    (grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1) ∂Q
  let U := ∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g (9 / 10) ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂Q
  let J := (1 / 10 : ℝ) * (∑ j ∈ Finset.range T, (9 / 10 : ℝ) ^ j *
    (∑ s ∈ Finset.range (T - j), ∫ ξ, lagPairing g grad (9 / 10) ρ η τ x0 ξ s j j ∂Q))
  have hρ1 : ρ < 1 := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hq : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hq1 : (9 / 10 : ℝ) ≤ 1 := by norm_num
  have hstable := AdamHeavyTailedTuning.fixed_momentum_stability hρsmall
  have hrsmall := (AdamHeavyTailedAlgebra.forgetting_geometric_ratio hρsmall).2
  have hS : 0 ≤ S := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => signalEnergy_nonneg hτ _ _
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hUb : U ≤ 32 * (S / τ + T) := AdamHeavyTailedHistory.trajectory_energy_integral_bound
    P hg hgi hL.le hlip (by linarith) hp2 hm hmass hq hq1 hρ hρ1 hτ hstable.1 hstable.2 hnoise x0 ω0 T
  have hJ := AdamHeavyTailedHistory.trajectory_pairing_signal_lower P hg hgi hL.le hlip hp hp2 hmean hm hmass hM
    (η := η) hq hq1 hρ hρ1 hτ hstable.1 hstable.2 hnoise hrsmall x0 ω0 T
  simp only [abs_of_pos hη] at hJ
  have hd := AdamHeavyTailedHistory.trajectory_expected_descent Q hg hf hL.le hlip
    (η := η) hq hq1 hρ hρ1 hτ hstable.1 x0 hgap T
  have hd' : η * J ≤ Δ + L * η ^ 2 / 2 * U := by norm_num only at hd; exact hd
  have hh := AdamHeavyTailedTuning.descent_energy_combine hS hTr.le hL.le hη hτ hUb hJ hd'
  exact AdamHeavyTailedTuning.normalized_signal_bound hS hTr hΔ hL hτ hρ hρsmall hh

lemma trajectory_accuracy_of_signal {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {grad : Point d → Point d} {L p M ε : ℝ}
    (hL : 0 < L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M) (hM : 0 ≤ M)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1000000000000) (hτε : ε ≤ τ)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : Point d) (ω0 : Ω) (T : ℕ) (hT : 0 < T) :
    let η := τ * ρ / (100000 * L)
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    τ * ((∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g (9 / 10) ρ η τ x0 ξ s).2.2
      (grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1) ∂Q) / T) ≤ ε ^ 2 / 100 →
    (∑ s ∈ Finset.range T, ∫ ξ, ‖grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1‖ ∂Q) / T ≤ ε := by
  dsimp only
  intro hsmall
  let η := τ * ρ / (100000 * L)
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let S := ∑ s ∈ Finset.range T, ∫ ξ, signalEnergy ρ τ (trajectory g (9 / 10) ρ η τ x0 ξ s).2.2
    (grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1) ∂Q
  let G := ∑ s ∈ Finset.range T, ∫ ξ, ‖grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1‖ ∂Q
  let A := ∑ s ∈ Finset.range T, ∫ ξ, AdamHeavyTailedHistory.trajectorySignalVariation g grad (9 / 10) ρ η τ x0 ξ s ∂Q
  let U := ∑ s ∈ Finset.range T, ∫ ξ, ‖velocity g (9 / 10) ρ η τ x0 ξ (s + 1)‖ ^ 2 ∂Q
  have hρ1 : ρ < 1 := by linarith
  have hτ : 0 < τ := hε.trans_le hτε
  have hη : 0 < η := by dsimp [η]; positivity
  have hq : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hq1 : (9 / 10 : ℝ) ≤ 1 := by norm_num
  have hstable := AdamHeavyTailedTuning.fixed_momentum_stability hρsmall
  have hS : 0 ≤ S := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => signalEnergy_nonneg hτ _ _
  have hG : 0 ≤ G := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => norm_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun s _ => integral_nonneg fun ξ => Real.sqrt_nonneg _
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hUb : U ≤ 32 * (S / τ + T) := AdamHeavyTailedHistory.trajectory_energy_integral_bound
    P hg hgi hL.le hlip (by linarith) hp2 hm hmass hq hq1 hρ hρ1 hτ hstable.1 hstable.2 hnoise x0 ω0 T
  have hv := AdamHeavyTailedHistory.trajectorySignalVariation_integral_square_sum (P := Q) (η := η)
    hg hL.le hlip hq hq1 hρ hρ1 hτ hstable.1 x0 T
  have he : L * |η| / ρ = τ / 100000 := by rw [abs_of_pos hη]; dsimp [η]; field_simp
  rw [he] at hv
  have hgg := AdamHeavyTailedHistory.trajectory_gradient_sum_sq_le P hg hL.le hlip hp hp2 hM hm hmass
    (η := η) hq hq1 hρ hρ1 hτ hstable.1 hnoise x0 ω0 T
  have hh := AdamHeavyTailedTuning.normalized_history_bound hTr hS hA hτ hUb hv hgg
  exact AdamHeavyTailedAlgebra.ordinary_gradient_accuracy (div_nonneg hG hTr.le)
    (div_nonneg hS hTr.le) hε hτε hsmall hh

lemma trajectory_tuned_accuracy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {f : Point d → ℝ} {grad : Point d → Point d} {L Δ p σ ε : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x) (hL : 0 < L) (hΔ : 0 ≤ Δ) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 1 < p) (hp2 : p ≤ 2) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ σ ^ p)
    (x0 : Point d) (hgap : ∀ x, f x0 - f x ≤ Δ) (ω0 : Ω) :
    let ρ := 1 / (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))
    let τ := ε / (100000 * Real.sqrt ρ)
    let η := τ * ρ / (100000 * L)
    let K := 1 + ⌈400000000 * Δ * L / ε ^ 2 * (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))⌉₊
    let Q := Measure.infinitePi (fun _ : ℕ => P)
    (∑ s ∈ Finset.range K, ∫ ξ, ‖grad (trajectory g (9 / 10) ρ η τ x0 ξ s).1‖ ∂Q) / K ≤ ε := by
  dsimp only
  let ρ := 1 / (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))
  let τ := ε / (100000 * Real.sqrt ρ)
  let η := τ * ρ / (100000 * L)
  let K := 1 + ⌈400000000 * Δ * L / ε ^ 2 * (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))⌉₊
  have htune := AdamHeavyTailedTuning.tuning_parameters hσ hε hp
  have hρ : 0 < ρ := htune.1
  have hρsmall : ρ ≤ 1 / 1000000000000 := htune.2.1
  have hτε : ε ≤ τ := htune.2.2.1
  have hτ : 0 < τ := hε.trans_le hτε
  have hnoise : σ ^ p * (Real.sqrt ρ / τ) ^ p ≤ ρ := htune.2.2.2
  have hK := AdamHeavyTailedTuning.iteration_budget_bound (Δ := Δ) (L := L) (p := p) hσ hε
  have hM := Real.rpow_nonneg hσ p
  have hS := trajectory_signal_bound P hg hgi hf hL hΔ hlip hp.le hp2 hmean hm hmass hM
    hρ hρsmall hτ hnoise x0 hgap ω0 K hK.1
  have hsmall := AdamHeavyTailedTuning.budget_signal_small hL hε hρ hK.1 hK.2 hS
  exact trajectory_accuracy_of_signal P hg hgi hL hlip hp.le hp2 hε hm hmass hM
    hρ hρsmall hτε hnoise x0 ω0 K hK.1 hsmall

lemma execution_accuracy {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (p : Measure Ω) (P : Measure (ℕ → Ω)))
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    {f : Point d → ℝ} {grad : Point d → Point d} {L Δ α σ ε : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x) (hL : 0 < L) (hΔ : 0 ≤ Δ) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hα : 1 < α) (hα2 : α ≤ 2) (hmean : ∀ x, ∫ ω, g x ω ∂p = grad x)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ α) p)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ α ∂p) ≤ σ ^ α)
    (x0 : Point d) (hgap : ∀ x, f x0 - f x ≤ Δ) :
    let ρ := 1 / (1000000000000 + (100000 * σ / ε) ^ (α / (α - 1)))
    let τ := ε / (100000 * Real.sqrt ρ)
    let η := τ * ρ / (100000 * L)
    let n := ⌈400000000 * Δ * L / ε ^ 2 * (1000000000000 + (100000 * σ / ε) ^ (α / (α - 1)))⌉₊
    let O : OracleTemplate.Oracle (Point d) (Point d) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    let out := fun z : Fin (n + 1) × (ℕ → Ω) => output O (9 / 10) ρ η τ n x0 z.1 z.2
    let Q := (PMF.uniformOfFintype (Fin (n + 1))).toMeasure.prod (P : Measure (ℕ → Ω))
    Measurable out ∧ Integrable (fun z => ‖grad (out z)‖) Q ∧ (∫ z, ‖grad (out z)‖ ∂Q) ≤ ε := by
  dsimp only
  simp_rw [output, execute_trajectory]
  let ρ := 1 / (1000000000000 + (100000 * σ / ε) ^ (α / (α - 1)))
  let τ := ε / (100000 * Real.sqrt ρ)
  let η := τ * ρ / (100000 * L)
  let n := ⌈400000000 * Δ * L / ε ^ 2 * (1000000000000 + (100000 * σ / ε) ^ (α / (α - 1)))⌉₊
  have htune := AdamHeavyTailedTuning.tuning_parameters hσ hε hα
  have hρ : 0 < ρ := htune.1
  have hρsmall : ρ ≤ 1 / 1000000000000 := htune.2.1
  have hτ : 0 < τ := hε.trans_le htune.2.2.1
  have hρ1 : ρ < 1 := by linarith
  have hstable := AdamHeavyTailedTuning.fixed_momentum_stability hρsmall
  have hgrad := measurable_gradient_of_lipschitz hL.le hlip
  have hi (t : ℕ) : Integrable (fun ξ => ‖grad (trajectory g (9 / 10) ρ η τ x0 ξ t).1‖) (P : Measure _) :=
    integrable_trajectory_gradient_norm hg hL.le hlip (by norm_num) (by norm_num) hρ hρ1 hτ hstable.1 x0 t
  refine ⟨measurable_selected_trajectory hg (9 / 10) ρ η τ x0 n,
    integrable_selected_gradient (P : Measure _) hg hgrad (9 / 10) ρ η τ x0 n hi, ?_⟩
  rw [integral_selected_gradient (P : Measure _) hg hgrad (9 / 10) ρ η τ x0 n hi]
  have hPQ := iid_sequence_law h_samples
  rw [hPQ]
  let ω0 : Ω := Classical.choice p.nonempty
  have hh := trajectory_tuned_accuracy (p : Measure Ω) hg hgi hf hL hΔ hσ hε hlip hα hα2 hmean hm hmass x0 hgap ω0
  change ((n + 1 : ℕ) : ℝ)⁻¹ * (∑ t ∈ Finset.range (n + 1), ∫ ξ,
    ‖grad (trajectory g (9 / 10) ρ η τ x0 ξ t).1‖ ∂Measure.infinitePi (fun _ : ℕ => (p : Measure Ω))) ≤ ε
  change (∑ t ∈ Finset.range (1 + n), ∫ ξ,
    ‖grad (trajectory g (9 / 10) ρ η τ x0 ξ t).1‖ ∂Measure.infinitePi (fun _ : ℕ => (p : Measure Ω))) /
      ((1 + n : ℕ) : ℝ) ≤ ε at hh
  simpa only [Nat.add_comm 1, div_eq_mul_inv, mul_comm] using hh

end LongTails.Proofs.AdamHeavyTailedRate
