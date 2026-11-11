import LongTails.Proofs.ParameterFreeNsgdmPhase
import LongTails.Proofs.ParameterFreeNsgdmBudget

open MeasureTheory

namespace LongTails.Proofs.ParameterFreeNsgdmMain

open OracleTemplate
open LongTails.Setups.ParameterFreeHeavyTailedSmooth
open LongTails.Algorithms.ParameterFreeNsgdm
open ParameterFreeNsgdmRun ParameterFreeNsgdmRunBound ParameterFreeNsgdmSelection
open ParameterFreeNsgdmExecution ParameterFreeNsgdmGrid ParameterFreeNsgdmPhase
open ParameterFreeNsgdmBudget

variable {d : Public} {Ω : Type} [MeasurableSpace Ω]

lemma phaseStart_strict (k : ℕ) : phaseStart k < phaseStart (k + 1) := by
  simp only [phaseStart, phaseCost]
  have := candidates_pos k
  have : 0 < horizon k := by unfold horizon; positivity
  have : 0 < candidates k * horizon k := by positivity
  omega

lemma phaseStart_mono {j k : ℕ} (h : j ≤ k) : phaseStart j ≤ phaseStart k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (phaseStart_strict _).le

lemma phaseStart_ge (k : ℕ) : k ≤ phaseStart k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => have := phaseStart_strict k; omega

lemma exists_phase (N : ℕ) : ∃ K, phaseStart K ≤ N ∧ N < phaseStart (K + 1) := by
  have hex : ∃ k, N < phaseStart (k + 1) := ⟨N, by have := phaseStart_ge (N + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; simp [phaseStart]
  · have := Nat.find_min hex (Nat.sub_lt h one_pos)
    have h1 : 1 ≤ Nat.find hex := h
    rw [Nat.sub_add_cancel h1] at this
    omega

lemma grid_index_lt {k i j : ℕ} (hi : i ≤ 2 * k) (hj : j ≤ 5 * k) :
    i * stepCount k + j < candidates k := by
  unfold candidates momentumCount stepCount
  nlinarith

lemma momentum_grid (k i j : ℕ) (hj : j ≤ 5 * k) :
    momentum k (i * stepCount k + j) = Real.exp (-(i : ℝ) / 2) := by
  unfold momentum
  have hs : 0 < stepCount k := by unfold stepCount; omega
  have hdiv : (i * stepCount k + j) / stepCount k = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt (by unfold stepCount; omega)]
    simp
  rw [hdiv]

lemma stepSize_grid (k i j : ℕ) (hj : j ≤ 5 * k) :
    stepSize k (i * stepCount k + j) = Real.exp ((k : ℝ) - (j : ℝ) / 2) := by
  unfold stepSize
  have hs : 0 < stepCount k := by unfold stepCount; omega
  have hmod : (i * stepCount k + j) % stepCount k = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by unfold stepCount; omega)]
  rw [hmod]

lemma first_term_le_runRate {L Δ σ p T α η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hT : 0 < T) :
    (Δ / η + 12 * σ / α + 12 * σ * T * α ^ ((p - 1) / p) +
      T * (2 * L * η * (1 - α) / α + L / 2 * η)) / T ≤ runRate L Δ σ p T α η := by
  unfold runRate
  have h1 : 2 * L * η * (1 - α) / α + L / 2 * η ≤ 3 * L * η / α := by
    have ha : 1 / 2 ≤ 1 / α := by
      rw [div_le_div_iff_of_pos_left one_pos (by norm_num) hα0]; linarith
    have h2 : L / 2 * η ≤ L * η / α := by
      rw [show L / 2 * η = L * η * (1 / 2) by ring, show L * η / α = L * η * (1 / α) by ring]
      exact mul_le_mul_of_nonneg_left ha (by positivity)
    have h3 : 2 * L * η * (1 - α) / α ≤ 2 * L * η / α := by
      apply div_le_div_of_nonneg_right _ hα0.le
      nlinarith [mul_nonneg hL hη.le]
    calc 2 * L * η * (1 - α) / α + L / 2 * η ≤ 2 * L * η / α + L * η / α := add_le_add h3 h2
      _ = 3 * L * η / α := by ring
  rw [div_le_iff₀ hT]
  have : Δ / η + 12 * σ / α + 12 * σ * T * α ^ ((p - 1) / p) + T * (2 * L * η * (1 - α) / α + L / 2 * η)
      ≤ Δ / η + 12 * σ / α + 12 * σ * T * α ^ ((p - 1) / p) + T * (3 * L * η / α) := by
    gcongr
  refine this.trans (le_of_eq ?_)
  have hη' : η ≠ 0 := hη.ne'
  have hα' : α ≠ 0 := hα0.ne'
  field_simp
  ring

lemma phase_bound_le_eps {L Δ σ p ε : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p)
    (hp2 : p ≤ 2) (hε : 0 < ε) {k : ℕ} (hk : levelStar L Δ σ p ε ≤ k) :
    ∃ c, c < candidates k ∧
      (Δ / stepSize k c + 12 * σ / momentum k c +
        12 * σ * (horizon k) * momentum k c ^ ((p - 1) / p) +
        (horizon k) * (2 * L * stepSize k c * (1 - momentum k c) / momentum k c +
          L / 2 * stepSize k c)) / horizon k +
      (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1)) ^ (1 / p) +
      (candidates k * (6 * σ ^ p / (horizon k : ℝ) ^ (p - 1))) ^ (1 / p) ≤ ε := by
  obtain ⟨hS, hK⟩ := twoPow_ge_of_level hL hΔ hσ hp hε hk
  have hT : (horizon k : ℝ) = 2 ^ k := by simp [horizon]
  have hT1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hT0 : (0 : ℝ) < 2 ^ k := by positivity
  unfold mainThreshold at hS
  have hp1 : 0 < p - 1 := by linarith
  have hterms : ∀ x ∈ ({8000 * L * Δ / ε ^ 2,
      L * Δ * σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1)),
      σ ^ ((5 * p - 2) / (2 * p - 2)) * (L * Δ) ^ (-(p / (2 * p - 2))) *
        (60 / ε) ^ ((3 * p - 2) / (2 * p - 2)),
      (σ ^ 2 / (L * Δ)) ^ (p / (2 * p - 2)), Real.sqrt (3 * L / Δ), (Δ / (3 * L)) ^ ((1 : ℝ) / 3),
      6 ^ ((1 : ℝ) / (p - 1)) * (5 * σ / ε) ^ (p / (p - 1))} : Set ℝ), x ≤ 2 ^ k := by
    intro x hx
    have hall : 0 ≤ 8000 * L * Δ / ε ^ 2 ∧ 0 ≤ L * Δ * σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1)) ∧
        0 ≤ σ ^ ((5 * p - 2) / (2 * p - 2)) * (L * Δ) ^ (-(p / (2 * p - 2))) *
          (60 / ε) ^ ((3 * p - 2) / (2 * p - 2)) ∧
        0 ≤ (σ ^ 2 / (L * Δ)) ^ (p / (2 * p - 2)) ∧ 0 ≤ Real.sqrt (3 * L / Δ) ∧
        0 ≤ (Δ / (3 * L)) ^ ((1 : ℝ) / 3) ∧ 0 ≤ 6 ^ ((1 : ℝ) / (p - 1)) * (5 * σ / ε) ^ (p / (p - 1)) :=
      ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity,
        by positivity⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hall
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
  have t1 := hterms _ (Set.mem_insert _ _)
  have t2 := hterms _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have t3 := hterms _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have t4 := hterms _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have t5 := hterms _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))
  have t6 := hterms _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert _ _))))))
  have t7 := hterms _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))))
  obtain ⟨hlow, hhigh⟩ := step_range (σ := σ) (p := p) hL hΔ hT1 t5 t6
  obtain ⟨i, j, hi, hj, hgrid⟩ := exists_grid_run hL hΔ hσ hp hp2 (k := k) (by simpa using hlow) hhigh
  refine ⟨i * stepCount k + j, grid_index_lt hi hj, ?_⟩
  rw [momentum_grid k i j hj, stepSize_grid k i j hj, hT]
  have hα0 : 0 < Real.exp (-(i : ℝ) / 2) := Real.exp_pos _
  have hα1 : Real.exp (-(i : ℝ) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : (0 : ℝ) ≤ i := by positivity
    linarith
  have hη : 0 < Real.exp ((k : ℝ) - (j : ℝ) / 2) := Real.exp_pos _
  have hfirst := first_term_le_runRate (L := L) (Δ := Δ) (σ := σ) (p := p) (T := (2 : ℝ) ^ k) hL.le hη hα0
    hα1 hT0
  have htuned := tuned_bound hL hΔ hσ hp hε hT1 t1 t2 t3 t4
  have hv1 := single_validation_bound hσ hp hε hT0 t7
  have hv2 := count_validation_bound hσ hp hp2 hε hK
  linarith


lemma law_eq_infinitePi {ν : Measure Ω} {P : Measure (ℕ → Ω)}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) ν P) :
    P = Measure.infinitePi (fun _ : ℕ => ν) := by
  have h := hIID.stream_law
  have hid : (fun (ω : ℕ → Ω) (k : ℕ) => ω k) = id := by funext ω; rfl
  rw [hid] at h
  have := h.map_eq
  rwa [Measure.map_id] at this

lemma main_success {f : d.E → ℝ} {g : d.E → Ω → d.E} {ν : ProbabilityMeasure Ω}
    {P : ProbabilityMeasure (ℕ → Ω)} {L Δ σ p ε : ℝ}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (ν : Measure Ω) (P : Measure (ℕ → Ω)))
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {lower : ℝ} (hlow : ∀ x, lower ≤ f x) (hgap : f d.x0 - lower ≤ Δ)
    (hmeas : Measurable (Function.uncurry g))
    (hint : ∀ x, Integrable (g x) (ν : Measure Ω))
    (hunb : ∀ x, ∫ ω, g x ω ∂(ν : Measure Ω) = gradient f x)
    (hmomint : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p) (ν : Measure Ω))
    (hmom : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ p ∂(ν : Measure Ω) ≤ σ ^ p)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε)
    (N : ℕ) (hN : phaseStart (levelStar L Δ σ p ε + 1) ≤ N) :
    let O : Oracle d.E d.E := { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    let output := fun seed : Seed × (ℕ → Ω) => execute O (algorithm d) (fun _ => N) seed.1 seed.2
    Measurable output ∧
      Integrable (fun z => ‖gradient f (output z)‖) ((seedLaw.prod (P : Measure (ℕ → Ω)))) ∧
      ∫ z, ‖gradient f (output z)‖ ∂(seedLaw.prod (P : Measure (ℕ → Ω))) ≤ ε := by
  intro O output
  have hO : Oracle (ν : Measure Ω) g (gradient f) σ p :=
    ⟨hmeas, hint, hunb, hmomint, hmom⟩
  have hPν : (P : Measure (ℕ → Ω)) = Measure.infinitePi (fun _ : ℕ => (ν : Measure Ω)) :=
    law_eq_infinitePi hIID
  obtain ⟨K, hK1, hK2⟩ := exists_phase N
  have hKstar : levelStar L Δ σ p ε + 1 ≤ K := by
    by_contra hcon
    rw [not_le] at hcon
    have := phaseStart_mono (show K + 1 ≤ levelStar L Δ σ p ε + 1 by omega)
    omega
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hk : levelStar L Δ σ p ε ≤ k := by omega
  have hout : output = fun z : Seed × (ℕ → Ω) => phaseOutput g z.1 k (phaseStart k) z.2 := by
    funext z
    show execute O (algorithm d) (fun _ => N) z.1 z.2 = _
    rw [execute_eq g P z.1 z.2 N, out_after g z.1 z.2 (k + 1) N hK1 hK2]
    rfl
  obtain ⟨c, hc, hbound⟩ := phase_bound_le_eps hL hΔ hσ hp hp2 hε hk
  have hphase := phase_expectation hO hg hlip hL.le hlow hgap hp hp2 hσ k (phaseStart k) hc
  rw [hPν]
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact phaseOutput_measurable hmeas k (phaseStart k)
  · rw [hout]
    exact hphase.1
  · rw [hout]
    exact hphase.2.trans hbound

end LongTails.Proofs.ParameterFreeNsgdmMain
