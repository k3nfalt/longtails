import LongTails.Proofs.CountdownMarkov

open MeasureTheory ProbabilityTheory Function Preorder

namespace OracleTemplate.CountdownMarkov

lemma stationary_transition_probability {Ω : Type} [MeasurableSpace Ω]
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (t : Set Ω) (ht : MeasurableSet t)
    (k : ℕ) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π : Measure (ℕ → Ω))
      {ξ | ξ k = b ∧ ξ (k + 1) ∈ t} = (π : Measure Ω) {b} * κ b t := by
  let P : Measure (ℕ → Ω) := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π
  let B : Set (Finset.Iic k → Ω) := {h | h ⟨k, Finset.mem_Iic.mpr le_rfl⟩ = b}
  have hB : MeasurableSet B := by
    have hm : Measurable (fun h : Finset.Iic k → Ω => h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) := by fun_prop
    exact hm hb
  have hj := OracleTemplate.HeavyTailedMarkovGradient.pathLaw_prefix_future κ π k 1
  have he := congrArg (fun μ : Measure ((Finset.Iic k → Ω) × Ω) => μ (B ×ˢ t)) hj
  rw [Measure.map_apply (by fun_prop) (hB.prod ht), Measure.compProd_apply_prod hB ht] at he
  simp only [pow_one, Kernel.comap_apply] at he
  change (∫⁻ h in B, κ (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) t ∂P.map (frestrictLe k)) =
    P {ξ | ξ k = b ∧ ξ (k + 1) ∈ t} at he
  have hi : (∫⁻ h in B, κ (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) t ∂P.map (frestrictLe k)) =
      κ b t * P.map (frestrictLe k) B := by
    calc
      _ = ∫⁻ _ in B, κ b t ∂P.map (frestrictLe k) := by
        apply setLIntegral_congr_fun hB
        intro h hh
        exact congrArg (fun z => κ z t) hh
      _ = _ := by rw [setLIntegral_const]
  have hm : P.map (frestrictLe k) B = (π : Measure Ω) {b} := by
    rw [Measure.map_apply (by fun_prop) hB]
    have hm := OracleTemplate.HeavyTailedMarkovGradient.pathLaw_stationary_marginal κ π hπ k
    have hx := congrArg (fun μ : Measure Ω => μ {b}) hm
    rw [Measure.map_apply (by fun_prop) hb] at hx
    exact hx
  rw [hi, hm] at he
  exact he.symm.trans (mul_comm _ _)


def commonPrefix {Ω : Type*} (b : Ω) (n : ℕ) : Set (ℕ → Ω) :=
  {ξ | ∀ k ≤ n, ξ k = b}

lemma measurableSet_commonPrefix {Ω : Type*} [MeasurableSpace Ω]
    (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (n : ℕ) :
    MeasurableSet (commonPrefix b n) := by
  unfold commonPrefix
  simpa only [Set.preimage, Set.mem_singleton_iff, Set.ofPred_forall] using
    (MeasurableSet.iInter fun (k : ℕ) => MeasurableSet.iInter fun (_ : k ≤ n) =>
      (measurable_pi_apply k) hb)

lemma commonPrefix_succ {Ω : Type*} (b : Ω) (n : ℕ) :
    commonPrefix b (n + 1) = commonPrefix b n ∩ {ξ | ξ (n + 1) = b} := by
  ext ξ
  simp only [commonPrefix, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h _ le_rfl⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases he : k = n + 1
    · simpa [he] using hn
    · exact h k (by omega)

lemma first_exit_cover {Ω : Type*} (b : Ω) (n : ℕ) (ξ : ℕ → Ω)
    (h : ξ ∉ commonPrefix b n) :
    ξ 0 ≠ b ∨ ∃ k < n, ξ k = b ∧ ξ (k + 1) ≠ b := by
  classical
  induction n with
  | zero =>
    left
    simpa [commonPrefix] using h
  | succ n ih =>
    by_cases hc : ξ ∈ commonPrefix b n
    · right
      refine ⟨n, by omega, hc n le_rfl, ?_⟩
      intro hn
      exact h (by rw [commonPrefix_succ]; exact ⟨hc, hn⟩)
    · rcases ih hc with h0 | ⟨k, hk, he, hn⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, by omega, he, hn⟩

lemma commonPrefix_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (n : ℕ) :
    1 - (P : Measure (ℕ → Ω)).real {ξ : ℕ → Ω | ξ 0 ≠ b} -
      ∑ k : Fin n, (P : Measure (ℕ → Ω)).real {ξ : ℕ → Ω | ξ k = b ∧ ξ (k + 1) ≠ b} ≤
      (P : Measure (ℕ → Ω)).real (commonPrefix b n) := by
  have hsub : (commonPrefix b n)ᶜ ⊆ {ξ : ℕ → Ω | ξ 0 ≠ b} ∪
      ⋃ k : Fin n, {ξ : ℕ → Ω | ξ k = b ∧ ξ (k + 1) ≠ b} := by
    intro ξ hξ
    rcases first_exit_cover b n ξ hξ with h0 | ⟨k, hk, he, hn⟩
    · exact Or.inl h0
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, hk⟩, he, hn⟩)
  have hu := (measureReal_mono (μ := (P : Measure (ℕ → Ω))) hsub).trans
    (measureReal_union_le _ _)
  have hs := measureReal_iUnion_fintype_le (μ := (P : Measure (ℕ → Ω)))
    (fun k : Fin n => {ξ : ℕ → Ω | ξ k = b ∧ ξ (k + 1) ≠ b})
  have hc := measureReal_add_measureReal_compl (μ := (P : Measure (ℕ → Ω)))
    (measurableSet_commonPrefix b hb n)
  have hone : (P : Measure (ℕ → Ω)).real Set.univ = 1 := by simp [measureReal_def]
  rw [hone] at hc
  linarith


lemma kernel_exit (H : ℕ) (hH : 0 < H) (p : unitInterval) :
    kernel H p 0 {x | x ≠ 0} = ENNReal.ofReal (p : ℝ) := by
  rw [kernel_zero]
  have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
  have hz : (H : ℝ) ≠ 0 := by positivity
  simp [bernoulliMeasure_apply p hs, hz]
  rw [← ENNReal.ofReal_coe_nnreal]
  rfl

lemma exit_probability (H : ℕ) (hH : 0 < H) (p : unitInterval) (k : ℕ) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (kernel H p) (stationaryLaw H p) : Measure (ℕ → ℝ)).real
      {ξ | ξ k = 0 ∧ ξ (k + 1) ≠ 0} = (p : ℝ) / (1 + H * (p : ℝ)) := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have he := stationary_transition_probability (kernel H p) (stationaryLaw H p)
    (stationary H p) 0 (measurableSet_singleton 0) {x | x ≠ 0}
    ((measurableSet_singleton 0).compl) k
  change _ = stationaryMeasure H p {0} * kernel H p 0 {x | x ≠ 0} at he
  simp only [Set.mem_ofPred_eq] at he
  rw [measureReal_def, he, stationaryMeasure_zero, kernel_exit H hH p,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal p.property.1]
  ring

lemma initial_nonzero (H : ℕ) (p : unitInterval) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (kernel H p) (stationaryLaw H p) : Measure (ℕ → ℝ)).real
      {ξ | ξ 0 ≠ 0} = H * (p : ℝ) / (1 + H * (p : ℝ)) := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hm := HeavyTailedMarkovGradient.pathLaw_map_zero (kernel H p) (stationaryLaw H p)
  have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
  have he := congrArg (fun μ : Measure ℝ => μ {x | x ≠ 0}) hm
  rw [Measure.map_apply (by fun_prop) hs] at he
  change _ = stationaryMeasure H p {x | x ≠ 0} at he
  change (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
    (kernel H p) (stationaryLaw H p) : Measure (ℕ → ℝ)) {ξ | ξ 0 ≠ 0} =
    stationaryMeasure H p {x | x ≠ 0} at he
  rw [measureReal_def, he, stationaryMeasure_nonzero, ENNReal.toReal_ofReal]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) p.property.1) (by positivity)

lemma commonPrefix_lower (H : ℕ) (hH : 0 < H) (p : unitInterval) (n : ℕ) :
    1 - H * (p : ℝ) / (1 + H * (p : ℝ)) - n * (p : ℝ) / (1 + H * (p : ℝ)) ≤
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (kernel H p) (stationaryLaw H p) : Measure (ℕ → ℝ)).real (commonPrefix 0 n) := by
  have h := commonPrefix_probability_lower
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw (kernel H p) (stationaryLaw H p))
    0 (measurableSet_singleton 0) n
  rw [initial_nonzero] at h
  simp_rw [exit_probability H hH p] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_assoc] using h

end OracleTemplate.CountdownMarkov
