import LongTails.Proofs.Execution
import LongTails.Proofs.TerminalClippingProbability

set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

lemma accuracy_budget {B G R δ ε : ℝ} {T : ℕ}
    (hB : 0 < B) (hG : 0 < G) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hT : 0 < T)
    (hbudget : (2 ^ 20 * (B * R ^ 2 + G ^ 2 / B) * Real.log (8 / δ)) ^ 2 ≤ (T : ℝ) * ε ^ 2) :
    16384 * B * (R ^ 2 + (G / B) ^ 2) * Real.log (8 / δ) / Real.sqrt T ≤ ε := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hq := confidence_pos hδ hδ1
  have hA : 0 ≤ 2 ^ 20 * (B * R ^ 2 + G ^ 2 / B) * Real.log (8 / δ) := by positivity
  have hsq : (Real.sqrt T * ε) ^ 2 = (T : ℝ) * ε ^ 2 := by rw [mul_pow, Real.sq_sqrt ht.le]
  have hroot := (sq_le_sq₀ hA (show 0 ≤ Real.sqrt T * ε by positivity)).mp (by rwa [hsq])
  have he : B * (R ^ 2 + (G / B) ^ 2) = B * R ^ 2 + G ^ 2 / B := by field_simp
  have hc := mul_le_mul_of_nonneg_right (show (16384 : ℝ) ≤ 2 ^ 20 by norm_num)
    (show 0 ≤ (B * R ^ 2 + G ^ 2 / B) * Real.log (8 / δ) by positivity)
  apply (div_le_iff₀ hs).mpr
  have he' : 16384 * B * (R ^ 2 + (G / B) ^ 2) * Real.log (8 / δ) =
      16384 * ((B * R ^ 2 + G ^ 2 / B) * Real.log (8 / δ)) := by rw [← he]; ring
  rw [he']
  nlinarith

lemma convergence : Convergence spec (fun p _ => 2 * p.T) := by
  apply convergence_of_public_budget (S := spec) (fun p => 2 * p.T)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨hB, hG, hδ, hδ1, hR, hε⟩ I O hadm
  have hT : 1 ≤ p.toPublic.T := le_max_left _ _
  have hbudget : (2 ^ 20 * (p.B * p.R ^ 2 + p.G ^ 2 / p.B) *
      Real.log (8 / p.δ)) ^ 2 ≤ (p.toPublic.T : ℝ) * p.ε ^ 2 := by
    have hc := Nat.le_ceil (2 ^ 40 * (p.B * p.R ^ 2 + p.G ^ 2 / p.B) ^ 2 *
      Real.log (8 / p.δ) ^ 2 / p.ε ^ 2)
    have hm : (⌈2 ^ 40 * (p.B * p.R ^ 2 + p.G ^ 2 / p.B) ^ 2 *
        Real.log (8 / p.δ) ^ 2 / p.ε ^ 2⌉₊ : ℝ) ≤ p.toPublic.T := by
      change (⌈2 ^ 40 * (p.B * p.R ^ 2 + p.G ^ 2 / p.B) ^ 2 *
        Real.log (8 / p.δ) ^ 2 / p.ε ^ 2⌉₊ : ℝ) ≤ (max 1 _ : ℕ)
      exact_mod_cast (le_max_right 1 _)
    have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp (hc.trans hm)
    nlinarith
  rcases hadm with ⟨g, projection, ν, P, hIID, hO, hX, hclosed, hx0, hf, hfm,
    ⟨u, hu, hmin, hdist⟩, hpm, hpX, hp, hg, hgi, hsub, hmi, hm⟩
  have hO' : O = sampleOracle p.toPublic g projection P := by
    rw [hO]
    unfold sampleOracle
    congr 1
    funext k query seed
    rcases query with ⟨i, query⟩
    cases query <;> rfl
  subst hO'
  have ht : 0 < p.T := hT
  let D := p.R ^ 2 + (p.G / p.B) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hstart : ‖p.x0 - u‖ ^ 2 ≤ D := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    dsimp [D]
    nlinarith [sq_nonneg (p.G / p.B)]
  have hGD : p.G ^ 2 ≤ p.B ^ 2 * D := by
    have he : p.B ^ 2 * (p.G / p.B) ^ 2 = p.G ^ 2 := by field_simp
    dsimp [D]
    nlinarith [mul_nonneg (sq_nonneg p.B) (sq_nonneg p.R)]
  have hrate := iid_accuracy p.toPublic g projection ν P hIID hg hpm hB hG hδ hδ1 ht
    hclosed.measurableSet hf hfm hx0 hpX hp hsub hgi hmi hm hu (fun x hx => hmin hx) hD hstart hGD
  have hacc := accuracy_budget hB hG hδ hδ1 hε ht hbudget
  have htail : (P : Measure (ℕ → p.Ω)) {ξ | p.ε < I.f (terminal p.toPublic g projection ξ) - I.f u} ≤
      ENNReal.ofReal p.δ := by
    apply (measure_mono ?_).trans hrate
    intro ξ hξ
    exact lt_of_le_of_lt hacc hξ
  have hexec := execute_terminal p.toPublic g projection P
  have hres : (fun seed : Unit × (ℕ → p.Ω) =>
      (execute (sampleOracle p.toPublic g projection P) (algorithm p.toPublic) (fun _ => (2 * p.T)) seed.1 seed.2)) =
      fun seed => terminal p.toPublic g projection seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact (hexec ξ)
  change spec.successful p I
      (fun seed : Unit × (ℕ → p.Ω) =>
        (execute (sampleOracle p.toPublic g projection P) (algorithm p.toPublic) (fun _ => (2 * p.T)) seed.1 seed.2))
      ⟨(Measure.dirac ()).prod (P : Measure (ℕ → p.Ω)), inferInstance⟩
  rw [hres]
  refine ⟨(terminal_measurable p.toPublic hg hpm).comp measurable_snd,
    fun seed => terminal_feasible p.toPublic g projection hpX hx0 seed.2, u, hu, hmin, ?_⟩
  have hsnd := measurePreserving_snd (μ := (Measure.dirac () : Measure Unit)) (ν := (P : Measure (ℕ → p.Ω)))
  exact (hsnd.measure_preimage_le {ξ | p.ε < I.f (terminal p.toPublic g projection ξ) - I.f u}).trans htail

end OracleTemplate.TerminalClipping
