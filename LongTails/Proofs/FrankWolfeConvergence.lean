import LongTails.Proofs.Execution
import LongTails.Proofs.FrankWolfeRate
import LongTails.Proofs.FrankWolfeExecution

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe

open LongTails.Setups.UniformlyConvexHolder

noncomputable def path (p : Public) (O : Oracle (p.E ⊕ p.E) p.E)
    (ξ : (k : ℕ) → O.Seed k) : ℕ → p.E
  | 0 => p.x0
  | n + 1 => shortStep p.L (path p O ξ n)
      (O.answer (2 * n) (0, (Sum.inl (path p O ξ n))) (ξ (2 * n)))
      (O.answer (2 * n + 1)
        (0, (Sum.inr (O.answer (2 * n) (0, (Sum.inl (path p O ξ n))) (ξ (2 * n))))) (ξ (2 * n + 1)))

lemma path_properties (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (p.E ⊕ p.E) p.E) (hO : spec.admissible p I O)
    (ξ : (k : ℕ) → O.Seed k) :
    ∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧
      (∀ n, path p.toPublic O ξ n ∈ I.C) ∧
      (∀ n, 0 ≤ I.f (path p.toPublic O ξ n) - I.f xstar) ∧
      I.f (path p.toPublic O ξ 1) - I.f xstar ≤ p.L * p.D ^ 2 ∧
      (∀ n, I.f (path p.toPublic O ξ (n + 1)) - I.f xstar ≤
        I.f (path p.toPublic O ξ n) - I.f xstar -
        min ((I.f (path p.toPublic O ξ n) - I.f xstar) / 2)
          ((I.f (path p.toPublic O ξ n) - I.f xstar) ^ (2 - 2 / (p.q * p.r)) /
            (2 * p.L * (2 * p.c / p.a) ^ (2 / p.q)))) := by
  rcases hp with ⟨hL, hD, ha, hq, hc, hr, hε⟩
  rcases hO with ⟨hcompact, hC, hx0, hdiam, hf, hg, hlip, hlmo, xstar, hxstar, hmin, herror⟩
  have hmem : ∀ n, path p.toPublic O ξ n ∈ I.C := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih =>
      exact short_step_mem hC.convex hL ih (hlmo _ _ _).1 ((hlmo _ _ _).2 _ ih)
  refine ⟨xstar, hxstar, hmin, hmem, fun n => sub_nonneg.mpr (hmin (hmem n)), ?_, ?_⟩
  · exact short_step_first_gap hC.convex hL hf (hg 0 (ξ 0)) (hlip 0 (ξ 0))
      hx0 (hlmo 1 (ξ 1) _).1 hxstar (hlmo 1 (ξ 1) _).2
      (hdiam _ (hlmo 1 (ξ 1) _).1 _ hx0)
  · intro n
    obtain ⟨y, hy, hmy, hdist⟩ := herror _ (hmem n)
    have heq : I.f y = I.f xstar := le_antisymm (hmy hxstar) (hmin hy)
    have hs := short_step_holder_decrease hL ha hc hq hr hC hf
      (hg (2 * n) (ξ (2 * n))) (hlip (2 * n) (ξ (2 * n)))
      (hmem n) (hlmo (2 * n + 1) (ξ (2 * n + 1)) _).1 hy hmy
      (hlmo (2 * n + 1) (ξ (2 * n + 1)) _).2 (by simpa [heq] using hdist)
    simpa only [path, heq] using hs

lemma bounded_power_recurrence {h : ℕ → ℝ} {H p B : ℝ}
    (hH : 0 < H) (hp : 0 < p) (hB : 0 < B) (hnonneg : ∀ n, 0 ≤ h n)
    (hfirst : h 1 ≤ H)
    (hstep : ∀ n, h (n + 1) ≤ h n - min (h n / 2) (h n ^ (1 + p) / B)) :
    ∀ n, h (n + 2) ≤ h (n + 1) - h (n + 1) ^ (1 + p) / (2 * H ^ p + B) := by
  have hmono : ∀ n, h (n + 1) ≤ h n := by
    intro n
    have hm : 0 ≤ min (h n / 2) (h n ^ (1 + p) / B) := le_min (div_nonneg (hnonneg n) (by norm_num))
      (div_nonneg (Real.rpow_nonneg (hnonneg n) _) hB.le)
    have := hstep n
    linarith
  have hb : ∀ n, h (n + 1) ≤ H := by
    intro n
    induction n with
    | zero => simpa using hfirst
    | succ n ih => exact (hmono (n + 1)).trans ih
  intro n
  have hm := minimum_power_decrease (hnonneg (n + 1)) hH (hb n) hp hB
  have hs := hstep (n + 1)
  linarith

lemma path_accuracy (p : Params) (hp : spec.valid p) (I : Instance p.toPublic)
    (O : Oracle (p.E ⊕ p.E) p.E) (hO : spec.admissible p I O)
    (ξ : (k : ℕ) → O.Seed k) (N : ℕ)
    (hN : (4 * (p.L * p.D ^ 2) ^ (1 - 2 / (p.q * p.r)) +
      4 * p.L * (2 * p.c / p.a) ^ (2 / p.q)) * p.ε ^ (-(1 - 2 / (p.q * p.r))) ≤ N) :
    ∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧
      path p.toPublic O ξ (N + 1) ∈ I.C ∧
      I.f (path p.toPublic O ξ (N + 1)) - I.f xstar ≤ p.ε := by
  obtain ⟨xstar, hxstar, hmin, hmem, hnonneg, hfirst, hstep⟩ := path_properties p hp I O hO ξ
  rcases hp with ⟨hL, hD, ha, hq, hc, hr, hε⟩
  have hqr : 4 < p.q * p.r := by nlinarith
  have hqrpos : 0 < p.q * p.r := by positivity
  have he : 1 / 2 < 1 - 2 / (p.q * p.r) := by
    have := (div_lt_iff₀ hqrpos).mpr (show 2 < (1 / 2 : ℝ) * (p.q * p.r) by linarith)
    linarith
  have he0 : 0 < 1 - 2 / (p.q * p.r) := by linarith
  have hH : 0 < p.L * p.D ^ 2 := by positivity
  have hB : 0 < 2 * p.L * (2 * p.c / p.a) ^ (2 / p.q) := by positivity
  have hs := bounded_power_recurrence hH he0 hB hnonneg hfirst
    (by simpa only [show 1 + (1 - 2 / (p.q * p.r)) = 2 - 2 / (p.q * p.r) by ring] using hstep)
  refine ⟨xstar, hxstar, hmin, hmem _, ?_⟩
  apply accuracy_of_power_descent (h := fun n => I.f (path p.toPublic O ξ (n + 1)) - I.f xstar)
    he (by positivity) hε (fun n => hnonneg _) hs N
  convert hN using 1; ring

lemma convergence : Convergence spec (fun p _ => 2 * (1 + ⌈(4 * (p.L * p.D ^ 2) ^ (1 - 2 / (p.q * p.r)) + 4 * p.L * (2 * p.c / p.a) ^ (2 / p.q)) * p.ε ^ (-(1 - 2 / (p.q * p.r)))⌉₊)) := by
  apply convergence_of_block_budget (S := spec) (fun p => 1 + ⌈(4 * (p.L * p.D ^ 2) ^ (1 - 2 / (p.q * p.r)) + 4 * p.L * (2 * p.c / p.a) ^ (2 / p.q)) * p.ε ^ (-(1 - 2 / (p.q * p.r)))⌉₊)
    (fun _ => 2)
  refine ⟨fun p => shortStepFrankWolfe p.L p.x0, ?_, fun _ _ => rfl⟩
  intro p hp K hK
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ K by omega)
  intro I O hO
  have hex : ∀ ξ : (k : ℕ) → O.Seed k,
      execute O (shortStepFrankWolfe p.L p.x0) (fun _ => (2 * (1 + N))) () ξ =
        path p.toPublic O ξ (N + 1) := by
    intro ξ
    simpa only [Nat.add_comm 1 N] using
      execute_short_step_even O p.L p.x0 ξ (path p.toPublic O ξ) rfl (fun _ => rfl) (1 + N)
  obtain ⟨xstar, hxstar, hmin, _⟩ := hO.2.2.2.2.2.2.2.2
  refine ⟨xstar, hxstar, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, ξ⟩
  change (execute O (shortStepFrankWolfe p.L p.x0) (fun _ => (2 * (1 + N))) () ξ) ∈ I.C ∧
    I.f (execute O (shortStepFrankWolfe p.L p.x0) (fun _ => (2 * (1 + N))) () ξ) - I.f xstar ≤ p.ε
  rw [hex]
  obtain ⟨y, hy, hmy, hmem, hacc⟩ := path_accuracy p hp I O hO ξ N ((Nat.le_ceil _).trans (Nat.cast_le.mpr (show ⌈(4 * (p.L * p.D ^ 2) ^ (1 - 2 / (p.q * p.r)) + 4 * p.L * (2 * p.c / p.a) ^ (2 / p.q)) * p.ε ^ (-(1 - 2 / (p.q * p.r)))⌉₊ ≤ N by omega)))
  have heq : I.f y = I.f xstar := le_antisymm (hmy hxstar) (hmin hy)
  exact ⟨hmem, by simpa [heq] using hacc⟩

end OracleTemplate.FrankWolfe
