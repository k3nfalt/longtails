import LongTails.Setups.FiniteDimensionalWeakMinty
import LongTails.Proofs.MintyPrefixLower
import LongTails.Proofs.MintyDimensionBudget

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyDimensionLowerBound

open LongTails.Setups.FiniteDimensionalWeakMinty MintyPrefixLower

def translated (p : Params) (z x : Space p) := p.L • (x-z)

lemma translated_admissible (p : Params) (hp : spec.valid p) (z : Space p)
    (hz : ‖z-p.x0‖ ≤ p.R) : spec.admissible p (translated p z) (exactOracle (translated p z)) := by
  have hL := hp.2.1
  refine ⟨fun _ _ _ => rfl, ?_, z, by simp [translated], hz, ?_⟩
  · intro x y
    rw [translated, translated, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hL]
  · intro x
    rw [translated, real_inner_smul_left, real_inner_self_eq_norm_sq, neg_mul]
    exact (neg_nonpos_of_nonneg (mul_nonneg hp.2.2.1 (sq_nonneg _))).trans
      (mul_nonneg hL.le (sq_nonneg _))

lemma zero_failure (p : Params) (hp : spec.valid p) (A : Algorithm (Space p) (Space p) (Space p)) :
    ∃ (F : Space p → Space p), spec.admissible p F (exactOracle F) ∧
      ¬spec.successful p F (fun w : A.Seed × (ℕ → Unit) =>
        execute (exactOracle F) A (fun _ => 0) w.1 w.2)
        ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩ := by
  have hL := hp.2.1
  have hR := pos_of_mul_pos_right (hp.2.2.2.2.1.trans hp.2.2.2.2.2) hL.le
  let i : Fin p.d := ⟨0, hp.1⟩
  let u : Space p := EuclideanSpace.single i p.R
  have hu : ‖u‖ = p.R := by simp [u, abs_of_pos hR]
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let g := fun (z : Space p) (w : A.Seed × (ℕ → Unit)) =>
    ‖translated p z (A.output (A.initial w.1))‖
  by_contra hf
  have hgood (z : Space p) (hz : ‖z-p.x0‖ ≤ p.R) :
      Integrable (g z) (P : Measure _) ∧ (∫ w, g z w ∂(P : Measure _)) ≤ p.ε := by
    have h : spec.successful p (translated p z) (fun w : A.Seed × (ℕ → Unit) =>
        execute (exactOracle (translated p z)) A (fun _ => 0) w.1 w.2) P := by
      by_contra hh
      exact hf ⟨_, translated_admissible p hp z hz, hh⟩
    exact h
  have h1 := hgood (p.x0+u) (by simp [hu])
  have h2 := hgood (p.x0-u) (by simp [sub_sub_cancel_left, hu])
  have hb : ∀ w, 2*p.L*p.R ≤ g (p.x0+u) w + g (p.x0-u) w := by
    intro w
    let x := A.output (A.initial w.1)
    have hh := norm_sub_le (x-(p.x0-u)) (x-(p.x0+u))
    rw [show x-(p.x0-u)-(x-(p.x0+u)) = (2:ℝ) • u by rw [two_smul]; abel,
      norm_smul, Real.norm_eq_abs, hu] at hh
    change _ ≤ ‖p.L • (x-(p.x0+u))‖ + ‖p.L • (x-(p.x0-u))‖
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    norm_num at hh
    nlinarith only [mul_le_mul_of_nonneg_left hh hL.le]
  have hi := integral_mono (μ := (P : Measure _)) (integrable_const _) (h1.1.add h2.1) hb
  rw [integral_const, probReal_univ, one_smul, integral_add h1.1 h2.1] at hi
  linarith only [hi, h1.2, h2.2, hp.2.2.2.2.2]

lemma failure (p : Params) (hp : spec.valid p) (A : Algorithm (Space p) (Space p) (Space p))
    (N : ℕ) (hN : N ≤ ⌊(p.d : ℝ) * Real.log (1 + (p.L*p.R/p.ε)^2/p.d) / 2^22⌋₊) :
    ∃ (F : Space p → Space p), spec.admissible p F (exactOracle F) ∧
      ¬spec.successful p F (fun w : A.Seed × (ℕ → Unit) =>
        execute (exactOracle F) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩ := by
  by_cases h : N = 0
  · subst N
    exact zero_failure p hp A
  have hL := hp.2.1
  have hε := hp.2.2.2.2.1
  have ht := div_pos (hε.trans hp.2.2.2.2.2) hε
  obtain ⟨k, m, hk, hkd, hm, hr, hc⟩ := MintyDimensionBudget.packing hp.1 ht (Nat.pos_of_ne_zero h)
    (by norm_num at hN ⊢; exact hN)
  cases k with
  | zero => omega
  | succ k =>
    refine some_failure p hp (Fin.castLEEmb hkd) (s := 8*p.ε/p.L) (by positivity)
      (by field_simp; linarith) ?_ A N (by omega : 0 < m) hc
    apply (mul_le_mul_iff_left₀ hL).mp
    have hb := (le_div_iff₀ hε).mp hr
    push_cast at hb
    field_simp
    nlinarith only [hb]

end LongTails.Proofs.MintyDimensionLowerBound
