import LongTails.Proofs.InterpolatedFiniteSumLinkLower
import LongTails.Proofs.InterpolatedFiniteSumLinkLength
import LongTails.Proofs.InterpolatedFiniteSumLinkBudget

open OracleTemplate MeasureTheory Classical
open LongTails LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

namespace LongTails.Proofs.InterpolatedFiniteSumLinkTuning

set_option maxHeartbeats 1600000 in
lemma link_failure (p : Params) (hp : spec.valid p) (hL : 0 < p.L1) (t : ℝ)
    (ht : 1 ≤ t) (hid : p.L1 * p.R = 64 * t * Real.sqrt t)
    (hq : 64 ≤ p.L1 * p.R) (hg : 4 * t ≤ (p.n / 2 : ℕ))
    (heta : Real.log (1 + 8 * (p.n / 2 : ℕ) * p.ε * p.L1 ^ 2 / p.L0) ≤ t / 8)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : (b : ℝ) ≤ (p.n / 2 : ℕ) * t /
      (4096 * (1 + Real.log (1 + 8 * (p.n / 2 : ℕ) * p.ε * p.L1 ^ 2 / p.L0)) ^ 2)) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let g := p.n / 2
  let δ := p.L0 / (4 * p.L1 ^ 2)
  let η := Real.log (1 + 8 * (g : ℝ) * p.ε * p.L1 ^ 2 / p.L0)
  have hgpos : 0 < g := by have := hp.2.2.2.2.1; dsimp [g]; omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos hp.1 (by positivity)
  have hL0 := hp.1
  have hε := hp.2.2.2.1
  have hR := hp.2.2.1
  have hη : 0 < η := by
    apply Real.log_pos
    have hh : 0 < 8 * (g : ℝ) * p.ε * p.L1 ^ 2 / p.L0 := by positivity
    linarith
  have hexp : δ * Real.exp η = δ + 2 * (g : ℝ) * p.ε := by
    dsimp [η]
    rw [Real.exp_log (by positivity)]
    dsimp [δ]
    field_simp
    ring
  obtain ⟨hT, htT, hTt⟩ := InterpolatedFiniteSumLinkLength.length_bounds t ht
  let k := ⌈t⌉₊ - 1
  have hk : k + 1 = ⌈t⌉₊ := by dsimp [k]; omega
  have htwo : 2 * (k + 1) ≤ g := by
    have hh : 2 * (⌈t⌉₊ : ℝ) ≤ g := by linarith
    rw [hk]
    exact_mod_cast hh
  obtain ⟨hd, hw, hshape, hTq⟩ :=
    InterpolatedFiniteSumLinkLength.shape_conditions (p.L1 * p.R) t η ht hη.le heta hid
  have hs : Real.sqrt (⌈t⌉₊ : ℝ) ≤ 2 * Real.sqrt t := by
    have h1 := Real.sq_sqrt (Nat.cast_nonneg ⌈t⌉₊)
    have h2 := Real.sq_sqrt (show 0 ≤ t by linarith)
    have h3 := Real.sqrt_nonneg t
    have h4 := Real.sqrt_nonneg (⌈t⌉₊ : ℝ)
    nlinarith
  have hcost := InterpolatedFiniteSumLinkBudget.small_budget g ⌈t⌉₊ b hgpos hT δ η p.ε p.L1 p.R t
    hδ hη hε hL hR (by linarith) hexp hd hs hid hb
  have hbT : b ≤ g * (k + 1) := by
    have hden : 1 ≤ 4096 * (1 + η) ^ 2 := by nlinarith only [hη, sq_nonneg η]
    have hh : (b : ℝ) ≤ (g : ℝ) * t := hb.trans (div_le_self (by positivity) hden)
    have hm := mul_le_mul_of_nonneg_left htT hgR.le
    rw [hk]
    exact_mod_cast hh.trans hm
  apply InterpolatedFiniteSumLinkLower.tuned_failure p hp hL δ η hδ rfl hη.le hexp htwo hq
    (by simpa only [hk] using hd) (by simpa only [hk] using hw)
    (by simpa only [hk] using hshape) (by simpa only [hk] using hTq) A b hbT
  simpa only [hk] using hcost

end LongTails.Proofs.InterpolatedFiniteSumLinkTuning
