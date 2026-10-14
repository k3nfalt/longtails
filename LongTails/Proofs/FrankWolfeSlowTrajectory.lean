import LongTails.Proofs.FrankWolfeNormalized

open Set

namespace OracleTemplate.FrankWolfe.HardDynamics

noncomputable def normalizedOrbit (q r m start : ℝ) : ℕ → ℝ × ℝ
  | 0 => (start, 1)
  | n + 1 =>
    let p := normalizedOrbit q r m start n
    (p.1 * (1 - radial q r m p.1 p.2 * p.1 ^ (r - 2 / q)), transverse q r m p.1 p.2)

lemma normalizedOrbit_invariant {q r m δ radius start : ℝ}
    (hq : 3 < q) (hr : 2 < r) (hδ : 0 ≤ δ) (hstart : 0 < start) (hstartmax : start ≤ radius)
    (hstable : ∀ u ∈ Icc (0 : ℝ) radius, ∀ v ∈ Icc (1 - δ) (1 + δ),
      0 < radial q r m u v ∧
      (r - 2 / q + 1) * radial q r m u v * u ^ (r - 2 / q) ≤ 1 / 2 ∧
      |transverse q r m u v - 1| ≤ δ) (n : ℕ) :
    0 < (normalizedOrbit q r m start n).1 ∧ (normalizedOrbit q r m start n).1 ≤ start ∧
      (normalizedOrbit q r m start n).2 ∈ Icc (1 - δ) (1 + δ) := by
  induction n with
  | zero => simp only [normalizedOrbit]; exact ⟨hstart, le_rfl, by constructor <;> linarith⟩
  | succ n ih =>
    let u := (normalizedOrbit q r m start n).1
    let v := (normalizedOrbit q r m start n).2
    obtain ⟨hc, hsmall, hV⟩ := hstable u ⟨ih.1.le, ih.2.1.trans hstartmax⟩ v ih.2.2
    have he := (exponents_pos hq hr).1
    let ρ := radial q r m u v * u ^ (r - 2 / q)
    have hρ : 0 ≤ ρ := mul_nonneg hc.le (Real.rpow_nonneg ih.1.le _)
    have hs : (r - 2 / q + 1) * ρ ≤ 1 / 2 := by simpa [ρ, mul_assoc] using hsmall
    have hρ1 : ρ < 1 := by nlinarith [mul_nonneg he.le hρ]
    change 0 < u * (1 - ρ) ∧ u * (1 - ρ) ≤ start ∧ _
    refine ⟨mul_pos ih.1 (by linarith), ?_, ?_⟩
    · have : u * (1 - ρ) ≤ u := by nlinarith [mul_nonneg ih.1.le hρ]
      exact this.trans ih.2.1
    · change transverse q r m u v ∈ Icc (1 - δ) (1 + δ)
      obtain ⟨hlo, hhi⟩ := abs_le.mp hV
      constructor <;> linarith

lemma normalizedOrbit_reciprocal_bound {q r m δ radius start : ℝ}
    (hq : 3 < q) (hr : 2 < r) (hδ : 0 ≤ δ)
    (hstart : 0 < start) (hstartmax : start ≤ radius)
    (hstable : ∀ u ∈ Icc (0 : ℝ) radius, ∀ v ∈ Icc (1 - δ) (1 + δ),
      0 < radial q r m u v ∧ radial q r m u v ≤ 32 * m ∧
      (r - 2 / q + 1) * radial q r m u v * u ^ (r - 2 / q) ≤ 1 / 2 ∧
      |transverse q r m u v - 1| ≤ δ) (n : ℕ) :
    (normalizedOrbit q r m start n).1 ^ (-(r - 2 / q)) ≤
      start ^ (-(r - 2 / q)) + 64 * (r - 2 / q) * m * n := by
  let u := fun n => (normalizedOrbit q r m start n).1
  let v := fun n => (normalizedOrbit q r m start n).2
  let c := fun n => radial q r m (u n) (v n)
  have hinv := normalizedOrbit_invariant hq hr hδ hstart hstartmax
    (fun u hu v hv => ⟨(hstable u hu v hv).1, (hstable u hu v hv).2.2⟩)
  have hs := fun n => hstable (u n) ⟨(hinv n).1.le, (hinv n).2.1.trans hstartmax⟩ (v n) (hinv n).2.2
  have he := (exponents_pos hq hr).1
  have hρ : ∀ n, 0 ≤ c n * u n ^ (r - 2 / q) := by
    intro n
    exact mul_nonneg (hs n).1.le (Real.rpow_nonneg (hinv n).1.le _)
  have hsmall : ∀ n, c n * u n ^ (r - 2 / q) < 1 := by
    intro n
    have hh := (hs n).2.2.1
    have heρ := mul_nonneg he.le (hρ n)
    dsimp [c] at heρ ⊢
    nlinarith
  have hf : ∀ n, (1 - c n * u n ^ (r - 2 / q)) ^ (-(r - 2 / q) - 1) ≤ 2 := by
    intro n
    have hh := negative_power_le_two (p := r - 2 / q + 1) (by linarith) (hsmall n)
      (by simpa [c, mul_assoc] using (hs n).2.2.1)
    rw [show -(r - 2 / q) - 1 = -(r - 2 / q + 1) by ring]
    exact hh
  have hbound := reciprocal_power_trajectory (u := u) (c := c) (p := r - 2 / q)
    (lower := 0) (upper := 32 * m) he.le le_rfl (fun n => (hinv n).1)
    (fun n => ⟨(hs n).1.le, (hs n).2.1⟩) hsmall hf (fun n => rfl) n
  have h := hbound.2
  change u n ^ (-(r - 2 / q)) ≤ _
  change u n ^ (-(r - 2 / q)) ≤ start ^ (-(r - 2 / q)) + 2 * (r - 2 / q) * (32 * m) * n at h
  convert h using 1; ring

end OracleTemplate.FrankWolfe.HardDynamics
