import LongTails.Proofs.AdamFinitePaths

namespace LongTails.Proofs.AdamFiniteLower

open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Proofs.AdamScalarProcess LongTails.Proofs.AdamFinitePaths

lemma finite_cost (p : Public) (hp : spec.valid p) (a : AdamTuning) (ha : a.Valid)
    {B T : ℕ} (hB : 0 < B)
    (hsuccess : let ℓ := p.L / 2;
      let c := 4 * p.ε / ((p.r : ℝ) - 1);
      let w := 8 * p.ε / p.L;
      let D := p.Δ / (4 * p.ε);
      let z := fun (ω : Fin (T + 1) → Fin B → Bool) => trajectory a p.r ℓ c w D (pathNoise p.ε B (T + 1) ω);
      (∑ j : Fin (T + 1), ∑ ω : Fin (T + 1) → Fin B → Bool,
        (ℓ * |(z ω j).stiff| + ((p.r : ℝ) - 1) * |c * SeparationInstance.valleySlope w D (z ω j).quiet|)) ≤
        (T + 1 : ℕ) * (Fintype.card (Fin (T + 1) → Fin B → Bool) : ℝ) * p.ε) :
    (p.r - 1 : ℕ) ≤ 64 * (B * (T + 1) : ℝ) ^ 2 ∨
      (p.r - 1 : ℕ) * p.L * p.Δ ≤ 4096 * p.ε ^ 2 * (B * (T + 1) : ℝ) ^ 3 := by
  obtain ⟨hr, hL, hΔ, hε, hgap⟩ := hp
  have hr' : 0 < (p.r : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < p.r - 1 by omega)
  have hrc : (p.r - 1 : ℕ) = (p.r : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hr0 : 0 < (p.r : ℝ) := by linarith
  have hΔ' : 0 < p.Δ := by nlinarith [sq_pos_of_pos hε]
  let R : ℝ := (p.r : ℝ) - 1
  let ℓ := p.L / 2
  let c := 4 * p.ε / R
  let w := 8 * p.ε / p.L
  let D := p.Δ / (4 * p.ε)
  let C : ℝ := Fintype.card (Fin (T + 1) → Fin B → Bool)
  let ξ := pathNoise p.ε B (T + 1)
  let z := fun (ω : Fin (T + 1) → Fin B → Bool) => trajectory a p.r ℓ c w D (ξ ω)
  let S := ∑ j ∈ Finset.range (T + 1), ∑ ω, |(z ω j).stiff|
  let V := a.η * ∑ j ∈ Finset.range T, ∑ ω,
    |diagDirection a p.r ℓ c w D (ξ ω) j - offDirection a p.r ℓ c w D (ξ ω) j|
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Fintype.card_pos
  have hℓ : 0 ≤ ℓ := by dsimp [ℓ]; positivity
  have hc : 0 ≤ c := by dsimp [c, R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hR : R ≠ 0 := hr'.ne'
  have hRc : R * c = 4 * p.ε := by dsimp [c]; field_simp
  have hDw : 2 * w ≤ D := by
    dsimp [w, D]
    rw [le_div_iff₀ (by positivity)]
    have heq : 2 * (8 * p.ε / p.L) * (4 * p.ε) = 64 * p.ε ^ 2 / p.L := by ring
    rw [heq]
    exact (div_le_iff₀ hL).mpr (by nlinarith [sq_nonneg p.ε])
  have hcs : p.ε / (p.r : ℝ) ≤ c := by
    dsimp [c, R]
    apply (div_le_div_iff₀ hr0 hr').mpr
    nlinarith
  change (∑ j : Fin (T + 1), ∑ ω, (ℓ * |(z ω j).stiff| +
    R * |c * SeparationInstance.valleySlope w D (z ω j).quiet|)) ≤ (T + 1 : ℕ) * C * p.ε at hsuccess
  have hS : ℓ * S ≤ (T + 1 : ℕ) * C * p.ε := by
    have hh : (∑ j : Fin (T + 1), ∑ ω, ℓ * |(z ω j).stiff|) ≤
        (T + 1 : ℕ) * C * p.ε := by
      apply le_trans (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun ω _ => ?_))) hsuccess
      have hq : 0 ≤ R * |c * SeparationInstance.valleySlope w D (z ω j).quiet| := mul_nonneg hr'.le (abs_nonneg _)
      linarith
    simpa only [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => ∑ ω, |(z ω j).stiff|) (T + 1)] using hh
  have hQ : (∑ j : Fin (T + 1), ∑ ω, R * |c * SeparationInstance.valleySlope w D (z ω j).quiet|) ≤
      (T + 1 : ℕ) * C * p.ε := by
    apply le_trans (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun ω _ => ?_))) hsuccess
    have := mul_nonneg hℓ (abs_nonneg (z ω j).stiff)
    linarith
  have hV : C * D / 4 ≤ V := path_success_travel a ha.1.le p.r ℓ R c w D p.ε
    hr'.le hc hw hD hε hRc hDw B T hQ
  have hkEq : 8 * c * B * T ^ 2 / p.ε = 32 * B * T ^ 2 / R := by
    dsimp [c]
    field_simp
    ring
  have hcost := AdamTravelBound.cost_dichotomy (R := R) (L := p.L) (Δ := p.Δ)
    (ε := p.ε) (V := V / C) (S := S / C) (B := B) (T := T) hr' hL hε hB
    (by
      rw [← mul_div_assoc, div_le_iff₀ hC]
      change ℓ * S ≤ _
      convert hS using 1
      push_cast
      ring)
    (by
      rw [le_div_iff₀ hC]
      convert hV using 1
      dsimp [D]
      ring)
    (by
      intro hk
      have ht := path_travel_bound a ha hr0 ℓ c w D p.ε hε hcs hB (by rwa [hkEq])
      change V ≤ 4 * (8 * c * B * T ^ 2 / p.ε) * S at ht
      rw [hkEq] at ht
      exact (div_le_div_of_nonneg_right ht hC.le).trans_eq (by ring))
  simpa only [hrc, R] using hcost

end LongTails.Proofs.AdamFiniteLower
