import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.BilevelEpochEnergy

open Finset

lemma scalar_energy_identity {η θ lam g δ zp z zn : ℝ} (hη : η ≠ 0)
    (hstep : zn = z + (1 - θ) * (z - zp) -
      η * (g + lam * (z + (1 - θ) * (z - zp)) + δ)) :
    (g * zn + lam / 2 * zn ^ 2) - (g * z + lam / 2 * z ^ 2) +
      ((1 - θ) * (1 / η - lam) / 2) * ((zn - z) ^ 2 - (z - zp) ^ 2) =
      -((1 - θ) * (1 / η - lam) / 2) * ((zn - z) - (z - zp)) ^ 2 -
        (θ / η + (1 / 2 - θ) * lam) * (zn - z) ^ 2 - δ * (zn - z) := by
  have hg : g = (z + (1 - θ) * (z - zp) - zn) / η -
      lam * (z + (1 - θ) * (z - zp)) - δ := by
    field_simp
    nlinarith [hstep]
  rw [hg]
  field_simp
  ring

lemma weak_scalar_energy_step {η θ lam g δ zp z zn : ℝ}
    (hη : 0 < η) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hlower : -θ / η ≤ lam) (hupper : η * lam ≤ 1 / 4)
    (hstep : zn = z + (1 - θ) * (z - zp) -
      η * (g + lam * (z + (1 - θ) * (z - zp)) + δ)) :
    (g * zn + lam / 2 * zn ^ 2) - (g * z + lam / 2 * z ^ 2) +
      ((1 - θ) * (1 / η - lam) / 2) * ((zn - z) ^ 2 - (z - zp) ^ 2) ≤
      -(3 * θ / (8 * η)) * (zn - z) ^ 2 + (2 * η / θ) * δ ^ 2 := by
  rw [scalar_energy_identity hη.ne' hstep]
  have hc : 0 ≤ (1 - θ) * (1 / η - lam) / 2 := by
    have hh : lam ≤ 1 / η := (le_div_iff₀ hη).mpr (by nlinarith)
    exact div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hh)) (by norm_num)
  have hbracket : θ / (2 * η) ≤ θ / η + (1 / 2 - θ) * lam := by
    have hm := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 1 / 2 - θ by linarith)
    have hp : 0 ≤ θ ^ 2 / η := by positivity
    have he : θ / η + (1 / 2 - θ) * (-θ / η) = θ / (2 * η) + θ ^ 2 / η := by ring
    linarith
  have hyoung : -δ * (zn - z) ≤ θ / (8 * η) * (zn - z) ^ 2 + 2 * η / θ * δ ^ 2 := by
    have hh := sq_nonneg (θ * (zn - z) + 4 * η * δ)
    apply (mul_le_mul_iff_right₀ (show 0 < 8 * η * θ by positivity)).mp
    field_simp
    nlinarith
  have hdrop := mul_nonneg hc (sq_nonneg ((zn - z) - (z - zp)))
  have hm := mul_le_mul_of_nonneg_right hbracket (sq_nonneg (zn - z))
  have he : θ / (2 * η) - θ / (8 * η) = 3 * θ / (8 * η) := by ring
  nlinarith


lemma negative_scalar_identity {η θ lam a δ d dn : ℝ} (hη : η ≠ 0)
    (hstep : dn = (1 - θ) * d - η * (a + lam * (1 - θ) * d + δ)) :
    a * dn - (1 - θ) * ((a - lam * d) * d) - η * δ ^ 2 / 2 =
      -(1 - θ) * (-η * lam) * (d ^ 2 + (d - η * a) ^ 2) / (2 * η) -
        η * (1 - (1 - θ) * (-η * lam)) * a ^ 2 / 2 - η * (a + δ) ^ 2 / 2 := by
  rw [hstep]
  field_simp
  ring

lemma negative_scalar_step {η θ lam a δ d dn : ℝ}
    (hη : 0 < η) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlam : lam ≤ 0) (hcurv : -η * lam ≤ 1)
    (hstep : dn = (1 - θ) * d - η * (a + lam * (1 - θ) * d + δ)) :
    a * dn ≤ (1 - θ) * ((a - lam * d) * d) + η * δ ^ 2 / 2 := by
  have hh := negative_scalar_identity hη.ne' hstep
  have hb : 0 ≤ 1 - θ := by linarith
  have hl : 0 ≤ -η * lam := by nlinarith
  have hbl : (1 - θ) * (-η * lam) ≤ 1 := by
    calc (1 - θ) * (-η * lam) ≤ 1 * 1 := mul_le_mul (by linarith) hcurv hl zero_le_one
      _ = 1 := one_mul _
  have h1 : 0 ≤ (1 - θ) * (-η * lam) * (d ^ 2 + (d - η * a) ^ 2) / (2 * η) := by positivity
  have h2 : 0 ≤ η * (1 - (1 - θ) * (-η * lam)) * a ^ 2 / 2 := by positivity
  have h3 : 0 ≤ η * (a + δ) ^ 2 / 2 := by positivity
  have he : -(1 - θ) * (-η * lam) * (d ^ 2 + (d - η * a) ^ 2) / (2 * η) =
      -((1 - θ) * (-η * lam) * (d ^ 2 + (d - η * a) ^ 2) / (2 * η)) := by ring
  rw [he] at hh
  linarith

lemma negative_scalar_initial {η a δ : ℝ} (hη : 0 ≤ η) :
    a * (-η * (a + δ)) ≤ η * δ ^ 2 / 2 := by
  have h1 := mul_nonneg hη (sq_nonneg a)
  have h2 := mul_nonneg hη (sq_nonneg (a + δ))
  nlinarith

lemma envelope_mass_identity (R δ : ℕ → ℝ) (β θ c : ℝ) (h0 : R 0 = 0)
    (hrec : ∀ k, R (k + 1) = β * R k + c * δ k ^ 2) (hθ : θ + β = 1) (m : ℕ) :
    θ * (∑ k ∈ range m, R (k + 1)) + β * R m = c * ∑ k ∈ range m, δ k ^ 2 := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ]
    calc
      _ = θ * (∑ k ∈ range m, R (k + 1)) + (θ + β) * R (m + 1) := by ring
      _ = θ * (∑ k ∈ range m, R (k + 1)) + β * R m + c * δ m ^ 2 := by rw [hθ, one_mul, hrec]; ring
      _ = _ := by rw [ih]; ring

lemma envelope_sum_bound (R δ b : ℕ → ℝ) {β θ c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hθ : 0 < θ) (hθβ : θ + β = 1) (h0 : R 0 = 0)
    (hrec : ∀ k, R (k + 1) = β * R k + c * δ k ^ 2)
    (hb0 : b 0 ≤ c * δ 0 ^ 2) (m : ℕ)
    (hb : ∀ k, k + 1 < m → b (k + 1) ≤ β * b k + c * δ (k + 1) ^ 2) :
    (∑ k ∈ range m, b k) ≤ c / θ * ∑ k ∈ range m, δ k ^ 2 := by
  have hR : ∀ k, 0 ≤ R k := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [hrec]; positivity
  have hdom : ∀ k, k < m → b k ≤ R (k + 1) := by
    intro k
    induction k with
    | zero => intro _; simpa [hrec, h0] using hb0
    | succ k ih =>
      intro hk
      rw [hrec (k + 1)]
      exact (hb k hk).trans (add_le_add (mul_le_mul_of_nonneg_left (ih (by omega)) hβ) le_rfl)
  have hs : (∑ k ∈ range m, b k) ≤ ∑ k ∈ range m, R (k + 1) :=
    sum_le_sum (fun k hk => hdom k (mem_range.mp hk))
  have hm := envelope_mass_identity R δ β θ c h0 hrec hθβ m
  have hn := mul_nonneg hβ (hR m)
  have ht := mul_le_mul_of_nonneg_right hs hθ.le
  calc
    (∑ k ∈ range m, b k) ≤ (c * ∑ k ∈ range m, δ k ^ 2) / θ :=
      (le_div_iff₀ hθ).mpr (by nlinarith)
    _ = _ := by ring

lemma weak_scalar_epoch {η θ lam g : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) (hlower : -θ / η ≤ lam) (hupper : η * lam ≤ 1 / 4)
    (z d δ : ℕ → ℝ) (m : ℕ) (hz0 : z 0 = 0) (hd0 : d 0 = 0)
    (hpos : ∀ k, k < m → z (k + 1) = z k + d (k + 1))
    (hvel : ∀ k, k < m → d (k + 1) = (1 - θ) * d k -
      η * (g + lam * (z k + (1 - θ) * d k) + δ k)) :
    g * z m + lam / 2 * (z m) ^ 2 ≤
      -(3 * θ / (8 * η)) * (∑ k ∈ range m, (d (k + 1)) ^ 2) +
      (2 * η / θ) * ∑ k ∈ range m, (δ k) ^ 2 := by
  let c := (1 - θ) * (1 / η - lam) / 2
  let P := fun k => g * z k + lam / 2 * (z k) ^ 2 + c * (d k) ^ 2
  have hc : 0 ≤ c := by
    have hl : lam ≤ 1 / η := (le_div_iff₀ hη).mpr (by nlinarith)
    dsimp [c]
    exact div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hl)) (by norm_num)
  have hstep : ∀ k, k < m → P (k + 1) - P k ≤
      -(3 * θ / (8 * η)) * (d (k + 1)) ^ 2 + (2 * η / θ) * (δ k) ^ 2 := by
    intro k hk
    have hs : z (k + 1) = z k + (1 - θ) * (z k - (z k - d k)) -
        η * (g + lam * (z k + (1 - θ) * (z k - (z k - d k))) + δ k) := by
      rw [hpos k hk, hvel k hk]
      ring
    have hh := weak_scalar_energy_step hη hθ hθhalf hlower hupper hs
    have he : z (k + 1) - z k = d (k + 1) := by rw [hpos k hk]; ring
    simp only [he, sub_sub_cancel] at hh
    dsimp [P, c]
    nlinarith only [hh]
  have hs := sum_le_sum (s := range m) (fun k hk => hstep k (mem_range.mp hk))
  rw [sum_range_sub, sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  have hp0 : P 0 = 0 := by simp [P, hz0, hd0]
  rw [hp0, sub_zero] at hs
  have hn := mul_nonneg hc (sq_nonneg (d m))
  dsimp [P] at hs
  linarith

lemma negative_scalar_epoch {η θ lam g : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    (hθhalf : θ ≤ 1 / 2) (hlower : lam < -θ / η) (hcurv : -η * lam ≤ 1)
    (z d δ : ℕ → ℝ) (m : ℕ) (hz0 : z 0 = 0) (hd0 : d 0 = 0)
    (hpos : ∀ k, k < m → z (k + 1) = z k + d (k + 1))
    (hvel : ∀ k, k < m → d (k + 1) = (1 - θ) * d k -
      η * (g + lam * (z k + (1 - θ) * d k) + δ k)) :
    g * z m + lam / 2 * (z m) ^ 2 ≤
      -(3 * θ / (8 * η)) * (∑ k ∈ range m, (d (k + 1)) ^ 2) +
      (2 * η / θ) * ∑ k ∈ range m, (δ k) ^ 2 := by
  by_cases hm : m = 0
  · simp [hm, hz0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hβ : 0 ≤ 1 - θ := by linarith
  rw [neg_div] at hlower
  have hlam : lam ≤ 0 := by have hh : 0 < θ / η := div_pos hθ hη; linarith
  let b := fun k => (g + lam * z k) * d (k + 1)
  let R : ℕ → ℝ := Nat.rec 0 (fun k v => (1 - θ) * v + (η / 2) * (δ k) ^ 2)
  have hR0 : R 0 = 0 := rfl
  have hRrec : ∀ k, R (k + 1) = (1 - θ) * R k + (η / 2) * (δ k) ^ 2 := fun _ => rfl
  have hb0 : b 0 ≤ (η / 2) * (δ 0) ^ 2 := by
    have hs := hvel 0 hmpos
    simp only [hd0, hz0, mul_zero, add_zero, zero_sub] at hs
    dsimp [b]
    rw [hz0, mul_zero, add_zero, hs]
    nlinarith only [negative_scalar_initial (a := g) (δ := δ 0) hη.le]
  have hb : ∀ k, k + 1 < m → b (k + 1) ≤ (1 - θ) * b k + (η / 2) * (δ (k + 1)) ^ 2 := by
    intro k hk
    have hs : d (k + 1 + 1) = (1 - θ) * d (k + 1) -
        η * ((g + lam * z (k + 1)) + lam * (1 - θ) * d (k + 1) + δ (k + 1)) := by
      rw [hvel (k + 1) hk]
      ring
    have hh := negative_scalar_step hη hθ.le (by linarith) hlam hcurv hs
    have he : (g + lam * z (k + 1)) - lam * d (k + 1) = g + lam * z k := by
      rw [hpos k (by omega)]
      ring
    rw [he] at hh
    dsimp [b]
    nlinarith only [hh]
  have hsum := envelope_sum_bound R δ b hβ (by positivity : 0 ≤ η / 2) hθ
    (by ring : θ + (1 - θ) = 1) hR0 hRrec hb0 m hb
  let Q := fun k => g * z k + lam / 2 * (z k) ^ 2
  have hquad : ∀ k, k < m → Q (k + 1) - Q k = b k + lam / 2 * (d (k + 1)) ^ 2 := by
    intro k hk
    dsimp [Q, b]
    rw [hpos k hk]
    ring
  have htel : (∑ k ∈ range m, (Q (k + 1) - Q k)) =
      ∑ k ∈ range m, (b k + lam / 2 * (d (k + 1)) ^ 2) :=
    sum_congr rfl (fun k hk => hquad k (mem_range.mp hk))
  rw [sum_range_sub, sum_add_distrib, ← mul_sum] at htel
  have hQ0 : Q 0 = 0 := by simp [Q, hz0]
  rw [hQ0, sub_zero] at htel
  have hD : 0 ≤ ∑ k ∈ range m, (d (k + 1)) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hδ : 0 ≤ ∑ k ∈ range m, (δ k) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hl : lam / 2 ≤ -(3 * θ / (8 * η)) := by
    have hh : 0 ≤ θ / η := le_of_lt (div_pos hθ hη)
    have he : 3 * θ / (8 * η) = (3 / 8) * (θ / η) := by ring
    rw [he]
    linarith
  have hn : (η / 2) / θ ≤ 2 * η / θ := by
    apply (div_le_div_iff_of_pos_right hθ).mpr
    linarith
  change Q m ≤ _
  rw [htel]
  have h1 := mul_le_mul_of_nonneg_right hl hD
  have h2 := mul_le_mul_of_nonneg_right hn hδ
  linarith

end LongTails.Proofs.BilevelEpochEnergy
