import LongTails.Theorems.BirchCollections
import LongTails.Proofs.BirchCollectionScaledReset

namespace LongTails.Proofs.BirchCollectionBounds

open LongTails.Setups.BirchCollections
open LongTails.Theorems.BirchCollections (budget)
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor packetControls)

lemma budget_tuned (p : Params) :
    budget p 0 = p.controls.initialization + p.controls.waste +
      ⌈(batchSize p : ℝ) * p.controls.amplification * ((horizon p : ℝ) * p.controls.upperMass)⌉₊ := by
  simp only [budget, batchSize, horizon, Nat.cast_add, Nat.cast_one]

lemma scaled_budget (p : Params) (lower upper window D : ℕ)
    (hu : 0 < upper) (h : p.controls = controls lower upper window D) :
    budget p 0 = D + batchSize p * (horizon p * upper) := by
  have hcN : 0 < divisor upper window := by unfold divisor; omega
  have hc : (0 : ℝ) < divisor upper window := Nat.cast_pos.mpr hcN
  rw [budget_tuned, h]
  change 0 + D + ⌈(batchSize p : ℝ) * (divisor upper window : ℝ) *
    ((horizon p : ℝ) * ((upper : ℝ) / divisor upper window))⌉₊ = _
  have he : (batchSize p : ℝ) * (divisor upper window : ℝ) *
      ((horizon p : ℝ) * ((upper : ℝ) / divisor upper window)) =
      ((batchSize p * (horizon p * upper) : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [he, Nat.ceil_natCast, zero_add]

lemma packet_budget (p : Params) (lower upper window D factor : ℕ)
    (hu : 0 < upper) (h : p.controls = packetControls lower upper window D factor) :
    budget p 0 = D + (batchSize p * factor) * (horizon p * upper) := by
  have hcN : 0 < divisor upper window := by unfold divisor; omega
  have hc : (0 : ℝ) < divisor upper window := Nat.cast_pos.mpr hcN
  rw [budget_tuned, h]
  change 0 + D + ⌈(batchSize p : ℝ) * ((divisor upper window : ℝ) * factor) *
    ((horizon p : ℝ) * ((upper : ℝ) / divisor upper window))⌉₊ = _
  have he : (batchSize p : ℝ) * ((divisor upper window : ℝ) * factor) *
      ((horizon p : ℝ) * ((upper : ℝ) / divisor upper window)) =
      (((batchSize p * factor) * (horizon p * upper) : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [he, Nat.ceil_natCast, zero_add]

lemma unit_budget (p : Params) (D : ℕ)
    (hI : p.controls.initialization = 0) (hD : p.controls.waste = D)
    (hJ : p.controls.amplification = 1) (hH : p.controls.upperMass = 1) :
    budget p 0 = D + batchSize p * horizon p := by
  rw [budget_tuned, hI, hD, hJ, hH, zero_add, mul_one, mul_one, ← Nat.cast_mul, Nat.ceil_natCast]

end LongTails.Proofs.BirchCollectionBounds
