import LongTails.Proofs.SelfConcordantBFGSExecution
import LongTails.Proofs.SelfConcordantSegment
import LongTails.Proofs.BFGSLogStep

open Set Matrix

namespace LongTails.Proofs.SelfConcordantBFGSRate

open OracleTemplate LongTails.Setups.SelfConcordantBFGS LongTails.Proofs.SelfConcordantBFGSExecution
open LongTails.Proofs.SelfConcordantSegment LongTails.Proofs.SelfConcordantCalculus
open LongTails.Proofs.BFGSLogPotential LongTails.Proofs.BFGSLogDet LongTails.Proofs.BFGSLogStep
open LongTails.Proofs.BFGSMatrix
open LongTails.Setups.LinearPredictorBFGS (bfgsUpdate)

lemma final_count {S A K' X B c : ℝ} (hc : 0 < c) (hS : 0 ≤ S) (hK : 0 ≤ K') (hX : 0 ≤ X)
    (hB : 0 ≤ B) (h1 : c * S ≤ A + K' * X) (h2 : X ^ 2 ≤ S * B) :
    S ≤ 2 * A / c + K' ^ 2 * B / c ^ 2 := by
  have hP : K' * X ≤ c * S / 2 + K' ^ 2 * B / (2 * c) := by
    have hsq : (K' * X) ^ 2 ≤ (c * S / 2 + K' ^ 2 * B / (2 * c)) ^ 2 := by
      have e : (c * S / 2 + K' ^ 2 * B / (2 * c)) ^ 2 =
          (c * S / 2 - K' ^ 2 * B / (2 * c)) ^ 2 + K' ^ 2 * (S * B) := by
        field_simp; ring
      rw [e, mul_pow]
      have := mul_le_mul_of_nonneg_left h2 (sq_nonneg K')
      nlinarith [sq_nonneg (c * S / 2 - K' ^ 2 * B / (2 * c))]
    have h0 : 0 ≤ c * S / 2 + K' ^ 2 * B / (2 * c) := by positivity
    exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).mp hsq
  have h3 : S * c ^ 2 ≤ 2 * A * c + K' ^ 2 * B := by
    have h4 : c * S ≤ A + c * S / 2 + K' ^ 2 * B / (2 * c) := by linarith
    have h5 : c * (c * S) ≤ c * (A + c * S / 2 + K' ^ 2 * B / (2 * c)) :=
      mul_le_mul_of_nonneg_left h4 hc.le
    have e : c * (A + c * S / 2 + K' ^ 2 * B / (2 * c)) =
        c * A + c ^ 2 * S / 2 + K' ^ 2 * B / 2 := by
      field_simp
    nlinarith
  have e : 2 * A / c + K' ^ 2 * B / c ^ 2 = (2 * A * c + K' ^ 2 * B) / c ^ 2 := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

lemma exp_half_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    2 * (1 - α) * Real.exp (α / 2) ≤ 2 - α := by
  have h1 : 1 - α / 2 ≤ Real.exp (-(α / 2)) := by linarith [Real.add_one_le_exp (-(α / 2))]
  have h2 : Real.exp (α / 2) * (1 - α / 2) ≤ 1 := by
    calc Real.exp (α / 2) * (1 - α / 2) ≤ Real.exp (α / 2) * Real.exp (-(α / 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 ≤ 1 - α := by linarith
  nlinarith [Real.exp_pos (α / 2)]

lemma log_rho_bound {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (k : ℕ)
    (hkd : k = ⌈1 / δ⌉₊ + 2) :
    Real.log ((1 - δ) * (1 + 1 / (2 * (k : ℝ) - 1))) ≤ -(δ / 2) := by
  have hk : 1 / δ + 2 ≤ (k : ℝ) := by
    rw [hkd]; push_cast; linarith [Nat.le_ceil (1 / δ)]
  have hδinv : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hN : 0 < 2 * (k : ℝ) - 1 := by linarith
  have hfrac : 1 / (2 * (k : ℝ) - 1) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    have : 2 / δ + 3 ≤ 2 * (k : ℝ) - 1 := by
      have e2 : 2 / δ = 2 * (1 / δ) := by ring
      linarith
    have h2 : 2 ≤ δ * (2 * (k : ℝ) - 1) := by
      have := mul_le_mul_of_nonneg_left this hδ.le
      have e : δ * (2 / δ + 3) = 2 + 3 * δ := by field_simp
      linarith
    linarith
  have hρpos : 0 < (1 - δ) * (1 + 1 / (2 * (k : ℝ) - 1)) := by
    have : 0 < 1 / (2 * (k : ℝ) - 1) := by positivity
    have : 0 < 1 - δ := by linarith
    positivity
  have hρ : (1 - δ) * (1 + 1 / (2 * (k : ℝ) - 1)) ≤ 1 - δ / 2 := by
    have : (1 - δ) * (1 + 1 / (2 * (k : ℝ) - 1)) ≤ (1 - δ) * (1 + δ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have := Real.log_le_sub_one_of_pos hρpos
  linarith

lemma bud_numeric {α δ dd Δ Φ0 lg kk : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hd : 0 ≤ dd) (hΔ : 0 ≤ Δ) (hΦ : 0 ≤ Φ0)
    (hk0 : 0 ≤ kk) (hk : kk ≤ 1 / δ + 3) :
    2 * (kk * Φ0 + 3 + 4 * Δ + lg + (24 * Δ + 37 + (2 * (3 * kk * dd + 1) + 1) * (6 * Δ + 6)) *
        (4096 * Δ / α ^ 3)) / (δ / 2) +
      (8 * (2 * (3 * kk * dd + 1) + 1)) ^ 2 * (4 * Δ / α) / (δ / 2) ^ 2 + 4096 * Δ / α ^ 3 ≤
      2 ^ 21 * (dd + 1) * (Δ + 1) * ((Δ + 1) / (α ^ 3 * δ ^ 2) + (dd + 1) / (α * δ ^ 4)) +
        10 * Φ0 / δ ^ 2 + 4 * lg / δ := by
  set u := 1 / δ with hu
  set w := 1 / α with hw
  have hu2 : 2 ≤ u := by rw [hu, le_div_iff₀ hδ]; linarith
  have hw1 : 1 ≤ w := by rw [hw, le_div_iff₀ hα]; linarith
  set P := 2 * (3 * kk * dd + 1) + 1 with hP
  have hk' : kk ≤ 5 / 2 * u := by linarith
  have hP0 : 0 ≤ P := by positivity
  have hPle : P ≤ 15 * (dd + 1) * u := by
    have : kk * dd ≤ 5 / 2 * u * dd := mul_le_mul_of_nonneg_right hk' hd
    rw [hP]; linarith
  have hR : 24 * Δ + 37 + P * (6 * Δ + 6) ≤ 109 * (dd + 1) * (Δ + 1) * u := by
    have h3 : P * (6 * Δ + 6) ≤ 15 * (dd + 1) * u * (6 * Δ + 6) :=
      mul_le_mul_of_nonneg_right hPle (by linarith)
    have h4 : 37 * (Δ + 1) ≤ 19 * (dd + 1) * (Δ + 1) * u := by
      have h1 : (Δ + 1) * 2 ≤ (Δ + 1) * u := mul_le_mul_of_nonneg_left hu2 (by linarith)
      have h2 : (Δ + 1) * u ≤ (dd + 1) * ((Δ + 1) * u) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      have h3 : 0 ≤ (dd + 1) * ((Δ + 1) * u) := by positivity
      linarith
    linarith
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw1
  have e1 : 2 * (kk * Φ0 + 3 + 4 * Δ + lg + (24 * Δ + 37 + P * (6 * Δ + 6)) *
      (4096 * Δ / α ^ 3)) / (δ / 2) =
      4 * u * (kk * Φ0 + 3 + 4 * Δ + lg + (24 * Δ + 37 + P * (6 * Δ + 6)) *
        (4096 * Δ * w ^ 3)) := by
    rw [hu, hw]; ring
  have e2 : (8 * P) ^ 2 * (4 * Δ / α) / (δ / 2) ^ 2 = 1024 * P ^ 2 * Δ * w * u ^ 2 := by
    rw [hu, hw]; ring
  have e3 : 4096 * Δ / α ^ 3 = 4096 * Δ * w ^ 3 := by rw [hw]; ring
  have e4 : 2 ^ 21 * (dd + 1) * (Δ + 1) * ((Δ + 1) / (α ^ 3 * δ ^ 2) + (dd + 1) / (α * δ ^ 4)) =
      2 ^ 21 * ((dd + 1) * (Δ + 1) ^ 2 * w ^ 3 * u ^ 2) +
        2 ^ 21 * ((dd + 1) ^ 2 * (Δ + 1) * w * u ^ 4) := by rw [hu, hw]; ring
  have e5 : 10 * Φ0 / δ ^ 2 = 10 * Φ0 * u ^ 2 := by rw [hu]; ring
  have e6 : 4 * lg / δ = 4 * lg * u := by rw [hu]; ring
  rw [e1, e2, e3, e4, e5, e6]
  set T1 := (dd + 1) * (Δ + 1) ^ 2 * w ^ 3 * u ^ 2 with hT1
  set T2 := (dd + 1) ^ 2 * (Δ + 1) * w * u ^ 4 with hT2
  have hd1 : 1 ≤ dd + 1 := by linarith
  have hD1 : Δ ≤ Δ + 1 := by linarith
  have hΔ1 : 1 ≤ Δ + 1 := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hk1 : kk * Φ0 ≤ 5 / 2 * u * Φ0 := mul_le_mul_of_nonneg_right hk' hΦ
  have hA2 : (24 * Δ + 37 + P * (6 * Δ + 6)) * (4096 * Δ * w ^ 3) ≤
      109 * (dd + 1) * (Δ + 1) * u * (4096 * Δ * w ^ 3) :=
    mul_le_mul_of_nonneg_right hR (by positivity)
  have hbase : 1 ≤ (dd + 1) * (Δ + 1) ^ 2 * w ^ 3 := by
    have h1 : 1 ≤ (dd + 1) * (Δ + 1) ^ 2 := one_le_mul_of_one_le_of_one_le hd1 (one_le_pow₀ hΔ1)
    exact one_le_mul_of_one_le_of_one_le h1 hw3
  have hm1 : 4 * u * (3 + 4 * Δ) ≤ 16 * T1 := by
    have h1 : 3 + 4 * Δ ≤ 4 * (Δ + 1) := by linarith
    have h2 : Δ + 1 ≤ (dd + 1) * (Δ + 1) ^ 2 * w ^ 3 := by
      have : Δ + 1 ≤ (Δ + 1) ^ 2 := le_self_pow₀ hΔ1 (by norm_num)
      have h3 : (Δ + 1) ^ 2 ≤ (dd + 1) * (Δ + 1) ^ 2 := le_mul_of_one_le_left (by positivity) hd1
      have h4 : (dd + 1) * (Δ + 1) ^ 2 ≤ (dd + 1) * (Δ + 1) ^ 2 * w ^ 3 :=
        le_mul_of_one_le_right (by positivity) hw3
      linarith
    have h5 : u * ((dd + 1) * (Δ + 1) ^ 2 * w ^ 3) ≤ u ^ 2 * ((dd + 1) * (Δ + 1) ^ 2 * w ^ 3) :=
      mul_le_mul_of_nonneg_right (by rw [sq]; exact le_mul_of_one_le_left hu0 (by linarith))
        (by positivity)
    have h6 : u * (3 + 4 * Δ) ≤ u * (4 * ((dd + 1) * (Δ + 1) ^ 2 * w ^ 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0
    have e : T1 = u ^ 2 * ((dd + 1) * (Δ + 1) ^ 2 * w ^ 3) := by rw [hT1]; ring
    rw [e]; linarith
  have hm2 : 4 * u * (109 * (dd + 1) * (Δ + 1) * u * (4096 * Δ * w ^ 3)) ≤ 1785856 * T1 := by
    have h1 : (dd + 1) * (Δ + 1) * Δ * (w ^ 3 * u ^ 2) ≤
        (dd + 1) * (Δ + 1) * (Δ + 1) * (w ^ 3 * u ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 (by positivity)) (by positivity)
    have e1 : 4 * u * (109 * (dd + 1) * (Δ + 1) * u * (4096 * Δ * w ^ 3)) =
        1785856 * ((dd + 1) * (Δ + 1) * Δ * (w ^ 3 * u ^ 2)) := by ring
    have e2 : T1 = (dd + 1) * (Δ + 1) * (Δ + 1) * (w ^ 3 * u ^ 2) := by rw [hT1]; ring
    rw [e1, e2]; linarith
  have hm3 : 4096 * Δ * w ^ 3 ≤ 4096 * T1 := by
    have h1 : Δ * w ^ 3 ≤ (dd + 1) * (Δ + 1) ^ 2 * w ^ 3 := by
      have h0 : Δ + 1 ≤ (Δ + 1) ^ 2 := le_self_pow₀ hΔ1 (by norm_num)
      have h0' : (Δ + 1) ^ 2 ≤ (dd + 1) * (Δ + 1) ^ 2 := le_mul_of_one_le_left (by positivity) hd1
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (dd + 1) * (Δ + 1) ^ 2 * w ^ 3 ≤ T1 := by
      rw [hT1]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))
    linarith
  have hm4 : 1024 * P ^ 2 * Δ * w * u ^ 2 ≤ 230400 * T2 := by
    have hP2 : P ^ 2 ≤ (15 * (dd + 1) * u) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
    have h1 : P ^ 2 * (Δ * w * u ^ 2) ≤ (15 * (dd + 1) * u) ^ 2 * (Δ * w * u ^ 2) :=
      mul_le_mul_of_nonneg_right hP2 (by positivity)
    have h2 : (dd + 1) ^ 2 * Δ * (w * u ^ 4) ≤ (dd + 1) ^ 2 * (Δ + 1) * (w * u ^ 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 (by positivity)) (by positivity)
    have e1 : (15 * (dd + 1) * u) ^ 2 * (Δ * w * u ^ 2) = 225 * ((dd + 1) ^ 2 * Δ * (w * u ^ 4)) := by
      ring
    have e2 : T2 = (dd + 1) ^ 2 * (Δ + 1) * (w * u ^ 4) := by rw [hT2]; ring
    have e3 : 1024 * P ^ 2 * Δ * w * u ^ 2 = 1024 * (P ^ 2 * (Δ * w * u ^ 2)) := by ring
    rw [e3, e2]; rw [e1] at h1; linarith
  have hexp : 4 * u * (kk * Φ0 + 3 + 4 * Δ + lg + (24 * Δ + 37 + P * (6 * Δ + 6)) *
      (4096 * Δ * w ^ 3)) ≤ 10 * Φ0 * u ^ 2 + 4 * lg * u + 16 * T1 + 1785856 * T1 := by
    have h1 : 4 * u * (kk * Φ0) ≤ 10 * Φ0 * u ^ 2 := by
      have := mul_le_mul_of_nonneg_left hk1 (by positivity : (0 : ℝ) ≤ 4 * u)
      have e : 4 * u * (5 / 2 * u * Φ0) = 10 * Φ0 * u ^ 2 := by ring
      linarith
    have h2 : 4 * u * ((24 * Δ + 37 + P * (6 * Δ + 6)) * (4096 * Δ * w ^ 3)) ≤
        4 * u * (109 * (dd + 1) * (Δ + 1) * u * (4096 * Δ * w ^ 3)) :=
      mul_le_mul_of_nonneg_left hA2 (by positivity)
    have e : 4 * u * (kk * Φ0 + 3 + 4 * Δ + lg + (24 * Δ + 37 + P * (6 * Δ + 6)) *
        (4096 * Δ * w ^ 3)) = 4 * u * (kk * Φ0) + 4 * u * (3 + 4 * Δ) + 4 * lg * u +
        4 * u * ((24 * Δ + 37 + P * (6 * Δ + 6)) * (4096 * Δ * w ^ 3)) := by ring
    rw [e]; linarith
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  linarith

section Step

variable {d : ℕ} {D : Set (Vec d)} {f : Vec d → ℝ} {Df : Vec d → Vec d →L[ℝ] ℝ}
  {D2f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] ℝ}
  {D3f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] Vec d →L[ℝ] ℝ}

lemma dir_pairing {B : Matrix (Fin d) (Fin d) ℝ} (g : Vec d) :
    g ⬝ᵥ direction B g = -(g ⬝ᵥ (B⁻¹ *ᵥ g)) := by
  simp [direction, dotProduct_neg]

lemma B_dir {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (g : Vec d) (η : ℝ) :
    B *ᵥ (η • direction B g) = (-η) • g := by
  rw [mulVec_smul, direction, mulVec_neg, mulVec_inv_mulVec hB, smul_neg, neg_smul]

lemma theta_sq_le {θ α β δ : ℝ} (hδ : δ = min α (1 - β)) (hlo : 1 - β ≤ θ) (hhi : θ ≤ 2 - α)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) : (θ - 1) ^ 2 ≤ 1 - δ := by
  have h1 : 1 - δ = max (1 - α) β := by
    rw [hδ]; rcases le_total α (1 - β) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  rw [h1]
  have hm1 : max (1 - α) β ≤ 1 := max_le (by linarith) hβ.le
  have hm0 : 0 ≤ max (1 - α) β := le_max_of_le_right (by linarith)
  have hb : |θ - 1| ≤ max (1 - α) β := by
    rw [abs_le]; constructor
    · linarith [le_max_right (1 - α) β]
    · linarith [le_max_left (1 - α) β]
  have : (θ - 1) ^ 2 ≤ (max (1 - α) β) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  nlinarith

lemma pure_step (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) (hconv : Convex ℝ D)
    {α β Δ : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hΔ0 : 0 ≤ Δ) {f0 : ℝ}
    (hlowf : ∀ y ∈ D, f0 - Δ ≤ f y)
    {x g g' : Vec d} {B : Matrix (Fin d) (Fin d) ℝ} {η : ℝ} (hx : x ∈ D) (hfx : f x ≤ f0)
    (hB : B.PosDef) (hg : ∀ w, Df x w = g ⬝ᵥ w) (hg0 : g ≠ 0) (hη : 0 < η)
    (hx' : x + η • direction B g ∈ D) (hg' : ∀ w, Df (x + η • direction B g) w = g' ⬝ᵥ w)
    (hg'0 : g' ≠ 0)
    (harm : f (x + η • direction B g) ≤ f x + α * η * Df x (direction B g))
    (hcurv : β * Df x (direction B g) ≤ Df (x + η • direction B g) (direction B g)) :
    let s := η • direction B g
    let δ := min α (1 - β)
    let k := ⌈1 / δ⌉₊ + 2
    let r := √(D2f x s s)
    let a := if r ≤ α / 32 then 8 * r else 6 * Δ + 6
    SegBound D2f x s a ∧ (segQ D2f x s).PosDef ∧ segQ D2f x s *ᵥ s = g' - g ∧
    U k (bfgsUpdate B s (g' - g)) (segQ D2f x s) g' ≤
      U k B (segQ D2f x s) g + (if r ≤ α / 32 then -(δ / 2) else 24 * Δ + 37) ∧
    (if r ≤ α / 32 then α * r ^ 2 / 4 else α ^ 3 / 4096) ≤ f x - f (x + s) := by
  intro s δ k r a
  set v := direction B g with hvdef
  have hBinv : 0 < g ⬝ᵥ (B⁻¹ *ᵥ g) := posDef_quad_pos hB.inv hg0
  have hdesc : Df x v < 0 := by rw [hg, dir_pairing]; linarith
  have hv0 : v ≠ 0 := by intro h0; rw [h0, map_zero] at hdesc; exact lt_irrefl _ hdesc
  have hs0 : s ≠ 0 := smul_ne_zero hη.ne' hv0
  have hsub : (x + s) - x = s := by abel
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D := by
    have := seg_mem hconv hx hx'
    simpa [hsub] using this
  have S := restrict_SC1 hSC hseg hs0
  have hφ1_0 : Df x s = η * Df x v := by
    show Df x (η • v) = _; rw [map_smul, smul_eq_mul]
  have harm' : f (x + (1 : ℝ) • s) ≤ f (x + (0 : ℝ) • s) + α * Df (x + (0 : ℝ) • s) s := by
    simp only [one_smul, zero_smul, add_zero]; rw [hφ1_0]; linarith
  have hcurv' : β * Df (x + (0 : ℝ) • s) s ≤ Df (x + (1 : ℝ) • s) s := by
    simp only [one_smul, zero_smul, add_zero]
    rw [hφ1_0]
    have : Df (x + s) s = η * Df (x + s) v := by
      show Df (x + s) (η • v) = _; rw [map_smul, smul_eq_mul]
    rw [this]; nlinarith
  have hdesc' : Df (x + (0 : ℝ) • s) s < 0 := by
    simp only [zero_smul, add_zero]; rw [hφ1_0]; nlinarith
  have hψ0 : D2f (x + (0 : ℝ) • s) s s = r ^ 2 := by
    simp only [zero_smul, add_zero]
    rw [Real.sq_sqrt (hSC.2.2.2.1 x hx s hs0).le]
  have hr0 : 0 < r := Real.sqrt_pos.mpr (hSC.2.2.2.1 x hx s hs0)
  have hBs : B *ᵥ s = (-η) • g := B_dir hB g η
  have he : g = (-(1 / η)) • (B *ᵥ s) := by
    rw [hBs, smul_smul]; field_simp; simp
  have hQs := segQ_mulVec hSC hD hseg hg (by simpa using hg')
  have hφ0 : f (x + (0 : ℝ) • s) = f x := by simp
  have hφ1 : f (x + (1 : ℝ) • s) = f (x + s) := by simp
  have hθdef : (s ⬝ᵥ (segQ D2f x s *ᵥ s)) / (-(((-(1 / η)) • (B *ᵥ s)) ⬝ᵥ s)) =
      (Df (x + (1 : ℝ) • s) s - Df (x + (0 : ℝ) • s) s) / (-Df (x + (0 : ℝ) • s) s) := by
    rw [← he, hQs, dotProduct_comm, sub_dotProduct]
    simp only [one_smul, zero_smul, add_zero, hg]
    rw [hg' s]
  have hδ0 : 0 < δ := lt_min hα (by linarith)
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h; push Not at h
    have h1 : 1 / 2 < α := lt_of_lt_of_le h (min_le_left _ _)
    have h2 : 1 / 2 < 1 - β := lt_of_lt_of_le h (min_le_right _ _)
    linarith
  have hk2 : 2 ≤ k := by simp only [k]; omega
  have hkR : (4 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (2 : ℝ) ≤ ⌈1 / δ⌉₊ := by
      have h := Nat.le_ceil (1 / δ)
      have : (2 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
      linarith
    simp only [k]; push_cast; linarith
  have hosc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ τ' ∈ Icc (0 : ℝ) 1, f (x + τ • s) - f (x + τ' • s) ≤ Δ := by
    intro τ hτ τ' hτ'
    have hc := chord S hτ
    rw [hφ0, hφ1] at hc
    have h1 : f (x + s) ≤ f x := by
      have := harm'; rw [hφ0, hφ1] at this
      have : α * Df (x + (0 : ℝ) • s) s < 0 := mul_neg_of_pos_of_neg hα hdesc'
      linarith
    have h2 : f (x + τ • s) ≤ f x := by nlinarith [hτ.1, hτ.2]
    have h3 := hlowf _ (hseg τ' hτ')
    linarith
  have hupd : bfgsUpdate B s (g' - g) = bfgsUpdate B s (segQ D2f x s *ᵥ s) := by rw [hQs]
  have hgg : g' = (-(1 / η)) • (B *ᵥ s) + segQ D2f x s *ᵥ s := by rw [← he, hQs]; abel
  have hθlo := wolfe_theta_lower (φ1 := fun τ : ℝ => Df (x + τ • s) s) hcurv' hdesc'
  have hgp : (-(1 / η)) • (B *ᵥ s) + segQ D2f x s *ᵥ s ≠ 0 := by rw [← hgg]; exact hg'0
  by_cases hr : r ≤ α / 32
  · have hab : a = 8 * r := ite_eq_left hr
    have hr2 : r ≤ 1 / 2 := by linarith
    have hSB : SegBound D2f x s (8 * r) := segBound_short hSC hseg hs0 hr2
    have hQpd := segQ_posDef hSC hD hseg hSB
    have hm : ∀ τ ∈ Icc (0 : ℝ) 1, Real.exp (-(8 * r)) * r ^ 2 ≤ D2f (x + τ • s) s s :=
      fun τ hτ => by
        have := hSB s 0 ⟨le_rfl, zero_le_one⟩ τ hτ
        rw [hψ0] at this
        rw [Real.exp_neg]
        rw [inv_mul_le_iff₀ (Real.exp_pos _)]
        exact this
    have hM : ∀ τ ∈ Icc (0 : ℝ) 1, D2f (x + τ • s) s s ≤ Real.exp (8 * r) * r ^ 2 :=
      fun τ hτ => by
        have := hSB s τ hτ 0 ⟨le_rfl, zero_le_one⟩
        rwa [hψ0] at this
    have hm0 : 0 < Real.exp (-(8 * r)) * r ^ 2 := by positivity
    have hθhi := wolfe_theta_upper S hm0 hm hM hα (by linarith) harm' hdesc'
    have hratio :
        2 * (1 - α) * (Real.exp (8 * r) * r ^ 2) / (Real.exp (-(8 * r)) * r ^ 2) ≤ 2 - α := by
      have hE : Real.exp (8 * r) = Real.exp (16 * r) * Real.exp (-(8 * r)) := by
        rw [← Real.exp_add]; ring_nf
      have h16 : Real.exp (16 * r) ≤ Real.exp (α / 2) := Real.exp_le_exp.mpr (by linarith)
      have hb : 2 * (1 - α) * Real.exp (16 * r) ≤ 2 - α := by
        have h1 : 0 ≤ 2 * (1 - α) := by linarith
        have := mul_le_mul_of_nonneg_left h16 h1
        linarith [exp_half_bound hα (by linarith : α < 1)]
      rw [div_le_iff₀ hm0, hE]
      calc 2 * (1 - α) * (Real.exp (16 * r) * Real.exp (-(8 * r)) * r ^ 2) =
            (2 * (1 - α) * Real.exp (16 * r)) * (Real.exp (-(8 * r)) * r ^ 2) := by ring
        _ ≤ (2 - α) * (Real.exp (-(8 * r)) * r ^ 2) := mul_le_mul_of_nonneg_right hb hm0.le
    have hν := theta_sq_le (θ := (Df (x + (1 : ℝ) • s) s - Df (x + (0 : ℝ) • s) s) /
      (-Df (x + (0 : ℝ) • s) s)) rfl hθlo (hθhi.trans hratio) hα hαβ hβ
    rw [← hθdef] at hν
    have hpot := U_step_contract hB hQpd hs0 (-(1 / η)) (by
      have : 0 < 1 / η := by positivity
      linarith) k hk2 (1 - δ) hν (by nlinarith) hgp
    rw [← hgg, ← hupd, ← he] at hpot
    have hρ := log_rho_bound hδ0 hδ2 k rfl
    have hdec := (wolfe_decrease S hm0.le hm hα (by linarith) harm').2
    rw [hφ0, hφ1] at hdec
    have hexp : 1 / 2 ≤ Real.exp (-(8 * r)) := by
      have := Real.add_one_le_exp (-(8 * r)); linarith
    refine ⟨hab ▸ hSB, hQpd, hQs, ?_, ?_⟩
    · rw [ite_eq_left hr]; linarith
    · rw [ite_eq_left hr]
      have h1 := mul_le_mul_of_nonneg_right hexp (sq_nonneg r)
      have h2 := mul_le_mul_of_nonneg_left h1 hα.le
      linarith
  · have hab : a = 6 * Δ + 6 := ite_eq_right hr
    push Not at hr
    have hSB : SegBound D2f x s (6 * Δ + 6) := segBound_long hSC hseg hs0 hΔ0 hosc
    have hQpd := segQ_posDef hSC hD hseg hSB
    have hm : ∀ τ ∈ Icc (0 : ℝ) 1, Real.exp (-(6 * Δ + 6)) * r ^ 2 ≤ D2f (x + τ • s) s s :=
      fun τ hτ => by
        have := hSB s 0 ⟨le_rfl, zero_le_one⟩ τ hτ
        rw [hψ0] at this
        rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
        exact this
    have hM : ∀ τ ∈ Icc (0 : ℝ) 1, D2f (x + τ • s) s s ≤ Real.exp (6 * Δ + 6) * r ^ 2 :=
      fun τ hτ => by
        have := hSB s τ hτ 0 ⟨le_rfl, zero_le_one⟩
        rwa [hψ0] at this
    have hm0 : 0 < Real.exp (-(6 * Δ + 6)) * r ^ 2 := by positivity
    have hθhi := wolfe_theta_upper S hm0 hm hM hα (by linarith) harm' hdesc'
    have hE : 2 * (1 - α) * (Real.exp (6 * Δ + 6) * r ^ 2) / (Real.exp (-(6 * Δ + 6)) * r ^ 2) ≤
        2 * Real.exp (12 * Δ + 12) := by
      have hE : Real.exp (6 * Δ + 6) = Real.exp (12 * Δ + 12) * Real.exp (-(6 * Δ + 6)) := by
        rw [← Real.exp_add]; ring_nf
      have hb : 2 * (1 - α) * Real.exp (12 * Δ + 12) ≤ 2 * Real.exp (12 * Δ + 12) := by
        have := Real.exp_pos (12 * Δ + 12)
        nlinarith
      rw [div_le_iff₀ hm0, hE]
      calc 2 * (1 - α) * (Real.exp (12 * Δ + 12) * Real.exp (-(6 * Δ + 6)) * r ^ 2) =
            (2 * (1 - α) * Real.exp (12 * Δ + 12)) * (Real.exp (-(6 * Δ + 6)) * r ^ 2) := by ring
        _ ≤ (2 * Real.exp (12 * Δ + 12)) * (Real.exp (-(6 * Δ + 6)) * r ^ 2) :=
            mul_le_mul_of_nonneg_right hb hm0.le
    set θ := (Df (x + (1 : ℝ) • s) s - Df (x + (0 : ℝ) • s) s) / (-Df (x + (0 : ℝ) • s) s)
    have hθ0 : 0 < θ := lt_of_lt_of_le (by linarith) hθlo
    have hθ1 : θ ≤ 2 * Real.exp (12 * Δ + 12) := hθhi.trans hE
    have hpot := U_step_any hB hQpd hs0 (-(1 / η)) (by
      have : 0 < 1 / η := by positivity
      linarith) k (by omega) hgp
    rw [← hgg, ← hupd, hθdef, ← he] at hpot
    have hR : Real.log (4 * (1 + (θ - 1) ^ 2 / 2)) ≤ 24 * Δ + 37 := by
      have hE24 : Real.exp (24 * Δ + 24) = Real.exp (12 * Δ + 12) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      have hθsq : θ ^ 2 ≤ 4 * Real.exp (24 * Δ + 24) := by
        rw [hE24]
        calc θ ^ 2 ≤ (2 * Real.exp (12 * Δ + 12)) ^ 2 := pow_le_pow_left₀ hθ0.le hθ1 2
          _ = 4 * Real.exp (12 * Δ + 12) ^ 2 := by ring
      have hpos : 0 < 4 * (1 + (θ - 1) ^ 2 / 2) := by positivity
      have hle : 4 * (1 + (θ - 1) ^ 2 / 2) ≤ 14 * Real.exp (24 * Δ + 24) := by
        have h1 : 1 ≤ Real.exp (24 * Δ + 24) := Real.one_le_exp (by linarith)
        have h2 : (θ - 1) ^ 2 = θ ^ 2 - 2 * θ + 1 := by ring
        linarith
      have := Real.log_le_log hpos hle
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
      have h14 : Real.log 14 ≤ 13 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 14); linarith
      linarith
    have hlong_m : ∀ τ ∈ Icc (0 : ℝ) 1, (α / 32) ^ 2 / 2 ≤ D2f (x + τ • s) s s := fun τ hτ => by
      have hh0 : hinv (fun τ => D2f (x + τ • s) s s) 0 = 1 / r := hinv_zero_eq
      have := hinv_lip_up S ⟨le_rfl, zero_le_one⟩ hτ hτ.1
      rw [hh0, sub_zero] at this
      have hge := psi_ge_of_hinv S hτ this
      refine le_trans ?_ hge
      have hr32 : 0 < α / 32 := by positivity
      have h1 : 1 / r + τ ≤ 1 / (α / 32) + 1 := by
        have : 1 / r ≤ 1 / (α / 32) := one_div_le_one_div_of_le hr32 hr.le
        linarith [hτ.2]
      have hp : 0 < 1 / r + τ := by have : 0 < 1 / r := by positivity
                                    linarith [hτ.1]
      have h2 : (1 / r + τ) ^ 2 ≤ (1 / (α / 32) + 1) ^ 2 := pow_le_pow_left₀ hp.le h1 2
      have h3 : 1 / (1 / (α / 32) + 1) ^ 2 ≤ 1 / (1 / r + τ) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) h2
      refine le_trans ?_ h3
      have hα32 : α / 32 ≤ 1 / 32 := by linarith
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have e : (1 / (α / 32) + 1) * (α / 32) = 1 + α / 32 := by field_simp
      have : (α / 32) ^ 2 * (1 / (α / 32) + 1) ^ 2 = (1 + α / 32) ^ 2 := by
        rw [← e]; ring
      rw [this]
      calc (1 + α / 32) ^ 2 ≤ (1 + 1 / 32) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ ≤ 1 * 2 := by norm_num
    have hdec := (wolfe_decrease S (by positivity) hlong_m hα (by linarith) harm').2
    rw [hφ0, hφ1] at hdec
    refine ⟨hab ▸ hSB, hQpd, hQs, ?_, ?_⟩
    · rw [ite_eq_right (not_le.mpr hr)]; linarith
    · rw [ite_eq_right (not_le.mpr hr)]
      have e : α * ((α / 32) ^ 2 / 2) / 2 = α ^ 3 / 4096 := by ring
      linarith

lemma count_bound {α δ dd Δ Φ0 lg kk S L X Y llam lε : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hd : 0 ≤ dd) (hΔ : 0 ≤ Δ) (hΦ : 0 ≤ Φ0)
    (hk0 : 0 ≤ kk) (hk : kk ≤ 1 / δ + 3) (hS : 0 ≤ S) (hL : 0 ≤ L) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hdec : α * Y / 4 + L * (α ^ 3 / 4096) ≤ Δ) (hXY : X ^ 2 ≤ S * Y)
    (hpot : llam ≤ kk * Φ0 + 3 + 4 * Δ + (-(δ / 2) * S + (24 * Δ + 37) * L) +
      (2 * (3 * kk * dd + 1) + 1) * (8 * X + (6 * Δ + 6) * L))
    (hlε : lε < llam) (hlgε : -lε ≤ lg) :
    S + L ≤ 2 ^ 21 * (dd + 1) * (Δ + 1) * ((Δ + 1) / (α ^ 3 * δ ^ 2) + (dd + 1) / (α * δ ^ 4)) +
        10 * Φ0 / δ ^ 2 + 4 * lg / δ := by
  have hnum := bud_numeric (lg := lg) hα hα1 hδ hδ2 hd hΔ hΦ hk0 hk
  set Kc := 3 * kk * dd + 1
  have hKc0 : 0 ≤ 2 * Kc + 1 := by positivity
  have hα3 : 0 < α ^ 3 := by positivity
  have hLm : L ≤ 4096 * Δ / α ^ 3 := by
    rw [le_div_iff₀ hα3]
    have : 0 ≤ α * Y / 4 := by positivity
    nlinarith
  have hYm : Y ≤ 4 * Δ / α := by
    rw [le_div_iff₀ hα]
    have : 0 ≤ L * (α ^ 3 / 4096) := by positivity
    nlinarith
  have hXY' : X ^ 2 ≤ S * (4 * Δ / α) := hXY.trans (mul_le_mul_of_nonneg_left hYm hS)
  have hcoef : 0 ≤ 24 * Δ + 37 + (2 * Kc + 1) * (6 * Δ + 6) := by positivity
  have h1 : δ / 2 * S ≤ (kk * Φ0 + 3 + 4 * Δ + lg +
      (24 * Δ + 37 + (2 * Kc + 1) * (6 * Δ + 6)) * (4096 * Δ / α ^ 3)) +
      8 * (2 * Kc + 1) * X := by
    have := mul_le_mul_of_nonneg_left hLm hcoef
    nlinarith
  have hfc := final_count (by positivity : (0 : ℝ) < δ / 2) hS (by positivity) hX
    (by positivity) h1 hXY'
  linarith

end Step



section Main

variable (q : Params) (I : Instance q.toPublic) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
  (ξ : (k : ℕ) → O.Seed k)

def OracleOK (Df : Vec q.d → Vec q.d →L[ℝ] ℝ) : Prop :=
  ∀ history x v seed, x ∈ I.D → Df x v ≤ 0 →
    x + (O.answer history (0, (x, v)) seed).1 • v ∈ I.D ∧
    (∀ w, Df (x + (O.answer history (0, (x, v)) seed).1 • v) w =
      (O.answer history (0, (x, v)) seed).2 ⬝ᵥ w) ∧
    (Df x v < 0 →
      0 < (O.answer history (0, (x, v)) seed).1 ∧
      I.f (x + (O.answer history (0, (x, v)) seed).1 • v) ≤
        I.f x + q.c1 * (O.answer history (0, (x, v)) seed).1 * Df x v ∧
      q.c2 * Df x v ≤ Df (x + (O.answer history (0, (x, v)) seed).1 • v) v)

lemma bfgsUpdate_zero {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (y : Vec d) :
    bfgsUpdate B 0 y = B := by
  simp [bfgsUpdate]

lemma vec_eq_of_dot {d : ℕ} {g g' : Vec d} (h : ∀ w : Vec d, g ⬝ᵥ w = g' ⬝ᵥ w) : g = g' := by
  ext i
  have := h (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using this

variable {q I O ξ}

lemma inv_run {Df : Vec q.d → Vec q.d →L[ℝ] ℝ} (hB0 : Matrix.PosDef q.B0) (hc1 : 0 < q.c1)
    (hc2 : q.c2 < 1)
    (hx0 : q.x0 ∈ I.D) (horc : OracleOK q I O Df) :
    ∀ n, (run q O ξ n).x ∈ I.D ∧ (∀ w, Df (run q O ξ n).x w = (run q O ξ n).g ⬝ᵥ w) ∧
      (run q O ξ n).B.PosDef ∧ I.f (run q O ξ n).x ≤ I.f q.x0 := by
  intro n
  induction n with
  | zero =>
    have h := answer0_spec q O ξ (fun r x v => x ∈ I.D → Df x v ≤ 0 →
      x + r.1 • v ∈ I.D ∧ (∀ w, Df (x + r.1 • v) w = r.2 ⬝ᵥ w) ∧ (Df x v < 0 → 0 < r.1 ∧
        I.f (x + r.1 • v) ≤ I.f x + q.c1 * r.1 * Df x v ∧ q.c2 * Df x v ≤ Df (x + r.1 • v) v))
      (fun hist x v seed => horc hist x v seed)
    obtain ⟨-, hrep, -⟩ := h hx0 (by simp)
    rw [run_zero]
    refine ⟨hx0, fun w => by simpa using hrep w, hB0, le_rfl⟩
  | succ n ih =>
    obtain ⟨hx, hrep, hB, hf⟩ := ih
    have h := answer_spec q O ξ (fun r x v => x ∈ I.D → Df x v ≤ 0 →
      x + r.1 • v ∈ I.D ∧ (∀ w, Df (x + r.1 • v) w = r.2 ⬝ᵥ w) ∧ (Df x v < 0 → 0 < r.1 ∧
        I.f (x + r.1 • v) ≤ I.f x + q.c1 * r.1 * Df x v ∧ q.c2 * Df x v ≤ Df (x + r.1 • v) v))
      (fun hist x v seed => horc hist x v seed) n
    have hle : Df (run q O ξ n).x (direction (run q O ξ n).B (run q O ξ n).g) ≤ 0 := by
      rw [hrep, dir_pairing]
      have := posDef_quad_nonneg hB.inv (run q O ξ n).g
      linarith
    obtain ⟨hmem, hrep', hwolfe⟩ := h hx hle
    rw [run_succ]
    refine ⟨hmem, hrep', ?_, ?_⟩
    · by_cases hg0 : (run q O ξ n).g = 0
      · have : direction (run q O ξ n).B (run q O ξ n).g = 0 := by simp [direction, hg0]
        simp only [this, smul_zero, bfgsUpdate_zero]
        exact hB
      · have hdesc : Df (run q O ξ n).x (direction (run q O ξ n).B (run q O ξ n).g) < 0 := by
          rw [hrep, dir_pairing]
          have := posDef_quad_pos hB.inv hg0
          linarith
        obtain ⟨hη, -, hcurv⟩ := hwolfe hdesc
        have hv0 : direction (run q O ξ n).B (run q O ξ n).g ≠ 0 := by
          intro h0; rw [h0, map_zero] at hdesc; exact lt_irrefl _ hdesc
        apply upd_posDef hB (smul_ne_zero hη.ne' hv0)
        rw [sub_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← hrep', ← hrep]
        have h1 : 0 < (1 - q.c2) * -(Df (run q O ξ n).x
            (direction (run q O ξ n).B (run q O ξ n).g)) := mul_pos (by linarith) (by linarith)
        have h2 := mul_pos hη h1
        have h3 := mul_le_mul_of_nonneg_left hcurv hη.le
        linarith
    · by_cases hg0 : (run q O ξ n).g = 0
      · have : direction (run q O ξ n).B (run q O ξ n).g = 0 := by simp [direction, hg0]
        simp only [this, smul_zero, add_zero]
        exact hf
      · have hdesc : Df (run q O ξ n).x (direction (run q O ξ n).B (run q O ξ n).g) < 0 := by
          rw [hrep, dir_pairing]
          have := posDef_quad_pos hB.inv hg0
          linarith
        obtain ⟨hη, harm, -⟩ := hwolfe hdesc
        have : q.c1 * (answer q O ξ n).1 *
            Df (run q O ξ n).x (direction (run q O ξ n).B (run q O ξ n).g) ≤ 0 := by
          have hc : 0 ≤ q.c1 * (answer q O ξ n).1 := (mul_pos hc1 hη).le
          nlinarith
        linarith

lemma zero_persist {Df : Vec q.d → Vec q.d →L[ℝ] ℝ} (horc : OracleOK q I O Df) {n : ℕ}
    (hx : (run q O ξ n).x ∈ I.D) (hrep : ∀ w, Df (run q O ξ n).x w = (run q O ξ n).g ⬝ᵥ w)
    (hg : (run q O ξ n).g = 0) :
    (run q O ξ (n + 1)).x = (run q O ξ n).x ∧ (run q O ξ (n + 1)).g = 0 := by
  have h := answer_spec q O ξ (fun r x v => x ∈ I.D → Df x v ≤ 0 →
    x + r.1 • v ∈ I.D ∧ (∀ w, Df (x + r.1 • v) w = r.2 ⬝ᵥ w) ∧ (Df x v < 0 → 0 < r.1 ∧
      I.f (x + r.1 • v) ≤ I.f x + q.c1 * r.1 * Df x v ∧ q.c2 * Df x v ≤ Df (x + r.1 • v) v))
    (fun hist x v seed => horc hist x v seed) n
  have hdir : direction (run q O ξ n).B (run q O ξ n).g = 0 := by simp [direction, hg]
  obtain ⟨-, hrep', -⟩ := h hx (by rw [hdir, map_zero])
  rw [hdir, smul_zero, add_zero] at hrep'
  rw [run_succ, hdir, smul_zero, add_zero]
  refine ⟨rfl, ?_⟩
  apply vec_eq_of_dot
  intro w
  rw [← hrep', hrep, hg]

lemma run_x_succ (n : ℕ) : (run q O ξ (n + 1)).x =
    (run q O ξ n).x + (answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g := by
  rw [run_succ]

lemma run_g_succ (n : ℕ) : (run q O ξ (n + 1)).g = (answer q O ξ n).2 := by rw [run_succ]

lemma run_B_succ (n : ℕ) : (run q O ξ (n + 1)).B =
    bfgsUpdate (run q O ξ n).B ((answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g)
      ((answer q O ξ n).2 - (run q O ξ n).g) := by rw [run_succ]

lemma sum_shift (a : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), (if n = 0 then 0 else a (n - 1)) = ∑ j ∈ Finset.range m, a j := by
  rw [Finset.sum_range_succ']
  simp

end Main

end LongTails.Proofs.SelfConcordantBFGSRate
