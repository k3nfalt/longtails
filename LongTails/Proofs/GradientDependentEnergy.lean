import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace LongTails.Proofs.GradientDependentEnergy

lemma incoming_gradient_charge {g a b d e μ x y ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hμ : 0 ≤ μ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hab : a ≤ 2 * b) (hde : d ≤ e) (hyρ : y ≤ ρ)
    (hcap : μ * (x - ρ) = 0)
    (hg : g ≤ 4 * (a * x ^ 2 + d * x + μ * x)) :
    g * y ≤ 9 * (a * x ^ 3 + d * x ^ 2 + μ * x ^ 2) +
      5 * (b * y ^ 3 + e * y ^ 2) := by
  have hcubic := mul_nonneg ha
    (mul_nonneg (sq_nonneg (x - y)) (show 0 ≤ 2 * x + y by positivity))
  have hratio := mul_le_mul_of_nonneg_right hab (pow_nonneg hy 3)
  have hquad := mul_nonneg hd (sq_nonneg (x - y))
  have hdelta := mul_le_mul_of_nonneg_right hde (sq_nonneg y)
  have hmu := mul_le_mul_of_nonneg_left hyρ (mul_nonneg hμ hx)
  have hcapx := congrArg (fun t : ℝ => t * x) hcap
  have hgy := mul_le_mul_of_nonneg_right hg hy
  have ha3 : 0 ≤ a * x ^ 3 := by positivity
  have hd2 : 0 ≤ d * x ^ 2 := by positivity
  have hm2 : 0 ≤ μ * x ^ 2 := by positivity
  have hb3 : 0 ≤ b * y ^ 3 := by positivity
  have he2 : 0 ≤ e * y ^ 2 := by positivity
  nlinarith

lemma quadratic_cubic_interpolation {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) :
    r ^ 2 ≤ b ^ 2 + r ^ 3 / b := by
  by_cases h : r ≤ b
  · have hs : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hr h 2
    have hc : 0 ≤ r ^ 3 / b := by positivity
    linarith
  · have hbr : b ≤ r := (lt_of_not_ge h).le
    have hc := mul_le_mul_of_nonneg_right hbr (sq_nonneg r)
    have hd : r ^ 2 ≤ r ^ 3 / b := (le_div_iff₀ hb).mpr (by nlinarith)
    nlinarith [sq_nonneg b]

lemma weighted_linear_charge {ι : Type*} (I : Finset ι) (d r : ι → ℝ)
    {R E : ℝ} (hR : 0 < R) (hd : ∀ i ∈ I, 0 ≤ d i)
    (hsum : ∑ i ∈ I, d i ≤ 100 * R ^ 2 * E)
    (henergy : ∑ i ∈ I, d i * r i ^ 2 ≤ E) :
    ∑ i ∈ I, d i * r i ≤ 10 * R * E := by
  have hs : ∀ i ∈ I, 20 * R * (d i * r i) ≤
      100 * R ^ 2 * (d i * r i ^ 2) + d i := by
    intro i hi
    nlinarith [mul_nonneg (hd i hi) (sq_nonneg (10 * R * r i - 1))]
  have hh := Finset.sum_le_sum hs
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have he := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 100 * R ^ 2 by positivity)
  nlinarith

lemma fresh_gradient_bound {r σ μ g h L₀ L₁ : ℝ}
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hμ : 0 ≤ μ) (hh : 0 ≤ h)
    (hcap : L₁ * r ^ 2 ≤ 1 / 10000)
    (htune : 100 * (L₀ + L₁ * g) ≤ σ)
    (hgrad : h ≤ μ * r + σ * r ^ 2 +
      2 * (L₀ + L₁ * g + L₁ * h) * r ^ 2) :
    h ≤ 2 * σ * r ^ 2 + 2 * μ * r := by
  have hc := mul_le_mul_of_nonneg_right hcap hh
  have ht := mul_le_mul_of_nonneg_right htune (sq_nonneg r)
  have hs : 0 ≤ σ * r ^ 2 := by positivity
  have hm : 0 ≤ μ * r := by positivity
  nlinarith

lemma global_absorption {S C D U E σ₀ T m L₀ L₁ Δ ε b q v R : ℝ}
    (hS : S ≤ 4 * C + 4 * D + 4 * U)
    (hC : C ≤ b ^ 2 * (2 * σ₀ + 200 * T * m * L₀ + 200 * L₁ * S) + E / b)
    (hD : D ≤ C / 25 + 10 * R * E)
    (hU : U ≤ (100 * v + ε / Δ) * E)
    (hEΔ : E ≤ 3 * Δ)
    (hσ₀ : σ₀ ≤ 500 * m * L₀ + 60000 * L₁ * v * Δ)
    (hT : 0 ≤ T) (hSn : 0 ≤ S) (hCn : 0 ≤ C)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hb : 0 < b)
    (hv : 0 ≤ v) (hR : v ≤ R)
    (hbq : b ^ 2 * m * L₀ ≤ ε / 10000)
    (hbv : b ^ 2 * L₁ ≤ 1 / 10000)
    (hbinv : 1 / b = 100 * (q + v)) :
    S ≤ S / 10 + T * ε / 10 + 1500 * Δ * q + 2880 * Δ * R + 25 * ε / 2 := by
  have hRv : 0 ≤ R := hv.trans hR
  have hsig := mul_le_mul_of_nonneg_left hσ₀ (sq_nonneg b)
  have hl := mul_le_mul_of_nonneg_right hbq (show 0 ≤ 200 * T by positivity)
  have hs := mul_le_mul_of_nonneg_right hbv (show 0 ≤ 200 * S by positivity)
  have hinit := mul_le_mul_of_nonneg_right hbv (show 0 ≤ 60000 * v * Δ by positivity)
  have he := mul_le_mul_of_nonneg_right hEΔ (show 0 ≤ 1 / b by positivity)
  have heq : E / b = E * (1 / b) := by ring
  rw [hbinv] at he
  have hc : C ≤ ε / 10 + T * ε / 50 + S / 50 + 300 * Δ * q + 312 * Δ * v := by
    rw [heq, hbinv] at hC
    nlinarith
  have hd := mul_le_mul_of_nonneg_right hEΔ (show 0 ≤ 10 * R by positivity)
  have hu := mul_le_mul_of_nonneg_right hEΔ (show 0 ≤ 100 * v + ε / Δ by positivity)
  have hcancel : ε / Δ * Δ = ε := div_mul_cancel₀ ε (ne_of_gt hΔ)
  have hvr := mul_le_mul_of_nonneg_left hR (show 0 ≤ Δ by positivity)
  nlinarith

lemma quadratic_cubic_burnin {u : ℝ} (hu : 0 ≤ u) :
    200 * u ^ 2 ≤ 1 / 4 + 3000 * u ^ 3 := by
  have h := mul_nonneg (sq_nonneg (u - 2 / 45))
    (show 0 ≤ u + 1 / 45 by positivity)
  nlinarith

lemma horizon_suffices {S T Δ ε q R : ℝ}
    (hε : 0 < ε) (hΔ : 0 ≤ Δ) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hS : S ≤ S / 10 + T * ε / 10 + 1500 * Δ * q +
      2880 * Δ * R + 25 * ε / 2)
    (hT : 27000 * Δ * q / ε + 15000 * Δ * R / ε + 72 ≤ T) :
    S < T * ε := by
  have ht := mul_le_mul_of_nonneg_right hT hε.le
  have hcq : (27000 * Δ * q / ε) * ε = 27000 * Δ * q :=
    div_mul_cancel₀ _ (ne_of_gt hε)
  have hcR : (15000 * Δ * R / ε) * ε = 15000 * Δ * R :=
    div_mul_cancel₀ _ (ne_of_gt hε)
  have hpq : 0 ≤ Δ * q := mul_nonneg hΔ hq
  have hpR : 0 ≤ Δ * R := mul_nonneg hΔ hR
  nlinarith

lemma prefix_transport {V : Type*} [NormedAddCommGroup V]
    (H : ℕ → V) (r e g : ℕ → ℝ) {L₀ L₁ : ℝ} (n : ℕ)
    (hL : 0 ≤ L₁) (he : ∀ j ≤ n, 0 ≤ e j)
    (hin : ∀ j < n, g j * r j ≤ 9 * e j + 5 * e (j + 1))
    (hout : ∀ j < n, g (j + 1) * r j ≤ 4 * e (j + 1))
    (hH : ∀ j < n, ‖H (j + 1) - H j‖ ≤
      2 * L₀ * r j + 2 * L₁ * (g j + g (j + 1)) * r j) :
    ‖H n - H 0‖ ≤ 2 * L₀ * (∑ j ∈ Finset.range n, r j) +
      36 * L₁ * (∑ j ∈ Finset.range (n + 1), e j) := by
  have htel : ∀ k, ‖H k - H 0‖ ≤ ∑ j ∈ Finset.range k, ‖H (j + 1) - H j‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hh := norm_add_le (H (k + 1) - H k) (H k - H 0)
      have hid : H (k + 1) - H k + (H k - H 0) = H (k + 1) - H 0 := by abel
      rw [hid] at hh
      linarith
  have hseg (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖H (j + 1) - H j‖ ≤ 2 * L₀ * r j + 18 * L₁ * (e j + e (j + 1)) := by
    have hjn := Finset.mem_range.mp hj
    have hi := hin j hjn
    have ho := hout j hjn
    have hh := hH j hjn
    have hc := mul_le_mul_of_nonneg_left (add_le_add hi ho) (show 0 ≤ 2 * L₁ by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum hseg
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hprev : ∑ j ∈ Finset.range n, e j ≤ ∑ j ∈ Finset.range (n + 1), e j := by
    rw [Finset.sum_range_succ]
    linarith [he n le_rfl]
  have hnext : ∑ j ∈ Finset.range n, e (j + 1) ≤ ∑ j ∈ Finset.range (n + 1), e j := by
    rw [Finset.sum_range_succ']
    linarith [he 0 (Nat.zero_le n)]
  have hm := mul_le_mul_of_nonneg_left (add_le_add hprev hnext) (show 0 ≤ 18 * L₁ by positivity)
  have hh := htel n
  nlinarith

lemma fresh_coefficient_recurrence {σ σnext r μ h c L₁ v : ℝ}
    (hσ : 0 ≤ σ) (hr : 0 ≤ r)
    (hL : 0 ≤ L₁) (hv : 0 ≤ v) (hv2 : v ^ 2 = L₁)
    (hg : h ≤ 2 * σ * r ^ 2 + 2 * μ * r)
    (hcap : L₁ * μ * r ≤ 100 * L₁ * v * μ * r ^ 2)
    (hnext : σnext ≤ σ / 2 + c + 100 * L₁ * h) :
    σnext ≤ (3 / 4) * σ + c +
      20000 * L₁ * v * (σ * r ^ 3 + μ * r ^ 2) := by
  have hsmall := quadratic_cubic_burnin (mul_nonneg hv hr)
  have hsmallσ := mul_le_mul_of_nonneg_left hsmall hσ
  have hgrad := mul_le_mul_of_nonneg_left hg (show 0 ≤ 100 * L₁ by positivity)
  have hpos : 0 ≤ L₁ * v * σ * r ^ 3 := by positivity
  have heq : (v * r) ^ 2 = L₁ * r ^ 2 := by rw [mul_pow, hv2]
  have heq3 : (v * r) ^ 3 = L₁ * v * r ^ 3 := by rw [mul_pow, pow_succ v 2, hv2]
  rw [heq, heq3] at hsmallσ
  nlinarith

lemma burnin_recurrence (σ e : ℕ → ℝ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : ∀ j, 0 ≤ e j)
    (hσ : ∀ j, σ (j + 1) ≤ (3 / 4) * σ j + c + d * e j) (k : ℕ) :
    σ k ≤ (3 / 4) ^ k * σ 0 + 4 * c + d * ∑ j ∈ Finset.range k, e j := by
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hh := hσ k
    have hsum : 0 ≤ ∑ j ∈ Finset.range k, e j := Finset.sum_nonneg (fun j _ => he j)
    have hde := mul_nonneg hd hsum
    nlinarith

lemma coefficient_prefix_sum (σ g : ℕ → ℝ) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hσ : ∀ j, 0 ≤ σ j) (hg : ∀ j, 0 ≤ g j)
    (hrec : ∀ j, σ (j + 1) ≤ σ j / 2 + c + d * g (j + 1)) (n : ℕ) :
    ∑ j ∈ Finset.range n, σ j ≤ 2 * σ 0 + 2 * n * c +
      2 * d * ∑ j ∈ Finset.range n, g (j + 1) := by
  have hstrong (k : ℕ) : ∑ j ∈ Finset.range (k + 1), σ j ≤
      2 * σ 0 + 2 * k * c + 2 * d * ∑ j ∈ Finset.range k, g (j + 1) - σ k := by
    induction k with
    | zero => simp; ring_nf; exact le_rfl
    | succ k ih =>
      rw [Finset.sum_range_succ (f := σ), Finset.sum_range_succ (f := fun j => g (j + 1))]
      push_cast
      have hh := hrec k
      nlinarith
  cases n with
  | zero => simp; exact hσ 0
  | succ n =>
    have hh := hstrong n
    rw [Finset.sum_range_succ (f := fun j => g (j + 1))]
    push_cast
    have hp := mul_nonneg hd (hg (n + 1))
    have hs := hσ n
    nlinarith

lemma cubic_sum_interpolation {ι : Type*} (I : Finset ι) (σ r : ι → ℝ)
    {b E : ℝ} (hb : 0 < b) (hσ : ∀ i ∈ I, 0 ≤ σ i) (hr : ∀ i ∈ I, 0 ≤ r i)
    (hE : ∑ i ∈ I, σ i * r i ^ 3 ≤ E) :
    ∑ i ∈ I, σ i * r i ^ 2 ≤ b ^ 2 * (∑ i ∈ I, σ i) + E / b := by
  have hh := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (quadratic_cubic_interpolation (hr i hi) hb) (hσ i hi))
  have he := div_le_div_of_nonneg_right hE hb.le
  have hid : (∑ i ∈ I, σ i * (b ^ 2 + r i ^ 3 / b)) =
      b ^ 2 * (∑ i ∈ I, σ i) + (∑ i ∈ I, σ i * r i ^ 3) / b := by
    simp only [mul_add, Finset.sum_add_distrib, mul_div_assoc, Finset.sum_div,
      ← Finset.sum_mul]
    ring
  rw [hid] at hh
  linarith

lemma path_damping_charge {ι : Type*} (I : Finset ι) (σ r path : ι → ℝ)
    {L₀ m : ℝ} (hL : 0 ≤ L₀) (hr : ∀ i ∈ I, 0 ≤ r i)
    (hm : (I.card : ℝ) ≤ m)
    (hpath : ∀ i ∈ I, path i ≤ ∑ j ∈ I, r j)
    (hσ : ∀ i ∈ I, 100 * m * L₀ ≤ σ i) :
    ∑ i ∈ I, 4 * L₀ * path i * r i ≤ (∑ i ∈ I, σ i * r i ^ 2) / 25 := by
  have hp := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpath i hi)
      (show 0 ≤ 4 * L₀ by positivity)) (hr i hi))
  have hq : (∑ i ∈ I, r i) ^ 2 ≤ m * ∑ i ∈ I, r i ^ 2 :=
    (sq_sum_le_card_mul_sum_sq (s := I) (f := r)).trans
      (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg (fun i _ => sq_nonneg (r i))))
  have hs := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_right (hσ i hi) (sq_nonneg (r i)))
  simp only [← Finset.mul_sum] at hp hs
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * L₀ by positivity)
  nlinarith

lemma cap_energy_bound {ρ μ r σ δ : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hcap : μ * (r - ρ) = 0) :
    μ * r ≤ (σ * r ^ 3 + δ * r ^ 2 + μ * r ^ 2) / ρ := by
  apply (le_div_iff₀ hρ).mpr
  have hh := congrArg (fun t : ℝ => t * r) hcap
  have hs : 0 ≤ σ * r ^ 3 := by positivity
  have hd : 0 ≤ δ * r ^ 2 := by positivity
  nlinarith

end LongTails.Proofs.GradientDependentEnergy
