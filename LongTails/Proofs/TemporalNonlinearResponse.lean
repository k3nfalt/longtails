import LongTails.Proofs.TemporalDifferenceResponse
import LongTails.Proofs.QuadraticTemporalEnergy

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def linearOrbit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V) (B : E →L[ℝ] V) (v0 : V) (e : ℕ → E) : ℕ → V
  | 0 => v0
  | n + 1 => T (linearOrbit T B v0 e n) + B (e n)

omit [CompleteSpace E] in
lemma energy_controls_coordinates (A : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) (s : E × E) :
    Real.sqrt μ * ‖s.1‖ ≤ energySeminorm A μ s ∧
      Real.sqrt μ * ‖s.2‖ ≤ energySeminorm A μ s := by
  have he := energySeminorm_sq A hμ.le s
  have hp := apply_nonneg (energySeminorm A μ) s
  have hs := Real.sq_sqrt hμ.le
  constructor
  · apply (sq_le_sq₀ (by positivity) hp).mp
    rw [mul_pow, hs]
    nlinarith [hlower s.1, sq_nonneg ‖s.2‖]
  · apply (sq_le_sq₀ (by positivity) hp).mp
    rw [mul_pow, hs]
    nlinarith [sq_nonneg ‖A s.1‖]

omit [CompleteSpace E] in
lemma energy_controls_query (A : E →L[ℝ] E) {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 ≤ θ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) (s : E × E) :
    Real.sqrt μ * ‖acceleratedQuery θ s‖ ≤ energySeminorm A μ s := by
  obtain ⟨hx, hz⟩ := energy_controls_coordinates A hμ hlower s
  have hden : 0 < 1 + θ := by linarith
  have hq : ‖acceleratedQuery θ s‖ ≤ (‖s.1‖ + θ * ‖s.2‖) / (1 + θ) := by
    simp only [acceleratedQuery, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + θ))]
    have hh := norm_add_le s.1 (θ • s.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] at hh
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_left hh (show 0 ≤ 1 / (1 + θ) by positivity)
  calc
    _ ≤ Real.sqrt μ * ((‖s.1‖ + θ * ‖s.2‖) / (1 + θ)) :=
      mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg _)
    _ ≤ energySeminorm A μ s := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      have hh := mul_le_mul_of_nonneg_left hz hθ
      nlinarith

def causalSum (ρ : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ρ ^ (n - 1 - i) * v i

lemma causalSum_succ (ρ : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    causalSum ρ v (n + 1) = ρ * causalSum ρ v n + v n := by
  rw [causalSum, Finset.sum_range_succ, causalSum, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hn : n - i = n - 1 - i + 1 := by omega
  rw [hn, pow_succ]
  ring

omit [CompleteSpace E] in
lemma seminorm_forcing_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V) (B : E →L[ℝ] V) (p : Seminorm ℝ V)
    {ρ β : ℝ} (hρ : 0 ≤ ρ)
    (hT : ∀ v, p (T v) ≤ ρ * p v) (hB : ∀ e, p (B e) ≤ β * ‖e‖)
    (v : ℕ → V) (e : ℕ → E)
    (hrec : ∀ k, v (k + 1) = T (v k) + B (e k)) (n : ℕ) :
    p (v n) ≤ ρ ^ n * p (v 0) + β * causalSum ρ (fun i => ‖e i‖) n := by
  induction n with
  | zero => simp [causalSum]
  | succ n ih =>
      rw [hrec]
      calc
        _ ≤ p (T (v n)) + p (B (e n)) := map_add_le_add p _ _
        _ ≤ ρ * p (v n) + β * ‖e n‖ := add_le_add (hT _) (hB _)
        _ ≤ ρ * (ρ ^ n * p (v 0) + β * causalSum ρ (fun i => ‖e i‖) n) + β * ‖e n‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ih hρ) le_rfl
        _ = _ := by rw [causalSum_succ, pow_succ]; ring

lemma causalSum_mono {ρ : ℝ} (hρ : 0 ≤ ρ) {v w : ℕ → ℝ}
    (hvw : ∀ i, v i ≤ w i) (n : ℕ) : causalSum ρ v n ≤ causalSum ρ w n := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hvw i) (pow_nonneg hρ _))

lemma causalSum_mul (ρ c : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    causalSum ρ (fun i => c * v i) n = c * causalSum ρ v n := by
  simp only [causalSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma scalar_forcing_envelope {ρ q F G : ℝ} (v : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hρq : ρ < q) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hstep : ∀ k, v (k + 1) ≤ ρ * v k + F * q ^ k + G) (n : ℕ) :
    v n ≤ ρ ^ n * v 0 + F * q ^ n / (q - ρ) + G / (1 - ρ) := by
  have hd : 0 < q - ρ := sub_pos.mpr hρq
  have hd' : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hq : 0 ≤ q := hρ.trans hρq.le
  induction n with
  | zero =>
      simp only [pow_zero, one_mul, mul_one]
      have h1 := div_nonneg hF hd.le
      have h2 := div_nonneg hG hd'.le
      linarith
  | succ n ih =>
      have hh := (hstep n).trans (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left ih hρ) le_rfl) le_rfl)
      calc
        _ ≤ ρ * (ρ ^ n * v 0 + F * q ^ n / (q - ρ) + G / (1 - ρ)) + F * q ^ n + G := hh
        _ = _ := by
          rw [pow_succ ρ n, pow_succ q n]
          field_simp [ne_of_gt hd, ne_of_gt hd']
          ring

lemma nonlinear_convolution_bootstrap {ρ A B C : ℝ} (v : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hv : ∀ n, 0 ≤ v n)
    (hrec : ∀ n, v n ≤ A * ρ ^ n + B + C * causalSum ρ (fun i => v i ^ 2) n)
    (hsmall : C * (A + 2 * B) ≤ (1 - ρ) / 2) (n : ℕ) :
    v n ≤ A * ((1 + ρ) / 2) ^ n + 2 * B := by
  let q := (1 + ρ) / 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  let w := fun k => A * ρ ^ k + B + C * causalSum ρ (fun i => v i ^ 2) k
  have hwrec (k : ℕ) : w (k + 1) = ρ * w k + (1 - ρ) * B + C * v k ^ 2 := by
    dsimp [w]
    rw [causalSum_succ, pow_succ]
    ring
  have hbound : ∀ k, w k ≤ A * q ^ k + 2 * B := by
    intro k
    induction k with
    | zero => simp only [w, causalSum, Finset.range_zero, Finset.sum_empty, mul_zero,
        pow_zero, mul_one, add_zero]; linarith
    | succ k ih =>
      have hvk : v k ≤ A * q ^ k + 2 * B := (hrec k).trans ih
      have hUk : A * q ^ k + 2 * B ≤ A + 2 * B := by
        have hh := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := k) hq hq1) hA
        linarith
      have hsq : v k ^ 2 ≤ (A + 2 * B) * (A * q ^ k + 2 * B) := by
        calc
          _ = v k * v k := pow_two _
          _ ≤ (A + 2 * B) * (A * q ^ k + 2 * B) :=
            mul_le_mul (hvk.trans hUk) hvk (hv k) (by positivity)
      have hU : 0 ≤ A * q ^ k + 2 * B := by positivity
      have hforce := mul_le_mul_of_nonneg_left hsq hC
      have hcoeff := mul_le_mul_of_nonneg_right hsmall hU
      have hw := mul_le_mul_of_nonneg_left ih hρ
      rw [hwrec, pow_succ q k]
      dsimp [q] at *
      nlinarith
  exact (hrec n).trans (hbound n)

end OracleTemplate.TemporalDiscrepancy
