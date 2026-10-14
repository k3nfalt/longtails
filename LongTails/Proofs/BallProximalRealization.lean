import LongTails.Proofs.BallProximalGram
import LongTails.Proofs.BallProximalPolyhedral
import LongTails.Proofs.BallProximalTrajectory
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BallProximal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_plane_eq {N : ℕ} {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) : ⟪a i • u i, u j⟫ = a j := by
  have hai := ne_of_gt (hap i (by omega))
  rw [real_inner_smul_left, hg i j hij hj]
  field_simp

lemma gram_plane_le {N : ℕ} {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {i j : ℕ} (hi : i < N) (hj : j < N) : ⟪a i • u i, u j⟫ ≤ a j := by
  rcases le_total i j with hij | hji
  · exact (gram_plane_eq hap hg hij hj).le
  · rw [real_inner_smul_left, real_inner_comm, hg j i hji hi]
    have haj := hap j hj
    have hai := hap i hi
    have hle := ham j i hji hi
    rw [← mul_div_assoc]
    apply (div_le_iff₀ haj).mpr
    nlinarith

def tailPoint (N : ℕ) (a : ℕ → ℝ) (u : ℕ → E) (r : ℝ) (i : ℕ) : E :=
  (∑ j ∈ Finset.Ico i N, u j) + (r / a (N - 1)) • u (N - 1)

def tailValue (N : ℕ) (a : ℕ → ℝ) (r : ℝ) (i : ℕ) : ℝ :=
  (∑ j ∈ Finset.Ico i N, a j) + r

lemma tailPoint_plane_le {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {j : ℕ} (hj : j < N) (r : ℝ) (i : ℕ) :
    ⟪a j • u j, tailPoint N a u r i⟫ ≤ tailValue N a r i := by
  have hl : N - 1 < N := by omega
  have he := gram_plane_eq hap hg (show j ≤ N - 1 by omega) hl
  have hal := ne_of_gt (hap _ hl)
  simp only [tailPoint, tailValue, inner_add_right, inner_sum, real_inner_smul_right, he]
  rw [div_mul_cancel₀ _ hal]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro k hk
  exact gram_plane_le hap ham hg hj (Finset.mem_Ico.mp hk).2

lemma tailPoint_plane_eq {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {j i : ℕ} (hj : j < N) (hji : j ≤ i) (r : ℝ) :
    ⟪a j • u j, tailPoint N a u r i⟫ = tailValue N a r i := by
  have hl : N - 1 < N := by omega
  have he := gram_plane_eq hap hg (show j ≤ N - 1 by omega) hl
  have hal := ne_of_gt (hap _ hl)
  simp only [tailPoint, tailValue, inner_add_right, inner_sum, real_inner_smul_right, he]
  rw [div_mul_cancel₀ _ hal]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  exact gram_plane_eq hap hg (le_trans hji hk'.1) hk'.2

lemma tailValue_nonneg {N : ℕ} {a : ℕ → ℝ}
    (hap : ∀ i < N, 0 < a i) {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    0 ≤ tailValue N a r i := by
  apply add_nonneg _ hr
  exact Finset.sum_nonneg (fun j hj => (hap j (Finset.mem_Ico.mp hj).2).le)

lemma polyObjective_tailPoint {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    polyObjective (fun j => a j • u j) N (tailPoint N a u r i) = tailValue N a r i := by
  apply le_antisymm
  · exact polyObjective_upper (fun j => a j • u j) (tailValue_nonneg hap hr i)
      (fun j hj => tailPoint_plane_le hN hap ham hg hj r i)
  · let j := min i (N - 1)
    have hj : j < N := by dsimp [j]; omega
    rw [← tailPoint_plane_eq (u := u) hN hap hg hj (show j ≤ i from min_le_left _ _) r]
    exact polyObjective_plane (fun j => a j • u j) hj (tailPoint N a u r i)

lemma tailPoint_step {N i : ℕ} (hi : i < N) (a : ℕ → ℝ) (u : ℕ → E) (r : ℝ) :
    tailPoint N a u r i = tailPoint N a u r (i + 1) + u i := by
  simp only [tailPoint]
  rw [Finset.sum_eq_sum_Ico_succ_bot hi]
  module

lemma tailValue_step {N i : ℕ} (hi : i < N) (a : ℕ → ℝ) (r : ℝ) :
    tailValue N a r i = tailValue N a r (i + 1) + a i := by
  simp only [tailValue]
  rw [Finset.sum_eq_sum_Ico_succ_bot hi]
  ring

lemma tailPoint_ball_minimum {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    (hu : ∀ i < N, ‖u i‖ = 1)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {r : ℝ} (hr : 0 ≤ r) {i : ℕ} (hi : i < N) :
    ∀ z, ‖z - tailPoint N a u r i‖ ≤ 1 →
      polyObjective (fun j => a j • u j) N (tailPoint N a u r (i + 1)) ≤
        polyObjective (fun j => a j • u j) N z := by
  have he : polyObjective (fun j => a j • u j) N (tailPoint N a u r (i + 1)) =
      ⟪a i • u i, tailPoint N a u r (i + 1)⟫ := by
    rw [polyObjective_tailPoint hN hap ham hg hr,
      tailPoint_plane_eq hN hap hg hi (by omega)]
  rw [tailPoint_step hi a u r]
  exact radial_ball_minimum (hap i hi) (hu i hi) (polyObjective_support _ hi he)


lemma tailPoint_distance_step {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) (hu : ∀ i < N, ‖u i‖ = 1)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    (r : ℝ) {i : ℕ} (hi : i < N) :
    ‖tailPoint N a u r i‖ ^ 2 =
      1 + 2 * tailValue N a r (i + 1) / a i + ‖tailPoint N a u r (i + 1)‖ ^ 2 := by
  have he := tailPoint_plane_eq hN hap hg hi (show i ≤ i + 1 by omega) r
  rw [real_inner_smul_left] at he
  have hai := ne_of_gt (hap i hi)
  have he' : ⟪u i, tailPoint N a u r (i + 1)⟫ = tailValue N a r (i + 1) / a i := by
    apply (eq_div_iff hai).mpr
    nlinarith
  rw [tailPoint_step hi a u r, norm_add_sq_real, real_inner_comm, he', hu i hi]
  ring

lemma tailPoint_distance {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) (hu : ∀ i < N, ‖u i‖ = 1)
    (hg : ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖tailPoint N a u r 0‖ ^ 2 =
      profileWork r (radialProfile 1 a N) + (r / a (N - 1)) ^ 2 := by
  have hh := radialProfile_energy_eq (t := 1) (c := a)
    (F := tailValue N a r) (D := fun i => ‖tailPoint N a u r i‖ ^ 2)
    (N := N) (by norm_num)
    (by intro i hi; simpa using tailValue_step hi a r)
    (by intro i hi; simpa using tailPoint_distance_step hN hap hu hg r hi)
  have hl : N - 1 < N := by omega
  have hn : ‖tailPoint N a u r N‖ = r / a (N - 1) := by
    simp only [tailPoint, Finset.Ico_self, Finset.sum_empty, zero_add, norm_smul,
      Real.norm_eq_abs, hu _ hl, mul_one]
    exact abs_of_nonneg (div_nonneg hr (hap _ hl).le)
  rw [hn] at hh
  simpa [tailValue] using hh.symm

lemma tailPoint_nearest_zero {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ} {u : ℕ → E}
    (hap : ∀ i < N, 0 < a i) {r : ℝ} (hr : 0 ≤ r) {z : E}
    (hz : polyObjective (fun j => a j • u j) N z ≤ 0) :
    ‖tailPoint N a u r 0‖ ≤ ‖tailPoint N a u r 0 - z‖ := by
  have hv : ∀ i < N, ⟪u i, z⟫ ≤ 0 := by
    intro i hi
    have hh := le_trans (polyObjective_plane (fun j => a j • u j) hi z) hz
    rw [real_inner_smul_left] at hh
    nlinarith [hap i hi]
  have hi : ⟪tailPoint N a u r 0, z⟫ ≤ 0 := by
    simp only [tailPoint, inner_add_left, sum_inner, real_inner_smul_left]
    apply add_nonpos
    · exact Finset.sum_nonpos (fun i hi => hv i (Finset.mem_Ico.mp hi).2)
    · exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hr (hap _ (by omega)).le)
        (hv _ (by omega))
  have he := norm_sub_sq_real (tailPoint N a u r 0) z
  nlinarith [sq_nonneg ‖z‖, norm_nonneg (tailPoint N a u r 0),
    norm_nonneg (tailPoint N a u r 0 - z)]


lemma realized_profile {N : ℕ} (hN : 0 < N) {a : ℕ → ℝ}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ (f : EuclideanSpace ℝ (Fin N) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin N)),
      ConvexOn ℝ Set.univ f ∧ Continuous f ∧ (∀ z, 0 ≤ f z) ∧ f 0 = 0 ∧
      (∀ i, f (x i) = tailValue N a r i) ∧
      ‖x 0‖ ^ 2 = profileWork r (radialProfile 1 a N) + (r / a (N - 1)) ^ 2 ∧
      (∀ z, f z ≤ 0 → ‖x 0‖ ≤ ‖x 0 - z‖) ∧
      ∀ i < N, ‖x (i + 1) - x i‖ = 1 ∧
        (∀ z, ‖z - x i‖ ≤ 1 → f (x (i + 1)) ≤ f z) ∧
        (∀ z, ‖z - x i‖ ≤ 1 → f z ≤ f (x (i + 1)) → z = x (i + 1)) := by
  obtain ⟨u, hu, hg⟩ := exists_unit_gram hap ham
  let v := fun j => a j • u j
  let f := polyObjective v N
  let x := tailPoint N a u r
  refine ⟨f, x, polyObjective_convex v N, polyObjective_continuous v N,
    polyObjective_nonneg v N, polyObjective_zero v N,
    polyObjective_tailPoint hN hap ham hg hr,
    tailPoint_distance hN hap hu hg hr,
    fun z hz => tailPoint_nearest_zero hN hap hr hz, ?_⟩
  intro i hi
  have hx : x i = x (i + 1) + u i := tailPoint_step hi a u r
  refine ⟨?_, tailPoint_ball_minimum hN hap ham hu hg hr hi, ?_⟩
  · rw [hx, show x (i + 1) - (x (i + 1) + u i) = -(u i) by module, norm_neg]
    exact hu i hi
  · intro z hz hf
    have he : f (x (i + 1)) = ⟪v i, x (i + 1)⟫ := by
      exact (polyObjective_tailPoint hN hap ham hg hr (i + 1)).trans
        (tailPoint_plane_eq hN hap hg hi (by omega) r).symm
    rw [hx] at hz
    exact radial_ball_unique (hap i hi) (hu i hi) (polyObjective_support v hi he z) hz hf


lemma profileWork_explicit (a : ℕ → ℝ) (N : ℕ) (r : ℝ) :
    profileWork r (radialProfile 1 a N) =
      N + 2 * ∑ i ∈ Finset.range N, (r + ∑ j ∈ Finset.Ico (i + 1) N, a j) / a i := by
  let D := fun i => ∑ j ∈ Finset.Ico i N, (1 + 2 * tailValue N a r (j + 1) / a j)
  have hD : ∀ i < N, D i = (1 : ℝ) ^ 2 + 2 * tailValue N a r (i + 1) / a i + D (i + 1) := by
    intro i hi
    dsimp [D]
    rw [Finset.sum_eq_sum_Ico_succ_bot hi]
    ring
  have hh := radialProfile_energy_eq (t := 1) (c := a) (N := N)
    (F := tailValue N a r) (D := D) (by norm_num)
    (by intro i hi; simpa using tailValue_step hi a r) hD
  simp only [tailValue, Finset.Ico_self, Finset.sum_empty, zero_add] at hh
  have hDN : D N = 0 := by simp [D]
  rw [hDN, add_zero] at hh
  rw [hh]
  dsimp [D]
  simp only [Nat.Ico_zero_eq_range, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tailValue]
  ring

end

end OracleTemplate.BallProximal
