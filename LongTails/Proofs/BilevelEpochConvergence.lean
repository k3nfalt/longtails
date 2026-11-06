import LongTails.Proofs.BilevelEpochDescent
import LongTails.Proofs.BilevelTuning

namespace LongTails.Proofs.BilevelEpochConvergence

open Finset BilevelEpochVector BilevelEpochDescent BilevelTuning
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma epoch_query_radius (Z D : ℕ → E) {m : ℕ} {B θ : ℝ}
    (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hprefix : ∀ k, k < m → (k : ℝ) * (∑ j ∈ range k, ‖D (j + 1)‖ ^ 2) ≤ B ^ 2) :
    ∀ k, k < m → ‖Z k + (1 - θ) • D k‖ ≤ 2 * B := by
  intro k hk
  have hh := prefix_radius Z D k hB hZ0 hD0 (fun j hj => hpos j (by omega)) (hprefix k hk)
  exact extrapolated_radius hθ hθ1 hh.1 hh.2

lemma failed_epoch_decrease {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (A x) x)
    {L ρ η B e : ℝ} {K m : ℕ}
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hη : 0 < η) (hB : 0 < B) (he : 0 < e)
    (hK : 2 ≤ K) (hm : 0 < m) (hmK : m ≤ K) (hηL : η * L ≤ 1 / 4)
    (hgrad : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hHess : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (hBe : ρ * B ^ 2 = e) (hmaster : 32 * η * (K : ℝ) ^ 2 * e ≤ B)
    (a : E) (hsym : (A a).toLinearMap.IsSymmetric) (hA : ‖A a‖ ≤ L)
    (Z D V : ℕ → E) (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < m → Z (k + 1) = Z k + D (k + 1))
    (hvel : ∀ k, k < m → D (k + 1) = (1 - 1 / (K : ℝ)) • D k - η • V k)
    (herr : ∀ k, k < m → ‖V k - g (a + (Z k + (1 - 1 / (K : ℝ)) • D k))‖ ≤ e / 100)
    (hprefix : ∀ k, k < m → (k : ℝ) * (∑ j ∈ range k, ‖D (j + 1)‖ ^ 2) ≤ B ^ 2)
    (hexit : B ^ 2 < (m : ℝ) * (∑ k ∈ range m, ‖D (k + 1)‖ ^ 2)) :
    f (a + Z m) - f a ≤ -(e * B) := by
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hθ : 0 < 1 / (K : ℝ) := by positivity
  have hθhalf : 1 / (K : ℝ) ≤ 1 / 2 := by apply one_div_le_one_div_of_le (by norm_num) hKR
  have hθ1 : 1 / (K : ℝ) ≤ 1 := by linarith
  have hp := master_decrease_parameters hη (show (1 : ℝ) ≤ K by linarith) hB he hBe hmaster
  have hquery := epoch_query_radius Z D hB.le hθ.le hθ1 hZ0 hD0 hpos hprefix
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let w := fun k => a + (Z k + (1 - 1 / (K : ℝ)) • D k)
  have hnext : ∀ k, k < r + 1 → a + Z (k + 1) = w k - η • V k := by
    intro k hk
    rw [hpos k hk, hvel k hk]
    dsimp [w]
    module
  by_cases hlarge : B ≤ η * ‖g (w r)‖
  · have hstep : ∀ k, k < r + 1 →
        8 * η * (f (a + Z (k + 1)) - f (a + Z k)) ≤
        5 * ‖D k‖ ^ 2 - 4 * ‖D (k + 1)‖ ^ 2 - 2 * η ^ 2 * ‖g (w k)‖ ^ 2 +
          8 * η * (e / 100) * ‖D k‖ + 6 * η ^ 2 * (e / 100) ^ 2 := by
      intro k hk
      have hh := smooth_step_energy hf hgrad hL hη hηL hθ.le hθ1 (a + Z k) (D k) (V k)
        (by simpa only [add_assoc] using herr k hk)
      rw [hnext k hk, hvel k hk]
      simpa only [w, add_assoc] using hh
    have hh := large_gradient_epoch (fun k => f (a + Z k)) D (fun k => g (w k)) r hη
      (by positivity) hB.le hD0 (hprefix r (by omega)) hlarge hstep
    simp only [hZ0, add_zero] at hh
    have hmKR : ((r + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hmK
    have hn := mul_le_mul_of_nonneg_right hmKR (show 0 ≤ 3 * η * (e / 100) ^ 2 by positivity)
    have hn' := hp.2.2.2.2.2.2.2
    have hdec := hp.2.2.2.2.2.1
    have hcross := hp.2.2.2.2.2.2.1
    have hnt : ((r + 1 : ℕ) : ℝ) * (3 * η * (e / 100) ^ 2) ≤ e * B := by nlinarith only [hn, hn']
    have hnη := mul_le_mul_of_nonneg_left hnt (show 0 ≤ 2 * η by positivity)
    have hcη := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 8 * η by positivity)
    push_cast at hnη
    apply (mul_le_mul_iff_right₀ (show 0 < 8 * η by positivity)).mp
    nlinarith only [hh, hdec, hnη, hcη, mul_pos hη (mul_pos he hB)]
  · have hend : ‖Z (r + 1)‖ ≤ 3 * B + η * (e / 100) := by
      have heq : Z (r + 1) = (Z r + (1 - 1 / (K : ℝ)) • D r) - η • V r := by
        rw [hpos r (by omega), hvel r (by omega)]
        module
      rw [heq]
      exact small_gradient_endpoint _ _ (g (w r)) hη.le (hquery r (by omega))
        (le_of_lt (lt_of_not_ge hlarge)) (herr r (by omega))
    have hf' : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x := fun x => (hf x).hasFDerivAt
    have hh := nonlinear_epoch_decrease hf' hg hρ.le hHess a hsym hA hη hθ hθhalf hηL
      Z D V (r + 1) hZ0 hD0 hpos hvel herr hquery hend
    have halg := small_exit_algebra hη hKpos (Nat.cast_nonneg (r + 1))
      (show ((r + 1 : ℕ) : ℝ) ≤ K by exact_mod_cast hmK) hB.le hρ.le
      (show 0 ≤ e / 100 by positivity) (show 0 ≤ e * B by positivity)
      (sum_nonneg fun _ _ => sq_nonneg _) hexit.le hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    have heq : -(3 * (1 / (K : ℝ)) / (8 * η)) = -(3 / (8 * η * K)) := by ring
    rw [heq, div_div_eq_mul_div] at hh
    have heq2 : 2 * η * (K : ℝ) / 1 = 2 * η * K := by ring
    rw [heq2] at hh
    exact hh.trans halg

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma prefix_movement_budget (D : ℕ → E) {K k : ℕ} (hk : k ≤ K) {B : ℝ}
    (hmove : (K : ℝ) * (∑ j ∈ range K, ‖D (j + 1)‖ ^ 2) ≤ B ^ 2) :
    (k : ℝ) * (∑ j ∈ range k, ‖D (j + 1)‖ ^ 2) ≤ B ^ 2 := by
  have hs : (∑ j ∈ range k, ‖D (j + 1)‖ ^ 2) ≤ ∑ j ∈ range K, ‖D (j + 1)‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_mono hk) (fun _ _ _ => sq_nonneg _)
  have hkR : (k : ℝ) ≤ K := by exact_mod_cast hk
  exact (mul_le_mul hkR hs (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg K)).trans hmove

omit [FiniteDimensional ℝ E] in
lemma successful_epoch_accuracy {g : E → E} {A : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (A x) x) {η ρ B e : ℝ} {K j : ℕ}
    (hη : 0 < η) (hρ : 0 ≤ ρ) (hB : 0 < B) (he : 0 < e) (hK : 2 ≤ K)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (hBe : ρ * B ^ 2 = e) (hlower : B ≤ 128 * η * (K : ℝ) ^ 2 * e)
    (a : E) (Z D V : ℕ → E) (hZ0 : Z 0 = 0) (hD0 : D 0 = 0)
    (hpos : ∀ k, k < K → Z (k + 1) = Z k + D (k + 1))
    (hvel : ∀ k, k < K → D (k + 1) = (1 - 1 / (K : ℝ)) • D k - η • V k)
    (herr : ∀ k, k < K → ‖V k - g (a + (Z k + (1 - 1 / (K : ℝ)) • D k))‖ ≤ e / 100)
    (hmove : (K : ℝ) * (∑ k ∈ range K, ‖D (k + 1)‖ ^ 2) ≤ B ^ 2)
    (hj : j ∈ Ico (K / 2) K)
    (hmin : ∀ k ∈ Ico (K / 2) K, ‖D (j + 1)‖ ^ 2 ≤ ‖D (k + 1)‖ ^ 2) :
    ‖g (a + ((j + 1 : ℕ) : ℝ)⁻¹ •
      (∑ k ∈ range (j + 1), (Z k + (1 - 1 / (K : ℝ)) • D k)))‖ ≤ 773 * e := by
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hθ : 0 ≤ 1 / (K : ℝ) := by positivity
  have hθ1 : 1 / (K : ℝ) ≤ 1 := (div_le_iff₀ hKpos).mpr (by linarith)
  have hjK : j + 1 ≤ K := by have := (mem_Ico.mp hj).2; omega
  have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hhalf : (K : ℝ) ≤ 2 * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show K ≤ 2 * (j + 1) by have := (mem_Ico.mp hj).1; omega)
  have hpref : ∀ k, k ≤ K → (k : ℝ) * (∑ i ∈ range k, ‖D (i + 1)‖ ^ 2) ≤ B ^ 2 :=
    fun k hk => prefix_movement_budget D hk hmove
  have hquery := epoch_query_radius Z D hB.le hθ hθ1 hZ0 hD0 hpos (fun k hk => hpref k (Nat.le_of_lt hk))
  have hzm := (prefix_radius Z D (j + 1) hB.le hZ0 hD0
    (fun k hk => hpos k (by omega)) (hpref (j + 1) hjK)).1
  have hdm := selected_movement_bound D (show 0 < K by omega) hB.le hmin hmove
  have hv := momentum_average_bound Z D V (Nat.succ_pos j) hη hθ hθ1 hZ0 hD0
    (fun k hk => hpos k (by omega)) (fun k hk => hvel k (by omega)) hzm hdm
  have hgav := average_gradient_bound hg hρ hLip a
    (fun k => Z k + (1 - 1 / (K : ℝ)) • D k) V (Nat.succ_pos j)
    (fun k hk => hquery k (by omega)) (fun k hk => herr k (by omega))
  have hvbound : ((1 / (K : ℝ)) * B + 2 * B / K) / (η * ((j + 1 : ℕ) : ℝ)) ≤ 6 * B / (η * (K : ℝ) ^ 2) := by
    apply (div_le_div_iff₀ (mul_pos hη hjpos) (by positivity : 0 < η * (K : ℝ) ^ 2)).mpr
    field_simp
    nlinarith only [hhalf]
  have hfinal : 6 * B / (η * (K : ℝ) ^ 2) ≤ 768 * e := by
    apply (div_le_iff₀ (by positivity : 0 < η * (K : ℝ) ^ 2)).mpr
    nlinarith only [hlower]
  have havg : ‖((j + 1 : ℕ) : ℝ)⁻¹ • (∑ k ∈ range (j + 1), V k)‖ ≤ 768 * e :=
    hv.trans (hvbound.trans hfinal)
  nlinarith only [hgav, havg, hBe, he]

end LongTails.Proofs.BilevelEpochConvergence
