import LongTails.Proofs.ReshuffledEpoch
import LongTails.Proofs.ReshufflingPermutationMoments

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledConvex

open LongTails.Setups.ReshuffledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ}
  [NeZero n]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma diag_moment (b : Fin n → E) {σ : ℝ} (hσ : ∑ i, ‖b i‖ ^ 2 ≤ n * σ ^ 2) (i : Fin n) :
    ∑ π : Equiv.Perm (Fin n), ‖b (π i)‖ ^ 2 ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * σ ^ 2 := by
  have hn := card_pos' n
  have hex : ∀ k : Fin n, ∑ π : Equiv.Perm (Fin n), ‖b (π k)‖ ^ 2 =
      ∑ π : Equiv.Perm (Fin n), ‖b (π i)‖ ^ 2 := by
    intro k
    apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i k))
    intro π
    simp [Equiv.Perm.mul_apply]
  have hperm : ∀ π : Equiv.Perm (Fin n), ∑ k, ‖b (π k)‖ ^ 2 = ∑ k, ‖b k‖ ^ 2 :=
    fun π => Equiv.sum_comp π (fun i => ‖b i‖ ^ 2)
  have htot : ∑ k : Fin n, ∑ π : Equiv.Perm (Fin n), ‖b (π k)‖ ^ 2 =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ k, ‖b k‖ ^ 2 := by
    rw [sum_comm]
    simp only [hperm, sum_const, card_univ, nsmul_eq_mul]
  have hleft : ∑ k : Fin n, ∑ π : Equiv.Perm (Fin n), ‖b (π k)‖ ^ 2 =
      n * ∑ π : Equiv.Perm (Fin n), ‖b (π i)‖ ^ 2 := by
    simp only [hex, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hleft] at htot
  have hN : (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin n)) := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hσ hN
  have h2 : (n : ℝ) * ∑ π : Equiv.Perm (Fin n), ‖b (π i)‖ ^ 2 ≤
      n * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * σ ^ 2) := by
    calc (n : ℝ) * ∑ π : Equiv.Perm (Fin n), ‖b (π i)‖ ^ 2 =
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ k, ‖b k‖ ^ 2 := htot
      _ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (n * σ ^ 2) := h1
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 hn

omit [CompleteSpace E] in
lemma subset_moment (b : Fin n → E) (hb : ∑ i, b i = 0) {σ : ℝ}
    (hσ : ∑ i, ‖b i‖ ^ 2 ≤ n * σ ^ 2) (s : Finset (Fin n)) :
    ∑ π : Equiv.Perm (Fin n), ‖∑ i ∈ s, b (π i)‖ ^ 2 ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * s.card * σ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd := diag_moment b hσ i
    have hc : (∑ π : Equiv.Perm (Fin n), ⟪b (π i), ∑ j ∈ s, b (π j)⟫) ≤ 0 := by
      simp_rw [inner_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_nonpos
      intro j hj
      exact Reshuffling.permutation_cross_nonpos b hb i j (fun hij => hi (hij ▸ hj))
    have he : (∑ π : Equiv.Perm (Fin n), ‖∑ j ∈ insert i s, b (π j)‖ ^ 2) =
        (∑ π : Equiv.Perm (Fin n), ‖b (π i)‖ ^ 2) +
        (∑ π : Equiv.Perm (Fin n), ‖∑ j ∈ s, b (π j)‖ ^ 2) +
        2 * (∑ π : Equiv.Perm (Fin n), ⟪b (π i), ∑ j ∈ s, b (π j)⟫) := by
      simp only [Finset.sum_insert hi, norm_add_sq_real, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    rw [he, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    nlinarith

omit [CompleteSpace E] in
lemma weighted_prefix_moment (b : Fin n → E) (hb : ∑ i, b i = 0) {σ c : ℝ}
    (hσ : ∑ i, ‖b i‖ ^ 2 ≤ n * σ ^ 2) (ℓ : Fin n → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hc : ∑ i, ℓ i ≤ c) (j : Fin n) :
    ∑ π : Equiv.Perm (Fin n), ℓ (π j) * ‖pre (fun m => b (π m)) j‖ ^ 2 ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (c * σ ^ 2) := by
  classical
  set S : Finset (Fin n) := univ.filter (fun m : Fin n => ¬ m.val < j.val) with hS
  have hjS : j ∈ S := by simp [hS]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨j, hjS⟩
  set T := ∑ π : Equiv.Perm (Fin n), ℓ (π j) * ‖pre (fun m => b (π m)) j‖ ^ 2 with hT
  have hswap : ∀ m ∈ S, ∑ π : Equiv.Perm (Fin n),
      ℓ (π m) * ‖pre (fun k => b (π k)) j‖ ^ 2 = T := by
    intro m hm
    have hmj : ¬ m.val < j.val := (mem_filter.mp hm).2
    apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j m))
    intro π
    have hpre : pre (fun k => b ((π * Equiv.swap j m) k)) j = pre (fun k => b (π k)) j := by
      unfold pre
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k.val < j.val := (mem_filter.mp hk).2
      have h1 : k ≠ j := fun h => by rw [h] at hkj; exact lt_irrefl _ hkj
      have h2 : k ≠ m := fun h => by rw [h] at hkj; exact hmj hkj
      show b ((π * Equiv.swap j m) k) = b (π k)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
    show ℓ (π m) * ‖pre (fun k => b (π k)) j‖ ^ 2 =
      ℓ ((π * Equiv.swap j m) j) * ‖pre (fun k => b ((π * Equiv.swap j m) k)) j‖ ^ 2
    rw [hpre, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have hsumS : (S.card : ℝ) * T =
      ∑ π : Equiv.Perm (Fin n), (∑ m ∈ S, ℓ (π m)) * ‖pre (fun k => b (π k)) j‖ ^ 2 := by
    have h1 : ∑ m ∈ S, ∑ π : Equiv.Perm (Fin n), ℓ (π m) * ‖pre (fun k => b (π k)) j‖ ^ 2 =
        S.card * T := by
      rw [Finset.sum_congr rfl hswap, sum_const, nsmul_eq_mul]
    rw [← h1, sum_comm]
    exact sum_congr rfl (fun π _ => by rw [sum_mul])
  have hwt : ∀ π : Equiv.Perm (Fin n), ∑ m ∈ S, ℓ (π m) ≤ c := fun π =>
    (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun m _ _ => hℓ _)).trans
      ((Equiv.sum_comp π ℓ).le.trans hc)
  have htail : ∀ π : Equiv.Perm (Fin n),
      ‖pre (fun k => b (π k)) j‖ ^ 2 = ‖∑ m ∈ S, b (π m)‖ ^ 2 := by
    intro π
    have hsplit := sum_filter_add_sum_filter_not univ (fun m : Fin n => m.val < j.val)
      (fun k => b (π k))
    have htot : ∑ k, b (π k) = 0 := (Equiv.sum_comp π b).trans hb
    rw [htot] at hsplit
    have he : pre (fun k => b (π k)) j = -∑ m ∈ S, b (π m) := eq_neg_of_add_eq_zero_left hsplit
    rw [he, norm_neg]
  have hmom := subset_moment b hb hσ S
  have h1 : (S.card : ℝ) * T ≤ c * ∑ π : Equiv.Perm (Fin n), ‖∑ m ∈ S, b (π m)‖ ^ 2 := by
    rw [hsumS, mul_sum]
    apply sum_le_sum
    intro π _
    rw [htail π]
    exact mul_le_mul_of_nonneg_right (hwt π) (sq_nonneg _)
  have hc0 : 0 ≤ c := (sum_nonneg (fun i _ => hℓ i)).trans hc
  have h2 := mul_le_mul_of_nonneg_left hmom hc0
  have h3 : (S.card : ℝ) * T ≤
      S.card * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (c * σ ^ 2)) := by
    calc (S.card : ℝ) * T ≤ c * ∑ π : Equiv.Perm (Fin n), ‖∑ m ∈ S, b (π m)‖ ^ 2 := h1
      _ ≤ c * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * S.card * σ ^ 2) := h2
      _ = _ := by ring
  exact le_of_mul_le_mul_left h3 hcard

variable {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
  {Lavg Lmax σ : ℝ} {xstar : E}

theorem scatter_sum_le (h : Hyp f g ℓ Lavg Lmax σ xstar) :
    ∑ π : Equiv.Perm (Fin n), scatter g ℓ xstar π ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ((n : ℝ) ^ 2 * Lavg * σ ^ 2) := by
  unfold scatter
  rw [sum_comm]
  have hb := fun j : Fin n => weighted_prefix_moment (fun i => g i xstar) h.sum_star
    h.sum_noise_le ℓ h.nonneg h.sum_ell_le j
  calc ∑ j : Fin n, ∑ π : Equiv.Perm (Fin n),
        ℓ (π j) * ‖pre (fun m => g (π m) xstar) j‖ ^ 2
      ≤ ∑ _j : Fin n, (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (n * Lavg * σ ^ 2) :=
        sum_le_sum (fun j _ => hb j)
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem scatter_le (h : Hyp f g ℓ Lavg Lmax σ xstar) (π : Equiv.Perm (Fin n)) :
    scatter g ℓ xstar π ≤ (n : ℝ) ^ 3 * Lavg * σ ^ 2 := by
  have hn := card_pos' n
  have hpre : ∀ j : Fin n, ‖pre (fun m => g (π m) xstar) j‖ ^ 2 ≤ (n : ℝ) ^ 2 * σ ^ 2 := by
    intro j
    have h1 := norm_pre_le (fun m => g (π m) xstar) j
    have h2 : (∑ m : Fin n, ‖g (π m) xstar‖) ^ 2 ≤ (n : ℝ) * ∑ m : Fin n, ‖g (π m) xstar‖ ^ 2 := by
      have := sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin n => (1 : ℝ))
        (fun m => ‖g (π m) xstar‖)
      simpa using this
    have h3 : ∑ m : Fin n, ‖g (π m) xstar‖ ^ 2 = ∑ i, ‖g i xstar‖ ^ 2 :=
      Equiv.sum_comp π (fun i => ‖g i xstar‖ ^ 2)
    have h4 := h.sum_noise_le
    calc ‖pre (fun m => g (π m) xstar) j‖ ^ 2 ≤ (∑ m : Fin n, ‖g (π m) xstar‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (n : ℝ) * ∑ m : Fin n, ‖g (π m) xstar‖ ^ 2 := h2
      _ ≤ (n : ℝ) * (n * σ ^ 2) := by rw [h3]; exact mul_le_mul_of_nonneg_left h4 hn.le
      _ = _ := by ring
  unfold scatter
  calc ∑ j : Fin n, ℓ (π j) * ‖pre (fun m => g (π m) xstar) j‖ ^ 2
      ≤ ∑ j : Fin n, ℓ (π j) * ((n : ℝ) ^ 2 * σ ^ 2) :=
        sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpre j) (h.nonneg _))
    _ = (∑ i, ℓ i) * ((n : ℝ) ^ 2 * σ ^ 2) := by
        rw [← sum_mul]; congr 1; exact Equiv.sum_comp π ℓ
    _ ≤ (n * Lavg) * ((n : ℝ) ^ 2 * σ ^ 2) :=
        mul_le_mul_of_nonneg_right h.sum_ell_le (by positivity)
    _ = _ := by ring

end OracleTemplate.ReshuffledConvex
