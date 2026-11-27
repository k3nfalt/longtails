import LongTails.Proofs.SlidingWireBlock

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireGeometry

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireBlock FrontierChainProfiles FrontierChain FrontierChainGeometry
open Classical

variable {d k : ℕ}

noncomputable def pt (π : Fin (k + 1) ↪ Fin d) (u : Point d) (p : ℕ) : ℝ :=
  if h : p < k + 1 then u (π ⟨p, h⟩) else 0

lemma pt_eq (π : Fin (k + 1) ↪ Fin d) (u : Point d) (p : Fin (k + 1)) :
    pt π u p.val = u (π p) := by
  simp [pt, p.isLt]

lemma single_emb (π : Fin (k + 1) ↪ Fin d) (p q : Fin (k + 1)) :
    (EuclideanSpace.single (π p) (1 : ℝ) : Point d) (π q) = if q = p then 1 else 0 := by
  rw [SlidingLowerChain.esingle_apply]
  by_cases h : q = p
  · simp [h]
  · rw [ite_eq_right (fun h' => h (π.injective h')), ite_eq_right h]

lemma component (r : ℕ) (δ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) (p : Fin (k + 1)) :
    field r δ π u (π p) =
      (if p.val = 0 then -potentialSlope (pt π u 0) else 0) +
      (if p.val < k then linkL r δ p.val (pt π u p.val) (pt π u (p.val + 1)) else 0) +
      (if 1 ≤ p.val then linkR r δ (p.val - 1) (pt π u (p.val - 1)) (pt π u p.val) else 0) := by
  have hi := field_inner r δ π u (EuclideanSpace.single (π p) (1 : ℝ))
  rw [EuclideanSpace.inner_single_right] at hi
  simp only [conj_trivial, one_mul] at hi
  rw [hi]
  simp only [single_emb]
  rw [Finset.sum_add_distrib]
  have h1 : -potentialSlope (u (π 0)) * (if (0 : Fin (k + 1)) = p then (1 : ℝ) else 0) =
      if p.val = 0 then -potentialSlope (pt π u 0) else 0 := by
    by_cases h0 : p.val = 0
    · have hp : (0 : Fin (k + 1)) = p := Fin.ext (by simp [h0])
      rw [ite_eq_left h0, ite_eq_left hp]
      simp [pt]
    · have hp : ¬ (0 : Fin (k + 1)) = p := fun h => h0 (by rw [← h]; rfl)
      rw [ite_eq_right h0, ite_eq_right hp]; ring
  have h2 : (∑ i : Fin k, linkL r δ i.val (u (π i.castSucc)) (u (π i.succ)) *
      (if i.castSucc = p then (1 : ℝ) else 0)) =
      if p.val < k then linkL r δ p.val (pt π u p.val) (pt π u (p.val + 1)) else 0 := by
    by_cases hp : p.val < k
    · rw [ite_eq_left hp, Finset.sum_eq_single ⟨p.val, hp⟩]
      · have hc : (⟨p.val, hp⟩ : Fin k).castSucc = p := Fin.ext rfl
        rw [ite_eq_left hc, mul_one]
        simp [pt, hp, Nat.lt_succ_of_lt hp]
      · intro j _ hj
        rw [ite_eq_right, mul_zero]
        intro hc
        apply hj
        exact Fin.ext (by simpa using congrArg Fin.val hc)
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hp]
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right, mul_zero]
      intro hc
      apply hp
      rw [← hc]
      exact j.isLt
  have h3 : (∑ i : Fin k, linkR r δ i.val (u (π i.castSucc)) (u (π i.succ)) *
      (if i.succ = p then (1 : ℝ) else 0)) =
      if 1 ≤ p.val then linkR r δ (p.val - 1) (pt π u (p.val - 1)) (pt π u p.val) else 0 := by
    by_cases hp : 1 ≤ p.val
    · have hlt : p.val - 1 < k := by have := p.isLt; omega
      rw [ite_eq_left hp, Finset.sum_eq_single ⟨p.val - 1, hlt⟩]
      · have hc : (⟨p.val - 1, hlt⟩ : Fin k).succ = p := Fin.ext (by simp; omega)
        rw [ite_eq_left hc, mul_one]
        have e1 : u (π (⟨p.val - 1, hlt⟩ : Fin k).castSucc) = pt π u (p.val - 1) := by
          simp [pt, show p.val - 1 < k + 1 by omega]
        have e2 : u (π (⟨p.val - 1, hlt⟩ : Fin k).succ) = pt π u p.val := by
          rw [hc, pt_eq]
        rw [e1, e2]
      · intro j _ hj
        rw [ite_eq_right, mul_zero]
        intro hc
        apply hj
        ext
        have := congrArg Fin.val hc
        simp at this
        simp; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hp]
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right, mul_zero]
      intro hc
      apply hp
      have := congrArg Fin.val hc
      simp at this
      omega
  rw [h1, h2, h3]
  ring


lemma phase_eq (r i j : ℕ) (hj : j < r ^ 2 + 2) : phase r (i * (r ^ 2 + 2) + j) = j := by
  unfold phase
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

lemma phase_pred (r i : ℕ) (hi : 1 ≤ i) : phase r (i * (r ^ 2 + 2) - 1) = r ^ 2 + 1 := by
  have he : i * (r ^ 2 + 2) - 1 = (i - 1) * (r ^ 2 + 2) + (r ^ 2 + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [he, phase_eq r (i - 1) (r ^ 2 + 1) (by omega)]

lemma linkL_start (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) (hr : 1 ≤ r) (h : phase r l = 0) :
    linkL r δ l s t = -7 * spS δ (-7 * s + r * t) := by
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have h1 : ¬ (0 = r ^ 2 + 1) := by omega
  simp only [linkL, stretch, cA, cB, h, h1, ite_true, ite_false]

lemma linkR_start (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) (hr : 1 ≤ r) (h : phase r l = 0) :
    linkR r δ l s t = r * spS δ (-7 * s + r * t) := by
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have h1 : ¬ (0 = r ^ 2 + 1) := by omega
  simp only [linkR, stretch, cA, cB, h, h1, ite_true, ite_false]

lemma linkL_mid (r : ℕ) (δ : ℝ) (l j : ℕ) (s t : ℝ) (h : phase r l = j) (h1 : 1 ≤ j)
    (h2 : j < r ^ 2) : linkL r δ l s t = (r : ℝ) ^ 2 * spS δ ((r : ℝ) ^ 2 * (s - t)) := by
  have a1 : ¬ (j = r ^ 2 + 1) := by omega
  have a2 : ¬ (j = 0) := by omega
  have a3 : ¬ (j = r ^ 2) := by omega
  simp only [linkL, stretch, cA, cB, h, a1, a2, a3, ite_false]
  congr 2
  ring

lemma linkR_mid (r : ℕ) (δ : ℝ) (l j : ℕ) (s t : ℝ) (h : phase r l = j) (h1 : 1 ≤ j)
    (h2 : j < r ^ 2) : linkR r δ l s t = -((r : ℝ) ^ 2) * spS δ ((r : ℝ) ^ 2 * (s - t)) := by
  have a1 : ¬ (j = r ^ 2 + 1) := by omega
  have a2 : ¬ (j = 0) := by omega
  have a3 : ¬ (j = r ^ 2) := by omega
  simp only [linkR, stretch, cA, cB, h, a1, a2, a3, ite_false]
  congr 2
  ring

lemma linkL_end (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) (hr : 1 ≤ r) (h : phase r l = r ^ 2) :
    linkL r δ l s t = r * spS δ (r * s - 7 / 2 * t) := by
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have a1 : ¬ (r ^ 2 = r ^ 2 + 1) := by omega
  have a2 : ¬ (r ^ 2 = 0) := by omega
  simp only [linkL, stretch, cA, cB, h, a1, a2, ite_true, ite_false]
  congr 2
  ring

lemma linkR_end (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) (hr : 1 ≤ r) (h : phase r l = r ^ 2) :
    linkR r δ l s t = -7 / 2 * spS δ (r * s - 7 / 2 * t) := by
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have a1 : ¬ (r ^ 2 = r ^ 2 + 1) := by omega
  have a2 : ¬ (r ^ 2 = 0) := by omega
  simp only [linkR, stretch, cA, cB, h, a1, a2, ite_true, ite_false]
  congr 2
  ring

lemma linkL_gate (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) (h : phase r l = r ^ 2 + 1) :
    linkL r δ l s t = edgeLeft s t := by
  unfold linkL; rw [ite_eq_left h]

lemma linkR_gate (r : ℕ) (δ : ℝ) (l : ℕ) (s t : ℝ) (h : phase r l = r ^ 2 + 1) :
    linkR r δ l s t = edgeRight s t := by
  unfold linkR; rw [ite_eq_left h]

noncomputable def blockOf (r : ℕ) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d)
    (u : Point d) (i : ℕ) : Block :=
  ⟨r, δ, pt π u (i * (r ^ 2 + 2)), pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1),
    fun j => pt π u (i * (r ^ 2 + 2) + j)⟩

lemma mul_facts (r i T : ℕ) (hi : i < T) : i * (r ^ 2 + 2) + (r ^ 2 + 2) ≤ T * (r ^ 2 + 2) := by
  have : (i + 1) * (r ^ 2 + 2) ≤ T * (r ^ 2 + 2) := Nat.mul_le_mul_right _ hi
  linarith [show (i + 1) * (r ^ 2 + 2) = i * (r ^ 2 + 2) + (r ^ 2 + 2) by ring]

lemma comp_x (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d)
    (u : Point d) (i : ℕ) (hi : i ≤ T) (hp : i * (r ^ 2 + 2) < T * (r ^ 2 + 2) + 1) :
    field r δ π u (π ⟨i * (r ^ 2 + 2), hp⟩) =
      (if i = 0 then -potentialSlope (pt π u 0)
        else edgeRight (pt π u (i * (r ^ 2 + 2) - 1)) (pt π u (i * (r ^ 2 + 2)))) +
      (if i < T then -7 * (blockOf r δ π u i).S0 else 0) := by
  rw [component]
  simp only
  have hm : 0 < r ^ 2 + 2 := by positivity
  by_cases h0 : i = 0
  · subst h0
    simp only [zero_mul, ite_true, Nat.le_zero, one_ne_zero, ite_false, add_zero]
    by_cases hT : 0 < T
    · have hk : 0 < T * (r ^ 2 + 2) := Nat.mul_pos hT hm
      rw [ite_eq_left hk, ite_eq_left hT]
      unfold linkL Block.S0 Block.e0 blockOf
      rw [show phase r 0 = 0 from by simp [phase]]
      simp only [show (0 : ℕ) ≠ r ^ 2 + 1 by omega, ite_false, cA, cB, stretch,
        show phase r 0 = 0 from by simp [phase], ite_true, zero_add, zero_mul]
    · have hT0 : T = 0 := by omega
      subst hT0
      simp
  · rw [ite_eq_right (by intro h; exact h0 (by
        rcases Nat.mul_eq_zero.mp h with h | h
        · exact h
        · omega)), ite_eq_right h0]
    have h1 : 1 ≤ i * (r ^ 2 + 2) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h0 (by omega))
    rw [ite_eq_left h1]
    have hR : linkR r δ (i * (r ^ 2 + 2) - 1) (pt π u (i * (r ^ 2 + 2) - 1))
        (pt π u (i * (r ^ 2 + 2))) =
        edgeRight (pt π u (i * (r ^ 2 + 2) - 1)) (pt π u (i * (r ^ 2 + 2))) := by
      unfold linkR
      rw [ite_eq_left (phase_pred r i (by omega))]
    rw [hR]
    by_cases hT : i < T
    · have hk : i * (r ^ 2 + 2) < T * (r ^ 2 + 2) := by
        have := mul_facts r i T hT; omega
      rw [ite_eq_left hk, ite_eq_left hT]
      have hph : phase r (i * (r ^ 2 + 2)) = 0 := by
        have := phase_eq r i 0 hm; simpa using this
      unfold linkL Block.S0 Block.e0 blockOf
      simp only [hph, show (0 : ℕ) ≠ r ^ 2 + 1 by omega, ite_false, cA, cB, stretch, ite_true]
      ring_nf
    · have hk : ¬ i * (r ^ 2 + 2) < T * (r ^ 2 + 2) := by
        intro h
        exact hT (lt_of_mul_lt_mul_right h (by positivity))
      rw [ite_eq_right hk, ite_eq_right hT]
      ring


lemma comp_y (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d)
    (u : Point d) (i j : ℕ) (hi : i < T) (hj1 : 1 ≤ j) (hjn : j ≤ r ^ 2)
    (hp : i * (r ^ 2 + 2) + j < T * (r ^ 2 + 2) + 1) :
    field r δ π u (π ⟨i * (r ^ 2 + 2) + j, hp⟩) = (blockOf r δ π u i).g j := by
  have hmf := mul_facts r i T hi
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  rw [component]
  simp only
  rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega), zero_add]
  rw [show i * (r ^ 2 + 2) + j + 1 = i * (r ^ 2 + 2) + (j + 1) from Nat.add_assoc _ _ _]
  have hphL : phase r (i * (r ^ 2 + 2) + j) = j := phase_eq r i j (by omega)
  have hphR : phase r (i * (r ^ 2 + 2) + j - 1) = j - 1 := by
    rw [show i * (r ^ 2 + 2) + j - 1 = i * (r ^ 2 + 2) + (j - 1) by omega]
    exact phase_eq r i (j - 1) (by omega)
  have hL : linkL r δ (i * (r ^ 2 + 2) + j) (pt π u (i * (r ^ 2 + 2) + j))
      (pt π u (i * (r ^ 2 + 2) + (j + 1))) =
      (if j = (blockOf r δ π u i).n then (r : ℝ) * (blockOf r δ π u i).Sn
        else (r : ℝ) ^ 2 * (blockOf r δ π u i).S j) := by
    have hn : (blockOf r δ π u i).n = r ^ 2 := rfl
    rw [hn]
    by_cases hjr : j = r ^ 2
    · rw [ite_eq_left hjr, linkL_end r δ _ _ _ hr (by rw [hphL, hjr])]
      subst hjr
      simp only [Block.Sn, Block.en, Block.n, blockOf]
      rw [show i * (r ^ 2 + 2) + r ^ 2 + 1 = i * (r ^ 2 + 2) + (r ^ 2 + 1) from Nat.add_assoc _ _ _]
    · rw [ite_eq_right hjr, linkL_mid r δ _ j _ _ hphL hj1 (by omega)]
      simp only [Block.S, Block.e, blockOf]
  have hR : linkR r δ (i * (r ^ 2 + 2) + j - 1) (pt π u (i * (r ^ 2 + 2) + j - 1))
      (pt π u (i * (r ^ 2 + 2) + j)) =
      (if j = 1 then (r : ℝ) * (blockOf r δ π u i).S0
        else -((r : ℝ) ^ 2) * (blockOf r δ π u i).S (j - 1)) := by
    by_cases h1 : j = 1
    · rw [ite_eq_left h1, linkR_start r δ _ _ _ hr (by rw [hphR]; omega)]
      simp only [Block.S0, Block.e0, blockOf]
      rw [show i * (r ^ 2 + 2) + j - 1 = i * (r ^ 2 + 2) by omega,
        show i * (r ^ 2 + 2) + 1 = i * (r ^ 2 + 2) + j by omega]
    · rw [ite_eq_right h1, linkR_mid r δ _ (j - 1) _ _ hphR (by omega) (by omega)]
      simp only [Block.S, Block.e, blockOf]
      rw [show i * (r ^ 2 + 2) + j - 1 = i * (r ^ 2 + 2) + (j - 1) by omega,
        show i * (r ^ 2 + 2) + (j - 1 + 1) = i * (r ^ 2 + 2) + j by omega]
  rw [hL, hR]
  simp only [Block.g, blockOf, Block.n]
  ring

lemma comp_z (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d)
    (u : Point d) (i : ℕ) (hi : i < T)
    (hp : i * (r ^ 2 + 2) + r ^ 2 + 1 < T * (r ^ 2 + 2) + 1) :
    field r δ π u (π ⟨i * (r ^ 2 + 2) + r ^ 2 + 1, hp⟩) =
      edgeLeft (pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1)) (pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1 + 1)) -
        7 / 2 * (blockOf r δ π u i).Sn := by
  have hmf := mul_facts r i T hi
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  rw [component]
  simp only
  rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega), zero_add]
  have hphL : phase r (i * (r ^ 2 + 2) + r ^ 2 + 1) = r ^ 2 + 1 := by
    rw [show i * (r ^ 2 + 2) + r ^ 2 + 1 = i * (r ^ 2 + 2) + (r ^ 2 + 1) by omega]
    exact phase_eq r i _ (by omega)
  have hphR : phase r (i * (r ^ 2 + 2) + r ^ 2 + 1 - 1) = r ^ 2 := by
    rw [show i * (r ^ 2 + 2) + r ^ 2 + 1 - 1 = i * (r ^ 2 + 2) + r ^ 2 by omega]
    exact phase_eq r i _ (by omega)
  rw [linkL_gate r δ _ _ _ hphL, linkR_end r δ _ _ _ hr hphR]
  simp only [Block.Sn, Block.en, Block.n, blockOf]
  rw [show i * (r ^ 2 + 2) + r ^ 2 + 1 - 1 = i * (r ^ 2 + 2) + r ^ 2 by omega]
  ring

lemma sum_fin_icc (F : ℕ → ℝ) (n : ℕ) :
    ∑ j : Fin n, F (j.val + 1) = ∑ j ∈ Finset.Icc 1 n, F j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc, Finset.sum_Icc_succ_top (by omega)]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]

noncomputable def yEmb (r : ℕ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (i : ℕ)
    (hi : i < T) : Fin (r ^ 2) ↪ Fin d :=
  ⟨fun j => π ⟨i * (r ^ 2 + 2) + (j.val + 1), by have := mul_facts r i T hi; omega⟩,
    fun a b h => by
      have := π.injective h
      simp only [Fin.mk.injEq] at this
      exact Fin.ext (by omega)⟩

lemma y_sum (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) {T : ℕ} (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d)
    (u : Point d) (i : ℕ) (hi : i < T) (c : Fin (r ^ 2) → ℝ) :
    ⟪field r δ π u, scatter (yEmb r π i hi) c⟫ =
      ∑ j : Fin (r ^ 2), c j * (blockOf r δ π u i).g (j.val + 1) := by
  rw [real_inner_comm, inner_scatter]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hmf := mul_facts r i T hi
  have := comp_y r hr δ π u i (j.val + 1) hi (by omega) (by have := j.isLt; omega)
    (by have := j.isLt; omega)
  simp only [yEmb, Function.Embedding.coeFn_mk]
  exact this

lemma gx_bounds (u : ℝ) (v : ℝ) : (-1 ≤ -potentialSlope u ∧ -potentialSlope u ≤ 0) ∧
    (-1 ≤ edgeRight v u ∧ edgeRight v u ≤ 0) := by
  have h1 := potentialSlope_bounds u
  have h2 := edgeRight_bounds v u
  exact ⟨⟨by linarith [h1.2], by linarith [h1.1]⟩, h2⟩

lemma scatter_one_norm {n : ℕ} (α : Fin n ↪ Fin d) :
    ‖scatter α (fun _ => (1 : ℝ))‖ = Real.sqrt n := by
  rw [← Real.sqrt_sq (norm_nonneg _), scatter_norm_sq]
  simp

lemma wire_deficient (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) (hδ : 0 ≤ δ) (hrδ : r * δ ≤ 1 / 4) {T : ℕ}
    (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (u : Point d)
    (htail : |u (π (Fin.last _))| < 1) :
    (∃ v : Point d, ‖v‖ ≤ 10 ∧ ⟪field r δ π u, v⟫ ≤ -(1 / 4)) ∨
      (∃ a : Fin d, 1 ≤ |u a| ∧ (1 ≤ u a → 1 ≤ field r δ π u a) ∧
        (u a ≤ -1 → field r δ π u a ≤ -1)) := by
  have hm : 0 < r ^ 2 + 2 := by positivity
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  by_cases hex : ∃ i, i < T ∧ |pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1)| < 1
  · let i := Nat.find hex
    obtain ⟨hi, hzs⟩ := Nat.find_spec hex
    have hmin : ∀ i' < i, 1 ≤ |pt π u (i' * (r ^ 2 + 2) + r ^ 2 + 1)| := by
      intro i' hi'
      by_contra hc
      push Not at hc
      exact Nat.find_min hex hi' ⟨by have := hi; omega, hc⟩
    have hmf := mul_facts r i T hi
    set B := blockOf r δ π u i with hB
    have hpx : i * (r ^ 2 + 2) < T * (r ^ 2 + 2) + 1 := by omega
    have hpz : i * (r ^ 2 + 2) + r ^ 2 + 1 < T * (r ^ 2 + 2) + 1 := by omega
    have hcx := comp_x r hr δ π u i hi.le hpx
    rw [ite_eq_left hi] at hcx
    have hcz := comp_z r hr δ π u i hi hpz
    rw [← hB] at hcx hcz
    have hBr : (B.r : ℝ) = r := rfl
    set gx := (if i = 0 then -potentialSlope (pt π u 0)
        else edgeRight (pt π u (i * (r ^ 2 + 2) - 1)) (pt π u (i * (r ^ 2 + 2)))) with hgx
    have hgxb : -1 ≤ gx ∧ gx ≤ 0 := by
      rw [hgx]
      split_ifs
      · exact (gx_bounds _ 0).1
      · exact (gx_bounds _ _).2
    have hux : pt π u (i * (r ^ 2 + 2)) = u (π ⟨i * (r ^ 2 + 2), hpx⟩) := by simp [pt, hpx]
    by_cases hxs : |pt π u (i * (r ^ 2 + 2))| < 1
    · have hg1 : gx = -1 := by
        rw [hgx]
        split_ifs with h0
        · have : pt π u 0 = pt π u (i * (r ^ 2 + 2)) := by rw [h0, zero_mul]
          rw [this, potentialSlope_one hxs.le]
        · have hp1 : i * (r ^ 2 + 2) - 1 = (i - 1) * (r ^ 2 + 2) + r ^ 2 + 1 := by
            obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            rw [hj]; simp only [Nat.add_sub_cancel]; ring_nf; omega
          have := hmin (i - 1) (by omega)
          rw [← hp1] at this
          exact edgeRight_large this hxs.le
      left
      let v : Point d := EuclideanSpace.single (π ⟨i * (r ^ 2 + 2), hpx⟩) (1 : ℝ) +
        (2 : ℝ) • EuclideanSpace.single (π ⟨i * (r ^ 2 + 2) + r ^ 2 + 1, hpz⟩) (1 : ℝ) +
        (7 / (r : ℝ)) • scatter (yEmb r π i hi) (fun _ => (1 : ℝ))
      refine ⟨v, ?_, ?_⟩
      · have h1 : ‖scatter (yEmb r π i hi) (fun _ => (1 : ℝ))‖ = r := by
          rw [scatter_one_norm]; push_cast; exact Real.sqrt_sq (by positivity)
        calc ‖v‖ ≤ ‖EuclideanSpace.single (π ⟨i * (r ^ 2 + 2), hpx⟩) (1 : ℝ)‖ +
              ‖(2 : ℝ) • EuclideanSpace.single (π ⟨i * (r ^ 2 + 2) + r ^ 2 + 1, hpz⟩) (1 : ℝ)‖ +
              ‖(7 / (r : ℝ)) • scatter (yEmb r π i hi) (fun _ => (1 : ℝ))‖ := norm_add₃_le
          _ = 1 + 2 + 7 := by
              rw [norm_smul, norm_smul, h1]
              simp
              field_simp
          _ ≤ 10 := by norm_num
      · have hy := y_sum r hr δ π u i hi (fun _ => (1 : ℝ))
        simp only [one_mul] at hy
        rw [sum_fin_icc (fun j => B.g j)] at hy
        have ht := Block.total_sum B hr
        rw [show B.n = r ^ 2 from rfl] at ht
        rw [ht] at hy
        simp only [v, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right,
          conj_trivial, one_mul]
        rw [hy, hcx, hcz, hg1]
        have he := (edgeLeft_bounds (pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1))
          (pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1 + 1))).2
        have hrz : (r : ℝ) ≠ 0 := by positivity
        rw [hBr]
        field_simp
        nlinarith [mul_nonpos_of_nonpos_of_nonneg he (show (0 : ℝ) ≤ r by positivity)]
    · push Not at hxs
      by_cases hg : ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 ≤ 1 / 16
      · right
        refine ⟨π ⟨i * (r ^ 2 + 2), hpx⟩, by rw [← hux]; exact hxs, ?_, ?_⟩
        · intro hpos
          rw [← hux] at hpos
          have hzz := abs_lt.mp hzs
          have hf := Block.force B hr hδ hrδ hg (by
            change 7 / 2 ≤ 7 * (pt π u (i * (r ^ 2 + 2)) - pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1) / 2)
            linarith)
          rw [hcx]
          linarith [hgxb.1]
        · intro hneg
          rw [← hux] at hneg
          have hzz := abs_lt.mp hzs
          have hf := Block.force_neg B hr hδ hrδ hg (by
            change 7 * (pt π u (i * (r ^ 2 + 2)) - pt π u (i * (r ^ 2 + 2) + r ^ 2 + 1) / 2) ≤ -(7 / 2)
            linarith)
          rw [hcx]
          linarith [hgxb.2]
      · left
        push Not at hg
        set Q := ∑ k ∈ Finset.Icc 1 B.n, B.g k ^ 2 with hQ
        have hQ0 : 0 < Q := by linarith
        have hsq : 1 / 4 < Real.sqrt Q := by
          rw [show (1 : ℝ) / 4 = Real.sqrt (1 / 16) by
            rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_lt_sqrt (by norm_num) hg
        have hsp : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
        let c : Fin (r ^ 2) → ℝ := fun j => -(B.g (j.val + 1) / Real.sqrt Q)
        refine ⟨scatter (yEmb r π i hi) c, ?_, ?_⟩
        · have hn : ‖scatter (yEmb r π i hi) c‖ ^ 2 = 1 := by
            rw [scatter_norm_sq]
            simp only [c, neg_sq, div_pow, Real.sq_sqrt hQ0.le]
            rw [← Finset.sum_div, sum_fin_icc (fun j => B.g j ^ 2)]
            exact div_self hQ0.ne'
          have : ‖scatter (yEmb r π i hi) c‖ ≤ 1 := by nlinarith [norm_nonneg (scatter (yEmb r π i hi) c)]
          linarith
        · rw [y_sum r hr δ π u i hi c]
          simp only [c]
          have he : ∑ j : Fin (r ^ 2), -(B.g (j.val + 1) / Real.sqrt Q) * B.g (j.val + 1) =
              -(Q / Real.sqrt Q) := by
            rw [hQ, ← sum_fin_icc (fun j => B.g j ^ 2), Finset.sum_div, ← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [he]
          have : Q / Real.sqrt Q = Real.sqrt Q := by
            rw [div_eq_iff hsp.ne', Real.mul_self_sqrt hQ0.le]
          rw [this]
          linarith
  · push Not at hex
    left
    have hlast : (Fin.last (T * (r ^ 2 + 2)) : Fin (T * (r ^ 2 + 2) + 1)) =
        ⟨T * (r ^ 2 + 2), by omega⟩ := rfl
    refine ⟨EuclideanSpace.single (π (Fin.last _)) (1 : ℝ), by simp, ?_⟩
    rw [EuclideanSpace.inner_single_right]
    simp only [conj_trivial, one_mul]
    rw [hlast, comp_x r hr δ π u T le_rfl (by omega), ite_eq_right (lt_irrefl T), add_zero]
    have hut : |pt π u (T * (r ^ 2 + 2))| < 1 := by
      have : pt π u (T * (r ^ 2 + 2)) = u (π (Fin.last _)) := by simp [pt]; rfl
      rw [this]; exact htail
    split_ifs with hT
    · have h0 : T * (r ^ 2 + 2) = 0 := by rw [hT, zero_mul]
      have : pt π u 0 = pt π u (T * (r ^ 2 + 2)) := congrArg (pt π u) h0.symm
      rw [this, potentialSlope_one hut.le]
      norm_num
    · have hp1 : T * (r ^ 2 + 2) - 1 = (T - 1) * (r ^ 2 + 2) + r ^ 2 + 1 := by
        obtain ⟨j, hj⟩ : ∃ j, T = j + 1 := ⟨T - 1, by omega⟩
        rw [hj]; simp only [Nat.add_sub_cancel]; ring_nf; omega
      have := hex (T - 1) (by omega)
      rw [← hp1] at this
      rw [edgeRight_large this hut.le]
      norm_num

end LongTails.Proofs.SlidingWireGeometry
