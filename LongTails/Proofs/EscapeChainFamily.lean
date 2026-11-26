import LongTails.Proofs.EscapeChainHiding

namespace LongTails.Proofs.EscapeChainFamily

open scoped RealInnerProductSpace BigOperators
open EscapeChainCoordinates EscapeChainHiding

variable {d n b : ℕ}

abbrev Hid (n b : ℕ) := Equiv.Perm (Fin n) × (Fin n → Fin b → Bool)

noncomputable def dirOf (hnb : n * b ≤ d) (θ : Hid n b) (i : Fin n) : EuclideanSpace ℝ (Fin d) :=
  blockVec hnb (θ.1 i) (θ.2 (θ.1 i))

noncomputable def uOf (hnb : n * b ≤ d) (θ : Hid n b) (l : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : 2 * l < n then dirOf hnb θ ⟨2 * l, h⟩ else 0

noncomputable def vOf (hnb : n * b ≤ d) (θ : Hid n b) (l : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : 2 * l + 1 < n then dirOf hnb θ ⟨2 * l + 1, h⟩ else 0

lemma dirOf_inner (hnb : n * b ≤ d) (hb : 0 < b) (θ : Hid n b) (i j : Fin n) :
    ⟪dirOf hnb θ i, dirOf hnb θ j⟫ = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl]; exact blockVec_inner_self hnb hb _ _
  · rw [ite_eq_right h]; exact blockVec_inner_ne hnb (fun he => h (θ.1.injective he)) _ _

lemma frame (hnb : n * b ≤ d) (hb : 0 < b) (θ : Hid n b) {K : ℕ} (hK : 2 * K ≤ n) :
    Frame K (uOf hnb θ) (vOf hnb θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj
    simp only [uOf, dite_eq_left (show 2 * i < n by omega), dite_eq_left (show 2 * j < n by omega)]
    rw [dirOf_inner hnb hb]
    by_cases h : i = j
    · subst h; simp
    · rw [ite_eq_right (by intro he; exact h (by simpa using Fin.mk.inj_iff.1 he)), ite_eq_right h]
  · intro i j hi hj
    simp only [vOf, dite_eq_left (show 2 * i + 1 < n by omega), dite_eq_left (show 2 * j + 1 < n by omega)]
    rw [dirOf_inner hnb hb]
    by_cases h : i = j
    · subst h; simp
    · rw [ite_eq_right (by intro he; exact h (by simpa using Fin.mk.inj_iff.1 he)), ite_eq_right h]
  · intro i j hi hj
    simp only [uOf, vOf, dite_eq_left (show 2 * i < n by omega), dite_eq_left (show 2 * j + 1 < n by omega)]
    rw [dirOf_inner hnb hb, ite_eq_right]
    intro he
    have := Fin.mk.inj_iff.1 he
    omega

lemma hoeffding (hnb : n * b ≤ d) (hb : 0 < b) (i : Fin n) (X : Hid n b → EuclideanSpace ℝ (Fin d))
    (hsign : ∀ θ : Hid n b, ∀ σs, X (θ.1, Function.update θ.2 (θ.1 i) σs) = X θ)
    {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) :
    ∑ θ : Hid n b, (if t ≤ |⟪dirOf hnb θ i, X θ⟫| ∧ ‖X θ‖ ≤ ρ then (1 : ℝ) else 0) ≤
      Fintype.card (Hid n b) * (2 * Real.exp (-(t ^ 2 * b / (2 * ρ ^ 2)))) := by
  classical
  rw [Fintype.sum_prod_type]
  have hcard : Fintype.card (Hid n b) = Fintype.card (Equiv.Perm (Fin n)) *
      Fintype.card (Fin n → Fin b → Bool) := Fintype.card_prod _ _
  rw [hcard, Nat.cast_mul, mul_assoc, ← Finset.card_univ (α := Equiv.Perm (Fin n)), ← nsmul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum fun σ _ => ?_
  set B := σ i with hB
  set H : (Fin n → Fin b → Bool) → ℝ := fun s =>
    if t ≤ |⟪dirOf hnb (σ, s) i, X (σ, s)⟫| ∧ ‖X (σ, s)‖ ≤ ρ then 1 else 0
  have hupd := sum_update B H
  have hinner : ∀ s : Fin n → Fin b → Bool, ∑ σs : Fin b → Bool, H (Function.update s B σs) ≤
      2 * ((2 : ℝ) ^ b * Real.exp (-(t ^ 2 * b / (2 * ρ ^ 2)))) := by
    intro s
    have hX : ∀ σs, X (σ, Function.update s B σs) = X (σ, s) := fun σs => hsign (σ, s) σs
    by_cases hn : ‖X (σ, s)‖ ≤ ρ
    · have hc := tail_count_abs hnb hb B (X (σ, s)) ht hρ hn
      refine le_trans (Finset.sum_le_sum fun σs _ => ?_) hc
      simp only [H, hX, dirOf, ← hB, Function.update_self]
      split_ifs <;> simp_all
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun σs _ => ?_)) (by positivity)
      simp only [H, hX]
      rw [ite_eq_right (fun h => hn h.2)]
  have hcardS : (Fintype.card (Fin b → Bool) : ℝ) = 2 ^ b := by simp
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (Fin n → Fin b → Bool))) =>
    hinner s
  rw [hupd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardS] at hsum
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  refine le_of_mul_le_mul_left (a := (2 : ℝ) ^ b) ?_ h2
  linarith [hsum]

lemma swap_apply_left (σ : Equiv.Perm (Fin n)) (i k : Fin n) : (σ * Equiv.swap i k) i = σ k := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

lemma second_moment (hnb : n * b ≤ d) (hb : 0 < b) (i : Fin n)
    (X : Hid n b → EuclideanSpace ℝ (Fin d)) (w : Hid n b → ℝ) (hw : ∀ θ, 0 ≤ w θ)
    (hswap : ∀ θ : Hid n b, ∀ k : Fin n, i ≤ k →
      X (θ.1 * Equiv.swap i k, θ.2) = X θ ∧ w (θ.1 * Equiv.swap i k, θ.2) = w θ)
    (hsign : ∀ θ : Hid n b, ∀ k : Fin n, i ≤ k → ∀ σs,
      X (θ.1, Function.update θ.2 (θ.1 k) σs) = X θ ∧ w (θ.1, Function.update θ.2 (θ.1 k) σs) = w θ) :
    ((n : ℝ) - i) * ∑ θ : Hid n b, ⟪dirOf hnb θ i, X θ⟫ ^ 2 * w θ ≤
      (1 / b) * ∑ θ : Hid n b, ‖X θ‖ ^ 2 * w θ := by
  classical
  set S : Finset (Fin n) := Finset.Ici i with hS
  have hcardS : (S.card : ℝ) = n - i := by
    rw [hS, Fin.card_Ici, Nat.cast_sub (by omega)]
  have hstep1 : ∀ k ∈ S, ∑ θ : Hid n b, ⟪dirOf hnb θ i, X θ⟫ ^ 2 * w θ =
      ∑ θ : Hid n b, ⟪blockVec hnb (θ.1 k) (θ.2 (θ.1 k)), X θ⟫ ^ 2 * w θ := by
    intro k hk
    have hik : i ≤ k := Finset.mem_Ici.1 hk
    let e : Hid n b ≃ Hid n b := (Equiv.mulRight (Equiv.swap i k)).prodCongr (Equiv.refl _)
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun θ _ => ?_
    obtain ⟨hX, hW⟩ := hswap θ k hik
    have hθ : e θ = (θ.1 * Equiv.swap i k, θ.2) := rfl
    rw [hθ, hX, hW]
    simp only [dirOf, swap_apply_left]
  have hstep2 : ∀ k ∈ S, ∑ θ : Hid n b, ⟪blockVec hnb (θ.1 k) (θ.2 (θ.1 k)), X θ⟫ ^ 2 * w θ =
      ∑ θ : Hid n b, (1 / b) * (∑ k', X θ (emb hnb (θ.1 k) k') ^ 2) * w θ := by
    intro k hk
    have hik : i ≤ k := Finset.mem_Ici.1 hk
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    set B := σ k
    set H : (Fin n → Fin b → Bool) → ℝ := fun s => ⟪blockVec hnb B (s B), X (σ, s)⟫ ^ 2 * w (σ, s)
    have hupd := sum_update B H
    have hin : ∀ s : Fin n → Fin b → Bool, ∑ σs : Fin b → Bool, H (Function.update s B σs) =
        (2 : ℝ) ^ b * ((1 / b) * (∑ k', X (σ, s) (emb hnb B k') ^ 2) * w (σ, s)) := by
      intro s
      have hXs : ∀ σs, X (σ, Function.update s B σs) = X (σ, s) := fun σs => (hsign (σ, s) k hik σs).1
      have hWs : ∀ σs, w (σ, Function.update s B σs) = w (σ, s) := fun σs => (hsign (σ, s) k hik σs).2
      simp only [H, hXs, hWs, Function.update_self]
      rw [← Finset.sum_mul, sign_second_moment hnb hb B (X (σ, s))]
      ring
    have hcardB : (Fintype.card (Fin b → Bool) : ℝ) = 2 ^ b := by simp
    have h2 : (0 : ℝ) < 2 ^ b := by positivity
    rw [Finset.sum_congr rfl fun s _ => hin s, ← Finset.mul_sum, hcardB] at hupd
    have := mul_left_cancel₀ h2.ne' hupd
    simpa [H] using this.symm
  have hsumk : ∑ k ∈ S, ∑ θ : Hid n b, ⟪dirOf hnb θ i, X θ⟫ ^ 2 * w θ =
      ((n : ℝ) - i) * ∑ θ : Hid n b, ⟪dirOf hnb θ i, X θ⟫ ^ 2 * w θ := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardS]
  rw [← hsumk, Finset.sum_congr rfl fun k hk => (hstep1 k hk).trans (hstep2 k hk), Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun θ _ => ?_
  have hmass : ∑ k ∈ S, ∑ k', X θ (emb hnb (θ.1 k) k') ^ 2 ≤ ‖X θ‖ ^ 2 := by
    have h := blocks_mass hnb (S.image θ.1) (X θ)
    rwa [Finset.sum_image (fun a _ b _ h => θ.1.injective h)] at h
  calc ∑ k ∈ S, (1 / b) * (∑ k', X θ (emb hnb (θ.1 k) k') ^ 2) * w θ
      = (1 / b) * (∑ k ∈ S, ∑ k', X θ (emb hnb (θ.1 k) k') ^ 2) * w θ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (1 / b) * ‖X θ‖ ^ 2 * w θ := by gcongr; exact hw θ
    _ = _ := by ring

end LongTails.Proofs.EscapeChainFamily
