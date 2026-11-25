import LongTails.Proofs.NcConcaveOracle

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveSecret

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcaveInstance
open LongTails.Proofs.NcConcaveGadgets LongTails.Proofs.NcConcaveHuber LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveC11 LongTails.Proofs.NcConcaveRhoModel
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveLocality
open LongTails.Proofs.NcConcaveAnalysis LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveReply LongTails.Proofs.NcConcaveValue
open LongTails.Proofs.NcConcaveOracle
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {n m : ℕ}

def W0 (n m : ℕ) : Word (K n m) n m := ⟨Function.Embedding.refl _⟩

lemma selC_emb (c : CS n m) : selC (W0 n m) 1 (embX (W0 n m) c) (embY (W0 n m) c) = c := by
  have hU := (W0 n m).coords.hU
  have hA : Function.Injective (W0 n m).πA := (W0 n m).coords.hA
  have hB : Function.Injective (W0 n m).πB := (W0 n m).coords.hB
  have hAB : ∀ i j, (W0 n m).πA i ≠ (W0 n m).πB j := (W0 n m).coords.hAB
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext j
    simp only [selC, embX, PiLp.toLp_apply, div_one]
    exact emb_apply hU c.1 j
  · funext i
    simp only [selC, embX, PiLp.toLp_apply, div_one]
    rw [ite_eq_right (by decide), emb_apply hA, emb_off c.2.2.1 _ (fun j h => hAB i j h.symm), add_zero]
  · funext i
    simp only [selC, embX, PiLp.toLp_apply, div_one]
    rw [ite_eq_right (by decide), emb_apply hB, emb_off c.2.1 _ (fun j h => hAB j i h), zero_add]
  · funext i k
    simp only [selC, div_one]
    rw [embY_eq]
    simp only
    exact emb2_apply (W0 n m).πY_inj (fun p => c.2.2.2 p.1 p.2) (i, k)

lemma chainSq_sub_comm (a b : CS n m) : chainSq (a - b) = chainSq (b - a) := by
  rw [← neg_sub b a]
  unfold chainSq nsq sq1 sq2 sqY
  simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, neg_sq]

lemma ite_sq_le (P : Prop) [Decidable P] (x : ℝ) : (if P then x else 0) ^ 2 ≤ x ^ 2 := by
  split_ifs
  · exact le_rfl
  · rw [zero_pow two_ne_zero]; exact sq_nonneg x

theorem gradC_lip {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (B : ℝ) (hB : 0 ≤ B)
    (c0 c1 : CS n m) (ha0 : sq2 c0.2.1 ≤ B ^ 2) (hb0 : ∀ i, |c0.2.2.1 i| ≤ B)
    (ha1 : sq2 c1.2.1 ≤ B ^ 2) (hb1 : ∀ i, |c1.2.2.1 i| ≤ B) :
    chainSq (gradC θ τ c0 - gradC θ τ c1) ≤ (6 * cF B) ^ 2 * chainSq (c0 - c1) := by
  have e0 := selC_emb c0
  have e1 := selC_emb c1
  have hK : 0 ≤ 1 * cF B := by unfold cF cP; linarith
  have hS := pair_lipschitz (fhat θ τ (W0 n m) 1 1) (gxh θ τ (W0 n m) 1 1) (gyh θ τ (W0 n m) 1 1)
    {z | sq2 (selC (W0 n m) 1 z.1 z.2).2.1 ≤ B ^ 2 ∧ ∀ i, |(selC (W0 n m) 1 z.1 z.2).2.2.1 i| ≤ B}
    (1 * cF B) hK
    (fun z hz x' y' => fhat_model hθ hθ1 hτ (W0 n m) one_pos zero_le_one B hB z.1 z.2 hz.1 hz.2 x' y')
    (embX (W0 n m) c0, embY (W0 n m) c0) (embX (W0 n m) c1, embY (W0 n m) c1)
    (show sq2 (selC (W0 n m) 1 (embX (W0 n m) c0) (embY (W0 n m) c0)).2.1 ≤ B ^ 2 ∧
        ∀ i, |(selC (W0 n m) 1 (embX (W0 n m) c0) (embY (W0 n m) c0)).2.2.1 i| ≤ B by
      rw [e0]; exact ⟨ha0, hb0⟩)
    (show sq2 (selC (W0 n m) 1 (embX (W0 n m) c1) (embY (W0 n m) c1)).2.1 ≤ B ^ 2 ∧
        ∀ i, |(selC (W0 n m) 1 (embX (W0 n m) c1) (embY (W0 n m) c1)).2.2.1 i| ≤ B by
      rw [e1]; exact ⟨ha1, hb1⟩)
  simp only [gxh, gyh, e0, e1, mul_one, one_mul, one_smul] at hS
  rw [← embX_sub, ← embY_sub, ← embX_sub, ← embY_sub, emb_norm, emb_norm] at hS
  exact hS

lemma dP_zero (θ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) : dP θ u a b 0 0 0 = 0 := by
  have h := dP_smul θ u a b 0 0 0 0
  simpa using h

lemma dB_zero (θ τ a b : ℝ) (y : Fin (m + 1) → ℝ) : dB θ τ a b y 0 0 0 = 0 := by
  have h := dB_smul θ τ a b y 0 0 0 0
  simpa using h

lemma gradC_Y (θ τ : ℝ) (c : CS n m) (i : Fin n) (k : Fin (m + 1)) :
    (gradC θ τ c).2.2.2 i k = dB θ τ (c.2.1 i) (c.2.2.1 i) (c.2.2.2 i) 0 0 (Pi.single k 1) := by
  simp only [gradC, DFc_apply, eY, dF, dP_zero, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [Pi.single_eq_of_ne hi']
    simpa using dB_zero θ τ (c.2.1 i') (c.2.2.1 i') (c.2.2.2 i')
  · simp

lemma single_castSucc_sum (k : Fin (m + 1)) :
    ∑ k' : Fin m, |(Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.castSucc - (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.succ| ≤ 2 := by
  have hpt : ∀ k' : Fin m, |(Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.castSucc - (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.succ| ≤
      (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.castSucc + (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.succ := by
    intro k'
    have h1 : (0 : ℝ) ≤ (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.castSucc := by
      simp only [Pi.single_apply]; split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) k'.succ := by
      simp only [Pi.single_apply]; split_ifs <;> norm_num
    rw [abs_le]; constructor <;> linarith
  have hs := Finset.sum_le_sum (fun k' (_ : k' ∈ Finset.univ) => hpt k')
  rw [Finset.sum_add_distrib] at hs
  have hnn : ∀ j, (0 : ℝ) ≤ (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) j := by
    intro j; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have htot : ∑ j : Fin (m + 1), (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) j = 1 := by simp
  have e1 := Fin.sum_univ_castSucc (fun j => (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) j)
  have e2 := Fin.sum_univ_succ (fun j => (Pi.single k (1 : ℝ) : Fin (m + 1) → ℝ) j)
  have := hnn (Fin.last m)
  have := hnn 0
  linarith

theorem gradC_Y_bound {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (c : CS n m) (i : Fin n) (k : Fin (m + 1))
    (hz : c.2.2.2 i k = 0) (ha : |c.2.1 i| ≤ 2) (hb : |c.2.2.1 i| ≤ 2) :
    |(gradC θ τ c).2.2.2 i k| ≤ 2 * τ + 3 * alpha m := by
  rw [gradC_Y]
  have hα := alpha_pos m
  have hα1 := alpha_le_one m
  set y := c.2.2.2 i
  set e : Fin (m + 1) → ℝ := Pi.single k 1
  have h0 : zeta θ (y 0) * e 0 = 0 := by
    by_cases hk : k = 0
    · subst hk; simp [y, hz, zeta_small hθ (by simp [hθ.le] : |(0 : ℝ)| ≤ θ)]
    · simp [e, Ne.symm hk]
  have hω0 : domega θ (y 0) * e 0 = 0 := by
    by_cases hk : k = 0
    · subst hk; simp [y, hz, domega_small hθ (by simp [hθ.le] : |(0 : ℝ)| ≤ θ)]
    · simp [e, Ne.symm hk]
  have hωl : domega θ (y (Fin.last m)) * e (Fin.last m) = 0 := by
    by_cases hk : k = Fin.last m
    · subst hk; simp [y, hz, domega_small hθ (by simp [hθ.le] : |(0 : ℝ)| ≤ θ)]
    · simp [e, Ne.symm hk]
  have hT0 : |betaT θ (c.2.1 i) (y 0) * e 0| ≤ 2 := by
    by_cases hk : k = 0
    · subst hk
      simp only [y, hz, e, Pi.single_eq_same, mul_one, betaT]
      rw [dzeta_small hθ (by simp [hθ.le]), mul_zero, add_zero]
      have := zeta_lip hθ (c.2.1 i) 0
      rw [zeta_small (t := 0) hθ (by rw [abs_zero]; exact hθ.le), sub_zero, sub_zero] at this
      linarith
    · simp [e, Ne.symm hk]
  have hTl : |betaT θ (c.2.2.1 i) (y (Fin.last m)) * e (Fin.last m)| ≤ 2 := by
    by_cases hk : k = Fin.last m
    · subst hk
      simp only [y, hz, e, Pi.single_eq_same, mul_one, betaT]
      rw [dzeta_small hθ (by simp [hθ.le]), mul_zero, add_zero]
      have := zeta_lip hθ (c.2.2.1 i) 0
      rw [zeta_small (t := 0) hθ (by rw [abs_zero]; exact hθ.le), sub_zero, sub_zero] at this
      linarith
    · simp [e, Ne.symm hk]
  have hH : |∑ k' : Fin m, dhuber τ (zeta (2 * θ) (y k'.castSucc - y k'.succ)) *
      dzeta (2 * θ) (y k'.castSucc - y k'.succ) * (e k'.castSucc - e k'.succ)| ≤ 2 * τ := by
    calc _ ≤ ∑ k' : Fin m, |dhuber τ (zeta (2 * θ) (y k'.castSucc - y k'.succ)) *
          dzeta (2 * θ) (y k'.castSucc - y k'.succ) * (e k'.castSucc - e k'.succ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k' : Fin m, τ * |e k'.castSucc - e k'.succ| := by
          apply Finset.sum_le_sum; intro k' _
          rw [abs_mul, abs_mul]
          have h1 := dhuber_abs hτ.le (zeta (2 * θ) (y k'.castSucc - y k'.succ))
          have h2 := dzeta_abs (by linarith : (0 : ℝ) < 2 * θ) (y k'.castSucc - y k'.succ)
          have h3 := abs_nonneg (e k'.castSucc - e k'.succ)
          calc _ ≤ τ * 1 * |e k'.castSucc - e k'.succ| :=
                mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) hτ.le) h3
            _ = _ := by ring
      _ = τ * ∑ k' : Fin m, |e k'.castSucc - e k'.succ| := by rw [Finset.mul_sum]
      _ ≤ τ * 2 := mul_le_mul_of_nonneg_left (single_castSucc_sum k) hτ.le
      _ = 2 * τ := by ring
  set H := ∑ k' : Fin m, dhuber τ (zeta (2 * θ) (y k'.castSucc - y k'.succ)) *
      dzeta (2 * θ) (y k'.castSucc - y k'.succ) * (e k'.castSucc - e k'.succ)
  have hdB : dB θ τ (c.2.1 i) (c.2.2.1 i) y 0 0 e =
      -(alpha m ^ 2 / 2) * (2 * dzeta θ (y 0) * (zeta θ (y 0) * e 0)) - H +
        alpha m * (betaT θ (c.2.1 i) (y 0) * e 0) -
        alpha m / 2 * (betaT θ (c.2.2.1 i) (y (Fin.last m)) * e (Fin.last m)) -
        2 * alpha m * θ * (domega θ (y 0) * e 0 + domega θ (y (Fin.last m)) * e (Fin.last m)) := by
    simp only [dB, H]; ring
  rw [hdB, h0, hω0, hωl]
  have q1 := abs_le.mp hH
  have q2 := abs_le.mp hT0
  have q3 := abs_le.mp hTl
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left q2.2 hα.le, mul_le_mul_of_nonneg_left q2.1 hα.le,
    mul_le_mul_of_nonneg_left q3.2 hα.le, mul_le_mul_of_nonneg_left q3.1 hα.le]

lemma pY_ne_pU (i : Fin n) (k : Fin (m + 1)) (j : Fin (n + 1)) : pU m j ≠ pY m i k := by
  intro h
  have h' : (j : ℕ) * (m + 4) + 0 = (i : ℕ) * (m + 4) + (2 + k) := by
    simp only [pU, pY] at h; omega
  have := (pos_inj (m := m) (by omega) (by omega) h').2
  omega

lemma pY_ne_pA (i : Fin n) (k : Fin (m + 1)) (j : Fin n) : pA m j ≠ pY m i k := by
  intro h
  have h' : (j : ℕ) * (m + 4) + 1 = (i : ℕ) * (m + 4) + (2 + k) := by
    simp only [pA, pY] at h; omega
  have := (pos_inj (m := m) (by omega) (by omega) h').2
  omega

lemma pY_ne_pB (i : Fin n) (k : Fin (m + 1)) (j : Fin n) : pB m j ≠ pY m i k := by
  intro h
  have h' : (j : ℕ) * (m + 4) + (m + 3) = (i : ℕ) * (m + 4) + (2 + k) := by
    simp only [pB, pY] at h; omega
  have := (pos_inj (m := m) (by omega) (by omega) h').2
  have := k.isLt
  omega

lemma pY_eq_iff (i i' : Fin n) (k k' : Fin (m + 1)) : pY m i' k' = pY m i k ↔ i' = i ∧ k' = k := by
  constructor
  · intro h
    have h' : (i' : ℕ) * (m + 4) + (2 + k') = (i : ℕ) * (m + 4) + (2 + k) := by
      simp only [pY] at h; omega
    have hk := k.isLt
    have hk' := k'.isLt
    obtain ⟨h1, h2⟩ := pos_inj (m := m) (by omega) (by omega) h'
    exact ⟨Fin.ext h1, Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma chainSq_add_le (a b : CS n m) : chainSq (a + b) ≤ 2 * chainSq a + 2 * chainSq b := by
  unfold chainSq nsq sq1 sq2 sqY
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have h : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
    nlinarith [sq_nonneg (x - y)]
  have h1 : ∑ j, (a.1 j + b.1 j) ^ 2 ≤ 2 * ∑ j, a.1 j ^ 2 + 2 * ∑ j, b.1 j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => h _ _
  have h2 : ∑ j, (a.2.1 j + b.2.1 j) ^ 2 ≤ 2 * ∑ j, a.2.1 j ^ 2 + 2 * ∑ j, b.2.1 j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => h _ _
  have h3 : ∑ j, (a.2.2.1 j + b.2.2.1 j) ^ 2 ≤ 2 * ∑ j, a.2.2.1 j ^ 2 + 2 * ∑ j, b.2.2.1 j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => h _ _
  have h4 : ∑ i, ∑ k, (a.2.2.2 i k + b.2.2.2 i k) ^ 2 ≤
      2 * ∑ i, ∑ k, a.2.2.2 i k ^ 2 + 2 * ∑ i, ∑ k, b.2.2.2 i k ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => h _ _
  linarith

lemma chainSq_prC_le (r : ℕ) (v : CS n m) : chainSq (prC r v) ≤ chainSq v := by
  rw [prC_apply]
  unfold chainSq nsq sq1 sq2 sqY
  have hp : ∀ (P : Prop) [Decidable P] (x : ℝ), (if P then x else 0) ^ 2 ≤ x ^ 2 := by
    intro P _ x; split_ifs <;> simp [sq_nonneg]
  have h1 : ∑ j, prU (m := m) r v.1 j ^ 2 ≤ ∑ j, v.1 j ^ 2 :=
    Finset.sum_le_sum fun j _ => by simp only [prU]; exact hp _ _
  have h2 : ∑ j, prA (m := m) r v.2.1 j ^ 2 ≤ ∑ j, v.2.1 j ^ 2 :=
    Finset.sum_le_sum fun j _ => by simp only [prA]; exact hp _ _
  have h3 : ∑ j, prB (m := m) r v.2.2.1 j ^ 2 ≤ ∑ j, v.2.2.1 j ^ 2 :=
    Finset.sum_le_sum fun j _ => by simp only [prB]; exact hp _ _
  have h4 : ∑ i, ∑ k, prY r v.2.2.2 i k ^ 2 ≤ ∑ i, ∑ k, v.2.2.2 i k ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by simp only [prY]; exact hp _ _
  linarith

lemma chainSq_pr_diff (v : CS n m) (i : Fin n) (k : Fin (m + 1)) :
    chainSq (prC (pY m i k + 1) v - prC (pY m i k) v) = v.2.2.2 i k ^ 2 := by
  rw [prC_apply, prC_apply]
  unfold chainSq nsq sq1 sq2 sqY
  simp only [Prod.mk_sub_mk, Pi.sub_apply]
  have h1 : ∑ j, (prU (m := m) (pY m i k + 1) v.1 j - prU (m := m) (pY m i k) v.1 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro j _
    have := pY_ne_pU i k j
    simp only [prU]; split_ifs <;> first | ring1 | (exfalso; omega)
  have h2 : ∑ j, (prA (m := m) (pY m i k + 1) v.2.1 j - prA (m := m) (pY m i k) v.2.1 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro j _
    have := pY_ne_pA i k j
    simp only [prA]; split_ifs <;> first | ring1 | (exfalso; omega)
  have h3 : ∑ j, (prB (m := m) (pY m i k + 1) v.2.2.1 j - prB (m := m) (pY m i k) v.2.2.1 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro j _
    have := pY_ne_pB i k j
    simp only [prB]; split_ifs <;> first | ring1 | (exfalso; omega)
  have h4 : ∑ i', ∑ k', (prY (pY m i k + 1) v.2.2.2 i' k' - prY (pY m i k) v.2.2.2 i' k') ^ 2 =
      v.2.2.2 i k ^ 2 := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp only [prY]; rw [ite_eq_left (by omega), ite_eq_right (by omega)]; ring
      · intro k' _ hk'
        have : pY m i k' ≠ pY m i k := fun h => hk' ((pY_eq_iff i i k k').mp h).2
        simp only [prY]; split_ifs <;> first | ring1 | (exfalso; omega)
      · simp
    · intro i' _ hi'
      apply Finset.sum_eq_zero; intro k' _
      have : pY m i' k' ≠ pY m i k := fun h => hi' ((pY_eq_iff i i' k k').mp h).1
      simp only [prY]; split_ifs <;> first | ring1 | (exfalso; omega)
    · simp
  rw [h1, h2, h3, h4]; ring

theorem secret_bound {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) {d : ℕ} (W : Word d n m)
    {s : ℝ} (hs : 0 < s) (x : Prim d) (y : Dual d) (hx : blockSq x 1 ≤ (2 * s) ^ 2) :
    chainSq (secretC θ τ (selC W s x y)) ≤ 18 * cF 2 ^ 2 * θ ^ 2 + 2 * (2 * τ + 3 * alpha m) ^ 2 := by
  set c := selC W s x y
  have hnn : 0 ≤ 18 * cF 2 ^ 2 * θ ^ 2 + 2 * (2 * τ + 3 * alpha m) ^ 2 := by positivity
  unfold secretC
  split_ifs with hm
  swap
  · simp [chainSq, nsq, sq1, sq2, sqY]; exact hnn
  obtain ⟨i, k, hik⟩ := hm
  set st := stage (θ / 2) c
  obtain ⟨ha, hb⟩ := selC_bounds_feasible W hs x y hx
  have hsm : SmallFrom (θ / 2) st c := smallFrom_stage c st le_rfl
  have hfull := gradC_local hθ hθ1 hτ c hsm
  rw [hfull]
  set c1 := prC (st + 1) c
  set c0 := prC st c
  have e : knownC θ τ (st + 1) c - knownC θ τ st c =
      prC (st + 1) (gradC θ τ c1 - gradC θ τ c0) + (prC (st + 1) (gradC θ τ c0) - prC st (gradC θ τ c0)) := by
    simp only [knownC, map_sub, c1, c0]; abel
  rw [e]
  refine (chainSq_add_le _ _).trans ?_
  have hprA : ∀ r, sq2 (prC r c).2.1 ≤ 2 ^ 2 := by
    intro r
    refine le_trans ?_ ha
    rw [prC_apply]
    unfold sq2
    exact Finset.sum_le_sum fun j _ => by simp only [prA]; exact ite_sq_le _ _
  have hprB : ∀ r i', |(prC r c).2.2.1 i'| ≤ 2 := by
    intro r i'
    rw [prC_apply]; simp only [prB]; split_ifs
    · exact hb i'
    · simp
  have hprA' : ∀ r i', |(prC r c).2.1 i'| ≤ 2 := by
    intro r i'
    have h1 : (prC r c).2.1 i' ^ 2 ≤ sq2 (prC r c).2.1 :=
      Finset.single_le_sum (f := fun j => (prC r c).2.1 j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i')
    exact abs_le.mpr (abs_le_of_sq_le_sq' (h1.trans (hprA r)) (by norm_num))
  have t1 : chainSq (prC (st + 1) (gradC θ τ c1 - gradC θ τ c0)) ≤ (6 * cF 2) ^ 2 * (θ / 2) ^ 2 := by
    refine (chainSq_prC_le _ _).trans ?_
    refine (gradC_lip hθ hθ1 hτ 2 (by norm_num) c1 c0 (hprA _) (hprB _) (hprA _) (hprB _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    show chainSq (prC (st + 1) c - prC st c) ≤ _
    rw [← hik, chainSq_pr_diff]
    have h := hsm.hy i k (by rw [hik])
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have t2 : chainSq (prC (st + 1) (gradC θ τ c0) - prC st (gradC θ τ c0)) ≤ (2 * τ + 3 * alpha m) ^ 2 := by
    rw [← hik, chainSq_pr_diff]
    have hz : c0.2.2.2 i k = 0 := by
      simp only [c0, prC_apply, prY]; rw [ite_eq_right (by omega)]
    have h := gradC_Y_bound hθ hτ c0 i k hz (hprA' _ i) (hprB _ i)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

end LongTails.Proofs.NcConcaveSecret
