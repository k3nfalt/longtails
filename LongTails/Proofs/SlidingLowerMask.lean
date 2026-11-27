import LongTails.Proofs.SlidingLowerChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerMask

open SlidingLowerChain FrontierChainProfiles FrontierChain
open Classical

variable {d T : ℕ}

noncomputable def top (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * T + 1))).filter
    (fun j => j.val < V ∧ 1 / 8 < |q (π j)|)).sup (fun j => j.val + 1)

noncomputable def coin (p : ℝ) (b : Bool) : ℝ := if b then 1 / p else 0

noncomputable def maskCoef (p : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (b : Bool)
    (q : Point d) (i : Fin T) : ℝ :=
  if top π V q = 2 * i.val + 1 then coin p b else 1

noncomputable def coupV (p : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (b : Bool) (q : Point d) :
    Point d :=
  ∑ i : Fin T, if 2 * i.val + 1 < V then maskCoef p π V b q i • coupTerm 8 π i q else 0

noncomputable def gateV (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d) : Point d :=
  (if 0 < V then -(potentialSlope (q (π (xi 0))) • EuclideanSpace.single (π (xi 0)) (1 : ℝ))
    else 0) +
    ∑ i : Fin T, if 2 * i.val + 2 < V then edgeField (π (zi i)) (π (xi i.succ)) q else 0

lemma top_congr (π ρ : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d)
    (h : ∀ j : Fin (2 * T + 1), j.val < V → π j = ρ j) : top π V q = top ρ V q := by
  unfold top
  congr 1
  apply Finset.filter_congr
  intro j _
  constructor
  · rintro ⟨hj, hl⟩
    exact ⟨hj, by rwa [← h j hj]⟩
  · rintro ⟨hj, hl⟩
    exact ⟨hj, by rwa [h j hj]⟩

lemma coupTerm_congr (π ρ : Fin (2 * T + 1) ↪ Fin d) (i : Fin T) (q : Point d)
    (h1 : π (xi i.castSucc) = ρ (xi i.castSucc)) (h2 : π (zi i) = ρ (zi i)) :
    coupTerm 8 π i q = coupTerm 8 ρ i q := by
  unfold coupTerm
  rw [h1, h2]

lemma coupV_congr (p : ℝ) (π ρ : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (b : Bool) (q : Point d)
    (h : ∀ j : Fin (2 * T + 1), j.val < V → π j = ρ j) : coupV p π V b q = coupV p ρ V b q := by
  unfold coupV maskCoef
  rw [top_congr π ρ V q h]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 2 * i.val + 1 < V
  · rw [ite_eq_left hi, ite_eq_left hi,
      coupTerm_congr π ρ i q (h _ (by simp [xi]; omega)) (h _ (by simp [zi]; omega))]
  · rw [ite_eq_right hi, ite_eq_right hi]

lemma gateV_congr (π ρ : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d)
    (h : ∀ j : Fin (2 * T + 1), j.val < V → π j = ρ j) : gateV π V q = gateV ρ V q := by
  unfold gateV
  congr 1
  · split_ifs with hV
    · rw [h (xi 0) (by simp [xi]; omega)]
    · rfl
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [h (zi i) (by simp [zi]; omega), h (xi i.succ) (by simp [xi]; omega)]
    · rfl

def Good (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d) : Prop :=
  ∀ j : Fin (2 * T + 1), V ≤ j.val → |q (π j)| ≤ 1 / 8

lemma top_lt (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d)
    (hg : Good π V q) {W : ℕ} (hW : V ≤ W) : top π W q = top π V q := by
  unfold top
  congr 1
  apply Finset.filter_congr
  intro j _
  constructor
  · rintro ⟨hj, hl⟩
    refine ⟨?_, hl⟩
    by_contra hc
    have := hg j (by omega)
    linarith
  · rintro ⟨hj, hl⟩
    exact ⟨by omega, hl⟩

lemma top_eq (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (q : Point d) (hg : Good π V q)
    (j : Fin (2 * T + 1)) (hjV : j.val + 1 = V) (hl : 1 / 8 < |q (π j)|) :
    top π (2 * T + 1) q = V := by
  unfold top
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hc
    have := hg i (by omega)
    linarith [hi.2]
  · rw [← hjV]
    exact Finset.le_sup (f := fun j : Fin (2 * T + 1) => j.val + 1)
      (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j.isLt, hl⟩)

lemma coupTerm_flat (π : Fin (2 * T + 1) ↪ Fin d) (i : Fin T) (q : Point d)
    (hx : |q (π (xi i.castSucc))| ≤ 1 / 8) (hz : |q (π (zi i))| ≤ 1 / 8) :
    coupTerm 8 π i q = 0 := by
  unfold coupTerm
  have ht : |q (π (xi i.castSucc)) - q (π (zi i)) / 2| ≤ 1 / 4 := by
    have h1 := abs_sub (q (π (xi i.castSucc))) (q (π (zi i)) / 2)
    rw [abs_div, abs_two] at h1
    linarith
  rw [(hub_flat ht).2]
  simp

lemma edgeField_flat (a b : Fin d) (q : Point d) (h : |q a| ≤ 1 / 2) : edgeField a b q = 0 := by
  unfold edgeField
  rw [(edge_flat h).2.1, (edge_flat h).2.2]
  simp

lemma coupV_eq (p : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (V V' : ℕ) (b : Bool) (q : Point d)
    (hV : V ≤ 2 * T + 1) (hVV : V ≤ V') (hg : Good π V q)
    (hb : V' = V → V < 2 * T + 1 → V % 2 = 1 → b = false) :
    coupV p π V' b q = coupV p π (2 * T + 1) b q := by
  unfold coupV maskCoef
  rw [top_lt π V q hg hVV, top_lt π V q hg (show V ≤ 2 * T + 1 from hV)]
  apply Finset.sum_congr rfl
  intro i _
  have hin : 2 * i.val + 1 < 2 * T + 1 := by omega
  rw [ite_eq_left hin]
  by_cases h1 : 2 * i.val + 1 < V'
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    by_cases hx : 2 * i.val < V
    · have hVe : V' = V ∧ V = 2 * i.val + 1 := by omega
      by_cases hl : 1 / 8 < |q (π (xi i.castSucc))|
      · have ht := top_eq π V q hg (xi i.castSucc) (by simp [xi]; omega) hl
        rw [← top_lt π V q hg (show V ≤ 2 * T + 1 from hV), ht, ite_eq_left (by omega)]
        have hbf := hb hVe.1 (by omega) (by omega)
        simp [coin, hbf]
      · push Not at hl
        rw [coupTerm_flat π i q hl (hg (zi i) (by simp [zi]; omega))]
        simp
    · rw [coupTerm_flat π i q (hg _ (by simp [xi]; omega)) (hg (zi i) (by simp [zi]; omega))]
      simp

lemma gateV_eq (π : Fin (2 * T + 1) ↪ Fin d) (V V' : ℕ) (q : Point d)
    (hVV : V ≤ V') (hV0 : 0 < V') (hg : Good π V q)
    (hodd : V' = V → V < 2 * T + 1 → V % 2 = 1) :
    gateV π V' q = gateV π (2 * T + 1) q := by
  unfold gateV
  rw [ite_eq_left hV0, ite_eq_left (by omega : 0 < 2 * T + 1)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_left (by omega : 2 * i.val + 2 < 2 * T + 1)]
  by_cases h1 : 2 * i.val + 2 < V'
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    have hz : V ≤ 2 * i.val + 1 := by
      by_contra hc
      have he : V' = V ∧ V = 2 * i.val + 2 := by omega
      have := hodd he.1 (by omega)
      omega
    rw [edgeField_flat _ _ q (by linarith [hg (zi i) (by simp [zi]; omega)])]

lemma gateV_full (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) :
    gateV π (2 * T + 1) q = gateField π q := by
  unfold gateV gateField
  rw [ite_eq_left (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_left (by omega)]

lemma coupV_one (π : Fin (2 * T + 1) ↪ Fin d) (q : Point d) :
    coupV 1 π (2 * T + 1) true q = coupField 8 π q := by
  unfold coupV coupField maskCoef coin
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_left (by omega)]
  split_ifs <;> simp_all

lemma coupV_split (p : ℝ) (π : Fin (2 * T + 1) ↪ Fin d) (b : Bool) (q : Point d) :
    coupV p π (2 * T + 1) b q = coupField 8 π q +
      ∑ i : Fin T, if top π (2 * T + 1) q = 2 * i.val + 1 then
        (coin p b - 1) • coupTerm 8 π i q else 0 := by
  unfold coupV coupField maskCoef
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_left (by omega)]
  split_ifs
  · rw [sub_smul, one_smul]; abel
  · simp

end LongTails.Proofs.SlidingLowerMask
