import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic

namespace LongTails.Proofs.MintyPrefixSearch

variable {d m : ℕ} {S : Type*}

abbrev Word (d m : ℕ) := Fin d → Fin m

def run (step : S → Word d m → S) : ℕ → S → Word d m → S
  | 0, s, _ => s
  | n+1, s, w => run step n (step s w) w

def Common (Z : Finset (Word d m)) (j : ℕ) : Prop :=
  ∀ w ∈ Z, ∀ v ∈ Z, ∀ i : Fin d, i.val < j → w i = v i

lemma common_mono {Z W : Finset (Word d m)} {j : ℕ} (h : Common Z j) (hsub : W ⊆ Z) :
    Common W j := fun w hw v hv => h w (hsub hw) v (hsub hv)

lemma count (step : S → Word d m → S) (classify : S → Fin d → Fin m → Ordering)
    (win : S → Word d m → Prop)
    (hu : ∀ s w v, win s w → win s v → w = v)
    (hnear : ∀ s i a b, classify s i a = .eq → classify s i b = .eq → a = b)
    (hfar : ∀ s (i : Fin d) w v, (∀ a : Fin d, a.val < i.val → w a = v a) →
      classify s i (w i) ≠ .eq → classify s i (w i) = classify s i (v i) →
      step s w = step s v) (n : ℕ) :
    ∀ (s : S) (j : ℕ) (Z : Finset (Word d m)), j ≤ d → Common Z j →
      (∀ w ∈ Z, win (run step n s w) w) → Z.card ≤ 4 ^ n * 2 ^ (d-j) := by
  classical
  induction n with
  | zero =>
    intro s j Z _ _ hw
    have hone : Z.card ≤ 1 := Finset.card_le_one.mpr
      (fun w hw' v hv => hu s w v (hw w hw') (hw v hv))
    exact hone.trans (by change 0 < _; positivity)
  | succ n outer =>
    intro s
    have scan (k : ℕ) : ∀ j, j + k = d → ∀ Z : Finset (Word d m), Common Z j →
        (∀ w ∈ Z, win (run step (n+1) s w) w) → Z.card ≤ 4 ^ (n+1) * 2 ^ k := by
      induction k with
      | zero =>
        intro j hj Z hc _
        have hone : Z.card ≤ 1 := Finset.card_le_one.mpr (fun w hw v hv => by
          funext i
          exact hc w hw v hv i (by omega))
        exact hone.trans (by change 0 < _; positivity)
      | succ k inner =>
        intro j hj Z hc hw
        let i : Fin d := ⟨j, by omega⟩
        let side := fun w : Word d m => classify s i (w i)
        let A := Z.filter fun w => side w = .lt
        let B := Z.filter fun w => side w = .gt
        let C := Z.filter fun w => side w = .eq
        have stop (o : Ordering) (ho : o ≠ .eq) :
            (Z.filter fun w => side w = o).card ≤ 4 ^ n * 2 ^ (k+1) := by
          let V := Z.filter fun w => side w = o
          by_cases h : V.Nonempty
          · obtain ⟨v, hv⟩ := h
            have he (w) (hw' : w ∈ V) : step s w = step s v := by
              have h1 := Finset.mem_filter.mp hw'
              have h2 := Finset.mem_filter.mp hv
              apply hfar s i w v (hc w h1.1 v h2.1)
              · exact fun hh => ho (h1.2.symm.trans hh)
              · exact h1.2.trans h2.2.symm
            have hb := outer (step s v) j V (by omega)
              (common_mono hc (Finset.filter_subset _ _)) (fun w hw' => by
                rw [← he w hw']
                exact hw w (Finset.mem_filter.mp hw').1)
            simpa only [show d - j = k+1 by omega] using hb
          · change V.card ≤ _
            simp [Finset.not_nonempty_iff_eq_empty.mp h]
        have hc' : Common C (j+1) := by
          intro w hw' v hv a ha
          have hw1 := Finset.mem_filter.mp hw'
          have hv1 := Finset.mem_filter.mp hv
          by_cases hj' : a.val < j
          · exact hc w hw1.1 v hv1.1 a hj'
          · have he : a = i := Fin.ext (by dsimp [i]; omega)
            subst a
            exact hnear s i _ _ hw1.2 hv1.2
        have hcBound := inner (j+1) (by omega) C hc' (fun w hw' => hw w (Finset.mem_filter.mp hw').1)
        have hadd : Z.card ≤ A.card + B.card + C.card := by
          have he : Z = A ∪ B ∪ C := by
            ext w
            cases h : side w <;> simp [A, B, C, h]
          calc
            Z.card = (A ∪ B ∪ C).card := congrArg Finset.card he
            _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
            _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
        have ha := stop .lt (by decide)
        have hb := stop .gt (by decide)
        change A.card ≤ _ at ha
        change B.card ≤ _ at hb
        simp only [pow_succ] at ha hb hcBound ⊢
        nlinarith only [hadd, ha, hb, hcBound]
    intro j Z hj hc hw
    exact scan (d-j) j (by omega) Z hc hw

end LongTails.Proofs.MintyPrefixSearch
