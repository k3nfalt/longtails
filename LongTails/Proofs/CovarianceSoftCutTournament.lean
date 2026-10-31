import LongTails.Proofs.CovarianceSoftCutSelection

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutTournament

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutSelection

lemma selectionBlocks_succ (K h : ℕ) : selectionBlocks K (h+1) = 2*selectionBlocks K h+K := by
  have hpos : 0 < (2 : ℕ)^h := pow_pos (by decide) _
  have hp : (2 : ℕ)^(h+1)-1 = 2*(2^h-1)+1 := by rw [pow_succ]; omega
  unfold selectionBlocks
  rw [hp]
  ring

lemma bisectReplyRun_eq (q : Params) (a : ℝ) (n m : ℕ) (initial : Space q × Space q)
    (replies : ℕ → Space q) (k : ℕ) :
    bisectReplyRun q a n m initial replies k = bisectRun q a initial
      (fun t => directionalMomBlock q n m
        (segmentDirection q (bisectReplyRun q a n m initial replies t))
        (fun i => replies (t*(n*m)+i.val))) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bisectRun, ← ih]
    rfl

lemma bisectReplyRun_prefix (q : Params) (a : ℝ) (n m : ℕ) (initial : Space q × Space q)
    (r s : ℕ → Space q) (k : ℕ) (h : ∀ i, i < k*(n*m) → r i = s i) :
    bisectReplyRun q a n m initial r k = bisectReplyRun q a n m initial s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih (fun i hi => h i (lt_of_lt_of_le hi (Nat.mul_le_mul_right (n*m) (Nat.le_succ k))))
    have hb : (fun i : Fin (n*m) => r (k*(n*m)+i.val)) =
        (fun i : Fin (n*m) => s (k*(n*m)+i.val)) := by
      funext i
      apply h
      rw [Nat.succ_mul]
      have hi := i.isLt
      omega
    simp only [bisectReplyRun, hp, hb]

lemma bisectProbe_prefix (q : Params) (a : ℝ) (n m : ℕ) (initial : Space q × Space q)
    (r s : ℕ → Space q) (k : ℕ) (h : ∀ i, i < k*(n*m) → r i = s i) :
    bisectProbe q a n m initial r k = bisectProbe q a n m initial s k := by
  unfold bisectProbe
  rw [bisectReplyRun_prefix q a n m initial r s k h]

lemma bisectReplyRun_radius (q : Params) (a R : ℝ) (n m : ℕ) (initial : Space q × Space q)
    (hl : ‖initial.1‖ ≤ R) (hr : ‖initial.2‖ ≤ R) (replies : ℕ → Space q) (k : ℕ) :
    ‖(bisectReplyRun q a n m initial replies k).1‖ ≤ R ∧
      ‖(bisectReplyRun q a n m initial replies k).2‖ ≤ R := by
  rw [bisectReplyRun_eq]
  exact bisectRun_radius q a R initial hl hr _ k

lemma selectionProbe_direction_norm (q : Params) (a : ℝ) (K n m h : ℕ)
    (leaves replies : ℕ → Space q) (t : ℕ) : ‖(selectionProbe q a K n m h leaves replies t).2‖ ≤ 1 := by
  induction h generalizing leaves replies t with
  | zero => simp [selectionProbe]
  | succ h ih =>
    simp only [selectionProbe]
    split_ifs
    · exact ih _ _ _
    · exact ih _ _ _
    · exact norm_segmentDirection_le q _

lemma selectionOutput_radius (q : Params) (a R : ℝ) (K n m h : ℕ)
    (leaves replies : ℕ → Space q) (hleaves : ∀ i, i < 2^h → ‖leaves i‖ ≤ R) :
    ‖selectionOutput q a K n m h leaves replies‖ ≤ R := by
  induction h generalizing leaves replies with
  | zero => exact hleaves 0 (by norm_num)
  | succ h ih =>
    have hleft : ‖selectionOutput q a K n m h leaves replies‖ ≤ R := by
      apply ih
      intro i hi
      apply hleaves i
      rw [pow_succ]
      omega
    have hright : ‖selectionOutput q a K n m h (fun i => leaves (2^h+i))
        (fun i => replies (selectionBlocks K h*(n*m)+i))‖ ≤ R := by
      apply ih
      intro i hi
      apply hleaves
      rw [pow_succ]
      omega
    let ends := (selectionOutput q a K n m h leaves replies,
      selectionOutput q a K n m h (fun i => leaves (2^h+i))
        (fun i => replies (selectionBlocks K h*(n*m)+i)))
    let tail := fun i => replies (2*(selectionBlocks K h*(n*m))+i)
    have he := bisectReplyRun_radius q a R n m ends hleft hright tail K
    change ‖segmentMid q (bisectReplyRun q a n m ends tail K)‖ ≤ R
    exact norm_segmentMid_le q (bisectReplyRun q a n m ends tail K) R he.1 he.2

lemma selectionOutput_prefix (q : Params) (a : ℝ) (K n m h : ℕ)
    (leaves r s : ℕ → Space q)
    (heq : ∀ i, i < selectionBlocks K h*(n*m) → r i = s i) :
    selectionOutput q a K n m h leaves r = selectionOutput q a K n m h leaves s := by
  induction h generalizing leaves r s with
  | zero => rfl
  | succ h ih =>
    have htotal : selectionBlocks K (h+1)*(n*m) = 2*(selectionBlocks K h*(n*m))+K*(n*m) := by
      rw [selectionBlocks_succ]
      ring
    have hl := ih leaves r s (fun i hi => heq i (by rw [htotal]; omega))
    have hr := ih (fun i => leaves (2^h+i))
      (fun i => r (selectionBlocks K h*(n*m)+i)) (fun i => s (selectionBlocks K h*(n*m)+i))
      (fun i hi => heq _ (by rw [htotal]; omega))
    simp only [selectionOutput]
    rw [hl, hr]
    apply congrArg (segmentMid q)
    apply bisectReplyRun_prefix
    intro i hi
    apply heq
    rw [htotal]
    omega

lemma selectionOutput_leaf_prefix (q : Params) (a : ℝ) (K n m h : ℕ)
    (left right replies : ℕ → Space q) (heq : ∀ i, i < 2^h → left i = right i) :
    selectionOutput q a K n m h left replies = selectionOutput q a K n m h right replies := by
  induction h generalizing left right replies with
  | zero => exact heq 0 (by norm_num)
  | succ h ih =>
    have hl := ih left right replies (fun i hi => heq i (by rw [pow_succ]; omega))
    have hr := ih (fun i => left (2^h+i)) (fun i => right (2^h+i))
      (fun i => replies (selectionBlocks K h*(n*m)+i))
      (fun i hi => heq _ (by rw [pow_succ]; omega))
    simp only [selectionOutput, hl, hr]

lemma selectionProbe_prefix (q : Params) (a : ℝ) (K n m h : ℕ)
    (leaves r s : ℕ → Space q) (t : ℕ) (heq : ∀ i, i < t*(n*m) → r i = s i) :
    selectionProbe q a K n m h leaves r t = selectionProbe q a K n m h leaves s t := by
  induction h generalizing leaves r s t with
  | zero => rfl
  | succ h ih =>
    simp only [selectionProbe]
    split_ifs with hl hr
    · exact ih leaves r s t heq
    · apply ih
      intro i hi
      apply heq
      have ht : selectionBlocks K h+(t-selectionBlocks K h) = t := Nat.add_sub_of_le (Nat.le_of_not_gt hl)
      have he : selectionBlocks K h*(n*m)+(t-selectionBlocks K h)*(n*m) = t*(n*m) := by
        rw [← Nat.add_mul, ht]
      rw [← he]
      exact Nat.add_lt_add_left hi _
    · have ht : 2*selectionBlocks K h+(t-2*selectionBlocks K h) = t :=
        Nat.add_sub_of_le (Nat.le_of_not_gt hr)
      have hbound : 2*(selectionBlocks K h*(n*m)) ≤ t*(n*m) := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (n*m) (Nat.le_of_not_gt hr)
      have hleft := selectionOutput_prefix q a K n m h leaves r s
        (fun i hi => heq i (by omega))
      have hright := selectionOutput_prefix q a K n m h (fun i => leaves (2^h+i))
        (fun i => r (selectionBlocks K h*(n*m)+i)) (fun i => s (selectionBlocks K h*(n*m)+i))
        (fun i hi => heq _ (by omega))
      rw [hleft, hright]
      apply bisectProbe_prefix
      intro i hi
      apply heq
      have he : 2*(selectionBlocks K h*(n*m))+(t-2*selectionBlocks K h)*(n*m) = t*(n*m) := by
        rw [← Nat.mul_assoc, ← Nat.add_mul, ht]
      rw [← he]
      exact Nat.add_lt_add_left hi _

lemma selectionProbe_leaf_prefix (q : Params) (a : ℝ) (K n m h : ℕ)
    (left right replies : ℕ → Space q) (t : ℕ) (heq : ∀ i, i < 2^h → left i = right i) :
    selectionProbe q a K n m h left replies t = selectionProbe q a K n m h right replies t := by
  induction h generalizing left right replies t with
  | zero => rfl
  | succ h ih =>
    have hl : ∀ i, i < 2^h → left i = right i := fun i hi => heq i (by rw [pow_succ]; omega)
    have hr : ∀ i, i < 2^h → left (2^h+i) = right (2^h+i) := fun i hi => heq _ (by rw [pow_succ]; omega)
    simp only [selectionProbe]
    split_ifs
    · exact ih _ _ _ _ hl
    · exact ih _ _ _ _ hr
    · rw [selectionOutput_leaf_prefix q a K n m h left right replies hl,
        selectionOutput_leaf_prefix q a K n m h _ _ _ hr]

lemma bisectReplyRun_tuned_accuracy (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hsupport : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (L R τ : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hτ : 0 < τ)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (n m K : ℕ)
    (initial : Space q × Space q) (hl : ‖initial.1‖ ≤ 2*R) (hr : ‖initial.2‖ ≤ 2*R)
    (replies : ℕ → Space q) (hpower : 4*L*R ≤ τ*(2 : ℝ)^K)
    (herr : ∀ t, t < K →
      |directionalMomBlock q n m (bisectProbe q (τ/(12*R)) n m initial replies t).2
        (fun i => replies (t*(n*m)+i.val)) -
      ⟪v (bisectProbe q (τ/(12*R)) n m initial replies t).1,
        (bisectProbe q (τ/(12*R)) n m initial replies t).2⟫| ≤ τ/(12*R)) :
    f (segmentMid q (bisectReplyRun q (τ/(12*R)) n m initial replies K)) ≤
      min (f initial.1) (f initial.2) + τ := by
  let estimates := fun t => directionalMomBlock q n m
    (segmentDirection q (bisectReplyRun q (τ/(12*R)) n m initial replies t))
    (fun i => replies (t*(n*m)+i.val))
  have h := bisectRun_tuned_accuracy q f v hsupport L R τ hL hR hτ hlip initial hl hr estimates K hpower
  have hh : ∀ t, t < K → |estimates t -
      ⟪v (segmentMid q (bisectRun q (τ/(12*R)) initial estimates t)),
        segmentDirection q (bisectRun q (τ/(12*R)) initial estimates t)⟫| ≤ τ/(12*R) := by
    intro t ht
    rw [← bisectReplyRun_eq]
    exact herr t ht
  have hout := h hh
  rw [← bisectReplyRun_eq] at hout
  exact hout

def SelectionGood (q : Params) (a : ℝ) (K n m h : ℕ) (leaves replies : ℕ → Space q)
    (v : Space q → Space q) : Prop :=
  ∀ t, t < selectionBlocks K h →
    |directionalMomBlock q n m (selectionProbe q a K n m h leaves replies t).2
      (fun i => replies (t*(n*m)+i.val)) -
    ⟪v (selectionProbe q a K n m h leaves replies t).1,
      (selectionProbe q a K n m h leaves replies t).2⟫| ≤ a

lemma selectionGood_left (q : Params) (a : ℝ) (K n m h : ℕ)
    (leaves replies : ℕ → Space q) (v : Space q → Space q)
    (hg : SelectionGood q a K n m (h+1) leaves replies v) :
    SelectionGood q a K n m h leaves replies v := by
  intro t ht
  have hh := hg t (by rw [selectionBlocks_succ]; omega)
  simpa only [selectionProbe, ite_eq_left ht] using hh

lemma selectionGood_right (q : Params) (a : ℝ) (K n m h : ℕ)
    (leaves replies : ℕ → Space q) (v : Space q → Space q)
    (hg : SelectionGood q a K n m (h+1) leaves replies v) :
    SelectionGood q a K n m h (fun i => leaves (2^h+i))
      (fun i => replies (selectionBlocks K h*(n*m)+i)) v := by
  intro t ht
  have hnot : ¬ selectionBlocks K h+t < selectionBlocks K h := by omega
  have hright : selectionBlocks K h+t < 2*selectionBlocks K h := by omega
  have hh := hg (selectionBlocks K h+t) (by rw [selectionBlocks_succ]; omega)
  simpa only [selectionProbe, ite_eq_right hnot, ite_eq_left hright,
    Nat.add_sub_cancel_left, Nat.add_mul, Nat.add_assoc] using hh

lemma selectionGood_merge (q : Params) (a : ℝ) (K n m h : ℕ)
    (leaves replies : ℕ → Space q) (v : Space q → Space q)
    (hg : SelectionGood q a K n m (h+1) leaves replies v) :
    let initial := (selectionOutput q a K n m h leaves replies,
      selectionOutput q a K n m h (fun i => leaves (2^h+i))
        (fun i => replies (selectionBlocks K h*(n*m)+i)))
    let tail := fun i => replies (2*(selectionBlocks K h*(n*m))+i)
    ∀ t, t < K → |directionalMomBlock q n m (bisectProbe q a n m initial tail t).2
        (fun i => tail (t*(n*m)+i.val)) -
      ⟪v (bisectProbe q a n m initial tail t).1, (bisectProbe q a n m initial tail t).2⟫| ≤ a := by
  intro initial tail t ht
  have hnot : ¬ 2*selectionBlocks K h+t < selectionBlocks K h := by omega
  have hnot' : ¬ 2*selectionBlocks K h+t < 2*selectionBlocks K h := by omega
  have hh := hg (2*selectionBlocks K h+t) (by rw [selectionBlocks_succ]; omega)
  simpa only [selectionProbe, ite_eq_right hnot, ite_eq_right hnot',
    Nat.add_sub_cancel_left, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc] using hh

lemma selectionOutput_accuracy (q : Params) (f : Space q → ℝ) (v : Space q → Space q)
    (hsupport : ∀ x y, ⟪v x, y-x⟫ ≤ f y-f x)
    (L R τ : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hτ : 0 < τ)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (K n m h : ℕ)
    (hpower : 4*L*R ≤ τ*(2 : ℝ)^K) (leaves replies : ℕ → Space q)
    (hrad : ∀ i, i < 2^h → ‖leaves i‖ ≤ 2*R)
    (hgood : SelectionGood q (τ/(12*R)) K n m h leaves replies v) :
    ∀ i, i < 2^h → f (selectionOutput q (τ/(12*R)) K n m h leaves replies) ≤ f (leaves i)+(h : ℝ)*τ := by
  induction h generalizing leaves replies with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by norm_num at hi; omega
    simp [selectionOutput, hi0]
  | succ h ih =>
    have hleft : ∀ i, i < 2^h → ‖leaves i‖ ≤ 2*R := fun i hi => hrad i (by rw [pow_succ]; omega)
    have hright : ∀ i, i < 2^h → ‖leaves (2^h+i)‖ ≤ 2*R := fun i hi => hrad _ (by rw [pow_succ]; omega)
    let left := selectionOutput q (τ/(12*R)) K n m h leaves replies
    let right := selectionOutput q (τ/(12*R)) K n m h (fun i => leaves (2^h+i))
      (fun i => replies (selectionBlocks K h*(n*m)+i))
    have hlrad : ‖left‖ ≤ 2*R := selectionOutput_radius q (τ/(12*R)) (2*R) K n m h leaves replies hleft
    have hrrad : ‖right‖ ≤ 2*R := selectionOutput_radius q (τ/(12*R)) (2*R) K n m h _ _ hright
    have hmerge := bisectReplyRun_tuned_accuracy q f v hsupport L R τ hL hR hτ hlip n m K
      (left, right) hlrad hrrad (fun i => replies (2*(selectionBlocks K h*(n*m))+i)) hpower
      (selectionGood_merge q (τ/(12*R)) K n m h leaves replies v hgood)
    intro i hi
    change f (segmentMid q (bisectReplyRun q (τ/(12*R)) n m (left, right)
      (fun i => replies (2*(selectionBlocks K h*(n*m))+i)) K)) ≤ _
    by_cases hside : i < 2^h
    · have hlacc := ih leaves replies hleft (selectionGood_left q (τ/(12*R)) K n m h leaves replies v hgood) i hside
      have hm : min (f left) (f right) ≤ f left := min_le_left _ _
      change f left ≤ _ at hlacc
      push_cast
      linarith
    · have hj : i-2^h < 2^h := by rw [pow_succ] at hi; omega
      have hracc := ih (fun j => leaves (2^h+j)) (fun j => replies (selectionBlocks K h*(n*m)+j))
        hright (selectionGood_right q (τ/(12*R)) K n m h leaves replies v hgood) (i-2^h) hj
      rw [Nat.add_sub_of_le (Nat.le_of_not_gt hside)] at hracc
      have hm : min (f left) (f right) ≤ f right := min_le_right _ _
      change f right ≤ _ at hracc
      push_cast
      linarith

lemma selectionProbe_point_radius (q : Params) (a R : ℝ) (hR : 0 ≤ R) (K n m h : ℕ)
    (leaves replies : ℕ → Space q) (t : ℕ) (hleaves : ∀ i, i < 2^h → ‖leaves i‖ ≤ R) :
    ‖(selectionProbe q a K n m h leaves replies t).1‖ ≤ R := by
  induction h generalizing leaves replies t with
  | zero => simpa only [selectionProbe, norm_zero] using hR
  | succ h ih =>
    have hl : ∀ i, i < 2^h → ‖leaves i‖ ≤ R := fun i hi => hleaves i (by rw [pow_succ]; omega)
    have hr : ∀ i, i < 2^h → ‖leaves (2^h+i)‖ ≤ R := fun i hi => hleaves _ (by rw [pow_succ]; omega)
    simp only [selectionProbe]
    split_ifs
    · exact ih _ _ _ hl
    · exact ih _ _ _ hr
    · let ends := (selectionOutput q a K n m h leaves replies,
        selectionOutput q a K n m h (fun i => leaves (2^h+i))
          (fun i => replies (selectionBlocks K h*(n*m)+i)))
      let tail := fun i => replies (2*(selectionBlocks K h*(n*m))+i)
      have hleft : ‖ends.1‖ ≤ R := selectionOutput_radius q a R K n m h leaves replies hl
      have hright : ‖ends.2‖ ≤ R := selectionOutput_radius q a R K n m h _ _ hr
      have hh := bisectReplyRun_radius q a R n m ends hleft hright tail (t-2*selectionBlocks K h)
      exact norm_segmentMid_le q (bisectReplyRun q a n m ends tail (t-2*selectionBlocks K h)) R hh.1 hh.2

end LongTails.Proofs.CovarianceSoftCutTournament





