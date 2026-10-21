import LongTails.Proofs.GeneralCovarianceReverseFisherParts
import LongTails.Proofs.GeneralCovarianceReverseFisherTail
import Mathlib.Algebra.Order.Chebyshev

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherBilinear

open LongTails.Proofs.GeneralCovarianceReverseFisherScore
open LongTails.Proofs.GeneralCovarianceReverseFisherDerivative
open LongTails.Proofs.GeneralCovarianceReverseFisherParts
open LongTails.Proofs.GeneralCovarianceReverseFisherTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

section Spectral

variable (A : E ≃L[ℝ] E) {lo hi : ℝ}

lemma sq_le_of_quartic {p q c : ℝ} (_hc : 0 < c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : c * (p ^ 2 * p ^ 2) ≤ q * p ^ 2) : c * p ^ 2 ≤ q := by
  rcases hp.lt_or_eq with h0 | h0
  · have hp2 : 0 < p ^ 2 := by positivity
    nlinarith
  · subst h0
    simpa using hq

lemma norm_precision_sq_le (hlo : 0 < lo) (h : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2) (w : E) :
    lo * ‖precision A w‖ ^ 2 ≤ ‖A.symm w‖ ^ 2 := by
  set p := ‖precision A w‖
  set q := ‖A.symm w‖
  set r := ‖A.symm (precision A w)‖
  have h1 : p ^ 2 ≤ q * r := by
    have e : p ^ 2 = ⟪A.symm w, A.symm (precision A w)⟫ := by
      rw [← precision_inner, real_inner_self_eq_norm_sq]
    rw [e]
    exact real_inner_le_norm _ _
  have h2 : lo * r ^ 2 ≤ p ^ 2 := h (precision A w)
  have hp := norm_nonneg (precision A w)
  have hq := norm_nonneg (A.symm w)
  have hr := norm_nonneg (A.symm (precision A w))
  have h4 : p ^ 2 * p ^ 2 ≤ (q * r) * (q * r) :=
    mul_self_le_mul_self (sq_nonneg p) h1
  refine sq_le_of_quartic hlo hp (sq_nonneg _) ?_
  calc lo * (p ^ 2 * p ^ 2) ≤ lo * ((q * r) * (q * r)) := by gcongr
    _ = q ^ 2 * (lo * r ^ 2) := by ring
    _ ≤ q ^ 2 * p ^ 2 := by gcongr

lemma norm_precision_sq_ge (hhi : 0 < hi) (h : ∀ w, ‖w‖ ^ 2 ≤ hi * ‖A.symm w‖ ^ 2) (w : E) :
    ‖A.symm w‖ ^ 2 ≤ hi * ‖precision A w‖ ^ 2 := by
  set p := ‖precision A w‖
  set q := ‖A.symm w‖
  have h1 : q ^ 2 ≤ p * ‖w‖ := by
    have e : q ^ 2 = ⟪precision A w, w⟫ := by
      rw [precision_inner, real_inner_self_eq_norm_sq]
    rw [e]
    exact real_inner_le_norm _ _
  have h2 := h w
  have hp := norm_nonneg (precision A w)
  have hq := norm_nonneg (A.symm w)
  have hw := norm_nonneg w
  have h4 : q ^ 2 * q ^ 2 ≤ (p * ‖w‖) * (p * ‖w‖) := mul_self_le_mul_self (sq_nonneg q) h1
  have h5 : (1 : ℝ) * (q ^ 2 * q ^ 2) ≤ (hi * p ^ 2) * q ^ 2 := by
    calc 1 * (q ^ 2 * q ^ 2) ≤ (p * ‖w‖) * (p * ‖w‖) := by linarith
      _ = p ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ p ^ 2 * (hi * q ^ 2) := by gcongr
      _ = (hi * p ^ 2) * q ^ 2 := by ring
  simpa using sq_le_of_quartic one_pos hq (by positivity) h5

end Spectral


lemma parseval (x y : E) :
    ∑ k, ⟪x, stdOrthonormalBasis ℝ E k⟫ * ⟪y, stdOrthonormalBasis ℝ E k⟫ = ⟪x, y⟫ := by
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner x y]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [real_inner_comm y]

lemma real_jensen {k : ℕ} (ρ : Fin k → ℝ) (hρ0 : ∀ j, 0 ≤ ρ j) (hρ : ∑ j, ρ j = 1)
    (z : Fin k → ℝ) : (∑ j, ρ j * z j) ^ 2 ≤ ∑ j, ρ j * z j ^ 2 := by
  have h := norm_sum_sq_le (V := ℝ) ρ hρ0 hρ z
  simpa [Real.norm_eq_abs, sq_abs, smul_eq_mul] using h

lemma sum_four_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → α → β → β → ℝ) :
    ∑ k, ∑ l, ∑ i, ∑ j, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
  calc ∑ k, ∑ l, ∑ i, ∑ j, f i j k l = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

section Pointwise

variable [NeZero n] (A : E ≃L[ℝ] E) (θ : Means E n) (x : E)

local notation "r" => resp A (fun l => θ l) x

noncomputable def dev (i : Fin n) : E := θ i - posteriorMean A (fun l => θ l) x

noncomputable def bar (Y : Fin n → E) : E := ∑ i, r i • Y i

noncomputable def coord (Y : Fin n → E) (k l : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ i, r i * (⟪precision A (dev A θ x i), stdOrthonormalBasis ℝ E k⟫ *
    ⟪precision A (Y i), stdOrthonormalBasis ℝ E l⟫)

noncomputable def bsec (Y Z : Fin n → E) : ℝ :=
  ∑ i, ∑ j, r i * r j *
    (⟪precision A (dev A θ x i), precision A (dev A θ x j)⟫ *
      ⟪precision A (Y i), precision A (Z j)⟫)

noncomputable def bpt (Y Z : Fin n → E) : ℝ :=
  ⟪A.symm (precision A (bar A θ x Y)), A.symm (precision A (bar A θ x Z))⟫ + bsec A θ x Y Z

omit [FiniteDimensional ℝ E] in
lemma sum_resp_dev : ∑ i, r i • dev A θ x i = 0 := sum_resp_smul_sub A (fun l => θ l) x

omit [NeZero n] in
lemma bsec_eq_coord (Y Z : Fin n → E) :
    bsec A θ x Y Z = ∑ k, ∑ l, coord A θ x Y k l * coord A θ x Z k l := by
  symm
  simp only [coord, Finset.sum_mul_sum]
  rw [sum_four_comm (fun i j k l => r i * (⟪precision A (dev A θ x i),
      stdOrthonormalBasis ℝ E k⟫ * ⟪precision A (Y i), stdOrthonormalBasis ℝ E l⟫) *
    (r j * (⟪precision A (dev A θ x j), stdOrthonormalBasis ℝ E k⟫ *
      ⟪precision A (Z j), stdOrthonormalBasis ℝ E l⟫)))]
  unfold bsec
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← parseval (precision A (dev A θ x i)) (precision A (dev A θ x j)),
    ← parseval (precision A (Y i)) (precision A (Z j)), Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

lemma coord_shift (Y : Fin n → E) (c : E) (k l : Fin (Module.finrank ℝ E)) :
    coord A θ x (fun i => Y i + c) k l = coord A θ x Y k l := by
  unfold coord
  have hz : ∑ i, r i * ⟪precision A (dev A θ x i), stdOrthonormalBasis ℝ E k⟫ = 0 := by
    have := congrArg (fun z => ⟪precision A z, stdOrthonormalBasis ℝ E k⟫) (sum_resp_dev A θ x)
    simpa [map_sum, map_smul, sum_inner, inner_smul_left] using this
  simp only [map_add, inner_add_left, mul_add, Finset.sum_add_distrib]
  rw [add_eq_left]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hz, zero_mul]

omit [NeZero n] in
lemma bsec_self_nonneg (Y : Fin n → E) : 0 ≤ bsec A θ x Y Y := by
  rw [bsec_eq_coord]
  exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => mul_self_nonneg _))

omit [NeZero n] in
lemma bpt_self_nonneg (Y : Fin n → E) : 0 ≤ bpt A θ x Y Y := by
  unfold bpt
  rw [real_inner_self_eq_norm_sq]
  exact add_nonneg (sq_nonneg _) (bsec_self_nonneg A θ x Y)

omit [NeZero n] in
lemma bpt_le_amgm (Y Z : Fin n → E) {s : ℝ} (hs : 0 < s) :
    bpt A θ x Y Z ≤ s / 2 * bpt A θ x Y Y + 1 / (2 * s) * bpt A θ x Z Z := by
  have key : ∀ a c : ℝ, a * c ≤ s / 2 * (a * a) + 1 / (2 * s) * (c * c) := by
    intro a c
    rw [← sub_nonneg]
    have : s / 2 * (a * a) + 1 / (2 * s) * (c * c) - a * c = (s * a - c) ^ 2 / (2 * s) := by
      field_simp; ring
    rw [this]
    positivity
  have hv : ∀ a c : E, ⟪a, c⟫ ≤ s / 2 * ⟪a, a⟫ + 1 / (2 * s) * ⟪c, c⟫ := by
    intro a c
    rw [← sub_nonneg]
    have : s / 2 * ⟪a, a⟫ + 1 / (2 * s) * ⟪c, c⟫ - ⟪a, c⟫ = ⟪s • a - c, s • a - c⟫ / (2 * s) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
        inner_smul_right, inner_smul_right, real_inner_comm c a]
      simp only [conj_trivial]
      field_simp
      ring
    rw [this]
    exact div_nonneg real_inner_self_nonneg (by positivity)
  unfold bpt
  rw [bsec_eq_coord, bsec_eq_coord, bsec_eq_coord]
  have h2 : ∑ k, ∑ l, coord A θ x Y k l * coord A θ x Z k l ≤
      s / 2 * ∑ k, ∑ l, coord A θ x Y k l * coord A θ x Y k l +
        1 / (2 * s) * ∑ k, ∑ l, coord A θ x Z k l * coord A θ x Z k l := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun l _ => key _ _)
  have h1 := hv (A.symm (precision A (bar A θ x Y))) (A.symm (precision A (bar A θ x Z)))
  linarith

end Pointwise


section Bounds

variable [NeZero n] (A : E ≃L[ℝ] E) (θ : Means E n) (x : E) {lo hi : ℝ}

local notation "r" => resp A (fun l => θ l) x

lemma bpt_upper (hlo : 0 < lo) (hl : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2) (Y : Fin n → E) :
    lo ^ 2 * bpt A θ x Y Y ≤
      ∑ i, r i * ((1 + ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2) := by
  have hr0 := resp_nonneg A (fun l => θ l) x
  have hr1 := sum_resp A (fun l => θ l) x
  have hP : ∀ w, lo * ‖precision A w‖ ^ 2 ≤ ‖A.symm w‖ ^ 2 := norm_precision_sq_le A hlo hl
  have h1 : lo ^ 2 * ‖A.symm (precision A (bar A θ x Y))‖ ^ 2 ≤ ∑ i, r i * ‖A.symm (Y i)‖ ^ 2 := by
    have a1 := hl (precision A (bar A θ x Y))
    have a2 := hP (bar A θ x Y)
    have a3 : ‖A.symm (bar A θ x Y)‖ ^ 2 ≤ ∑ i, r i * ‖A.symm (Y i)‖ ^ 2 := by
      have := norm_sum_sq_le r hr0 hr1 (fun i => A.symm (Y i))
      simpa [bar, map_sum, map_smul] using this
    nlinarith
  have h2 : lo ^ 2 * bsec A θ x Y Y ≤
      ∑ i, r i * (‖A.symm (dev A θ x i)‖ ^ 2 * ‖A.symm (Y i)‖ ^ 2) := by
    rw [bsec_eq_coord]
    have hc : ∀ k l, coord A θ x Y k l * coord A θ x Y k l ≤
        ∑ i, r i * (⟪precision A (dev A θ x i), stdOrthonormalBasis ℝ E k⟫ *
          ⟪precision A (Y i), stdOrthonormalBasis ℝ E l⟫) ^ 2 := by
      intro k l
      rw [← sq]
      exact real_jensen r hr0 hr1 _
    have hs : ∑ k, ∑ l, coord A θ x Y k l * coord A θ x Y k l ≤
        ∑ i, r i * (‖precision A (dev A θ x i)‖ ^ 2 * ‖precision A (Y i)‖ ^ 2) := by
      refine (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hc k l))).trans
        (le_of_eq ?_)
      simp_rw [mul_pow]
      rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left (precision A (dev A θ x i)),
        ← (stdOrthonormalBasis ℝ E).sum_sq_inner_left (precision A (Y i)), Finset.sum_mul_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
    have hl2 : 0 ≤ lo ^ 2 := sq_nonneg lo
    refine (mul_le_mul_of_nonneg_left hs hl2).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have a1 := hP (dev A θ x i)
    have a2 := hP (Y i)
    have hri := hr0 i
    have : lo ^ 2 * (‖precision A (dev A θ x i)‖ ^ 2 * ‖precision A (Y i)‖ ^ 2) ≤
        ‖A.symm (dev A θ x i)‖ ^ 2 * ‖A.symm (Y i)‖ ^ 2 := by
      calc lo ^ 2 * (‖precision A (dev A θ x i)‖ ^ 2 * ‖precision A (Y i)‖ ^ 2)
          = (lo * ‖precision A (dev A θ x i)‖ ^ 2) * (lo * ‖precision A (Y i)‖ ^ 2) := by ring
        _ ≤ ‖A.symm (dev A θ x i)‖ ^ 2 * ‖A.symm (Y i)‖ ^ 2 :=
            mul_le_mul a1 a2 (by positivity) (sq_nonneg _)
    calc lo ^ 2 * (r i * (‖precision A (dev A θ x i)‖ ^ 2 * ‖precision A (Y i)‖ ^ 2))
        = r i * (lo ^ 2 * (‖precision A (dev A θ x i)‖ ^ 2 * ‖precision A (Y i)‖ ^ 2)) := by ring
      _ ≤ r i * (‖A.symm (dev A θ x i)‖ ^ 2 * ‖A.symm (Y i)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this hri
  unfold bpt
  rw [real_inner_self_eq_norm_sq, mul_add]
  have : ∑ i, r i * ((1 + ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2) =
      ∑ i, r i * ‖A.symm (Y i)‖ ^ 2 +
        ∑ i, r i * (‖A.symm (dev A θ x i)‖ ^ 2 * ‖A.symm (Y i)‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this]
  linarith

omit [FiniteDimensional ℝ E] in
lemma bar_shift (t : E) : bar A θ x (fun i => θ i - t) = center A t θ x := by
  rw [center_eq]; rfl

omit [FiniteDimensional ℝ E] [NeZero n] in
lemma shift_dev (t : E) :
    (fun i => θ i - t) = fun i => dev A θ x i + center A t θ x := by
  funext i
  simp only [dev, center]
  abel

lemma bsec_shift_left (Y Z : Fin n → E) (c : E) :
    bsec A θ x (fun i => Y i + c) Z = bsec A θ x Y Z := by
  rw [bsec_eq_coord, bsec_eq_coord]
  simp_rw [coord_shift]

lemma bsec_shift_right (Y Z : Fin n → E) (c : E) :
    bsec A θ x Y (fun i => Z i + c) = bsec A θ x Y Z := by
  rw [bsec_eq_coord, bsec_eq_coord]
  simp_rw [coord_shift]

omit [NeZero n] in
lemma bsec_dev_ge_d [Nontrivial E] :
    (∑ i, r i * ‖precision A (dev A θ x i)‖ ^ 2) ^ 2 / (Module.finrank ℝ E) ≤
      bsec A θ x (dev A θ x) (dev A θ x) := by
  rw [bsec_eq_coord]
  have hdiag : ∑ k, coord A θ x (dev A θ x) k k = ∑ i, r i * ‖precision A (dev A θ x i)‖ ^ 2 := by
    unfold coord
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum, ← (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
    simp_rw [sq]
  have h1 : (∑ k, coord A θ x (dev A θ x) k k) ^ 2 ≤
      (Module.finrank ℝ E) * ∑ k, coord A θ x (dev A θ x) k k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun k => coord A θ x (dev A θ x) k k)
    simpa using this
  have h2 : ∑ k, coord A θ x (dev A θ x) k k ^ 2 ≤
      ∑ k, ∑ l, coord A θ x (dev A θ x) k l * coord A θ x (dev A θ x) k l := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [sq]
    exact Finset.single_le_sum (f := fun l => coord A θ x (dev A θ x) k l *
      coord A θ x (dev A θ x) k l) (fun l _ => mul_self_nonneg _) (Finset.mem_univ k)
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  rw [div_le_iff₀ hd, ← hdiag]
  nlinarith

lemma bsec_dev_ge_n :
    (∑ i, r i * ‖precision A (dev A θ x i)‖ ^ 2) ^ 2 / n ≤
      bsec A θ x (dev A θ x) (dev A θ x) := by
  have hr0 := resp_nonneg A (fun l => θ l) x
  have h1 : (∑ i, r i * ‖precision A (dev A θ x i)‖ ^ 2) ^ 2 ≤
      n * ∑ i, (r i * ‖precision A (dev A θ x i)‖ ^ 2) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i => r i * ‖precision A (dev A θ x i)‖ ^ 2)
    simpa using this
  have h2 : ∑ i, (r i * ‖precision A (dev A θ x i)‖ ^ 2) ^ 2 ≤
      bsec A θ x (dev A θ x) (dev A θ x) := by
    unfold bsec
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hnn : ∀ j, 0 ≤ r i * r j * (⟪precision A (dev A θ x i), precision A (dev A θ x j)⟫ *
        ⟪precision A (dev A θ x i), precision A (dev A θ x j)⟫) := fun j =>
      mul_nonneg (mul_nonneg (hr0 i) (hr0 j)) (mul_self_nonneg _)
    have := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    refine le_trans (le_of_eq ?_) this
    rw [real_inner_self_eq_norm_sq]
    ring
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [div_le_iff₀ hn]
  nlinarith

lemma bpt_lower [Nontrivial E] (hhi : 0 < hi) (hh : ∀ w, ‖w‖ ^ 2 ≤ hi * ‖A.symm w‖ ^ 2) (t : E) :
    ‖A.symm (center A t θ x)‖ ^ 2 +
        (∑ i, r i * ‖A.symm (dev A θ x i)‖ ^ 2) ^ 2 / (min n (Module.finrank ℝ E) : ℕ) ≤
      hi ^ 2 * bpt A θ x (fun i => θ i - t) (fun i => θ i - t) := by
  have hr0 := resp_nonneg A (fun l => θ l) x
  have hP := norm_precision_sq_ge A hhi hh
  unfold bpt
  rw [bar_shift, real_inner_self_eq_norm_sq, shift_dev, bsec_shift_left, bsec_shift_right]
  have hfirst : ‖A.symm (center A t θ x)‖ ^ 2 ≤
      hi ^ 2 * ‖A.symm (precision A (center A t θ x))‖ ^ 2 := by
    have a1 := hP (center A t θ x)
    have a2 := hh (precision A (center A t θ x))
    nlinarith
  set S := ∑ i, r i * ‖precision A (dev A θ x i)‖ ^ 2
  set ST := ∑ i, r i * ‖A.symm (dev A θ x i)‖ ^ 2
  have hST : ST ≤ hi * S := by
    simp only [ST, S, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := hP (dev A θ x i)
    nlinarith [hr0 i]
  have hST0 : 0 ≤ ST := Finset.sum_nonneg (fun i _ => mul_nonneg (hr0 i) (sq_nonneg _))
  have hsq : ST ^ 2 ≤ hi ^ 2 * S ^ 2 := by
    have := pow_le_pow_left₀ hST0 hST 2
    nlinarith
  have hm : (0 : ℝ) < (min n (Module.finrank ℝ E) : ℕ) := by
    have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
    exact_mod_cast lt_min (Nat.pos_of_ne_zero (NeZero.ne n)) hd
  have hsec : S ^ 2 / (min n (Module.finrank ℝ E) : ℕ) ≤ bsec A θ x (dev A θ x) (dev A θ x) := by
    rcases le_total n (Module.finrank ℝ E) with h | h
    · rw [min_eq_left h]; exact bsec_dev_ge_n A θ x
    · rw [min_eq_right h]; exact bsec_dev_ge_d A θ x
  have : ST ^ 2 / (min n (Module.finrank ℝ E) : ℕ) ≤
      hi ^ 2 * (S ^ 2 / (min n (Module.finrank ℝ E) : ℕ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hsq hm.le
  nlinarith [mul_le_mul_of_nonneg_left hsec (sq_nonneg hi)]

lemma pairing_eq (t : E) (Y : Fin n → E) :
    pairing A t θ x (WithLp.toLp 2 (fun i => precision A (Y i))) =
      2 * total A (fun l => θ l) x * bpt A θ x Y (fun i => θ i - t) := by
  have hw : ∀ i, weight A (fun l => θ l) x i = total A (fun l => θ l) x * r i := by
    intro i
    unfold resp
    field_simp [(total_pos A (fun l => θ l) x).ne']
  unfold pairing bpt
  rw [shift_dev, bsec_shift_right, ← shift_dev, bar_shift]
  simp only [hw]
  have e1 : ∑ i, total A (fun l => θ l) x * r i *
      (2 * ⟪precision A (precision A (center A t θ x)), precision A (Y i)⟫) =
      2 * total A (fun l => θ l) x *
        ⟪A.symm (precision A (bar A θ x Y)), A.symm (precision A (center A t θ x))⟫ := by
    rw [real_inner_comm, ← precision_inner]
    simp only [bar, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have e2 : ∑ i, total A (fun l => θ l) x * r i * ⟪gradPsi A θ x i, precision A (Y i)⟫ =
      2 * total A (fun l => θ l) x * bsec A θ x Y (dev A θ x) := by
    simp only [gradPsi, bsec, dev, inner_smul_left, sum_inner, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [real_inner_comm (precision A (θ j - posteriorMean A (fun l => θ l) x))
      (precision A (θ i - posteriorMean A (fun l => θ l) x)),
      real_inner_comm (precision A (θ j - posteriorMean A (fun l => θ l) x)) (precision A (Y i))]
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [e1, e2]

omit [NeZero n] in
lemma bpt_neg_left (Y Z : Fin n → E) :
    bpt A θ x (fun i => -Y i) Z = -bpt A θ x Y Z := by
  unfold bpt bsec bar
  simp only [smul_neg, Finset.sum_neg_distrib, map_neg, inner_neg_left, mul_neg, neg_add]

omit [NeZero n] in
lemma abs_bpt_le (Y Z : Fin n → E) :
    |bpt A θ x Y Z| ≤ (bpt A θ x Y Y + bpt A θ x Z Z) / 2 := by
  have h1 := bpt_le_amgm A θ x Y Z one_pos
  have h2 := bpt_le_amgm A θ x (fun i => -Y i) Z one_pos
  have h3 : bpt A θ x (fun i => -Y i) (fun i => -Y i) = bpt A θ x Y Y := by
    rw [bpt_neg_left]
    have : bpt A θ x Y (fun i => -Y i) = -bpt A θ x Y Y := by
      unfold bpt bsec bar
      simp only [smul_neg, Finset.sum_neg_distrib, map_neg, inner_neg_right, mul_neg, neg_add]
    rw [this, neg_neg]
  rw [bpt_neg_left, h3] at h2
  rw [abs_le]
  constructor <;> linarith

lemma continuous_bpt (Y Z : Fin n → E) : Continuous (fun x => bpt A θ x Y Z) := by
  have hr : ∀ i, Continuous (fun x => resp A (fun l => θ l) x i) := continuous_resp A _
  have hd : ∀ i, Continuous (fun x => precision A (dev A θ x i)) := fun i =>
    (precision A).continuous.comp (continuous_const.sub (continuous_posteriorMean A _))
  have hb : ∀ W : Fin n → E, Continuous (fun x => A.symm (precision A (bar A θ x W))) :=
    fun W => (A.symm : E →L[ℝ] E).continuous.comp ((precision A).continuous.comp
      (continuous_finsetSum _ (fun i _ => (hr i).smul continuous_const)))
  unfold bpt bsec
  exact ((hb Y).inner (hb Z)).add (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
    (fun j _ => ((hr i).mul (hr j)).mul (((hd i).inner (hd j)).mul continuous_const))))

end Bounds

end LongTails.Proofs.GeneralCovarianceReverseFisherBilinear
