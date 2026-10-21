import LongTails.Proofs.GeneralCovarianceReverseFisherLoss
import Mathlib.Algebra.QuadraticDiscriminant

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherDescent

open LongTails.Proofs.GeneralCovarianceReverseFisherScore
open LongTails.Proofs.GeneralCovarianceReverseFisherDerivative
open LongTails.Proofs.GeneralCovarianceReverseFisherParts
open LongTails.Proofs.GeneralCovarianceReverseFisherTail
open LongTails.Proofs.GeneralCovarianceReverseFisherBilinear
open LongTails.Proofs.GeneralCovarianceReverseFisherLoss

lemma descent_algebra {V0 V1 a VG bGU bGG bUU c γ m : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hγ : γ = m / (2 * c)) (hV : V1 = V0 - 2 * γ * a + γ ^ 2 * VG)
    (ha : a = 2 / m * bUU) (hVG : VG = 2 / m * bGU) (hGG : bGG ≤ c * VG)
    (hamgm : bGU ≤ m / (2 * c) / 2 * bGG + 1 / (2 * (m / (2 * c))) * bUU) :
    V1 ≤ V0 - bUU / c := by
  have h1 : bGU ≤ 2 * c / m * bUU := by
    have e1 : m / (2 * c) / 2 * bGG ≤ m / (2 * c) / 2 * (c * (2 / m * bGU)) := by
      rw [← hVG]; exact mul_le_mul_of_nonneg_left hGG (by positivity)
    have e2 : m / (2 * c) / 2 * (c * (2 / m * bGU)) = bGU / 2 := by
      field_simp
    have e3 : 1 / (2 * (m / (2 * c))) * bUU = c / m * bUU := by
      field_simp
    have e4 : 2 * c / m * bUU = 2 * (c / m * bUU) := by ring
    rw [e4]
    linarith
  have h2 : VG ≤ 4 * c / m ^ 2 * bUU := by
    rw [hVG]
    calc 2 / m * bGU ≤ 2 / m * (2 * c / m * bUU) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * c / m ^ 2 * bUU := by ring
  rw [hV, ha, hγ]
  have h3 : (m / (2 * c)) ^ 2 * VG ≤ (m / (2 * c)) ^ 2 * (4 * c / m ^ 2 * bUU) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have e5 : (m / (2 * c)) ^ 2 * (4 * c / m ^ 2 * bUU) = bUU / c := by
    field_simp
    ring
  have e6 : 2 * (m / (2 * c)) * (2 / m * bUU) = 2 * (bUU / c) := by
    field_simp
  linarith

lemma min_split {X Y W N : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hW : X + Y = W) (hN : 0 < N) :
    min (W / 2) (W ^ 2 / (4 * N)) ≤ X + Y ^ 2 / N := by
  rcases le_total (W / 2) X with h | h
  · have : 0 ≤ Y ^ 2 / N := by positivity
    exact (min_le_left _ _).trans (by linarith)
  · have hY2 : W / 2 ≤ Y := by linarith
    have hW0 : 0 ≤ W / 2 := by linarith
    have hsq : (W / 2) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hW0 hY2 2
    have : W ^ 2 / (4 * N) ≤ Y ^ 2 / N := by
      rw [div_le_div_iff₀ (by positivity) hN]
      nlinarith
    exact (min_le_right _ _).trans (by linarith)

section Integrals

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ} [NeZero n]
  (A : E ≃L[ℝ] E) (θ : Means E n) {lo hi : ℝ}

noncomputable def vnorm (Y : Fin n → E) : ℝ := ∑ i, ‖A.symm (Y i)‖ ^ 2

noncomputable def beta (Y Z : Fin n → E) : ℝ :=
  normalizer A * ∫ x, total A (fun l => θ l) x * bpt A θ x Y Z

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NeZero n] in
lemma total_mul (x : E) (F : ℝ) :
    total A (fun l => θ l) x * F = ∑ i, weight A (fun l => θ l) x i * F := by
  unfold total; rw [Finset.sum_mul]

omit [MeasurableSpace E] [BorelSpace E] in
omit [FiniteDimensional ℝ E] in
lemma weight_eq_total_mul_resp (x : E) (i : Fin n) :
    weight A (fun l => θ l) x i = total A (fun l => θ l) x * resp A (fun l => θ l) x i := by
  unfold resp
  field_simp [(total_pos A (fun l => θ l) x).ne']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_symm_dev_le (x : E) (i : Fin n) :
    ‖A.symm (dev A θ x i)‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (2 * spread 0 θ) := by
  refine (ContinuousLinearMap.le_opNorm (A.symm : E →L[ℝ] E) _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sub_mean_le A 0 θ x i) (norm_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] in
lemma bpt_self_bound (hlo : 0 < lo) (hl : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2) (x : E)
    (Y : Fin n → E) :
    bpt A θ x Y Y ≤ (1 + (‖(A.symm : E →L[ℝ] E)‖ * (2 * spread 0 θ)) ^ 2) * vnorm A Y / lo ^ 2 := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine (bpt_upper A θ x hlo hl Y).trans ?_
  unfold vnorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hr0 := resp_nonneg A (fun l => θ l) x i
  have hr1 := resp_le_one A θ x i
  have hd := pow_le_pow_left₀ (norm_nonneg _) (norm_symm_dev_le A θ x i) 2
  have : (1 + ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2 ≤
      (1 + (‖(A.symm : E →L[ℝ] E)‖ * (2 * spread 0 θ)) ^ 2) * ‖A.symm (Y i)‖ ^ 2 := by
    gcongr
  calc resp A (fun l => θ l) x i * ((1 + ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2)
      ≤ 1 * ((1 + ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hr1 (by positivity)
    _ ≤ _ := by rw [one_mul]; exact this

lemma integrable_total_bpt (hlo : 0 < lo) (hl : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2)
    (Y Z : Fin n → E) :
    Integrable (fun x => total A (fun l => θ l) x * bpt A θ x Y Z) := by
  simp_rw [total_mul]
  set Cd := ‖(A.symm : E →L[ℝ] E)‖ * (2 * spread 0 θ)
  refine integrable_finsetSum _ (fun i _ => integrable_weight_mul A _ i
    (continuous_bpt A θ Y Z) (C := ((1 + Cd ^ 2) * vnorm A Y / lo ^ 2 +
      (1 + Cd ^ 2) * vnorm A Z / lo ^ 2) / 2) (fun x => ?_))
  refine (abs_bpt_le A θ x Y Z).trans ?_
  have h1 := bpt_self_bound A θ hlo hl x Y
  have h2 := bpt_self_bound A θ hlo hl x Z
  exact div_le_div_of_nonneg_right (add_le_add h1 h2) zero_le_two

lemma weighted_cauchy_schwarz {g f : E → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g)
    (hgf : Integrable (fun x => g x * f x)) (hgf2 : Integrable (fun x => g x * f x ^ 2)) :
    (∫ x, g x * f x) ^ 2 ≤ (∫ x, g x) * ∫ x, g x * f x ^ 2 := by
  have h : ∀ a : ℝ, 0 ≤ (∫ x, g x) * (a * a) + (-2 * ∫ x, g x * f x) * a +
      ∫ x, g x * f x ^ 2 := by
    intro a
    have hnn : 0 ≤ ∫ x, g x * (f x - a) ^ 2 :=
      integral_nonneg (fun x => mul_nonneg (hg0 x) (sq_nonneg _))
    have hexp : ∫ x, g x * (f x - a) ^ 2 =
        (∫ x, g x * f x ^ 2) - 2 * a * (∫ x, g x * f x) + a ^ 2 * (∫ x, g x) := by
      have e : ∀ x, g x * (f x - a) ^ 2 =
          g x * f x ^ 2 - 2 * a * (g x * f x) + a ^ 2 * g x := fun x => by ring
      simp_rw [e]
      have i1 : Integrable (fun x => g x * f x ^ 2 - 2 * a * (g x * f x)) :=
        hgf2.sub (hgf.const_mul (2 * a))
      have i2 : Integrable (fun x => a ^ 2 * g x) := hg.const_mul _
      have i3 : Integrable (fun x => 2 * a * (g x * f x)) := hgf.const_mul (2 * a)
      rw [integral_add i1 i2, integral_sub hgf2 i3, integral_const_mul, integral_const_mul]
    rw [hexp] at hnn
    nlinarith [hnn]
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

lemma integrable_weight_bounded {k : ℕ} (c : Fin k → E) (i : Fin k) {F : E → ℝ}
    (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    Integrable (fun x => weight A c x i * F x) := integrable_weight_mul A c i hF hC

omit [NeZero n] in
lemma integrable_total_mul {F : E → ℝ} (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    Integrable (fun x => total A (fun l => θ l) x * F x) := by
  simp_rw [total_mul]
  exact integrable_finsetSum _ (fun i _ => integrable_weight_mul A _ i hF hC)

omit [NeZero n] in
lemma normalizer_integral_total :
    normalizer A * ∫ x, total A (fun l => θ l) x = n := by
  unfold total
  rw [integral_finsetSum _ (fun i _ => integrable_weight A _ i), Finset.mul_sum]
  simp [normalizer_mul_integral_weight]

omit [NeZero n] in
lemma normalizer_integral_total_mul (F : Fin n → ℝ) :
    normalizer A * ∫ x, ∑ i, weight A (fun l => θ l) x i * F i = ∑ i, F i := by
  rw [integral_finsetSum _ (fun i _ => (integrable_weight A _ i).mul_const _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_mul_const, ← mul_assoc, normalizer_mul_integral_weight, one_mul]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma continuous_dev (i : Fin n) : Continuous (fun x => A.symm (dev A θ x i)) :=
  (A.symm : E →L[ℝ] E).continuous.comp (continuous_const.sub (continuous_posteriorMean A _))

lemma beta_self_le (hlo : 0 < lo) (hl : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2) (Y : Fin n → E) :
    lo ^ 2 * beta A θ Y Y ≤ (1 + 8 * Real.log n) * vnorm A Y := by
  set Cd := ‖(A.symm : E →L[ℝ] E)‖ * (2 * spread 0 θ)
  have hint : ∀ i, Integrable (fun x => weight A (fun l => θ l) x i *
      ‖A.symm (dev A θ x i)‖ ^ 2) := fun i =>
    integrable_weight_mul A _ i ((continuous_dev A θ i).norm.pow 2) (C := Cd ^ 2) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_symm_dev_le A θ x i) 2)
  have hpt : ∀ x, lo ^ 2 * (total A (fun l => θ l) x * bpt A θ x Y Y) ≤
      ∑ i, (weight A (fun l => θ l) x i +
        weight A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2 := by
    intro x
    have hb := bpt_upper A θ x hlo hl Y
    have ht := (total_pos A (fun l => θ l) x).le
    calc lo ^ 2 * (total A (fun l => θ l) x * bpt A θ x Y Y)
        = total A (fun l => θ l) x * (lo ^ 2 * bpt A θ x Y Y) := by ring
      _ ≤ total A (fun l => θ l) x * ∑ i, resp A (fun l => θ l) x i *
          ((1 + ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb ht
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [weight_eq_total_mul_resp A θ x i]
          ring
  have hI : ∀ i, Integrable (fun x => (weight A (fun l => θ l) x i +
      weight A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2) :=
    fun i => ((integrable_weight A _ i).add (hint i)).mul_const _
  have hR : Integrable (fun x => ∑ i, (weight A (fun l => θ l) x i +
      weight A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2) :=
    integrable_finsetSum _ (fun i _ => hI i)
  have hκ := (normalizer_pos A).le
  unfold beta vnorm
  calc lo ^ 2 * (normalizer A * ∫ x, total A (fun l => θ l) x * bpt A θ x Y Y)
      = normalizer A * ∫ x, lo ^ 2 * (total A (fun l => θ l) x * bpt A θ x Y Y) := by
        rw [integral_const_mul]; ring
    _ ≤ normalizer A * ∫ x, ∑ i, (weight A (fun l => θ l) x i +
          weight A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (integral_mono
          ((integrable_total_bpt A θ hlo hl Y Y).const_mul _) hR hpt) hκ
    _ = ∑ i, (1 + normalizer A * ∫ x, weight A (fun l => θ l) x i *
          ‖A.symm (dev A θ x i)‖ ^ 2) * ‖A.symm (Y i)‖ ^ 2 := by
        rw [integral_finsetSum _ (fun i _ => hI i), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_mul_const, integral_add (integrable_weight A _ i) (hint i)]
        linear_combination ‖A.symm (Y i)‖ ^ 2 * normalizer_mul_integral_weight A (fun l => θ l) i
    _ ≤ ∑ i, (1 + 8 * Real.log n) * ‖A.symm (Y i)‖ ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h : normalizer A * ∫ x, weight A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2 ≤
            8 * Real.log n := tail_x A (fun l => θ l) i
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

lemma beta_amgm (hlo : 0 < lo) (hl : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2) (Y Z : Fin n → E)
    {s : ℝ} (hs : 0 < s) :
    beta A θ Y Z ≤ s / 2 * beta A θ Y Y + 1 / (2 * s) * beta A θ Z Z := by
  have hκ := (normalizer_pos A).le
  have hYY := integrable_total_bpt A θ hlo hl Y Y
  have hZZ := integrable_total_bpt A θ hlo hl Z Z
  unfold beta
  have hm : ∫ x, total A (fun l => θ l) x * bpt A θ x Y Z ≤
      ∫ x, (s / 2 * (total A (fun l => θ l) x * bpt A θ x Y Y) +
        1 / (2 * s) * (total A (fun l => θ l) x * bpt A θ x Z Z)) := by
    refine integral_mono (integrable_total_bpt A θ hlo hl Y Z)
      ((hYY.const_mul _).add (hZZ.const_mul _)) (fun x => ?_)
    have h := bpt_le_amgm A θ x Y Z hs
    have ht := (total_pos A (fun l => θ l) x).le
    nlinarith [mul_le_mul_of_nonneg_left h ht]
  rw [integral_add (hYY.const_mul _) (hZZ.const_mul _), integral_const_mul,
    integral_const_mul] at hm
  nlinarith [mul_le_mul_of_nonneg_left hm hκ]

lemma beta_lower [Nontrivial E] (hlo : 0 < lo) (hl : ∀ w, lo * ‖A.symm w‖ ^ 2 ≤ ‖w‖ ^ 2)
    (hhi : 0 < hi) (hh : ∀ w, ‖w‖ ^ 2 ≤ hi * ‖A.symm w‖ ^ 2) (t : E) :
    min (vnorm A (fun i => θ i - t) / 2)
        (vnorm A (fun i => θ i - t) ^ 2 / (4 * (n * (min n (Module.finrank ℝ E) : ℕ)))) ≤
      hi ^ 2 * beta A θ (fun i => θ i - t) (fun i => θ i - t) := by
  set k' : ℝ := ((min n (Module.finrank ℝ E) : ℕ) : ℝ)
  have hk' : 0 < k' := by
    have : 0 < min n (Module.finrank ℝ E) :=
      lt_min (Nat.pos_of_ne_zero (NeZero.ne n)) Module.finrank_pos
    exact Nat.cast_pos.mpr this
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set κ := normalizer A
  have hκ : 0 < κ := normalizer_pos A
  set g : E → ℝ := fun x => ‖A.symm (center A t θ x)‖ ^ 2
  set f : E → ℝ := fun x => ∑ i, resp A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2
  set Cd := ‖(A.symm : E →L[ℝ] E)‖ * (2 * spread 0 θ)
  have hgc : Continuous g :=
    ((A.symm : E →L[ℝ] E).continuous.comp (continuous_center A t θ)).norm.pow 2
  have hfc : Continuous f := continuous_finsetSum _ (fun i _ =>
    (continuous_resp A _ i).mul ((continuous_dev A θ i).norm.pow 2))
  have hg0 : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hf0 : ∀ x, 0 ≤ f x := fun x => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (resp_nonneg A _ x i) (sq_nonneg _))
  have hgb : ∀ x, |g x| ≤ (‖(A.symm : E →L[ℝ] E)‖ * spread t θ) ^ 2 := fun x => by
    rw [abs_of_nonneg (hg0 x)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((ContinuousLinearMap.le_opNorm (A.symm : E →L[ℝ] E) _).trans
      (mul_le_mul_of_nonneg_left (norm_center_le A t θ x) (norm_nonneg _))) 2
  have hfb : ∀ x, |f x| ≤ Cd ^ 2 := fun x => by
    rw [abs_of_nonneg (hf0 x)]
    calc f x ≤ ∑ i, resp A (fun l => θ l) x i * Cd ^ 2 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_symm_dev_le A θ x i) 2)
            (resp_nonneg A _ x i))
      _ = Cd ^ 2 := by rw [← Finset.sum_mul, sum_resp, one_mul]
  have hf2b : ∀ x, |f x ^ 2| ≤ (Cd ^ 2) ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2
  have hIg := integrable_total_mul A θ hgc hgb
  have hIf := integrable_total_mul A θ hfc hfb
  have hIf2 : Integrable (fun x => total A (fun l => θ l) x * f x ^ 2) :=
    integrable_total_mul A θ (F := fun x => f x ^ 2) (hfc.pow 2) hf2b
  have hIt : Integrable (fun x => total A (fun l => θ l) x) := by
    unfold total; exact integrable_finsetSum _ (fun i _ => integrable_weight A _ i)
  set X := κ * ∫ x, total A (fun l => θ l) x * g x
  set Yv := κ * ∫ x, total A (fun l => θ l) x * f x
  set Q := κ * ∫ x, total A (fun l => θ l) x * f x ^ 2
  have hX0 : 0 ≤ X := mul_nonneg hκ.le (integral_nonneg (fun x =>
    mul_nonneg (total_pos A _ x).le (hg0 x)))
  have hY0 : 0 ≤ Yv := mul_nonneg hκ.le (integral_nonneg (fun x =>
    mul_nonneg (total_pos A _ x).le (hf0 x)))
  have hXY : X + Yv = vnorm A (fun i => θ i - t) := by
    have hpt : ∀ x, total A (fun l => θ l) x * g x + total A (fun l => θ l) x * f x =
        ∑ i, weight A (fun l => θ l) x i * ‖A.symm (θ i - t)‖ ^ 2 := by
      intro x
      have hv := weighted_variance (resp A (fun l => θ l) x) (sum_resp A _ x)
        (fun i => A.symm (θ i - t))
      have hc : ∑ l, resp A (fun l => θ l) x l • A.symm (θ l - t) = A.symm (center A t θ x) := by
        rw [center_eq, map_sum]; simp_rw [map_smul]
      rw [hc] at hv
      have hd : ∀ i, A.symm (θ i - t) - A.symm (center A t θ x) = A.symm (dev A θ x i) := by
        intro i; rw [← map_sub]; congr 1; simp only [dev, center]; abel
      simp_rw [hd] at hv
      rw [← mul_add, show g x + f x = ‖A.symm (center A t θ x)‖ ^ 2 +
        ∑ i, resp A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2 from rfl, ← hv,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [weight_eq_total_mul_resp A θ x i]
      ring
    have := normalizer_integral_total_mul A θ (fun i => ‖A.symm (θ i - t)‖ ^ 2)
    simp only [X, Yv, ← mul_add]
    rw [← integral_add hIg hIf]
    simp_rw [hpt]
    rw [this]
    rfl
  have hCS : Yv ^ 2 ≤ n * Q := by
    have h := weighted_cauchy_schwarz (fun x => (total_pos A (fun l => θ l) x).le) hIt hIf hIf2
    have hn' := normalizer_integral_total A θ
    calc Yv ^ 2 = κ ^ 2 * (∫ x, total A (fun l => θ l) x * f x) ^ 2 := by ring
      _ ≤ κ ^ 2 * ((∫ x, total A (fun l => θ l) x) * ∫ x, total A (fun l => θ l) x * f x ^ 2) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = (κ * ∫ x, total A (fun l => θ l) x) * Q := by ring
      _ = n * Q := by rw [hn']
  have hlow : X + Q / k' ≤ hi ^ 2 * beta A θ (fun i => θ i - t) (fun i => θ i - t) := by
    have hpt : ∀ x, total A (fun l => θ l) x * g x + total A (fun l => θ l) x * f x ^ 2 / k' ≤
        hi ^ 2 * (total A (fun l => θ l) x * bpt A θ x (fun i => θ i - t) (fun i => θ i - t)) := by
      intro x
      have hb := bpt_lower A θ x hhi hh t
      have ht := (total_pos A (fun l => θ l) x).le
      have := mul_le_mul_of_nonneg_left hb ht
      calc total A (fun l => θ l) x * g x + total A (fun l => θ l) x * f x ^ 2 / k'
          = total A (fun l => θ l) x * (‖A.symm (center A t θ x)‖ ^ 2 +
            (∑ i, resp A (fun l => θ l) x i * ‖A.symm (dev A θ x i)‖ ^ 2) ^ 2 /
              ((min n (Module.finrank ℝ E) : ℕ) : ℝ)) := by
            simp only [g, f, k']; ring
        _ ≤ _ := this
        _ = _ := by ring
    have hI1 : Integrable (fun x => total A (fun l => θ l) x * g x +
        total A (fun l => θ l) x * f x ^ 2 / k') := hIg.add (hIf2.div_const k')
    have hm := integral_mono hI1
      ((integrable_total_bpt A θ hlo hl _ _).const_mul (hi ^ 2)) hpt
    rw [integral_add hIg (hIf2.div_const k'), integral_div, integral_const_mul] at hm
    unfold beta
    have := mul_le_mul_of_nonneg_left hm hκ.le
    simp only [X, Q]
    have e : κ * ((∫ x, total A (fun l => θ l) x * g x) +
        (∫ x, total A (fun l => θ l) x * f x ^ 2) / k') =
        κ * (∫ x, total A (fun l => θ l) x * g x) +
          κ * (∫ x, total A (fun l => θ l) x * f x ^ 2) / k' := by ring
    rw [e] at this
    nlinarith
  have hYQ : Yv ^ 2 / (n * k') ≤ Q / k' := by
    rw [div_le_div_iff₀ (by positivity) hk']
    nlinarith
  calc _ ≤ X + Yv ^ 2 / (n * k') := min_split hX0 hY0 hXY (by positivity)
    _ ≤ X + Q / k' := by linarith
    _ ≤ _ := hlow

end Integrals

end LongTails.Proofs.GeneralCovarianceReverseFisherDescent
