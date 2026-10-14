import LongTails.Algorithms.DriftCorrectedGD
import LongTails.Proofs.ZerothOrderEstimator
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.GdPL

open scoped RealInnerProductSpace

namespace OracleTemplate.AffineDriftPL

open LongTails.Setups.AffineDriftPL

open ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex hiding Params spec

lemma driftQuery_zero {d : ℕ} (h : ℝ) (x : Point d) : driftQuery h x 0 = x := by
  simp [driftQuery]

lemma driftQuery_last {d : ℕ} (h : ℝ) (x : Point d) :
    driftQuery h x ⟨d + 1, by omega⟩ = x := by simp [driftQuery]

lemma driftQuery_sample {d : ℕ} (h : ℝ) (x : Point d) (i : Fin d) :
    driftQuery h x ⟨i.val + 1, by omega⟩ = x + h • direction i := by
  have hi : ¬(i.val + 1 = 0 ∨ i.val + 1 = d + 1) := by omega
  rw [driftQuery, dite_eq_right hi]
  simp only [Nat.add_sub_cancel]


lemma driftDecode_apply {d : ℕ} (h : ℝ) (r : Fin (d + 2) → ℝ) (i : Fin d) :
    driftDecode h r i = (r ⟨i.val + 1, by omega⟩ -
      ((1 - ((i.val : ℝ) + 1) / ((d : ℝ) + 1)) * r 0 +
        (((i.val : ℝ) + 1) / ((d : ℝ) + 1)) * r ⟨d + 1, by omega⟩)) / h := by
  simp [driftDecode, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma forward_error {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hh : 0 < h) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : Point d) (i : Fin d) :
    |difference h x f i - gradient f x i| ≤ L * h / 2 := by
  have hu := Gradient.smooth_upper_bound hg hlip x (x + h • direction i)
  have hneg : ∀ x, HasGradientAt (fun y => -f y) (-gradient f x) x := by
    intro x
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hg x).hasFDerivAt.neg using 1; simp
  have hneglip : ∀ x y, ‖-gradient f x - -gradient f y‖ ≤ L * ‖x - y‖ := by
    intro x y
    rw [neg_sub_neg, norm_sub_rev]
    exact hlip x y
  have hl := Gradient.smooth_upper_bound hneg hneglip x (x + h • direction i)
  have he : x + h • direction i - x = h • direction i := by module
  rw [he, inner_smul_right, norm_smul, direction_norm, Real.norm_eq_abs, abs_of_pos hh, mul_one] at hu hl
  have hi : ⟪gradient f x, direction i⟫ = gradient f x i := EuclideanSpace.inner_basisFun_real _ _ _
  simp only [inner_neg_left, hi] at hu hl
  rw [difference_apply, abs_le]
  constructor
  · have hh' := (le_div_iff₀ hh).mpr (show (-(L * h / 2) + gradient f x i) * h ≤
        f (x + h • direction i) - f x by nlinarith only [hl])
    linarith only [hh']
  · have hh' := (div_le_iff₀ hh).mpr (show f (x + h • direction i) - f x ≤
        (L * h / 2 + gradient f x i) * h by nlinarith only [hu])
    linarith only [hh']

lemma drift_bias {d : ℕ} (h ν a b : ℝ) (f : Point d → ℝ) (x : Point d)
    (e : Fin (d + 2) → ℝ) (hh : 0 < h) (he : ∀ j, |e j| ≤ ν) (i : Fin d) :
    |driftDecode h (fun j => f (driftQuery h x j) + a + b * (j.val : ℝ) + e j) i -
      difference h x f i| ≤ 2 * ν / h := by
  let t := ((i.val : ℝ) + 1) / ((d : ℝ) + 1)
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt i.isLt) 1)
  have heq : driftDecode h (fun j => f (driftQuery h x j) + a + b * (j.val : ℝ) + e j) i -
      difference h x f i = (e ⟨i.val + 1, by omega⟩ - ((1 - t) * e 0 + t * e ⟨d + 1, by omega⟩)) / h := by
    rw [driftDecode_apply, difference_apply, driftQuery_sample, driftQuery_zero, driftQuery_last]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    dsimp [t]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hh]
  apply (div_le_div_iff_of_pos_right hh).mpr
  have hmix : |(1 - t) * e 0 + t * e ⟨d + 1, by omega⟩| ≤ ν := by
    calc
      _ ≤ |(1 - t) * e 0| + |t * e ⟨d + 1, by omega⟩| := abs_add_le _ _
      _ = (1 - t) * |e 0| + t * |e ⟨d + 1, by omega⟩| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht]
      _ ≤ (1 - t) * ν + t * ν := add_le_add
        (mul_le_mul_of_nonneg_left (he 0) (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left (he _) ht)
      _ = ν := by ring
  have ha := abs_add_le (e ⟨i.val + 1, by omega⟩) (-((1 - t) * e 0 + t * e ⟨d + 1, by omega⟩))
  simp only [abs_neg, ← sub_eq_add_neg] at ha
  linarith [he ⟨i.val + 1, by omega⟩]

lemma estimator_error {d : ℕ} (L h ν a b : ℝ) (f : Point d → ℝ) (x : Point d)
    (e : Fin (d + 2) → ℝ) (hh : 0 < h) (he : ∀ j, |e j| ≤ ν)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ‖driftDecode h (fun j => f (driftQuery h x j) + a + b * (j.val : ℝ) + e j) - gradient f x‖ ^ 2 ≤
      (d : ℝ) * (L * h / 2 + 2 * ν / h) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin d, (L * h / 2 + 2 * ν / h) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hb := drift_bias h ν a b f x e hh he i
      have hf := forward_error hh hg hlip x i
      have ha : |driftDecode h (fun j => f (driftQuery h x j) + a + b * (j.val : ℝ) + e j) i -
          gradient f x i| ≤ L * h / 2 + 2 * ν / h := by
        have := abs_add_le
          (driftDecode h (fun j => f (driftQuery h x j) + a + b * (j.val : ℝ) + e j) i - difference h x f i)
          (difference h x f i - gradient f x i)
        rw [sub_add_sub_cancel] at this
        linarith
      have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
      simpa only [sq_abs, PiLp.sub_apply] using hs
    _ = _ := by simp

lemma inexact_step {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x v : E) :
    f (x - (1 / L) • v) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) + ‖v - gradient f x‖ ^ 2 / (2 * L) := by
  have hd := Gradient.smooth_upper_bound hg hlip x (x - (1 / L) • v)
  rw [show x - (1 / L) • v - x = -(1 / L) • v by module] at hd
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (one_div_pos.mpr hL), mul_pow] at hd
  rw [norm_sub_sq_real, ← real_inner_comm v (gradient f x)]
  convert hd using 1; field_simp; ring

lemma tuned_error (p : Params) (hp : spec.valid p) (f : Point p.d → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (a b : ℝ) (x : Point p.d) (e : Fin (p.d + 2) → ℝ) (he : ∀ j, |e j| ≤ p.ν) :
    let h := Real.sqrt (p.μ * p.ε / (p.d : ℝ)) / p.L
    ‖driftDecode h (fun j => f (driftQuery h x j) + a + b * (j.val : ℝ) + e j) - gradient f x‖ ^ 2 ≤ p.μ * p.ε := by
  rcases hp with ⟨hd, hμ, hμL, hΔ, hν, hε, hn⟩
  have hL : 0 < p.L := hμ.trans_le hμL
  have hdr : (0 : ℝ) < p.d := by exact_mod_cast hd
  let h := Real.sqrt (p.μ * p.ε / (p.d : ℝ)) / p.L
  have hh : 0 < h := div_pos (Real.sqrt_pos.mpr (by positivity)) hL
  have hs : (p.d : ℝ) * p.L ^ 2 * h ^ 2 = p.μ * p.ε := by
    dsimp [h]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hn' : 4 * p.ν ≤ p.L * h ^ 2 := by
    have hcancel : (p.d : ℝ) * p.L * (4 * p.ν) ≤ (p.d : ℝ) * p.L * (p.L * h ^ 2) := by
      nlinarith only [hn, hs]
    exact (mul_le_mul_iff_right₀ (mul_pos hdr hL)).mp hcancel
  have hnoise : 2 * p.ν / h ≤ p.L * h / 2 := (div_le_iff₀ hh).mpr (by nlinarith only [hn'])
  have hcoef : (p.L * h / 2 + 2 * p.ν / h) ^ 2 ≤ (p.L * h) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hh' := mul_le_mul_of_nonneg_left hcoef hdr.le
  have hb := estimator_error p.L h p.ν a b f x e hh he hg hlip
  dsimp only
  calc
    _ ≤ (p.d : ℝ) * (p.L * h / 2 + 2 * p.ν / h) ^ 2 := hb
    _ ≤ (p.d : ℝ) * (p.L * h) ^ 2 := hh'
    _ = p.μ * p.ε := by nlinarith only [hs]

open StochasticGradient HeavyTailedMarkovGradient in
lemma inexact_rate {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (v : ℕ → E → E) (L μ Δ ε : ℝ) (x0 u : E)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hε : 0 < ε) (hgap : f x0 - f u ≤ Δ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2)
    (hv : ∀ k x, ‖v k x - gradient f x‖ ^ 2 ≤ μ * ε) (K : ℕ) :
    f (advance (fun k x => x - (1 / L) • v k x) K 0 x0) - f u ≤
      (1 - μ / L) ^ K * Δ + ε / 2 := by
  have hL : 0 < L := hμ.trans_le hμL
  have hq : 0 ≤ 1 - μ / L := sub_nonneg.mpr ((div_le_one hL).mpr hμL)
  let step := fun k x => x - (1 / L) • v k x
  change f (advance step K 0 x0) - f u ≤ _
  induction K with
  | zero => simp only [advance, pow_zero, one_mul]; linarith
  | succ K ih =>
    rw [advance_add, Nat.zero_add]
    let x := advance step K 0 x0
    have hd := inexact_step f L hL hg hlip x (v K x)
    have h1 := (div_le_div_iff_of_pos_right (show 0 < 2 * L by positivity)).mpr (hpl x)
    have h2 := (div_le_div_iff_of_pos_right (show 0 < 2 * L by positivity)).mpr (hv K x)
    have h3 := mul_le_mul_of_nonneg_left ih hq
    have he1 : 2 * μ * (f x - f u) / (2 * L) = (μ / L) * (f x - f u) := by ring
    have he2 : μ * ε / (2 * L) = (μ / L) * (ε / 2) := by ring
    rw [he1] at h1
    rw [he2] at h2
    rw [pow_succ]
    change f (x - (1 / L) • v K x) - f u ≤ _
    change (1 - μ / L) * (f x - f u) ≤ _ at h3
    nlinarith only [hd, h1, h2, h3]

open StochasticGradient HeavyTailedMarkovGradient in
lemma execute_accuracy (p : Params) (f : Point p.d → ℝ) (O : Oracle (Point p.d) ℝ)
    (hp : spec.valid p) (ho : spec.admissible p f O)
    (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hiterations : ⌈(p.L / p.μ) * Real.log (1 + p.Δ / (p.ε / 2))⌉₊ ≤ K) :
    let output := execute O (driftCorrectedGD p.toPublic) (fun _ => (K * (p.d + 2))) () ξ
    ∃ u, IsMinOn f Set.univ u ∧ f output - f u ≤ p.ε := by
  have hvalid := hp
  obtain ⟨hd, hμ, hμL, hΔ, hν, hε, hn⟩ := hp
  rcases ho with ⟨hg, hlip, ⟨a, b, e, herr, hans⟩, u, hmin, hgap, hpl⟩
  let h := Real.sqrt (p.μ * p.ε / (p.d : ℝ)) / p.L
  let n := p.d + 2
  let g := fun (x : Point p.d) (k : ℕ) => f x + a (k / n) + b (k / n) * (k % n : ℕ) + e k x
  let v := fun k x => driftDecode h (fun i : Fin n => g (driftQuery h x i) (k * n + i.val))
  have hv : ∀ k x, ‖v k x - gradient f x‖ ^ 2 ≤ p.μ * p.ε := by
    intro k x
    have heq : (fun i : Fin n => g (driftQuery h x i) (k * n + i.val)) =
        (fun i : Fin n => f (driftQuery h x i) + a k + b k * (i.val : ℝ) + e (k * n + i.val) (driftQuery h x i)) := by
      funext i
      dsimp [g]
      have hnpos : 0 < n := by dsimp [n]; omega
      have hi : (k * n + i.val) / n = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnpos, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
      simp [hi, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    dsimp [v]
    rw [heq]
    exact tuned_error p hvalid f hg hlip (a k) (b k) x
      (fun i => e (k * n + i.val) (driftQuery h x i)) (fun i => herr _ _)
  have hr := inexact_rate f v p.L p.μ p.Δ p.ε p.x0 u hμ hμL hε hgap hg hlip hpl hv K
  have hb := PLGradient.geometric_budget p.L p.μ p.Δ (p.ε / 2) hμ hμL hΔ (by positivity) K hiterations
  change (1 - p.μ / p.L) ^ K * p.Δ ≤ p.ε / 2 at hb
  have hacc : f (advance (fun k x => x - (1 / p.L) • v k x) K 0 p.x0) - f u ≤ p.ε := by
    linarith only [hr, hb]
  dsimp only
  unfold driftCorrectedGD
  erw [execute_advance]
  simp only [batched]
  simp only [hans]
  have he := advance_batched (show 0 < n by dsimp [n]; omega) (Gradient.gd (p.L, p.x0))
    (driftQuery h) (fun _ => driftDecode h) 0 g (fun k => k) K 0 p.x0
  simp only [Nat.zero_mul] at he
  erw [he]
  exact ⟨u, hmin, hacc⟩

end OracleTemplate.AffineDriftPL
