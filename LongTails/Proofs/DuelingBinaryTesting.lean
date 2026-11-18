import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace LongTails.Proofs.DuelingBinaryTesting

noncomputable def affinity (p q : ℝ) : ℝ :=
  Real.sqrt p * Real.sqrt q + Real.sqrt (1-p) * Real.sqrt (1-q)

lemma sqrt_sum_products {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d ≤
      Real.sqrt (a+c) * Real.sqrt (b+d) := by
  have h := sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt c * Real.sqrt b)
  have hs : (Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d) ^ 2 ≤
      (Real.sqrt (a+c) * Real.sqrt (b+d)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring_nf at h ⊢
    simp only [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc, Real.sq_sqrt hd] at h ⊢
    linarith
  exact le_of_sq_le_sq hs (by positivity)

def mix (p a b : ℝ) : ℝ := p*a+(1-p)*b

lemma mix_mem {p a b : ℝ} (hp : p ∈ Set.Icc 0 1) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) : mix p a b ∈ Set.Icc 0 1 := by
  unfold mix
  constructor
  · exact add_nonneg (mul_nonneg hp.1 ha.1) (mul_nonneg (sub_nonneg.mpr hp.2) hb.1)
  · nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr ha.2),
      mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hb.2)]

lemma affinity_mix {p q a b c d : ℝ} (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    Real.sqrt p * Real.sqrt q * affinity a c +
      Real.sqrt (1-p) * Real.sqrt (1-q) * affinity b d ≤
      affinity (mix p a b) (mix q c d) := by
  have hp' := sub_nonneg.mpr hp.2
  have hq' := sub_nonneg.mpr hq.2
  have hone := sqrt_sum_products (mul_nonneg hp.1 ha.1) (mul_nonneg hq.1 hc.1)
    (mul_nonneg hp' hb.1) (mul_nonneg hq' hd.1)
  have hzero := sqrt_sum_products (mul_nonneg hp.1 (sub_nonneg.mpr ha.2))
    (mul_nonneg hq.1 (sub_nonneg.mpr hc.2)) (mul_nonneg hp' (sub_nonneg.mpr hb.2))
    (mul_nonneg hq' (sub_nonneg.mpr hd.2))
  simp only [Real.sqrt_mul hp.1, Real.sqrt_mul hq.1, Real.sqrt_mul hp',
    Real.sqrt_mul hq'] at hone hzero
  unfold affinity mix
  rw [show 1-(p*a+(1-p)*b) = p*(1-a)+(1-p)*(1-b) by ring,
      show 1-(q*c+(1-q)*d) = q*(1-c)+(1-q)*(1-d) by ring]
  linarith only [hone,hzero]

lemma sqrt_close {a b δ : ℝ} (ha : 1/4 ≤ a) (hb : 1/4 ≤ b) (hd : |a-b| ≤ δ) :
    (Real.sqrt a - Real.sqrt b)^2 ≤ δ^2 := by
  have hsa : 1/2 ≤ Real.sqrt a := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hsb : 1/2 ≤ Real.sqrt b := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hprod : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a-b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)),
      ← abs_mul, sub_mul, mul_add, mul_add]
    congr 1
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ a), Real.sq_sqrt (by linarith : 0 ≤ b)]
  have h := mul_le_mul_of_nonneg_left (show 1 ≤ Real.sqrt a + Real.sqrt b by linarith)
    (abs_nonneg (Real.sqrt a - Real.sqrt b))
  rw [mul_one, hprod] at h
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h.trans hd) 2

lemma affinity_close {p q δ : ℝ} (hp : p ∈ Set.Icc (1/4) (3/4))
    (hq : q ∈ Set.Icc (1/4) (3/4)) (hd : |p-q| ≤ δ) :
    1 - δ^2 ≤ affinity p q ∧ affinity p q ≤ 1 := by
  have hu := sqrt_close hp.1 hq.1 hd
  have he : |(1-p)-(1-q)| ≤ δ := by simpa only [sub_sub_sub_cancel_left, abs_sub_comm q p] using hd
  have hv := sqrt_close (show 1/4 ≤ 1-p by linarith [hp.2])
    (show 1/4 ≤ 1-q by linarith [hq.2]) he
  have hi : 2*(1-affinity p q) =
      (Real.sqrt p - Real.sqrt q)^2 + (Real.sqrt (1-p) - Real.sqrt (1-q))^2 := by
    unfold affinity
    nlinarith [Real.sq_sqrt (by linarith [hp.1] : 0 ≤ p),
      Real.sq_sqrt (by linarith [hq.1] : 0 ≤ q),
      Real.sq_sqrt (by linarith [hp.2] : 0 ≤ 1-p),
      Real.sq_sqrt (by linarith [hq.2] : 0 ≤ 1-q)]
  constructor
  · linarith
  · nlinarith [sq_nonneg (Real.sqrt p-Real.sqrt q), sq_nonneg (Real.sqrt (1-p)-Real.sqrt (1-q))]

def acceptance {S : Type*} (step : S → Bool → S) (prob : S → ℝ) (test : S → Bool) :
    ℕ → S → ℝ
  | 0, s => if test s then 1 else 0
  | n+1, s => mix (prob s) (acceptance step prob test n (step s true))
      (acceptance step prob test n (step s false))

lemma acceptance_mem {S : Type*} (step : S → Bool → S) (prob : S → ℝ) (test : S → Bool)
    (hp : ∀ s, prob s ∈ Set.Icc 0 1) (n : ℕ) (s : S) :
    acceptance step prob test n s ∈ Set.Icc 0 1 := by
  induction n generalizing s with
  | zero => cases h : test s <;> simp [acceptance,h]
  | succ n ih => exact mix_mem (hp _) (ih _) (ih _)

lemma acceptance_affinity {S : Type*} (step : S → Bool → S) (p q : S → ℝ) (test : S → Bool)
    (hp : ∀ s, p s ∈ Set.Icc (1/4) (3/4)) (hq : ∀ s, q s ∈ Set.Icc (1/4) (3/4))
    {δ : ℝ} (hd : ∀ s, |p s-q s| ≤ δ) (n : ℕ) (s : S) :
    1 - n * δ^2 ≤ affinity (acceptance step p test n s) (acceptance step q test n s) := by
  have hP (s : S) : p s ∈ Set.Icc 0 1 := ⟨by linarith [(hp s).1], by linarith [(hp s).2]⟩
  have hQ (s : S) : q s ∈ Set.Icc 0 1 := ⟨by linarith [(hq s).1], by linarith [(hq s).2]⟩
  induction n generalizing s with
  | zero => cases ht : test s <;> norm_num [acceptance, affinity, ht]
  | succ n ih =>
    have hm := affinity_mix (hP s) (hQ s) (acceptance_mem step p test hP n (step s true))
      (acceptance_mem step p test hP n (step s false))
      (acceptance_mem step q test hQ n (step s true)) (acceptance_mem step q test hQ n (step s false))
    apply le_trans _ hm
    have hl := affinity_close (hp s) (hq s) (hd s)
    have ht := mul_le_mul_of_nonneg_left (ih (step s true))
      (mul_nonneg (Real.sqrt_nonneg (p s)) (Real.sqrt_nonneg (q s)))
    have hf := mul_le_mul_of_nonneg_left (ih (step s false))
      (mul_nonneg (Real.sqrt_nonneg (1-p s)) (Real.sqrt_nonneg (1-q s)))
    have he := mul_le_mul_of_nonneg_left hl.2 (show (0:ℝ) ≤ n*δ^2 by positivity)
    unfold affinity at hl he
    push_cast
    nlinarith only [hl.1, he, ht, hf]

lemma sum_errors {p q : ℝ} (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (ha : 3/4 ≤ affinity p q) : 1/4 ≤ p+(1-q) := by
  have hsp := Real.sqrt_le_sqrt hp.2
  have hsq := Real.sqrt_le_sqrt hq.2
  have hspp := Real.sqrt_le_sqrt (show 1-p ≤ 1 by linarith [hp.1])
  simp only [Real.sqrt_one] at hsp hsq hspp
  have hu := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg p)
  have hv := mul_le_mul_of_nonneg_right hspp (Real.sqrt_nonneg (1-q))
  unfold affinity at ha
  have hs : 3/4 ≤ Real.sqrt p + Real.sqrt (1-q) := by linarith
  have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/4) hs 2
  nlinarith [Real.sq_sqrt hp.1, Real.sq_sqrt (sub_nonneg.mpr hq.2),
    sq_nonneg (Real.sqrt p-Real.sqrt (1-q))]

end LongTails.Proofs.DuelingBinaryTesting
