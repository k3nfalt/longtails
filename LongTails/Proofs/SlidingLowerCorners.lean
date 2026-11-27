import LongTails.Proofs.SlidingLowerFailure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerCorners

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingLowerHiding SlidingLowerSim SlidingLowerExposure SlidingLowerFailure QuasarCoinLaw
open SlidingLowerAdmissible

variable {T : ℕ}

lemma coinReveal_zero (b : Bool) : coinReveal 0 b = 0 := by simp [coinReveal]

lemma coinReveal_one_true : coinReveal 1 true = 1 := by simp [coinReveal]

def hCorner (T : ℕ) : Corner T where
  lev e := min (2 * e + 1) (2 * T + 1)
  rv := coinReveal
  mono := fun a b h => by
    change min (2 * a + 1) (2 * T + 1) ≤ min (2 * b + 1) (2 * T + 1)
    omega
  le := fun e => min_le_right _ _
  fpos := fun e b => by
    rw [coinReveal_zero, add_zero]
    omega
  fodd := fun e b _ h1 => by
    change min (2 * e + 1) (2 * T + 1) < 2 * T + 1 at h1
    omega
  hcoin := fun e b h h1 _ => by
    cases b
    · rfl
    · exfalso
      rw [coinReveal_one_true] at h
      change min (2 * (e + 1) + 1) (2 * T + 1) = min (2 * e + 1) (2 * T + 1) at h
      change min (2 * e + 1) (2 * T + 1) < 2 * T + 1 at h1
      omega

def fCorner (T : ℕ) : Corner T where
  lev e := min (2 * e) (2 * T + 1)
  rv i _ := if i = 0 then 1 else 0
  mono := fun a b h => by
    change min (2 * a) (2 * T + 1) ≤ min (2 * b) (2 * T + 1)
    omega
  le := fun e => min_le_right _ _
  fpos := fun e b => by
    rw [ite_eq_left rfl]
    omega
  fodd := fun e b h h1 => by
    rw [ite_eq_left rfl] at h
    change min (2 * (e + 1)) (2 * T + 1) = min (2 * e) (2 * T + 1) at h
    change min (2 * e) (2 * T + 1) < 2 * T + 1 at h1
    omega
  hcoin := fun e b _ h1 h2 => by
    change min (2 * e) (2 * T + 1) < 2 * T + 1 at h1
    change min (2 * e) (2 * T + 1) % 2 = 1 at h2
    omega

lemma h_excess (q : Params) (Q : Scale) (hV : Valid q T Q) (hT : 0 < T) (A : Alg q)
    (b : Fin 2 → ℕ) (hb : 4 * Q.p * b 1 ≤ T) (seed : A.Seed) (π : Fin (2 * T + 1) ↪ Fin q.d) :
    ∫ β, excess (hCorner T) Q q A b seed π β
      ∂(coinPath Q.p hV.p_pos.le hV.p_le : Measure (ℕ → Bool)) ≤ 1 / 4 := by
  have hE := exposure_integral_le hV.p_pos.le hV.p_le (toRun A seed)
    (partialReply (hCorner T) Q q.x0) π b (∑ i, b i)
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hpt : ∀ β, excess (hCorner T) Q q A b seed π β ≤
      ((simSeq (toRun A seed) coinReveal (partialReply (hCorner T) Q q.x0) π β b
        (∑ i, b i)).exposure : ℝ) / T := by
    intro β
    unfold excess
    split_ifs with h
    · positivity
    · rw [le_div_iff₀ hTr, one_mul]
      have : T ≤ (simSeq (toRun A seed) coinReveal (partialReply (hCorner T) Q q.x0) π β b
          (∑ i, b i)).exposure := by
        change ¬ min (2 * (simSeq (toRun A seed) coinReveal (partialReply (hCorner T) Q q.x0) π β b
          (∑ i, b i)).exposure + 1) (2 * T + 1) ≤ 2 * T at h
        omega
      exact_mod_cast this
  have hi : Integrable (excess (hCorner T) Q q A b seed π)
      (coinPath Q.p hV.p_pos.le hV.p_le : Measure (ℕ → Bool)) := by
    apply Integrable.of_bound (excess_measurable _ Q q A b seed π).aestronglyMeasurable 1
    filter_upwards [] with β
    have := excess_bounds (hCorner T) Q q A b seed π β
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  have hm := integral_mono hi (hE.1.div_const (T : ℝ)) hpt
  rw [integral_div] at hm
  have h2 : Q.p * (b 1 : ℝ) / T ≤ 1 / 4 := by
    rw [div_le_iff₀ hTr]; linarith
  have h3 : (∫ β, ((simSeq (toRun A seed) coinReveal (partialReply (hCorner T) Q q.x0) π β b
      (∑ i, b i)).exposure : ℝ) ∂(coinPath Q.p hV.p_pos.le hV.p_le : Measure (ℕ → Bool))) / T ≤
      Q.p * (b 1 : ℝ) / T := div_le_div_of_nonneg_right hE.2 hTr.le
  exact hm.trans (h3.trans h2)

lemma f_exposure_le {q : Params} (A : Alg q) (seed : A.Seed) (Q : Scale) (b : Fin 2 → ℕ)
    (π : Fin (2 * T + 1) ↪ Fin q.d) (β : ℕ → Bool) (N : ℕ) :
    (simSeq (toRun A seed) (fCorner T).rv (partialReply (fCorner T) Q q.x0) π β b N).exposure ≤
      b 0 := by
  have he := exposure_eq (toRun A seed) (fCorner T).rv (partialReply (fCorner T) Q q.x0) π β b N
  have hs := active_sum_le (toRun A seed) (fCorner T).rv (partialReply (fCorner T) Q q.x0) π β b 0 N
  have hr : (∑ t ∈ Finset.range N, ∑ i : Fin 2,
      active (toRun A seed) (fCorner T).rv (partialReply (fCorner T) Q q.x0) π β b i t *
        ((fCorner T).rv i (β t) : ℝ)) =
      ∑ t ∈ Finset.range N,
        active (toRun A seed) (fCorner T).rv (partialReply (fCorner T) Q q.x0) π β b 0 t := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Fin.sum_univ_two]
    simp [fCorner]
  rw [hr] at he
  have : ((simSeq (toRun A seed) (fCorner T).rv (partialReply (fCorner T) Q q.x0) π β b N).exposure
      : ℝ) ≤ b 0 := by linarith
  exact_mod_cast this

lemma f_excess (q : Params) (Q : Scale) (hV : Valid q T Q) (A : Alg q)
    (b : Fin 2 → ℕ) (hb : b 0 ≤ T) (seed : A.Seed) (π : Fin (2 * T + 1) ↪ Fin q.d) :
    ∫ β, excess (fCorner T) Q q A b seed π β
      ∂(coinPath Q.p hV.p_pos.le hV.p_le : Measure (ℕ → Bool)) ≤ 1 / 4 := by
  have hz : ∀ β, excess (fCorner T) Q q A b seed π β = 0 := by
    intro β
    unfold excess
    rw [ite_eq_left]
    have := f_exposure_le A seed Q b π β (∑ i, b i)
    change min (2 * _) (2 * T + 1) ≤ 2 * T
    omega
  simp only [hz, integral_zero]
  norm_num

end LongTails.Proofs.SlidingLowerCorners
