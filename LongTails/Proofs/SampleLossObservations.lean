import LongTails.Proofs.SampleLossHiding
import LongTails.Proofs.SampleLossEpoch

open Classical
open scoped BigOperators RealInnerProductSpace
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossEpoch LongTails.Proofs.SampleLossFrame
open LongTails.Proofs.SampleLossHiding LongTails.Proofs.SampleLossChain
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SoftRadialProjection

namespace LongTails.Proofs.SampleLossObservations

variable {n d : ℕ} {J : Type} [Fintype J]

noncomputable def threshold (n : ℕ) : ℝ := 1 / (512 * Real.sqrt (rows n))

noncomputable def observation (x : Space n (rows n) d) (j : Fin n) := project 1 (proj j x)

def bad (ξ : ℕ → Fin (rows n)) (stage : J → ℕ)
    (x : J → Table n (rows n) d → Space n (rows n) d) (π : Table n (rows n) d) : Prop :=
  ∃ a : J, ∃ l : Fin n × Fin (rows n), l ∉ exposed ξ (n^2) (stage a) ∧
    π l ∈ large (threshold n) (observation (x a π) l.1) l.2

omit [Fintype J] in
lemma good_small (ξ : ℕ → Fin (rows n)) (stage : J → ℕ)
    (x : J → Table n (rows n) d → Space n (rows n) d) (π : Table n (rows n) d)
    (hg : ¬ bad ξ stage x π) (a : J) (j : Fin n) (hj : stage a ≤ j.val) :
    signal proj (direction π) j (x a π) < 1/128 := by
  let s := if j.val = stage a then exposedRows ξ (n^2) (stage a) else ∅
  have hout (i : Fin (rows n)) (hi : i ∉ s) : π (j,i) ∉ large (threshold n) (observation (x a π) j) i := by
    intro hh
    apply hg ⟨a,(j,i),?_,hh⟩
    simp only [exposed,Finset.mem_filter,Finset.mem_univ,true_and]
    rintro (h | ⟨h,hm⟩)
    · omega
    · exact hi (by simpa [s,h] using hm)
  have hc : s.card ≤ n^2 := by
    dsimp only [s]
    split_ifs
    · exact Finset.card_image_le.trans (Finset.card_range _).le
    · simp
  have hsc : Real.sqrt s.card ≤ (n:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast hc⟩
  have hm : 0 < rows n := by unfold rows; positivity
  have hr : 0 < Real.sqrt (rows n) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have ht : 0 < threshold n := by unfold threshold; positivity
  have h := hidden_alignment π j s hm (observation (x a π) j) (norm_project_le (by norm_num) _) ht.le hout
  have hsr : Real.sqrt (rows n) = 512 * ((n:ℝ)+1) := by simp [rows,Real.sqrt_sq (by positivity : 0 ≤ 512*((n:ℝ)+1))]
  apply (le_abs_self _).trans_lt (h.trans_lt _)
  apply (div_lt_iff₀ hr).mpr
  unfold threshold
  rw [show (rows n : ℝ) * (1 / (512 * Real.sqrt (rows n))) = Real.sqrt (rows n)/512 by
    field_simp; nlinarith [Real.sq_sqrt (Nat.cast_nonneg (rows n))]]
  linarith [hsr, (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]

lemma bad_count (ξ : ℕ → Fin (rows n)) (stage : J → ℕ)
    (x : J → Table n (rows n) d → Space n (rows n) d)
    (hstable : ∀ a π ρ, (∀ l ∈ exposed ξ (n^2) (stage a), π l = ρ l) → x a π = x a ρ)
    (hc : Fintype.card J ≤ 2*n^3+1) {extra : ℕ} (hd : d = width n extra) :
    2 * (∑ π : Table n (rows n) d, if bad ξ stage x π then (1:ℝ) else 0) ≤
      Fintype.card (Table n (rows n) d) := by
  classical
  have hm : 0 < rows n := by unfold rows; positivity
  have ht : 0 < threshold n := by unfold threshold; exact div_pos zero_lt_one (mul_pos (by norm_num) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)))
  have h := observation_bound (fun a => exposed ξ (n^2) (stage a)) (fun a π => observation (x a π))
    (fun a π ρ he => by rw [hstable a π ρ he]) ht
  have h' : (d:ℝ) * (∑ π : Table n (rows n) d, if bad ξ stage x π then (1:ℝ) else 0) ≤
      (Fintype.card J:ℝ)*n*rows n*(1/threshold n^2)*Fintype.card (Table n (rows n) d) := by
    apply le_trans (le_of_eq ?_) h
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    unfold bad
    split_ifs <;> rfl
  clear h
  have ht' : 1 / threshold n ^ 2 = 262144 * (rows n:ℝ) := by
    unfold threshold
    simp only [one_div, inv_pow, inv_inv, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num
  rw [ht'] at h'
  let C : ℝ := (Fintype.card J:ℝ) * n * rows n * (262144 * (rows n:ℝ))
  change _ ≤ C * _ at h'
  have hC : 2*C ≤ (d:ℝ) := by
    rw [hd]
    unfold C width
    push_cast
    have hh : (Fintype.card J:ℝ) ≤ 2*(n:ℝ)^3+1 := by exact_mod_cast hc
    have hw := mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ)) (sq_nonneg (rows n:ℝ))
    have hpow := pow_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ)) 3
    nlinarith [mul_le_mul_of_nonneg_right hh hw, mul_nonneg (by linarith : 0 ≤ 2*(n:ℝ)^3+1) hw, (Nat.cast_nonneg extra : 0 ≤ (extra:ℝ))]
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by rw [hd]; exact Nat.zero_lt_succ _)
  apply (mul_le_mul_iff_left₀ hdpos).mp
  nlinarith [mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg (Fintype.card (Table n (rows n) d)))]

end LongTails.Proofs.SampleLossObservations
