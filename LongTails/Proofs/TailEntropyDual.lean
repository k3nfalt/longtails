import LongTails.Proofs.TailEntropyCurvature
import LongTails.Proofs.GeneralizedSmoothHardDual
import LongTails.Proofs.CompactConjugate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set Finset
open scoped BigOperators Topology

namespace LongTails.Proofs.TailEntropyDual

open TailEntropyCurvature
open GeneralizedSmoothHardDual (radial radial_derivative radial_nonneg feasible)

noncomputable def ext {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (k : ℕ) : ℝ :=
  if h : k < m then z ⟨k, h⟩ else 0

lemma ext_fin {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) : ext z i = z i := by
  simp [ext, i.isLt]

lemma sum_fin_eq {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (g : ℝ → ℝ) :
    ∑ i, g (z i) = ∑ k ∈ range m, g (ext z k) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => g (ext z k)) m]
  simp only [ext_fin]

lemma sum_eq_tail {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) : ∑ i, z i = tail (ext z) m 0 := by
  have h := sum_fin_eq z id
  simp only [id] at h
  rw [h, tail, Finset.range_eq_Ico]

lemma norm_sq_eq {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) :
    ‖z‖ ^ 2 = ∑ k ∈ range m, ext z k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact sum_fin_eq z (fun x => x ^ 2)

lemma ext_nonneg {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) (k : ℕ) :
    0 ≤ ext z k := by
  unfold ext
  split_ifs
  · exact hz _
  · rfl

lemma ext_le_norm {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (k : ℕ) : ext z k ≤ ‖z‖ := by
  unfold ext
  split_ifs with h
  · exact (le_abs_self _).trans (PiLp.norm_apply_le z ⟨k, h⟩)
  · exact norm_nonneg z

lemma ext_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    ext (x + y) k = ext x k + ext y k := by
  unfold ext; split_ifs <;> simp

lemma ext_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    ext (c • x) k = c * ext x k := by
  unfold ext; split_ifs <;> simp

lemma ext_sub {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    ext (x - y) k = ext x k - ext y k := by
  unfold ext; split_ifs <;> simp

lemma continuous_ext {m : ℕ} (k : ℕ) : Continuous (fun z : EuclideanSpace ℝ (Fin m) => ext z k) := by
  unfold ext
  split_ifs with h
  · exact PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) (⟨k, h⟩ : Fin m)
  · exact continuous_const

lemma continuous_tail {m : ℕ} (k : ℕ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin m) => tail (ext z) m k) := by
  unfold tail
  exact continuous_finsetSum _ (fun i _ => continuous_ext i)

noncomputable def entropyTerm (x T : ℝ) : ℝ := x * Real.log (x / T)

lemma entropyTerm_eq (x T : ℝ) (hx : 0 ≤ x) (hxT : x ≤ T) :
    entropyTerm x T = x * Real.log x - x * Real.log T := by
  unfold entropyTerm
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' (by linarith : T ≠ 0)]
    ring

lemma entropyTerm_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => entropyTerm p.1 p.2) {p | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  have heq : EqOn (fun p : ℝ × ℝ => entropyTerm p.1 p.2)
      (fun p => p.1 * Real.log p.1 - p.1 * Real.log p.2) {p | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    fun p hp => entropyTerm_eq p.1 p.2 hp.1 hp.2
  refine ContinuousOn.congr ?_ heq
  apply ContinuousOn.sub (Real.continuous_mul_log.comp continuous_fst).continuousOn
  intro p hp
  rcases hp.1.lt_or_eq with h1 | h1
  · have hT : p.2 ≠ 0 := by linarith [hp.2]
    exact ((continuous_fst.continuousAt).mul
      ((Real.continuousAt_log hT).comp continuous_snd.continuousAt)).continuousWithinAt
  · rcases (hp.1.trans hp.2).lt_or_eq with h2 | h2
    · exact ((continuous_fst.continuousAt).mul
        ((Real.continuousAt_log h2.ne').comp continuous_snd.continuousAt)).continuousWithinAt
    · have hp0 : p = (0, 0) := Prod.ext h1.symm h2.symm
      subst hp0
      simp only [ContinuousWithinAt, Real.log_zero, mul_zero]
      have hlim : Tendsto (fun q : ℝ × ℝ => q.2 * Real.log q.2) (𝓝[{p | 0 ≤ p.1 ∧ p.1 ≤ p.2}] (0, 0))
          (𝓝 0) := by
        have hc := (Real.continuous_mul_log.comp continuous_snd).tendsto ((0 : ℝ), (0 : ℝ))
        simp only [Function.comp, Real.log_zero, mul_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      apply squeeze_zero_norm' _ (by simpa using hlim.norm)
      filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq.1, abs_of_nonneg (hq.1.trans hq.2)]
      exact mul_le_mul_of_nonneg_right hq.2 (abs_nonneg _)

noncomputable def tailEntropy {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ k ∈ range m, entropyTerm (ext z k) (tail (ext z) m k)

lemma tailEntropy_continuousOn {m : ℕ} :
    ContinuousOn (tailEntropy (m := m)) {z | ∀ i, 0 ≤ z i} := by
  unfold tailEntropy
  apply continuousOn_finsetSum
  intro k hk
  have hmaps : MapsTo (fun z : EuclideanSpace ℝ (Fin m) => (ext z k, tail (ext z) m k))
      {z | ∀ i, 0 ≤ z i} {p | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
    intro z hz
    exact ⟨ext_nonneg z hz k, tail_le (ext z) (Finset.mem_range.mp hk)
      (fun i _ => ext_nonneg z hz i)⟩
  exact entropyTerm_continuousOn.comp
    ((continuous_ext k).prodMk (continuous_tail k)).continuousOn hmaps

lemma tailEntropy_lower {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) :
    -(Real.log m * ∑ i, z i) ≤ tailEntropy z := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [tailEntropy]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnn (i : ℕ) : 0 ≤ ext z i := ext_nonneg z hz i
  have hZ : ∀ k, tail (ext z) m k ≤ tail (ext z) m 0 := by
    intro k
    unfold tail
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro i _ _; exact hnn i
  have hterm (k : ℕ) (hk : k < m) :
      -(Real.log m * ext z k) - (tail (ext z) m k / m - ext z k) ≤
        entropyTerm (ext z k) (tail (ext z) m k) := by
    have hT := tail_le (ext z) hk (fun i _ => hnn i)
    rcases (hnn k).eq_or_lt with h0 | hpos
    · rw [← h0]
      have : 0 ≤ tail (ext z) m k := tail_nonneg (ext z) m k (fun i _ => hnn i)
      simp [entropyTerm]
      positivity
    · have hTpos : 0 < tail (ext z) m k := lt_of_lt_of_le hpos hT
      have hl := Real.log_le_sub_one_of_pos
        (show 0 < tail (ext z) m k / (m * ext z k) by positivity)
      have hsplit : Real.log (tail (ext z) m k / ext z k) =
          Real.log m + Real.log (tail (ext z) m k / (m * ext z k)) := by
        rw [← Real.log_mul hmR.ne' (by positivity)]
        congr 1
        field_simp
      unfold entropyTerm
      have hinv : Real.log (ext z k / tail (ext z) m k) =
          -Real.log (tail (ext z) m k / ext z k) := by
        rw [← Real.log_inv, inv_div]
      rw [hinv, hsplit]
      have hmul := mul_le_mul_of_nonneg_left hl hpos.le
      have he : ext z k * (tail (ext z) m k / (m * ext z k) - 1) =
          tail (ext z) m k / m - ext z k := by
        field_simp
      nlinarith
  have hsum := Finset.sum_le_sum (fun k hk => hterm k (Finset.mem_range.mp hk))
  have hT : ∑ k ∈ range m, tail (ext z) m k ≤ m * tail (ext z) m 0 := by
    calc ∑ k ∈ range m, tail (ext z) m k ≤ ∑ _k ∈ range m, tail (ext z) m 0 :=
          Finset.sum_le_sum (fun k _ => hZ k)
      _ = m * tail (ext z) m 0 := by simp
  have hZe : tail (ext z) m 0 = ∑ k ∈ range m, ext z k := by
    rw [tail, Finset.range_eq_Ico]
  unfold tailEntropy
  rw [sum_eq_tail]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
    at hsum
  rw [← hZe] at hsum
  have h1 : (∑ k ∈ range m, tail (ext z) m k) / m ≤ tail (ext z) m 0 := by
    rw [div_le_iff₀ hmR]; linarith
  linarith

noncomputable def dual {m : ℕ} (L₀ L₁ : ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  2 * radial L₀ L₁ (∑ i, z i) + 28 / L₁ * (tailEntropy z + Real.log m * ∑ i, z i)

lemma dual_zero {m : ℕ} (L₀ L₁ : ℝ) : dual L₀ L₁ (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
  have h : tailEntropy (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
    simp [tailEntropy, ext, entropyTerm]
  simp [dual, h, radial]

lemma dual_nonneg {m : ℕ} (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) : 0 ≤ dual L₀ L₁ z := by
  have hZ : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
  have hr := radial_nonneg L₀ L₁ _ hL₀ hL₁ hZ
  have he := tailEntropy_lower z hz
  have : 0 ≤ tailEntropy z + Real.log m * ∑ i, z i := by linarith
  unfold dual
  positivity

lemma dual_continuousOn_nonnegative {m : ℕ} (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) :
    ContinuousOn (dual (m := m) L₀ L₁) {z | ∀ i, 0 ≤ z i} := by
  have hsum : Continuous (fun z : EuclideanSpace ℝ (Fin m) => ∑ i, z i) :=
    continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)
  have hrad : ContinuousOn (fun z : EuclideanSpace ℝ (Fin m) => radial L₀ L₁ (∑ i, z i))
      {z | ∀ i, 0 ≤ z i} := by
    intro z hz
    have hZ : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
    exact ((radial_derivative L₀ L₁ _ hL₀ hL₁ hZ).continuousAt.comp
      (f := fun z : EuclideanSpace ℝ (Fin m) => ∑ i, z i) hsum.continuousAt).continuousWithinAt
  unfold dual
  exact (continuousOn_const.mul hrad).add (continuousOn_const.mul
    (tailEntropy_continuousOn.add (continuousOn_const.mul hsum.continuousOn)))

lemma dual_continuousOn_feasible {m : ℕ} (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
    (G : Fin m → ℝ) : ContinuousOn (dual (m := m) L₀ L₁) (feasible G) :=
  (dual_continuousOn_nonnegative L₀ L₁ hL₀ hL₁).mono (fun _ hz => hz.1)

end LongTails.Proofs.TailEntropyDual
