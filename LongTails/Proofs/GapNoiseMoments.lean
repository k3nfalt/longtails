import LongTails.Proofs.HeavyTailedClipping
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.GapNoiseMoments

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma clipped_variance_bias {g : Ω → E} {u : E} {T V : ℝ}
    (hg : Measurable g) (hi : Integrable g P) (hmean : (∫ ω, g ω ∂P) = u)
    (hT : 0 < T) (hV : 0 ≤ V) (hu : ‖u‖ ≤ T / 2)
    (hvi : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hv : (∫ ω, ‖g ω - u‖ ^ 2 ∂P) ≤ V) :
    ‖(∫ ω, OracleTemplate.clip T (g ω) ∂P) - u‖ ≤ 2 * V / T ∧
      (∫ ω, ‖OracleTemplate.clip T (g ω) - u‖ ^ 2 ∂P) ≤ V := by
  have hri : Integrable (fun ω => ‖g ω - u‖ ^ (2 : ℝ)) P := by
    simpa only [Real.rpow_two] using hvi
  have hrv : (∫ ω, ‖g ω - u‖ ^ (2 : ℝ) ∂P) ≤ Real.sqrt V ^ (2 : ℝ) := by
    simpa only [Real.rpow_two, Real.sq_sqrt hV] using hv
  have hb := OracleTemplate.clipped_bias_bound hg hi hmean hT (by norm_num : (1 : ℝ) ≤ 2)
    hu hri hrv
  have hs := OracleTemplate.clipped_second_moment_bound hg hT.le (by norm_num : (0 : ℝ) ≤ 2)
    (le_refl (2 : ℝ)) (by linarith : ‖u‖ ≤ T) hri hrv
  norm_num only [Real.rpow_two, Real.sq_sqrt hV, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one] at hb
  norm_num only [Real.rpow_two, Real.sq_sqrt hV, sub_self, Real.rpow_zero, one_mul] at hs
  constructor
  · convert hb using 1
    ring
  · exact hs

omit [CompleteSpace E] in
lemma clipped_energy_noise {g : Ω → E} {u z : E} {T V η D : ℝ}
    (hg : Measurable g) (hi : Integrable g P) (hmean : (∫ ω, g ω ∂P) = u)
    (hT : 0 < T) (hV : 0 ≤ V) (hu : ‖u‖ ≤ T / 2)
    (hη : 0 ≤ η) (hz : ‖z‖ ≤ D)
    (hvi : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hv : (∫ ω, ‖g ω - u‖ ^ 2 ∂P) ≤ V) :
    -2 * η * ⟪(∫ ω, OracleTemplate.clip T (g ω) ∂P) - u, z⟫ +
      30 * η ^ 2 * (∫ ω, ‖OracleTemplate.clip T (g ω) - u‖ ^ 2 ∂P) ≤
      30 * η ^ 2 * V + 4 * η * D * V / T := by
  obtain ⟨hb, hs⟩ := clipped_variance_bias hg hi hmean hT hV hu hvi hv
  have hm := real_inner_le_norm (-((∫ ω, OracleTemplate.clip T (g ω) ∂P) - u)) z
  rw [inner_neg_left, norm_neg] at hm
  have hn := mul_le_mul hb hz (norm_nonneg _) (by positivity : 0 ≤ 2 * V / T)
  have hi' := mul_le_mul_of_nonneg_left (hm.trans hn) (by positivity : 0 ≤ 2 * η)
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 30 * η ^ 2)
  have he : 2 * η * (2 * V / T * D) = 4 * η * D * V / T := by ring
  rw [he] at hi'
  linarith

omit [IsProbabilityMeasure P] in
lemma nonnegative_energy_event {energy : Ω → ℝ} {bad : Set Ω} {threshold budget : ℝ}
    (hi : Integrable energy P) (hn : ∀ ω, 0 ≤ energy ω) (ht : 0 < threshold)
    (he : ∀ ω ∈ bad, threshold ≤ energy ω) (hb : (∫ ω, energy ω ∂P) ≤ budget) :
    P bad ≤ ENNReal.ofReal (budget / threshold) := by
  have hm := (hi.div_const threshold).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (hn ω) ht.le))
    (s := bad) (by intro ω hω; exact (one_le_div ht).mpr (he ω hω))
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  exact div_le_div_of_nonneg_right hb ht.le

omit [IsProbabilityMeasure P] in
lemma integral_drift_sum (energy loss : ℕ → Ω → ℝ) {N : ℕ} {κ β : ℝ}
    (hκ : 0 ≤ κ) (he : ∀ n ω, 0 ≤ energy n ω) (hl : ∀ n ω, 0 ≤ loss n ω)
    (hstep : ∀ n < N, (∫ ω, energy (n + 1) ω ∂P) + κ * (∫ ω, loss n ω ∂P) ≤
      (∫ ω, energy n ω ∂P) + β) :
    (∫ ω, energy N ω ∂P) ≤ (∫ ω, energy 0 ω ∂P) + N * β ∧
      κ * ∑ n ∈ Finset.range N, (∫ ω, loss n ω ∂P) ≤
        (∫ ω, energy 0 ω ∂P) + N * β := by
  have hs : ∀ k ≤ N, (∫ ω, energy k ω ∂P) +
      κ * ∑ n ∈ Finset.range k, (∫ ω, loss n ω ∂P) ≤
        (∫ ω, energy 0 ω ∂P) + k * β := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := ih (by omega)
      have ht := hstep k (by omega)
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      linarith
  have h := hs N le_rfl
  have hn : 0 ≤ ∑ n ∈ Finset.range N, (∫ ω, loss n ω ∂P) := by
    apply Finset.sum_nonneg
    intro n _
    exact integral_nonneg (hl n)
  constructor
  · nlinarith [mul_nonneg hκ hn]
  · have henergy : 0 ≤ (∫ ω, energy N ω ∂P) := integral_nonneg (he N)
    linarith

lemma batch_gap_absorption {K η ηmax σ v gap batch t : ℝ}
    (hK : 0 ≤ K) (hη : 0 ≤ η) (hηmax : η ≤ ηmax) (hv : 0 ≤ v)
    (hgap : 0 ≤ gap) (hbatch : 0 < batch) (hsize : K * ηmax * v ≤ batch * t) :
    K * η ^ 2 * ((σ ^ 2 + v * gap) / batch) ≤
      η * t * gap + K * ηmax ^ 2 * σ ^ 2 / batch := by
  have hcoef : K * η * v ≤ batch * t := by
    have hm := mul_le_mul_of_nonneg_right hηmax (mul_nonneg hK hv)
    nlinarith
  have hgap' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hη hgap)
  have hnoise : K * η ^ 2 * σ ^ 2 ≤ K * ηmax ^ 2 * σ ^ 2 := by
    gcongr
  apply (mul_le_mul_iff_left₀ hbatch).mp
  have he : (K * η ^ 2 * ((σ ^ 2 + v * gap) / batch)) * batch =
      K * η ^ 2 * (σ ^ 2 + v * gap) := by field_simp
  rw [he]
  have hcancel : (K * ηmax ^ 2 * σ ^ 2 / batch) * batch = K * ηmax ^ 2 * σ ^ 2 :=
    div_mul_cancel₀ _ hbatch.ne'
  rw [add_mul, hcancel]
  nlinarith

lemma drift_after_gap_absorption {newEnergy oldEnergy η ηmax J floor α Q t gap κ noise : ℝ}
    (hη : 0 ≤ η) (hηmax : η ≤ ηmax) (hfloor : 0 ≤ floor) (hαQ : 0 ≤ α * Q)
    (hstep : newEnergy ≤ oldEnergy - 2 * η * J + η * t * gap + noise)
    (hstrong : α * Q + t * gap ≤ J + floor)
    (hprogress : κ * Q ≤ η * (J + floor)) :
    newEnergy + κ * Q ≤ oldEnergy + 2 * ηmax * floor + noise := by
  have h1 := mul_le_mul_of_nonneg_left hstrong hη
  have h2 := mul_le_mul_of_nonneg_right hηmax hfloor
  nlinarith [mul_nonneg hη hαQ]

lemma integrate_clipped_energy {g : Ω → E} {u z : E} {T V η D C : ℝ} {energy : Ω → ℝ}
    (hg : Measurable g) (hi : Integrable g P) (hmean : (∫ ω, g ω ∂P) = u)
    (hT : 0 < T) (hV : 0 ≤ V) (hu : ‖u‖ ≤ T / 2)
    (hη : 0 ≤ η) (hz : ‖z‖ ≤ D)
    (hvi : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hv : (∫ ω, ‖g ω - u‖ ^ 2 ∂P) ≤ V) (hei : Integrable energy P)
    (hpoint : ∀ ω, energy ω ≤ C - 2 * η * ⟪OracleTemplate.clip T (g ω) - u, z⟫ +
      30 * η ^ 2 * ‖OracleTemplate.clip T (g ω) - u‖ ^ 2) :
    (∫ ω, energy ω ∂P) ≤ C + 30 * η ^ 2 * V + 4 * η * D * V / T := by
  let e : Ω → E := fun ω => OracleTemplate.clip T (g ω) - u
  have hci := OracleTemplate.integrable_clip (P := P) hg hT.le
  have he : Integrable e P := hci.sub (integrable_const u)
  have hr : Integrable (fun ω => ‖g ω - u‖ ^ (2 : ℝ)) P := by
    simpa only [Real.rpow_two] using hvi
  have he2 : Integrable (fun ω => ‖e ω‖ ^ 2) P := by
    simpa only [Real.rpow_two] using OracleTemplate.clipped_moment_integrable hg hT.le
      (by norm_num : (0 : ℝ) ≤ 2) (by linarith : ‖u‖ ≤ T) hr
  have hem : (∫ ω, e ω ∂P) = (∫ ω, OracleTemplate.clip T (g ω) ∂P) - u := by
    dsimp [e]
    rw [integral_sub hci (integrable_const u)]
    simp
  have hin : (∫ ω, ⟪e ω, z⟫ ∂P) = ⟪(∫ ω, OracleTemplate.clip T (g ω) ∂P) - u, z⟫ := by
    calc
      _ = ∫ ω, ⟪z, e ω⟫ ∂P := integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => (real_inner_comm (e ω) z).symm))
      _ = _ := by rw [integral_inner he, hem, real_inner_comm]
  have hlin := (he.inner_const z).const_mul (2 * η)
  have hquad := he2.const_mul (30 * η ^ 2)
  have hbound := integral_mono hei (((integrable_const C).sub hlin).add hquad) hpoint
  have hsplit := integral_add ((integrable_const C).sub hlin) hquad
  have hsub := integral_sub (integrable_const C) hlin
  simp only [Pi.add_apply, Pi.sub_apply] at hbound hsplit hsub
  rw [hsplit, hsub, integral_const_mul, integral_const_mul, hin] at hbound
  simp only [integral_const, probReal_univ, one_smul] at hbound
  have hn := clipped_energy_noise hg hi hmean hT hV hu hη hz hvi hv
  dsimp [e] at hbound
  linarith

end LongTails.Proofs.GapNoiseMoments
