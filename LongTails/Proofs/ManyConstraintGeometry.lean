import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsProj (K : Set E) (z q : E) : Prop :=
  q ∈ K ∧ ∀ w ∈ K, ⟪z - q, w - q⟫ ≤ 0

lemma proj_sq_le {K : Set E} {z q w : E} (hq : IsProj K z q) (hw : w ∈ K) :
    ‖q - w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖z - q‖ ^ 2 := by
  have h := hq.2 w hw
  have hexp : ‖z - w‖ ^ 2 = ‖z - q‖ ^ 2 + ‖q - w‖ ^ 2 - 2 * ⟪z - q, w - q⟫ := by
    have : z - w = (z - q) + (q - w) := by abel
    rw [this, norm_add_sq_real]
    have : ⟪z - q, q - w⟫ = -⟪z - q, w - q⟫ := by
      rw [← inner_neg_right]; congr 1; abel
    rw [this]; ring
  nlinarith

lemma proj_dist_le {K C : Set E} (hC : C ⊆ K) {z q w : E} (hq : IsProj K z q) (hw : w ∈ C) :
    ‖q - w‖ ≤ ‖z - w‖ := by
  have h := proj_sq_le hq (hC hw)
  have h0 : 0 ≤ ‖z - q‖ ^ 2 := sq_nonneg _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

lemma fejer_cleanup {C : Set E} (K : ℕ → Set E) (hK : ∀ s, C ⊆ K s) (y : ℕ → E)
    (hy : ∀ s, IsProj (K s) (y s) (y (s + 1))) {w : E} (hw : w ∈ C) (n : ℕ) :
    ‖y n - w‖ ≤ ‖y 0 - w‖ ∧ ‖y n - y 0‖ ≤ 2 * ‖y 0 - w‖ := by
  have hmono : ∀ n, ‖y n - w‖ ≤ ‖y 0 - w‖ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (proj_dist_le (hK n) (hy n) hw).trans ih
  refine ⟨hmono n, ?_⟩
  calc ‖y n - y 0‖ = ‖(y n - w) - (y 0 - w)‖ := by congr 1; abel
    _ ≤ ‖y n - w‖ + ‖y 0 - w‖ := norm_sub_le _ _
    _ ≤ 2 * ‖y 0 - w‖ := by linarith [hmono n]

lemma value_lower_bound {f : E → ℝ} {g xs x w : E} {fs : ℝ}
    (hconv : f xs + ⟪g, x - xs⟫ ≤ f x) (hfs : fs = f xs)
    (hopt : 0 ≤ ⟪g, w - xs⟫) :
    fs - ‖g‖ * ‖x - w‖ ≤ f x := by
  have h1 : ⟪g, x - xs⟫ = ⟪g, x - w⟫ + ⟪g, w - xs⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have h2 : -(‖g‖ * ‖x - w‖) ≤ ⟪g, x - w⟫ := by
    have := abs_real_inner_le_norm g (x - w)
    linarith [neg_abs_le ⟪g, x - w⟫]
  rw [hfs]; linarith

lemma penalty_feasibility {G κ β ε' d fx hx fs : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hG : 0 ≤ G)
    (hε : 0 ≤ ε') (hf : fs - G * d ≤ fx) (hh : β / (2 * κ) * d ^ 2 ≤ hx)
    (hsum : fx + hx ≤ fs + ε') :
    d ≤ 2 * κ * G / β + Real.sqrt (2 * κ * ε' / β) := by
  have key : β / (2 * κ) * d ^ 2 ≤ G * d + ε' := by linarith
  have key' : d ^ 2 ≤ (2 * κ * G / β) * d + 2 * κ * ε' / β := by
    have hc : 0 < β / (2 * κ) := by positivity
    have : d ^ 2 ≤ (G * d + ε') / (β / (2 * κ)) := by
      rw [le_div_iff₀ hc]; linarith
    calc d ^ 2 ≤ (G * d + ε') / (β / (2 * κ)) := this
      _ = (2 * κ * G / β) * d + 2 * κ * ε' / β := by field_simp
  set a := 2 * κ * G / β
  set b := 2 * κ * ε' / β
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hs := Real.sqrt_nonneg b
  have hsq := Real.sq_sqrt hb
  by_contra hcon
  push Not at hcon
  have h1 : a + Real.sqrt b < d := hcon
  have : (a + Real.sqrt b) * d < d * d := by
    have : 0 < d := lt_of_le_of_lt (by positivity) h1
    nlinarith
  nlinarith

lemma proj_eq_infDist {K : Set E} {z q : E} (hq : IsProj K z q) :
    ‖z - q‖ = Metric.infDist z K := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro η hη
    obtain ⟨w, hw, hlt⟩ := (Metric.infDist_lt_iff ⟨q, hq.1⟩).mp
      (lt_add_of_pos_right (Metric.infDist z K) hη)
    have h := proj_sq_le hq hw
    have : ‖z - q‖ ≤ ‖z - w‖ := by
      have h0 : 0 ≤ ‖q - w‖ ^ 2 := sq_nonneg _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
    rw [dist_eq_norm] at hlt
    linarith
  · rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hq.1

lemma infDist_proj_sq {K C : Set E} (hC : C ⊆ K) (hne : C.Nonempty) {z q : E}
    (hq : IsProj K z q) :
    Metric.infDist q C ^ 2 ≤ Metric.infDist z C ^ 2 - Metric.infDist z K ^ 2 := by
  rw [← proj_eq_infDist hq]
  have key : ∀ η > 0, Metric.infDist q C ^ 2 ≤ (Metric.infDist z C + η) ^ 2 - ‖z - q‖ ^ 2 := by
    intro η hη
    obtain ⟨w, hw, hlt⟩ := (Metric.infDist_lt_iff hne).mp
      (lt_add_of_pos_right (Metric.infDist z C) hη)
    rw [dist_eq_norm] at hlt
    have h1 : Metric.infDist q C ≤ ‖q - w‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hw
    have h2 := proj_sq_le hq (hC hw)
    have h3 : ‖z - w‖ ^ 2 ≤ (Metric.infDist z C + η) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
    have h4 : Metric.infDist q C ^ 2 ≤ ‖q - w‖ ^ 2 :=
      pow_le_pow_left₀ Metric.infDist_nonneg h1 2
    linarith
  have hlim : Filter.Tendsto (fun η : ℝ => (Metric.infDist z C + η) ^ 2 - ‖z - q‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Metric.infDist z C + 0) ^ 2 - ‖z - q‖ ^ 2)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add continuous_id).pow 2 |>.sub continuous_const).tendsto 0
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => key η hη)

lemma avg_contraction {m : ℕ} (hm : 0 < m) (Kj : Fin m → Set E) {C : Set E}
    (hC : ∀ j, C ⊆ Kj j) (hne : C.Nonempty) {κ : ℝ} (hκ : 0 < κ) (z : E) (q : Fin m → E)
    (hq : ∀ j, IsProj (Kj j) z (q j))
    (hreg : Metric.infDist z C ^ 2 ≤ κ * ((1 / (m : ℝ)) * ∑ j, Metric.infDist z (Kj j) ^ 2)) :
    (1 / (m : ℝ)) * ∑ j, Metric.infDist (q j) C ^ 2 ≤ (1 - 1 / κ) * Metric.infDist z C ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hstep : ∀ j, Metric.infDist (q j) C ^ 2 ≤
      Metric.infDist z C ^ 2 - Metric.infDist z (Kj j) ^ 2 :=
    fun j => infDist_proj_sq (hC j) hne (hq j)
  have hsum : ∑ j, Metric.infDist (q j) C ^ 2 ≤
      ∑ j, (Metric.infDist z C ^ 2 - Metric.infDist z (Kj j) ^ 2) :=
    Finset.sum_le_sum fun j _ => hstep j
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have havg : (1 / (m : ℝ)) * ∑ j, Metric.infDist z (Kj j) ^ 2 ≥
      Metric.infDist z C ^ 2 / κ := by
    rw [ge_iff_le, div_le_iff₀ hκ]; linarith
  have : (1 / (m : ℝ)) * ∑ j, Metric.infDist (q j) C ^ 2 ≤
      Metric.infDist z C ^ 2 - (1 / (m : ℝ)) * ∑ j, Metric.infDist z (Kj j) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hmR))
    calc (1 / (m : ℝ)) * ∑ j, Metric.infDist (q j) C ^ 2
        ≤ (1 / (m : ℝ)) * ((m : ℝ) * Metric.infDist z C ^ 2 -
            ∑ j, Metric.infDist z (Kj j) ^ 2) := h
      _ = Metric.infDist z C ^ 2 - (1 / (m : ℝ)) * ∑ j, Metric.infDist z (Kj j) ^ 2 := by
          field_simp
  have hd : Metric.infDist z C ^ 2 / κ = (1 / κ) * Metric.infDist z C ^ 2 := by ring
  nlinarith

lemma cleanup_damage {f : E → ℝ} {y p gy gs : E} {L G D d : ℝ} (hL : 0 ≤ L)
    (hsmooth : f p ≤ f y + ⟪gy, p - y⟫ + L / 2 * ‖p - y‖ ^ 2)
    (hG : ‖gs‖ ≤ G) (hcoco : ‖gy - gs‖ ^ 2 ≤ 2 * L * D) (hmove : ‖p - y‖ ≤ 2 * d) :
    f p - f y ≤ 2 * G * d + 2 * d * Real.sqrt (2 * L * D) + 2 * L * d ^ 2 := by
  have hdiff : ‖gy - gs‖ ≤ Real.sqrt (2 * L * D) := by
    rw [← Real.sqrt_sq (norm_nonneg (gy - gs))]; exact Real.sqrt_le_sqrt hcoco
  have hgy : ‖gy‖ ≤ G + Real.sqrt (2 * L * D) := by
    calc ‖gy‖ = ‖gs + (gy - gs)‖ := by congr 1; abel
      _ ≤ ‖gs‖ + ‖gy - gs‖ := norm_add_le _ _
      _ ≤ G + Real.sqrt (2 * L * D) := by linarith
  have hin : ⟪gy, p - y⟫ ≤ (G + Real.sqrt (2 * L * D)) * (2 * d) := by
    calc ⟪gy, p - y⟫ ≤ ‖gy‖ * ‖p - y‖ := real_inner_le_norm _ _
      _ ≤ (G + Real.sqrt (2 * L * D)) * (2 * d) :=
          mul_le_mul hgy hmove (norm_nonneg _) (by linarith [norm_nonneg gs, Real.sqrt_nonneg (2 * L * D)])
  have hsq : ‖p - y‖ ^ 2 ≤ (2 * d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmove 2
  nlinarith

lemma proj_lipschitz {K : Set E} {P : E → E} (hP : ∀ z, IsProj K z (P z)) (z w : E) :
    ‖P z - P w‖ ≤ ‖z - w‖ := by
  have h1 := (hP z).2 (P w) (hP w).1
  have h2 := (hP w).2 (P z) (hP z).1
  have hsum : ‖P z - P w‖ ^ 2 ≤ ⟪z - w, P z - P w⟫ := by
    have e : ⟪z - w, P z - P w⟫ - ‖P z - P w‖ ^ 2 =
        -⟪z - P z, P w - P z⟫ - ⟪w - P w, P z - P w⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      have : z - w = (z - P z) - (w - P w) + (P z - P w) := by abel
      rw [this, inner_add_left, inner_sub_left]
      have h3 : ⟪z - P z, P w - P z⟫ = -⟪z - P z, P z - P w⟫ := by
        rw [← inner_neg_right, neg_sub]
      rw [h3]; ring
    linarith
  have hcs := real_inner_le_norm (z - w) (P z - P w)
  by_cases h0 : ‖P z - P w‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖P z - P w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma proj_continuous {K : Set E} {P : E → E} (hP : ∀ z, IsProj K z (P z)) : Continuous P :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun z w => by
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]; exact proj_lipschitz hP z w)

end LongTails.Proofs.ManyConstraintGeometry
