import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped RealInnerProductSpace
open Finset

namespace LongTails.Proofs.TwoSidedPerceptronLinearComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Family (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) where
  e : E
  u : Fin m ⊕ Fin m → E
  e_unit : ‖e‖ = 1
  centered : ∀ i, ⟪e, u i⟫ = 0
  u_norm : ∀ i, ‖u i‖ ≤ (Real.sqrt 2)⁻¹

variable {m : ℕ}

def weight (μ : ℝ) : Fin m ⊕ Fin m → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -(1 + μ)

noncomputable def sample (F : Family E m) (μ : ℝ) (i : Fin m ⊕ Fin m) : E :=
  weight μ i • F.e + μ • F.u i

noncomputable def batchStep (F : Family E m) (μ ϕ : ℝ) (z : E) : E :=
  z + (ϕ / (2 * m)) • ∑ i ∈ univ.filter (fun i => ⟪sample F μ i, z⟫ ≤ 0), sample F μ i

noncomputable def cyclicStep (F : Family E m) (μ ϕ : ℝ) (i : Fin m ⊕ Fin m) (x : E) : E :=
  if ⟪sample F μ i, x⟫ ≤ 0 then x + ϕ • sample F μ i else x

def visit (m : ℕ) (hm : 0 < m) (t : ℕ) : Fin m ⊕ Fin m :=
  if t % 2 = 0 then Sum.inl ⟨(t / 2) % m, Nat.mod_lt _ hm⟩ else Sum.inr ⟨(t / 2) % m, Nat.mod_lt _ hm⟩

noncomputable def cyclicIterate (F : Family E m) (μ ϕ : ℝ) (hm : 0 < m) : ℕ → E
  | 0 => 0
  | t + 1 => cyclicStep F μ ϕ (visit m hm t) (cyclicIterate F μ ϕ hm t)

section Basic

variable (F : Family E m) {μ : ℝ}

lemma inner_sample_decomp {X : ℝ} {R : E} (hR : ⟪F.e, R⟫ = 0) (i : Fin m ⊕ Fin m) :
    ⟪sample F μ i, X • F.e + R⟫ = weight μ i * X + μ * ⟪F.u i, R⟫ := by
  have he : ⟪F.e, F.e⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, F.e_unit]; norm_num
  have hu : ⟪F.u i, F.e⟫ = 0 := by rw [real_inner_comm]; exact F.centered i
  simp only [sample, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    he, hu, hR]
  ring

lemma inner_residual_bound (hμ : 0 ≤ μ) {R : E} {ρ : ℝ} (hRn : ‖R‖ ≤ ρ) (i : Fin m ⊕ Fin m) :
    |μ * ⟪F.u i, R⟫| ≤ μ * ρ / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 := abs_real_inner_le_norm (F.u i) R
  have h2 := F.u_norm i
  have h3 : ‖F.u i‖ * ‖R‖ ≤ (Real.sqrt 2)⁻¹ * ρ :=
    mul_le_mul h2 hRn (norm_nonneg _) (by positivity)
  rw [abs_mul, abs_of_nonneg hμ]
  calc
    μ * |⟪F.u i, R⟫| ≤ μ * ((Real.sqrt 2)⁻¹ * ρ) := by
      apply mul_le_mul_of_nonneg_left (h1.trans h3) hμ
    _ = μ * ρ / Real.sqrt 2 := by field_simp

lemma sum_samples_inl : ∑ j : Fin m, sample F μ (Sum.inl j) =
    (m : ℝ) • F.e + μ • ∑ j : Fin m, F.u (Sum.inl j) := by
  simp only [sample, weight, one_smul, sum_add_distrib, ← smul_sum, sum_const, card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]

lemma sum_samples_inr : ∑ j : Fin m, sample F μ (Sum.inr j) =
    (-(m : ℝ) * (1 + μ)) • F.e + μ • ∑ j : Fin m, F.u (Sum.inr j) := by
  simp only [sample, weight, sum_add_distrib, ← smul_sum, sum_const, card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]
  module

lemma norm_sum_u_le (s : Finset (Fin m ⊕ Fin m)) :
    ‖∑ i ∈ s, F.u i‖ ≤ (s.card : ℝ) * (Real.sqrt 2)⁻¹ := by
  calc
    ‖∑ i ∈ s, F.u i‖ ≤ ∑ i ∈ s, ‖F.u i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, (Real.sqrt 2)⁻¹ := sum_le_sum fun i _ => F.u_norm i
    _ = _ := by simp

lemma norm_sum_u_inl_le : ‖∑ j : Fin m, F.u (Sum.inl j)‖ ≤ (m : ℝ) * (Real.sqrt 2)⁻¹ := by
  calc
    _ ≤ ∑ j : Fin m, ‖F.u (Sum.inl j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, (Real.sqrt 2)⁻¹ := sum_le_sum fun j _ => F.u_norm _
    _ = _ := by simp

lemma norm_sum_u_inr_le : ‖∑ j : Fin m, F.u (Sum.inr j)‖ ≤ (m : ℝ) * (Real.sqrt 2)⁻¹ := by
  calc
    _ ≤ ∑ j : Fin m, ‖F.u (Sum.inr j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, (Real.sqrt 2)⁻¹ := sum_le_sum fun j _ => F.u_norm _
    _ = _ := by simp

lemma inner_e_sum_u (s : Finset (Fin m ⊕ Fin m)) : ⟪F.e, ∑ i ∈ s, F.u i⟫ = 0 := by
  rw [inner_sum]; exact sum_eq_zero fun i _ => F.centered i

end Basic

section Batch

variable (F : Family E m) {μ ϕ : ℝ}

noncomputable def coefX (μ ϕ : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 0 else if t % 2 = 0 then ϕ / 2 * (1 - (t / 2 : ℕ) * μ)
    else -(ϕ / 2) * ((t / 2 : ℕ) + 1) * μ

def BatchGood (F : Family E m) (μ ϕ : ℝ) (t : ℕ) (z : E) : Prop :=
  ∃ R : E, z = coefX μ ϕ t • F.e + R ∧ ⟪F.e, R⟫ = 0 ∧ ‖R‖ ≤ t * (ϕ * μ) / Real.sqrt 2

lemma batchGood_zero : BatchGood F μ ϕ 0 (0 : E) :=
  ⟨0, by simp [coefX], by simp, by simp⟩

lemma filter_all_of (z : E) (h : ∀ i, ⟪sample F μ i, z⟫ ≤ 0) :
    univ.filter (fun i => ⟪sample F μ i, z⟫ ≤ 0) = univ := by
  ext i; simp [h i]

lemma sum_filter_inl (z : E) (hl : ∀ j : Fin m, ⟪sample F μ (Sum.inl j), z⟫ ≤ 0)
    (hr : ∀ j : Fin m, 0 < ⟪sample F μ (Sum.inr j), z⟫) :
    ∑ i ∈ univ.filter (fun i => ⟪sample F μ i, z⟫ ≤ 0), sample F μ i =
      ∑ j : Fin m, sample F μ (Sum.inl j) := by
  rw [sum_filter, Fintype.sum_sum_type]
  have h1 : ∀ j : Fin m, (if ⟪sample F μ (Sum.inl j), z⟫ ≤ 0 then sample F μ (Sum.inl j) else 0) =
      sample F μ (Sum.inl j) := fun j => by simp [hl j]
  have h2 : ∀ j : Fin m, (if ⟪sample F μ (Sum.inr j), z⟫ ≤ 0 then sample F μ (Sum.inr j) else 0) =
      0 := fun j => by simp [not_le.mpr (hr j)]
  simp only [h1, h2, sum_const_zero, add_zero]

lemma sum_filter_inr (z : E) (hl : ∀ j : Fin m, 0 < ⟪sample F μ (Sum.inl j), z⟫)
    (hr : ∀ j : Fin m, ⟪sample F μ (Sum.inr j), z⟫ ≤ 0) :
    ∑ i ∈ univ.filter (fun i => ⟪sample F μ i, z⟫ ≤ 0), sample F μ i =
      ∑ j : Fin m, sample F μ (Sum.inr j) := by
  rw [sum_filter, Fintype.sum_sum_type]
  have h1 : ∀ j : Fin m, (if ⟪sample F μ (Sum.inl j), z⟫ ≤ 0 then sample F μ (Sum.inl j) else 0) =
      0 := fun j => by simp [not_le.mpr (hl j)]
  have h2 : ∀ j : Fin m, (if ⟪sample F μ (Sum.inr j), z⟫ ≤ 0 then sample F μ (Sum.inr j) else 0) =
      sample F μ (Sum.inr j) := fun j => by simp [hr j]
  simp only [h1, h2, sum_const_zero, zero_add]

lemma batch_step (hm : 0 < m) (hμ : 0 < μ) (hμ4 : μ ≤ 1 / 4) (hϕ : 0 < ϕ) {t : ℕ} {z : E}
    (ht : (t : ℝ) * μ ≤ 1) (hz : BatchGood F μ ϕ t z) :
    BatchGood F μ ϕ (t + 1) (batchStep F μ ϕ z) ∧ ∃ i, ⟪sample F μ i, z⟫ ≤ 0 := by
  obtain ⟨R, hdecomp, hcent, hnorm⟩ := hz
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hinner := fun i => inner_sample_decomp F (μ := μ) (X := coefX μ ϕ t) hcent i
  have hres := fun i => inner_residual_bound F hμ.le hnorm i
  have hresb : ∀ i, |μ * ⟪F.u i, R⟫| ≤ t * (ϕ * μ ^ 2) / 2 := by
    intro i
    have := hres i
    have e : μ * (t * (ϕ * μ) / Real.sqrt 2) / Real.sqrt 2 = t * (ϕ * μ ^ 2) / 2 := by
      field_simp; nlinarith [hs2]
    linarith [e]
  have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hUl := norm_sum_u_inl_le F
  have hUr := norm_sum_u_inr_le F
  have hcl := inner_e_sum_u F (univ.map ⟨Sum.inl, Sum.inl_injective⟩)
  have hstep_norm : ∀ (U : E), ‖U‖ ≤ (m : ℝ) * (Real.sqrt 2)⁻¹ →
      ‖R + (ϕ / (2 * m)) • (μ • U)‖ ≤ (t + 1 : ℕ) * (ϕ * μ) / Real.sqrt 2 := by
    intro U hU
    calc
      ‖R + (ϕ / (2 * m)) • (μ • U)‖ ≤ ‖R‖ + ‖(ϕ / (2 * m)) • (μ • U)‖ := norm_add_le _ _
      _ = ‖R‖ + ϕ / (2 * m) * (μ * ‖U‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
          abs_of_pos hμ]
      _ ≤ t * (ϕ * μ) / Real.sqrt 2 + ϕ / (2 * m) * (μ * ((m : ℝ) * (Real.sqrt 2)⁻¹)) := by
        gcongr
      _ ≤ (t + 1 : ℕ) * (ϕ * μ) / Real.sqrt 2 := by
        have e : ϕ / (2 * m) * (μ * ((m : ℝ) * (Real.sqrt 2)⁻¹)) = ϕ * μ / Real.sqrt 2 / 2 := by
          field_simp; try ring
        have e2 : ((t + 1 : ℕ) : ℝ) * (ϕ * μ) / Real.sqrt 2 =
            t * (ϕ * μ) / Real.sqrt 2 + ϕ * μ / Real.sqrt 2 := by push_cast; ring
        rw [e, e2]
        have : 0 ≤ ϕ * μ / Real.sqrt 2 := by positivity
        linarith
  rw [hdecomp]
  rcases Nat.eq_zero_or_pos t with ht0' | htpos
  · -- t = 0: everything is misclassified
    subst ht0'
    have hX : coefX μ ϕ 0 = 0 := by simp [coefX]
    have hall : ∀ i, ⟪sample F μ i, coefX μ ϕ 0 • F.e + R⟫ ≤ 0 := by
      intro i
      rw [hinner i, hX]
      have : R = 0 := by simpa using hnorm
      simp [this]
    refine ⟨?_, ⟨Sum.inl ⟨0, hm⟩, hall _⟩⟩
    have hR0 : R = 0 := by simpa using hnorm
    refine ⟨(ϕ / (2 * m)) • (μ • (∑ j : Fin m, F.u (Sum.inl j) + ∑ j : Fin m, F.u (Sum.inr j))),
      ?_, ?_, ?_⟩
    · unfold batchStep
      rw [filter_all_of F _ hall, Fintype.sum_sum_type, sum_samples_inl, sum_samples_inr, hX, hR0]
      have hX1 : coefX μ ϕ 1 = -(ϕ / 2) * μ := by simp [coefX]
      rw [hX1]
      have e : (ϕ / (2 * m)) * (-(m : ℝ) * (1 + μ) + m) = -(ϕ / 2) * μ := by
        field_simp; ring
      calc
        (0 : ℝ) • F.e + 0 + (ϕ / (2 * m)) • ((m : ℝ) • F.e + μ • ∑ j : Fin m, F.u (Sum.inl j) +
            ((-(m : ℝ) * (1 + μ)) • F.e + μ • ∑ j : Fin m, F.u (Sum.inr j))) =
          ((ϕ / (2 * m)) * (-(m : ℝ) * (1 + μ) + m)) • F.e +
            (ϕ / (2 * m)) • (μ • (∑ j : Fin m, F.u (Sum.inl j) + ∑ j : Fin m, F.u (Sum.inr j))) := by
          module
        _ = _ := by rw [e]
    · rw [real_inner_smul_right, real_inner_smul_right, inner_add_right]
      have h1 : ⟪F.e, ∑ j : Fin m, F.u (Sum.inl j)⟫ = 0 := by
        rw [inner_sum]; exact sum_eq_zero fun j _ => F.centered _
      have h2 : ⟪F.e, ∑ j : Fin m, F.u (Sum.inr j)⟫ = 0 := by
        rw [inner_sum]; exact sum_eq_zero fun j _ => F.centered _
      rw [h1, h2]; ring
    · have hU : ‖∑ j : Fin m, F.u (Sum.inl j) + ∑ j : Fin m, F.u (Sum.inr j)‖ ≤
          (2 * m : ℝ) * (Real.sqrt 2)⁻¹ := by
        calc
          _ ≤ ‖∑ j : Fin m, F.u (Sum.inl j)‖ + ‖∑ j : Fin m, F.u (Sum.inr j)‖ := norm_add_le _ _
          _ ≤ (m : ℝ) * (Real.sqrt 2)⁻¹ + (m : ℝ) * (Real.sqrt 2)⁻¹ := add_le_add hUl hUr
          _ = _ := by ring
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
        abs_of_pos hμ]
      calc
        ϕ / (2 * m) * (μ * ‖∑ j : Fin m, F.u (Sum.inl j) + ∑ j : Fin m, F.u (Sum.inr j)‖) ≤
            ϕ / (2 * m) * (μ * ((2 * m : ℝ) * (Real.sqrt 2)⁻¹)) := by gcongr
        _ = ((0 + 1 : ℕ) : ℝ) * (ϕ * μ) / Real.sqrt 2 := by push_cast; field_simp; try ring
  · -- t ≥ 1: alternate between the two classes
    rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- t = 2k with k ≥ 1: negatives misclassified, positives correct
      have hk1 : 1 ≤ k := by omega
      have hX : coefX μ ϕ t = ϕ / 2 * (1 - k * μ) := by
        have h1 : t ≠ 0 := by omega
        have h2 : t % 2 = 0 := by omega
        have h3 : t / 2 = k := by omega
        simp [coefX, h1, h2, h3]
      have hkμ : (k : ℝ) * μ ≤ 1 / 2 := by
        have : (t : ℝ) = 2 * k := by rw [hk]; push_cast; ring
        rw [this] at ht; linarith
      have hXpos : 0 < coefX μ ϕ t := by rw [hX]; nlinarith
      have htk : (t : ℝ) = 2 * k := by rw [hk]; push_cast; ring
      have hposok : ∀ j : Fin m, 0 < ⟪sample F μ (Sum.inl j), coefX μ ϕ t • F.e + R⟫ := by
        intro j
        rw [hinner, hX]
        simp only [weight, one_mul]
        have := hresb (Sum.inl j)
        rw [htk] at this
        have hb := neg_abs_le (μ * ⟪F.u (Sum.inl j), R⟫)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have : (k : ℝ) * μ ^ 2 ≤ μ / 2 := by nlinarith
        nlinarith
      have hnegbad : ∀ j : Fin m, ⟪sample F μ (Sum.inr j), coefX μ ϕ t • F.e + R⟫ ≤ 0 := by
        intro j
        rw [hinner, hX]
        simp only [weight]
        have := hresb (Sum.inr j)
        rw [htk] at this
        have hb := le_abs_self (μ * ⟪F.u (Sum.inr j), R⟫)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have : (k : ℝ) * μ ^ 2 ≤ μ / 2 := by nlinarith
        nlinarith
      refine ⟨?_, ⟨Sum.inr ⟨0, hm⟩, hnegbad _⟩⟩
      refine ⟨R + (ϕ / (2 * m)) • (μ • ∑ j : Fin m, F.u (Sum.inr j)), ?_, ?_, hstep_norm _ hUr⟩
      · unfold batchStep
        rw [sum_filter_inr F _ hposok hnegbad, sum_samples_inr]
        have hX' : coefX μ ϕ (t + 1) = -(ϕ / 2) * ((k : ℝ) + 1) * μ := by
          have h2 : (t + 1) % 2 ≠ 0 := by omega
          have h3 : (t + 1) / 2 = k := by omega
          simp [coefX, h2, h3]
        rw [hX', hX]
        have e : ϕ / 2 * (1 - k * μ) + (ϕ / (2 * m)) * (-(m : ℝ) * (1 + μ)) =
            -(ϕ / 2) * ((k : ℝ) + 1) * μ := by
          field_simp; ring
        calc
          (ϕ / 2 * (1 - k * μ)) • F.e + R + (ϕ / (2 * m)) •
              ((-(m : ℝ) * (1 + μ)) • F.e + μ • ∑ j : Fin m, F.u (Sum.inr j)) =
            (ϕ / 2 * (1 - k * μ) + (ϕ / (2 * m)) * (-(m : ℝ) * (1 + μ))) • F.e +
              (R + (ϕ / (2 * m)) • (μ • ∑ j : Fin m, F.u (Sum.inr j))) := by module
          _ = _ := by rw [e]
      · rw [inner_add_right, hcent, real_inner_smul_right, real_inner_smul_right]
        have : ⟪F.e, ∑ j : Fin m, F.u (Sum.inr j)⟫ = 0 := by
          rw [inner_sum]; exact sum_eq_zero fun j _ => F.centered _
        rw [this]; ring
    · -- t = 2k+1: positives misclassified, negatives correct
      have hX : coefX μ ϕ t = -(ϕ / 2) * ((k : ℝ) + 1) * μ := by
        have h1 : t ≠ 0 := by omega
        have h2 : t % 2 ≠ 0 := by omega
        have h3 : t / 2 = k := by omega
        simp [coefX, h1, h2, h3]
      have htk : (t : ℝ) = 2 * k + 1 := by rw [hk]; push_cast; ring
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hposbad : ∀ j : Fin m, ⟪sample F μ (Sum.inl j), coefX μ ϕ t • F.e + R⟫ ≤ 0 := by
        intro j
        rw [hinner, hX]
        simp only [weight, one_mul]
        have := hresb (Sum.inl j)
        rw [htk] at this
        have hb := le_abs_self (μ * ⟪F.u (Sum.inl j), R⟫)
        have : (2 * (k : ℝ) + 1) * μ ^ 2 ≤ ((k : ℝ) + 1) * μ := by nlinarith
        nlinarith
      have hnegok : ∀ j : Fin m, 0 < ⟪sample F μ (Sum.inr j), coefX μ ϕ t • F.e + R⟫ := by
        intro j
        rw [hinner, hX]
        simp only [weight]
        have := hresb (Sum.inr j)
        rw [htk] at this
        have hb := neg_abs_le (μ * ⟪F.u (Sum.inr j), R⟫)
        have : (2 * (k : ℝ) + 1) * μ ^ 2 ≤ ((k : ℝ) + 1) * μ := by nlinarith
        have hpos : 0 < (1 + μ) * (ϕ / 2) * ((k : ℝ) + 1) * μ := by positivity
        nlinarith
      refine ⟨?_, ⟨Sum.inl ⟨0, hm⟩, hposbad _⟩⟩
      refine ⟨R + (ϕ / (2 * m)) • (μ • ∑ j : Fin m, F.u (Sum.inl j)), ?_, ?_, hstep_norm _ hUl⟩
      · unfold batchStep
        rw [sum_filter_inl F _ hposbad hnegok, sum_samples_inl]
        have hX' : coefX μ ϕ (t + 1) = ϕ / 2 * (1 - ((k : ℝ) + 1) * μ) := by
          have h2 : (t + 1) % 2 = 0 := by omega
          have h3 : (t + 1) / 2 = k + 1 := by omega
          simp [coefX, h2, h3]
        rw [hX', hX]
        have e : -(ϕ / 2) * ((k : ℝ) + 1) * μ + (ϕ / (2 * m)) * (m : ℝ) =
            ϕ / 2 * (1 - ((k : ℝ) + 1) * μ) := by
          field_simp; ring
        calc
          (-(ϕ / 2) * ((k : ℝ) + 1) * μ) • F.e + R + (ϕ / (2 * m)) •
              ((m : ℝ) • F.e + μ • ∑ j : Fin m, F.u (Sum.inl j)) =
            (-(ϕ / 2) * ((k : ℝ) + 1) * μ + (ϕ / (2 * m)) * (m : ℝ)) • F.e +
              (R + (ϕ / (2 * m)) • (μ • ∑ j : Fin m, F.u (Sum.inl j))) := by module
          _ = _ := by rw [e]
      · rw [inner_add_right, hcent, real_inner_smul_right, real_inner_smul_right]
        have : ⟪F.e, ∑ j : Fin m, F.u (Sum.inl j)⟫ = 0 := by
          rw [inner_sum]; exact sum_eq_zero fun j _ => F.centered _
        rw [this]; ring

theorem batch_not_separated (hm : 0 < m) (hμ : 0 < μ) (hμ4 : μ ≤ 1 / 4) (hϕ : 0 < ϕ) :
    ∀ t : ℕ, (t : ℝ) * μ ≤ 1 →
      ∃ i, ⟪sample F μ i, (batchStep F μ ϕ)^[t] 0⟫ ≤ 0 := by
  have key : ∀ t : ℕ, (t : ℝ) * μ ≤ 1 → BatchGood F μ ϕ t ((batchStep F μ ϕ)^[t] 0) := by
    intro t
    induction t with
    | zero => intro _; exact batchGood_zero F
    | succ t ih =>
      intro ht
      have ht' : (t : ℝ) * μ ≤ 1 := by
        have : (t : ℝ) ≤ (t + 1 : ℕ) := by push_cast; linarith
        nlinarith
      rw [Function.iterate_succ_apply']
      exact (batch_step F hm hμ hμ4 hϕ ht' (ih ht')).1
  intro t ht
  exact (batch_step F hm hμ hμ4 hϕ ht (key t ht)).2

end Batch

section Cyclic

variable (F : Family E m) {μ ϕ : ℝ}

noncomputable def coefY (μ ϕ : ℝ) (t : ℕ) : ℝ :=
  if t % 2 = 0 then -(t / 2 : ℕ) * (ϕ * μ) else ϕ * (1 - (t / 2 : ℕ) * μ)

def CyclicGood (F : Family E m) (μ ϕ : ℝ) (t : ℕ) (x : E) : Prop :=
  ∃ R : E, x = coefY μ ϕ t • F.e + R ∧ ⟪F.e, R⟫ = 0 ∧ ‖R‖ ≤ t * (ϕ * μ) / Real.sqrt 2

lemma cyclic_step (hm : 0 < m) (hμ : 0 < μ) (hμ4 : μ ≤ 1 / 4) (hϕ : 0 < ϕ) {t : ℕ} {x : E}
    (ht : (t : ℝ) * μ ≤ 1) (hx : CyclicGood F μ ϕ t x) :
    ⟪sample F μ (visit m hm t), x⟫ ≤ 0 ∧
      CyclicGood F μ ϕ (t + 1) (cyclicStep F μ ϕ (visit m hm t) x) := by
  obtain ⟨R, hdecomp, hcent, hnorm⟩ := hx
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinner := fun i => inner_sample_decomp F (μ := μ) (X := coefY μ ϕ t) hcent i
  have hres := fun i => inner_residual_bound F hμ.le hnorm i
  have hresb : ∀ i, |μ * ⟪F.u i, R⟫| ≤ t * (ϕ * μ ^ 2) / 2 := by
    intro i
    have := hres i
    have e : μ * (t * (ϕ * μ) / Real.sqrt 2) / Real.sqrt 2 = t * (ϕ * μ ^ 2) / 2 := by
      field_simp; nlinarith [hs2]
    linarith [e]
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hmis : ⟪sample F μ (visit m hm t), x⟫ ≤ 0 := by
    rw [hdecomp, hinner]
    unfold visit
    rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h2 : t % 2 = 0 := by omega
      have h3 : t / 2 = k := by omega
      have hY : coefY μ ϕ t = -(k : ℝ) * (ϕ * μ) := by simp [coefY, h2, h3]
      simp only [h2, ite_true, weight, one_mul]
      rw [hY]
      have := hresb (Sum.inl ⟨(t / 2) % m, Nat.mod_lt _ hm⟩)
      have htk : (t : ℝ) = 2 * k := by rw [hk]; push_cast; ring
      rw [htk] at this
      have hb := le_abs_self (μ * ⟪F.u (Sum.inl ⟨(t / 2) % m, Nat.mod_lt _ hm⟩), R⟫)
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hkk : (k : ℝ) * (ϕ * μ ^ 2) ≤ k * (ϕ * μ) := by
        have h0 : 0 ≤ (k : ℝ) * ϕ := mul_nonneg hk0 hϕ.le
        have h1 : 0 ≤ μ - μ ^ 2 := by nlinarith
        have := mul_nonneg h0 h1
        linarith [this]
      linarith
    · have h2 : t % 2 ≠ 0 := by omega
      have h3 : t / 2 = k := by omega
      have hY : coefY μ ϕ t = ϕ * (1 - (k : ℝ) * μ) := by simp [coefY, h2, h3]
      simp only [h2, ite_false, weight]
      rw [hY]
      have := hresb (Sum.inr ⟨(t / 2) % m, Nat.mod_lt _ hm⟩)
      have htk : (t : ℝ) = 2 * k + 1 := by rw [hk]; push_cast; ring
      rw [htk] at this
      have hb := le_abs_self (μ * ⟪F.u (Sum.inr ⟨(t / 2) % m, Nat.mod_lt _ hm⟩), R⟫)
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hkμ : (k : ℝ) * μ ≤ 1 / 2 := by rw [htk] at ht; linarith
      have h1 : (2 * (k : ℝ) + 1) * μ ^ 2 ≤ μ + μ ^ 2 := by nlinarith
      have h2' : μ + μ ^ 2 ≤ 2 * (1 - (k : ℝ) * μ) * (1 + μ) := by nlinarith
      nlinarith
  refine ⟨hmis, ?_⟩
  refine ⟨R + ϕ • (μ • F.u (visit m hm t)), ?_, ?_, ?_⟩
  · have hcs : cyclicStep F μ ϕ (visit m hm t) x = x + ϕ • sample F μ (visit m hm t) := by
      simp [cyclicStep, hmis]
    rw [hcs, hdecomp]
    have hw : coefY μ ϕ t + ϕ * weight μ (visit m hm t) = coefY μ ϕ (t + 1) := by
      unfold visit coefY
      rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
      · have h2 : t % 2 = 0 := by omega
        have h2' : (t + 1) % 2 ≠ 0 := by omega
        have h3 : t / 2 = k := by omega
        have h3' : (t + 1) / 2 = k := by omega
        simp [h2, h2', h3, h3', weight]; ring
      · have h2 : t % 2 ≠ 0 := by omega
        have h2' : (t + 1) % 2 = 0 := by omega
        have h3 : t / 2 = k := by omega
        have h3' : (t + 1) / 2 = k + 1 := by omega
        simp [h2, h2', h3, h3', weight]; ring
    calc
      coefY μ ϕ t • F.e + R + ϕ • sample F μ (visit m hm t) =
          (coefY μ ϕ t + ϕ * weight μ (visit m hm t)) • F.e + (R + ϕ • (μ • F.u (visit m hm t))) := by
        unfold sample; module
      _ = _ := by rw [hw]
  · rw [inner_add_right, hcent, real_inner_smul_right, real_inner_smul_right, F.centered]; ring
  · calc
      ‖R + ϕ • (μ • F.u (visit m hm t))‖ ≤ ‖R‖ + ‖ϕ • (μ • F.u (visit m hm t))‖ := norm_add_le _ _
      _ = ‖R‖ + ϕ * (μ * ‖F.u (visit m hm t)‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hϕ, abs_of_pos hμ]
      _ ≤ t * (ϕ * μ) / Real.sqrt 2 + ϕ * (μ * (Real.sqrt 2)⁻¹) := by
        gcongr; exact F.u_norm _
      _ = (t + 1 : ℕ) * (ϕ * μ) / Real.sqrt 2 := by push_cast; field_simp; try ring

theorem cyclic_all_mistakes (hm : 0 < m) (hμ : 0 < μ) (hμ4 : μ ≤ 1 / 4) (hϕ : 0 < ϕ) :
    ∀ t : ℕ, (t : ℝ) * μ ≤ 1 → ⟪sample F μ (visit m hm t), cyclicIterate F μ ϕ hm t⟫ ≤ 0 := by
  have key : ∀ t : ℕ, (t : ℝ) * μ ≤ 1 → CyclicGood F μ ϕ t (cyclicIterate F μ ϕ hm t) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨0, by simp [cyclicIterate, coefY], by simp, by simp⟩
    | succ t ih =>
      intro ht
      have ht' : (t : ℝ) * μ ≤ 1 := by
        have : (t : ℝ) ≤ (t + 1 : ℕ) := by push_cast; linarith
        nlinarith
      exact (cyclic_step F hm hμ hμ4 hϕ ht' (ih ht')).2
  intro t ht
  exact (cyclic_step F hm hμ hμ4 hϕ ht (key t ht)).1

end Cyclic

end LongTails.Proofs.TwoSidedPerceptronLinearComparison
