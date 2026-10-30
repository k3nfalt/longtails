import LongTails.Proofs.VarianceReducedWeakMintySampling
import LongTails.Proofs.CappedProximalGeometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CappedProximalSampling

set_option maxHeartbeats 800000 in
lemma uniform_snoc {Ω V : Type*} [Fintype Ω] [AddCommMonoid V] [Module ℚ≥0 V]
    {k : ℕ} (f : (Fin (k + 1) → Ω) → V) :
    (𝔼 ξ, f ξ) = 𝔼 history : Fin k → Ω, 𝔼 last : Ω, f (Fin.snoc history last) := by
  rw [Fintype.expect_equiv (Fin.snocEquiv (fun _ : Fin (k + 1) => Ω)).symm
    f (fun pair => f (Fin.snoc pair.2 pair.1)) (by
      intro ξ
      exact congrArg f ((Fin.snocEquiv (fun _ : Fin (k + 1) => Ω)).apply_symm_apply ξ).symm)]
  calc
    _ = 𝔼 last : Ω, 𝔼 history : Fin k → Ω, f (Fin.snoc history last) :=
      Finset.expect_product Finset.univ Finset.univ _
    _ = _ := Finset.expect_comm Finset.univ Finset.univ _

lemma uniform_trajectory_step {Ω S V : Type*} [Fintype Ω]
    [AddCommMonoid V] [Module ℚ≥0 V]
    (state : (n : ℕ) → (Fin n → Ω) → S) (step : ℕ → S → Ω → S)
    (hstep : ∀ n ξ ω, state (n + 1) (Fin.snoc ξ ω) = step n (state n ξ) ω)
    (f : S → V) (n : ℕ) :
    (𝔼 ξ, f (state (n + 1) ξ)) = 𝔼 ξ, 𝔼 ω, f (step n (state n ξ) ω) := by
  rw [uniform_snoc]
  simp_rw [hstep]

lemma uniform_coordinate_split {ι Ω V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [AddCommMonoid V] [Module ℚ≥0 V]
    (j : ι) (f : (ι → Ω) → V) :
    (𝔼 ξ, f ξ) = 𝔼 a : Ω, 𝔼 rest : {k : ι // k ≠ j} → Ω,
      f ((Equiv.funSplitAt j Ω).symm (a, rest)) := by
  rw [Fintype.expect_equiv (Equiv.funSplitAt j Ω) f
    (fun pair => f ((Equiv.funSplitAt j Ω).symm pair)) (by
      intro ξ
      exact congrArg f ((Equiv.funSplitAt j Ω).symm_apply_apply ξ).symm)]
  exact Finset.expect_product Finset.univ Finset.univ _

lemma uniform_coordinate_mean {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] (j : ι) (f : Ω → ℝ) :
    (𝔼 ξ : ι → Ω, f (ξ j)) = 𝔼 a, f a := by
  rw [uniform_coordinate_split j]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

lemma uniform_cohort_mean {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (𝔼 ξ : ι → Ω, 𝔼 j, f (ξ j)) = 𝔼 a, f a := by
  rw [Finset.expect_comm]
  simp_rw [uniform_coordinate_mean]
  exact Fintype.expect_const _

lemma split_sample_sum {ι Ω V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid V] (j : ι) (u : Ω → V) (a : Ω)
    (rest : {k : ι // k ≠ j} → Ω) :
    (∑ k, u ((Equiv.funSplitAt j Ω).symm (a, rest) k)) =
      u a + ∑ k, u (rest k) := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun k : ι => k = j)
    (fun k => u ((Equiv.funSplitAt j Ω).symm (a, rest) k))
  rw [← h]
  congr 1
  · let : Fintype {k : ι // k = j} := Subtype.fintype (fun k => k = j)
    calc
      _ = u ((Equiv.funSplitAt j Ω).symm (a, rest) j) :=
        Fintype.sum_subsingleton
          (fun k : {k : ι // k = j} => u ((Equiv.funSplitAt j Ω).symm (a, rest) k)) ⟨j, rfl⟩
      _ = u a := by simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · apply Finset.sum_congr rfl
    intro k _
    simp [Equiv.funSplitAt, Equiv.piSplitAt, k.property]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma split_sample_displacement {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (u : Ω → E) (a : Ω) (rest : {k : ι // k ≠ j} → Ω)
    (U : E) (c : ℝ) :
    c • (∑ k, u ((Equiv.funSplitAt j Ω).symm (a, rest) k)) -
      c • (U + ∑ k, u (rest k)) = c • (u a - U) := by
  rw [split_sample_sum]
  module

lemma averaged_replacement {Ω : Type*} [Fintype Ω]
    (u : Ω → E) (D : Ω → E → E) (U R : E) {c K : ℝ} (hc : 0 ≤ c)
    (hD : ∀ i x y, ‖D i x - D i y‖ ≤ K * ‖x - y‖) :
    (𝔼 i, ⟪D i (c • (u i + R)), u i - U⟫) ≤
      (𝔼 i, ⟪D i (c • (U + R)), u i - U⟫) +
        K * c * (𝔼 i, ‖u i - U‖ ^ 2) := by
  have hi (i : Ω) := CappedProximalGeometry.leave_one_out_replacement (D i) hc
    (show c • (u i + R) - c • (U + R) = c • (u i - U) by module)
    (hD i (c • (u i + R)) (c • (U + R)))
  have ht := Finset.expect_le_expect (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.expect_add_distrib, ← Finset.mul_expect] using ht

lemma independent_cross {m : ℕ} [NeZero m] (d v : Fin m → E)
    {delta r : ℝ} (hd : 0 ≤ delta) (hr : 0 ≤ r)
    (h : (𝔼 i, ‖d i‖ ^ 2) ≤ delta ^ 2 * r ^ 2) :
    (𝔼 i, ⟪d i, v i⟫) ≤ delta * r * Real.sqrt (𝔼 i, ‖v i‖ ^ 2) := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hc := CappedProximalGeometry.average_inner_le d v hm
  have hn : Real.sqrt (𝔼 i, ‖d i‖ ^ 2) ≤ delta * r := by
    apply (Real.sqrt_le_left (mul_nonneg hd hr)).2
    simpa only [mul_pow] using h
  have ht := mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg (𝔼 i, ‖v i‖ ^ 2))
  apply le_trans _ ht
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, one_div_mul_eq_div] using hc

lemma batch_sum_norm_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (v : Ω → E) (hv : ∑ i, v i = 0) (k : ℕ) :
    (𝔼 ξ : Fin k → Ω, ‖∑ j, v (ξ j)‖) ≤
      Real.sqrt ((k : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) := by
  have hc := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ξ : Fin k → Ω => ‖∑ j, v (ξ j)‖) (fun _ => (1 : ℝ))
  have ht : (𝔼 ξ : Fin k → Ω, ‖∑ j, v (ξ j)‖) ^ 2 ≤
      (𝔼 ξ : Fin k → Ω, ‖∑ j, v (ξ j)‖ ^ 2) := by
    simpa only [mul_one, one_pow, Fintype.expect_const] using hc
  rw [OracleTemplate.VarianceReducedWeakMinty.batch_sum_second_moment v hv k] at ht
  exact Real.le_sqrt_of_sq_le ht

lemma batch_sum_norm_bound_fintype {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] (v : Ω → E) (hv : ∑ i, v i = 0) :
    (𝔼 ξ : ι → Ω, ‖∑ j, v (ξ j)‖) ≤
      Real.sqrt ((Fintype.card ι : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) := by
  let e := Fintype.equivFin ι
  let ef := Equiv.arrowCongr e (Equiv.refl Ω)
  have he (ξ : ι → Ω) : ‖∑ j, v (ξ j)‖ = ‖∑ j, v (ef ξ j)‖ := by
    congr 1
    apply Fintype.sum_equiv e
    intro j
    simp [ef]
  rw [Fintype.expect_equiv ef (fun ξ : ι → Ω => ‖∑ j, v (ξ j)‖)
    (fun ξ : Fin (Fintype.card ι) → Ω => ‖∑ j, v (ξ j)‖) he]
  exact batch_sum_norm_bound v hv (Fintype.card ι)

lemma remaining_sum_norm_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (v : Ω → E) (hv : ∑ i, v i = 0) {k : ℕ} (j : Fin (k + 1)) :
    (𝔼 ξ : {i : Fin (k + 1) // i ≠ j} → Ω, ‖∑ i, v (ξ i)‖) ≤
      Real.sqrt ((k : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) := by
  have hcard := Fintype.card_congr (finSuccAboveEquiv j)
  simpa only [← hcard, Fintype.card_fin] using
    (batch_sum_norm_bound_fintype (ι := {i : Fin (k + 1) // i ≠ j}) v hv)

lemma averaged_independent_cross {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} [NeZero m] (v : Fin m → E) (hv : ∑ i, v i = 0)
    (D : Fin m → E → E) {delta c : ℝ} (hd : 0 ≤ delta) (hc : 0 ≤ c)
    (hD : ∀ z, (𝔼 i, ‖D i z‖ ^ 2) ≤ delta ^ 2 * ‖z‖ ^ 2) :
    (𝔼 ξ : ι → Fin m, 𝔼 i, ⟪D i (c • ∑ j, v (ξ j)), v i⟫) ≤
      delta * c * Real.sqrt ((Fintype.card ι : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) *
        Real.sqrt (𝔼 i, ‖v i‖ ^ 2) := by
  have hi (ξ : ι → Fin m) := independent_cross
    (fun i => D i (c • ∑ j, v (ξ j))) v hd (norm_nonneg _) (hD _)
  calc
    _ ≤ 𝔼 ξ : ι → Fin m,
        delta * ‖c • ∑ j, v (ξ j)‖ * Real.sqrt (𝔼 i, ‖v i‖ ^ 2) :=
      Finset.expect_le_expect (fun ξ _ => hi ξ)
    _ = (delta * c * Real.sqrt (𝔼 i, ‖v i‖ ^ 2)) *
        (𝔼 ξ : ι → Fin m, ‖∑ j, v (ξ j)‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
        ← Finset.mul_expect, ← Finset.expect_mul]
      ring
    _ ≤ (delta * c * Real.sqrt (𝔼 i, ‖v i‖ ^ 2)) *
        Real.sqrt ((Fintype.card ι : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (batch_sum_norm_bound_fintype v hv) (by positivity)
    _ = _ := by ring

lemma coordinate_cross_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} [NeZero m] (j : ι) (v : Fin m → E) (hv : ∑ i, v i = 0)
    (D : Fin m → E → E) {delta c K : ℝ} (hd : 0 ≤ delta) (hc : 0 ≤ c)
    (hD : ∀ z, (𝔼 i, ‖D i z‖ ^ 2) ≤ delta ^ 2 * ‖z‖ ^ 2)
    (hlip : ∀ i x y, ‖D i x - D i y‖ ≤ K * ‖x - y‖) :
    (𝔼 ξ : ι → Fin m, ⟪D (ξ j) (c • ∑ k, v (ξ k)), v (ξ j)⟫) ≤
      delta * c * Real.sqrt ((Fintype.card {k : ι // k ≠ j} : ℝ) *
        (𝔼 i, ‖v i‖ ^ 2)) * Real.sqrt (𝔼 i, ‖v i‖ ^ 2) +
        K * c * (𝔼 i, ‖v i‖ ^ 2) := by
  have he (a : Fin m) (rest : {k : ι // k ≠ j} → Fin m) :
      let ξ := (Equiv.funSplitAt j (Fin m)).symm (a, rest)
      ⟪D (ξ j) (c • ∑ k, v (ξ k)), v (ξ j)⟫ =
        ⟪D a (c • (v a + ∑ k, v (rest k))), v a⟫ := by
    dsimp only
    rw [split_sample_sum]
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [uniform_coordinate_split j, Finset.expect_comm]
  simp_rw [he]
  have hr (rest : {k : ι // k ≠ j} → Fin m) :=
    averaged_replacement v D 0 (∑ k, v (rest k)) hc hlip
  simp only [sub_zero, zero_add] at hr
  have ht := Finset.expect_le_expect (fun rest (_ : rest ∈ Finset.univ) => hr rest)
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at ht
  exact ht.trans (add_le_add
    (averaged_independent_cross (ι := {k : ι // k ≠ j}) v hv D hd hc hD) le_rfl)

lemma cohort_cross_bound {m k : ℕ} [NeZero m]
    (v : Fin m → E) (hv : ∑ i, v i = 0) (D : Fin m → E → E)
    {delta c K : ℝ} (hd : 0 ≤ delta) (hc : 0 ≤ c)
    (hD : ∀ z, (𝔼 i, ‖D i z‖ ^ 2) ≤ delta ^ 2 * ‖z‖ ^ 2)
    (hlip : ∀ i x y, ‖D i x - D i y‖ ≤ K * ‖x - y‖) :
    (𝔼 ξ : Fin (k + 1) → Fin m, 𝔼 j, ⟪D (ξ j) (c • ∑ t, v (ξ t)), v (ξ j)⟫) ≤
      delta * c * Real.sqrt ((k : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) *
        Real.sqrt (𝔼 i, ‖v i‖ ^ 2) + K * c * (𝔼 i, ‖v i‖ ^ 2) := by
  have hi (j : Fin (k + 1)) := coordinate_cross_bound j v hv D hd hc hD hlip
  have hb (j : Fin (k + 1)) :
      (𝔼 ξ : Fin (k + 1) → Fin m, ⟪D (ξ j) (c • ∑ t, v (ξ t)), v (ξ j)⟫) ≤
        delta * c * Real.sqrt ((k : ℝ) * (𝔼 i, ‖v i‖ ^ 2)) *
          Real.sqrt (𝔼 i, ‖v i‖ ^ 2) + K * c * (𝔼 i, ‖v i‖ ^ 2) := by
    have hcard := Fintype.card_congr (finSuccAboveEquiv j)
    simpa only [← hcard, Fintype.card_fin] using hi j
  rw [Finset.expect_comm]
  have ht := Finset.expect_le_expect (fun j (_ : j ∈ Finset.univ) => hb j)
  simpa only [Fintype.expect_const] using ht

lemma normalized_cohort_cross_bound {m k : ℕ} [NeZero m]
    (v : Fin m → E) (hv : ∑ i, v i = 0) (D : Fin m → E → E)
    {delta K : ℝ} (hd : 0 ≤ delta)
    (hD : ∀ z, (𝔼 i, ‖D i z‖ ^ 2) ≤ delta ^ 2 * ‖z‖ ^ 2)
    (hlip : ∀ i x y, ‖D i x - D i y‖ ≤ K * ‖x - y‖) :
    (𝔼 ξ : Fin (k + 1) → Fin m,
      𝔼 j, ⟪D (ξ j) (((k : ℝ) + 1)⁻¹ • ∑ t, v (ξ t)), v (ξ j)⟫) ≤
      ((delta * Real.sqrt k + K) / ((k : ℝ) + 1)) * (𝔼 i, ‖v i‖ ^ 2) := by
  have h := cohort_cross_bound (k := k) v hv D hd
    (show 0 ≤ ((k : ℝ) + 1)⁻¹ by positivity) hD hlip
  have hV : 0 ≤ (𝔼 i, ‖v i‖ ^ 2) := Finset.expect_nonneg (fun i _ => sq_nonneg _)
  convert h using 1
  rw [Real.sqrt_mul (Nat.cast_nonneg k)]
  ring_nf
  rw [Real.sq_sqrt hV]

lemma sample_mean_translation {m s : ℕ} (hs : 0 < s)
    (u : Fin m → E) (U : E) (ξ : Fin s → Fin m) :
    (s : ℝ)⁻¹ • (∑ j, u (ξ j)) = U + (s : ℝ)⁻¹ • (∑ j, (u (ξ j) - U)) := by
  have h := OracleTemplate.RobustGradient.finite_mean_centered (X := u) U s hs ξ
  simp only [one_div] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

lemma sampled_primal_second_moment {m s : ℕ} [NeZero m]
    (hs : 0 < s) (u : Fin m → E) :
    (𝔼 indices : Fin s → Fin m,
      ‖(s : ℝ)⁻¹ • (∑ j, u (indices j)) - (m : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2) =
      ((1 / (m : ℝ)) * ∑ i, ‖u i - (m : ℝ)⁻¹ • (∑ k, u k)‖ ^ 2) / s := by
  have hc (indices : Fin s → Fin m) := OracleTemplate.RobustGradient.finite_mean_centered
    (X := u) ((m : ℝ)⁻¹ • ∑ i, u i) s hs indices
  simp only [one_div] at hc
  simp_rw [hc]
  rw [OracleTemplate.VarianceReducedWeakMinty.batch_mean_second_moment _
    (OracleTemplate.VarianceReducedWeakMinty.component_centered_sum (NeZero.pos m) u) hs]
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, one_div_mul_eq_div]

lemma sampled_primal_centered_sum {m s : ℕ} [NeZero m]
    (hs : 0 < s) (u : Fin m → E) :
    (∑ indices : Fin s → Fin m,
      ((s : ℝ)⁻¹ • (∑ j, u (indices j)) - (m : ℝ)⁻¹ • (∑ i, u i))) = 0 := by
  have hc (indices : Fin s → Fin m) := OracleTemplate.RobustGradient.finite_mean_centered
    (X := u) ((m : ℝ)⁻¹ • ∑ i, u i) s hs indices
  simp only [one_div] at hc
  simp_rw [hc]
  rw [← Finset.smul_sum, OracleTemplate.VarianceReducedWeakMinty.batch_sum_zero _
    (OracleTemplate.VarianceReducedWeakMinty.component_centered_sum (NeZero.pos m) u) s,
    smul_zero]

lemma sampled_primal_inner_zero {m s : ℕ} [NeZero m]
    (hs : 0 < s) (u : Fin m → E) (G : E) :
    (𝔼 indices : Fin s → Fin m,
      ⟪G, (s : ℝ)⁻¹ • (∑ j, u (indices j)) - (m : ℝ)⁻¹ • (∑ i, u i)⟫) = 0 := by
  rw [Fintype.expect_eq_sum_div_card, ← inner_sum,
    sampled_primal_centered_sum hs u, inner_zero_right, zero_div]

lemma uniform_mean_of_centered_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (z : Ω → E) (U : E) (hz : ∑ i, (z i - U) = 0) :
    (∑ i, (1 / (Fintype.card Ω : ℝ)) • z i) = U := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ i, z i) = (Fintype.card Ω) • U := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      sub_eq_zero] using hz
  rw [← Finset.smul_sum, hs, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    one_div_mul_cancel hn, one_smul]

lemma uniform_covariance {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (z : Ω → E) (U x v : E) (hz : ∑ i, (z i - U) = 0) :
    (𝔼 i, ⟪x - z i, z i - v⟫) = ⟪x - U, U - v⟫ - (𝔼 i, ‖z i - U‖ ^ 2) := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := CappedProximalGeometry.sampled_covariance
    (fun _ : Ω => 1 / (Fintype.card Ω : ℝ)) z U x v (by simp [hn])
    (uniform_mean_of_centered_sum z U hz)
  simpa only [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum,
    one_div_mul_eq_div, ← Finset.sum_div] using h

lemma sampled_primal_covariance {m s : ℕ} [NeZero m]
    (hs : 0 < s) (u : Fin m → E) (x v : E) :
    let U := (m : ℝ)⁻¹ • ∑ i, u i
    let z := fun ξ : Fin s → Fin m => (s : ℝ)⁻¹ • ∑ j, u (ξ j)
    (𝔼 ξ, ⟪x - z ξ, z ξ - v⟫) = ⟪x - U, U - v⟫ -
      ((1 / (m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) / s := by
  dsimp only
  have h := uniform_covariance (fun ξ : Fin s → Fin m => (s : ℝ)⁻¹ • ∑ j, u (ξ j))
    ((m : ℝ)⁻¹ • ∑ i, u i) x v (sampled_primal_centered_sum hs u)
  rw [sampled_primal_second_moment hs u] at h
  exact h

lemma uniform_squared_distance {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (z : Ω → E) (U x : E) (hz : ∑ i, (z i - U) = 0) :
    (𝔼 i, ‖z i - x‖ ^ 2) = (𝔼 i, ‖z i - U‖ ^ 2) + ‖U - x‖ ^ 2 := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := CappedProximalGeometry.variance_decomposition
    (fun _ : Ω => 1 / (Fintype.card Ω : ℝ)) z U x (by simp [hn])
    (uniform_mean_of_centered_sum z U hz)
  simpa only [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum,
    one_div_mul_eq_div, ← Finset.sum_div] using h

lemma sampled_residual_covariance {m s : ℕ} [NeZero m]
    (hs : 0 < s) (u : Fin m → E) (x v : E) (lam : ℝ) :
    let U := (m : ℝ)⁻¹ • ∑ i, u i
    let z := fun ξ : Fin s → Fin m => (s : ℝ)⁻¹ • ∑ j, u (ξ j)
    (𝔼 ξ, ⟪lam • (x - z ξ), z ξ - v⟫) = ⟪lam • (x - U), U - v⟫ -
      lam / s * ((1 / (m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) := by
  dsimp only
  simp only [real_inner_smul_left, ← Finset.mul_expect]
  rw [sampled_primal_covariance hs u x v]
  ring

lemma sampled_squared_distance {m s : ℕ} [NeZero m]
    (hs : 0 < s) (u : Fin m → E) (x : E) :
    let U := (m : ℝ)⁻¹ • ∑ i, u i
    let z := fun ξ : Fin s → Fin m => (s : ℝ)⁻¹ • ∑ j, u (ξ j)
    (𝔼 ξ, ‖x - z ξ‖ ^ 2) = ‖x - U‖ ^ 2 +
      ((1 / (m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2) / s := by
  dsimp only
  have h := uniform_squared_distance
    (fun ξ : Fin s → Fin m => (s : ℝ)⁻¹ • ∑ j, u (ξ j))
    ((m : ℝ)⁻¹ • ∑ i, u i) x (sampled_primal_centered_sum hs u)
  rw [sampled_primal_second_moment hs u] at h
  simpa only [norm_sub_rev, add_comm] using h

lemma expected_primal_from_certificate {m k : ℕ} [NeZero m]
    (v : Fin m → E) (hv : ∑ i, v i = 0) (D : Fin m → E → E)
    (F : E → ℝ) (B : Fin m → ℝ) (G : E)
    (z : (Fin (k + 1) → Fin m) → E)
    (hz : ∀ ξ, z ξ = ((k : ℝ) + 1)⁻¹ • ∑ j, v (ξ j))
    {delta K : ℝ} (hd : 0 ≤ delta)
    (hD : ∀ x, (𝔼 i, ‖D i x‖ ^ 2) ≤ delta ^ 2 * ‖x‖ ^ 2)
    (hlip : ∀ i x y, ‖D i x - D i y‖ ≤ K * ‖x - y‖)
    (hpoint : ∀ ξ, F (z ξ) - F 0 ≤ (𝔼 j, B (ξ j)) + ⟪G, z ξ⟫ +
      (𝔼 j, ⟪D (ξ j) (z ξ), v (ξ j)⟫) + K / 2 * ‖z ξ‖ ^ 2) :
    (𝔼 ξ, (F (z ξ) - F 0)) ≤ (𝔼 i, B i) +
      ((delta * Real.sqrt k + 3 * K / 2) / ((k : ℝ) + 1)) * (𝔼 i, ‖v i‖ ^ 2) := by
  have hlin : (𝔼 ξ, ⟪G, z ξ⟫) = 0 := by
    have h := sampled_primal_inner_zero (Nat.succ_pos k) v G
    simp only [hv, smul_zero, sub_zero, Nat.cast_succ] at h
    simpa only [hz] using h
  have hmoment : (𝔼 ξ, ‖z ξ‖ ^ 2) = (𝔼 i, ‖v i‖ ^ 2) / ((k : ℝ) + 1) := by
    simp_rw [hz]
    simpa only [Nat.cast_succ] using
      OracleTemplate.VarianceReducedWeakMinty.batch_mean_second_moment v hv (Nat.succ_pos k)
  have hcross : (𝔼 ξ, 𝔼 j, ⟪D (ξ j) (z ξ), v (ξ j)⟫) ≤
      ((delta * Real.sqrt k + K) / ((k : ℝ) + 1)) * (𝔼 i, ‖v i‖ ^ 2) := by
    simpa only [hz] using normalized_cohort_cross_bound (k := k) v hv D hd hD hlip
  have ht := Finset.expect_le_expect (fun ξ (_ : ξ ∈ Finset.univ) => hpoint ξ)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, uniform_cohort_mean,
    hlin, add_zero, hmoment] at ht
  have he : ((delta * Real.sqrt k + 3 * K / 2) / ((k : ℝ) + 1)) * (𝔼 i, ‖v i‖ ^ 2) =
      ((delta * Real.sqrt k + K) / ((k : ℝ) + 1)) * (𝔼 i, ‖v i‖ ^ 2) +
        K / 2 * ((𝔼 i, ‖v i‖ ^ 2) / ((k : ℝ) + 1)) := by ring
  rw [he]
  have hstep := add_le_add (add_le_add (le_refl (𝔼 i, B i)) hcross)
    (le_refl (K / 2 * ((𝔼 i, ‖v i‖ ^ 2) / ((k : ℝ) + 1))))
  exact ht.trans (by simpa only [add_assoc] using hstep)

lemma average_stochastic_certificate {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (gap pairing movement : Ω → Ξ → ℝ) (error noise : Ω → ℝ)
    {lam variance : ℝ} (hl : 0 < lam)
    (hpoint : ∀ ω, (𝔼 ξ, gap ω ξ) ≤ (𝔼 ξ, pairing ω ξ) +
      lam / 8 * (𝔼 ξ, movement ω ξ) + 4 / lam * error ω - noise ω)
    (hvariance : (𝔼 ω, error ω) ≤ variance)
    (hnoise : (𝔼 ω, noise ω) = 0) :
    (𝔼 ω, 𝔼 ξ, gap ω ξ) ≤ (𝔼 ω, 𝔼 ξ, pairing ω ξ) +
      lam / 8 * (𝔼 ω, 𝔼 ξ, movement ω ξ) + 4 / lam * variance := by
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, hnoise, sub_zero] at ht
  apply ht.trans
  gcongr

lemma expected_potential_step {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A B a lam fy fs err : ℝ} (fz : Ω → ℝ) (z r : Ω → E) (x y v xs : E)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hlam : 0 < lam)
    (hA : A = B + a) (haA : a ^ 2 * lam = A)
    (hx : A • x = B • y + a • v) (hr : ∀ ω, r ω = lam • (x - z ω))
    (hy : (𝔼 ω, (fz ω - fy)) ≤ (𝔼 ω, ⟪r ω, z ω - y⟫) + err)
    (hs : (𝔼 ω, (fz ω - fs)) ≤ (𝔼 ω, ⟪r ω, z ω - xs⟫) + err) :
    (𝔼 ω, (A * (fz ω - fs) + ‖v - a • r ω - xs‖ ^ 2 / 2)) ≤
      B * (fy - fs) + ‖v - xs‖ ^ 2 / 2 -
        A / (2 * lam) * (𝔼 ω, ‖r ω‖ ^ 2) + A * err := by
  let ey := fun ω => fz ω - fy - ⟪r ω, z ω - y⟫
  let es := fun ω => fz ω - fs - ⟪r ω, z ω - xs⟫
  have hye : (𝔼 ω, ey ω) ≤ err := by
    dsimp [ey]
    rw [Finset.expect_sub_distrib]
    linarith
  have hse : (𝔼 ω, es ω) ≤ err := by
    dsimp [es]
    rw [Finset.expect_sub_distrib]
    linarith
  have hp (ω : Ω) := CappedProximalGeometry.potential_step
    (fz := fz ω) (errY := ey ω) (errS := es ω)
    hB ha hlam hA haA hx (hr ω) (by dsimp [ey]; linarith) (by dsimp [es]; linarith)
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) => hp ω)
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const] at ht
  have hy' := mul_le_mul_of_nonneg_left hye hB
  have hs' := mul_le_mul_of_nonneg_left hse ha
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const]
  rw [hA] at ht ⊢
  linarith

end LongTails.Proofs.CappedProximalSampling
