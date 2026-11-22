import LongTails.Setups.BroxGeneralNormConstrainedPL
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open Set

namespace OracleTemplate.WarmHalvingBrox

open LongTails.Setups.BroxGeneralNormConstrainedPL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadratic_bound {f : E → ℝ} {C : Set E} {L : ℝ} (hC : Convex ℝ C)
    (hd : ∀ x ∈ C, DifferentiableAt ℝ f x)
    (hL : ∀ x ∈ C, ∀ y ∈ C, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    |f y - f x - fderiv ℝ f x (y - x)| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ C := fun t ht => hC.add_smul_sub_mem hx hy ht
  let g : ℝ → ℝ := fun t => f (x + t • v) - f x - t * fderiv ℝ f x v
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (x + t • v) v - fderiv ℝ f x v
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) :=
      (hd _ (hpt t ht)).hasFDerivAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt (fun s : ℝ => s * fderiv ℝ f x v) (fderiv ℝ f x v) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ f x v)
    exact (h3.sub_const (f x)).sub h4
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖g' t‖ ≤ L * ‖v‖ ^ 2 * t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hlip := hL x hx _ (hpt t ht')
    have hsub : x + t • v - x = t • v := by abel
    rw [hsub, norm_smul, Real.norm_of_nonneg ht.1] at hlip
    have hop : ‖(fderiv ℝ f (x + t • v) - fderiv ℝ f x) v‖ ≤
        ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    have hnv := norm_nonneg v
    calc ‖g' t‖ = ‖(fderiv ℝ f (x + t • v) - fderiv ℝ f x) v‖ := by
          simp [g']
      _ ≤ ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ * ‖v‖ := hop
      _ ≤ L * (t * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hlip hnv
      _ = L * ‖v‖ ^ 2 * t := by ring
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hB : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => L * ‖v‖ ^ 2 / 2 * s ^ 2) (L * ‖v‖ ^ 2 * t) (Ici t) t := by
    intro t _
    have := ((hasDerivAt_pow 2 t).const_mul (L * ‖v‖ ^ 2 / 2)).hasDerivWithinAt (s := Ici t)
    convert this using 1
    push_cast
    ring
  have hfinal := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hcont
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun s : ℝ => L * ‖v‖ ^ 2 / 2 * s ^ 2) (by simp [g])
    (by fun_prop) hB hbound (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hfin2 : |f (x + (1 : ℝ) • v) - f x - 1 * fderiv ℝ f x v| ≤ L * ‖v‖ ^ 2 / 2 * 1 ^ 2 := by
    simpa only [g, Real.norm_eq_abs] using hfinal
  rw [one_smul, one_mul, one_pow, mul_one, show x + v = y by simp [v]] at hfin2
  linarith

lemma lmo_slope {g : E →L[ℝ] ℝ} {C : Set E} (hC : Convex ℝ C) {x q : E} {r : ℝ}
    (hx : x ∈ C) (hr : 0 < r) (hqr : ‖q - x‖ ≤ r)
    (hopt : ∀ z ∈ C, ‖z - x‖ ≤ r → g q ≤ g z) {z : E} (hz : z ∈ C) :
    r * (-g (z - q)) ≤ -g (q - x) * ‖z - q‖ := by
  set a := ‖z - q‖
  have ha : 0 ≤ a := norm_nonneg _
  set β := r / (r + a)
  have hra : 0 < r + a := by linarith
  have hβ0 : 0 ≤ β := div_nonneg hr.le hra.le
  have hβ1 : β ≤ 1 := (div_le_one hra).2 (by linarith)
  have hu : x + β • (z - x) ∈ C := hC.add_smul_sub_mem hx hz ⟨hβ0, hβ1⟩
  have hux : ‖x + β • (z - x) - x‖ ≤ r := by
    have h1 : x + β • (z - x) - x = β • (z - x) := by abel
    rw [h1, norm_smul, Real.norm_of_nonneg hβ0]
    have h2 : ‖z - x‖ ≤ a + r := by
      calc ‖z - x‖ = ‖(z - q) + (q - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - q‖ + ‖q - x‖ := norm_add_le _ _
        _ ≤ a + r := by linarith
    calc β * ‖z - x‖ ≤ β * (a + r) := mul_le_mul_of_nonneg_left h2 hβ0
      _ = r := by
        simp only [β]
        field_simp
        ring
  have h := hopt _ hu hux
  have hlin : g (x + β • (z - x)) = g x + β * (g (z - q) + g (q - x)) := by
    rw [map_add, map_smul, smul_eq_mul, ← map_add, sub_add_sub_cancel]
  rw [hlin] at h
  have hgq : g q = g x + g (q - x) := by rw [map_sub]; ring
  rw [hgq] at h
  have hβr : β * (r + a) = r := by
    simp only [β]
    field_simp
  have h' : g (q - x) ≤ β * (g (z - q) + g (q - x)) := by linarith
  have h3 : (r + a) * g (q - x) ≤ (r + a) * (β * (g (z - q) + g (q - x))) :=
    mul_le_mul_of_nonneg_left h' hra.le
  have h4 : (r + a) * (β * (g (z - q) + g (q - x))) = r * (g (z - q) + g (q - x)) := by
    rw [← mul_assoc, mul_comm (r + a) β, hβr]
  nlinarith [h3, h4]

lemma normal_cone_approx {C : Set E} (hC : Convex ℝ C) {q : E} (hq : q ∈ C)
    (φ : E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ z ∈ C, φ (z - q) ≤ M * ‖z - q‖) :
    ∃ n ∈ normalCone C q, ‖φ - n‖ ≤ M := by
  let K : Set E := {k | ∃ t : ℝ, 0 ≤ t ∧ ∃ z ∈ C, k = t • (z - q)}
  have hK0 : (0 : E) ∈ K := ⟨0, le_rfl, q, hq, by simp⟩
  have hKsmul : ∀ c : ℝ, 0 < c → ∀ k ∈ K, c • k ∈ K := by
    rintro c hc k ⟨t, ht, z, hz, rfl⟩
    exact ⟨c * t, mul_nonneg hc.le ht, z, hz, by rw [smul_smul]⟩
  have hKadd : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ + k₂ ∈ K := by
    rintro k₁ ⟨t₁, ht₁, z₁, hz₁, rfl⟩ k₂ ⟨t₂, ht₂, z₂, hz₂, rfl⟩
    rcases eq_or_lt_of_le (add_nonneg ht₁ ht₂) with h0 | hpos
    · have h1 : t₁ = 0 := by linarith
      have h2 : t₂ = 0 := by linarith
      exact ⟨0, le_rfl, q, hq, by simp [h1, h2]⟩
    · refine ⟨t₁ + t₂, hpos.le, (t₁ / (t₁ + t₂)) • z₁ + (t₂ / (t₁ + t₂)) • z₂,
        hC hz₁ hz₂ (div_nonneg ht₁ hpos.le) (div_nonneg ht₂ hpos.le) (by field_simp), ?_⟩
      have hne : t₁ + t₂ ≠ 0 := hpos.ne'
      have e1 : (t₁ + t₂) * (t₁ / (t₁ + t₂)) = t₁ := by field_simp
      have e2 : (t₁ + t₂) * (t₂ / (t₁ + t₂)) = t₂ := by field_simp
      rw [smul_sub (t₁ + t₂) _ q, smul_add, smul_smul, smul_smul, e1, e2, add_smul t₁ t₂ q,
        smul_sub t₁ z₁ q, smul_sub t₂ z₂ q]
      abel
  have hφK : ∀ k ∈ K, φ k ≤ M * ‖k‖ := by
    rintro k ⟨t, ht, z, hz, rfl⟩
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg ht]
    have := h z hz
    nlinarith
  let N : E → ℝ := fun v => ⨅ k : K, (M * ‖v + (k : E)‖ - φ (k : E))
  have hlow : ∀ v, ∀ k ∈ K, -(M * ‖v‖) ≤ M * ‖v + k‖ - φ k := by
    intro v k hk
    have h1 := hφK k hk
    have h2 : ‖k‖ ≤ ‖v + k‖ + ‖v‖ := by
      calc ‖k‖ = ‖(v + k) - v‖ := by abel_nf
        _ ≤ ‖v + k‖ + ‖v‖ := norm_sub_le _ _
    nlinarith
  have hbdd : ∀ v, BddBelow (Set.range fun k : K => M * ‖v + (k : E)‖ - φ (k : E)) := by
    intro v
    refine ⟨-(M * ‖v‖), ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hlow v k k.2
  have : Nonempty K := ⟨⟨0, hK0⟩⟩
  have hNle : ∀ v, ∀ k ∈ K, N v ≤ M * ‖v + k‖ - φ k := fun v k hk =>
    ciInf_le (hbdd v) ⟨k, hk⟩
  have hNge : ∀ v b, (∀ k ∈ K, b ≤ M * ‖v + k‖ - φ k) → b ≤ N v := fun v b hb =>
    le_ciInf fun k => hb k k.2
  have N_hom : ∀ c : ℝ, 0 < c → ∀ v, N (c • v) = c * N v := by
    intro c hc v
    apply le_antisymm
    · have : N (c • v) / c ≤ N v := by
        apply hNge
        intro k hk
        rw [div_le_iff₀ hc]
        have := hNle (c • v) (c • k) (hKsmul c hc k hk)
        rw [← smul_add, norm_smul, Real.norm_of_nonneg hc.le, map_smul, smul_eq_mul] at this
        nlinarith
      rw [div_le_iff₀ hc] at this
      linarith
    · have : c * N v ≤ N (c • v) := by
        apply hNge
        intro k hk
        have hk' : c⁻¹ • k ∈ K := hKsmul c⁻¹ (inv_pos.2 hc) k hk
        have h2 := hNle v (c⁻¹ • k) hk'
        have hck : c • v + k = c • (v + c⁻¹ • k) := by
          rw [smul_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
        have hφ : φ k = c * φ (c⁻¹ • k) := by
          rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
        rw [hck, norm_smul, Real.norm_of_nonneg hc.le, hφ]
        nlinarith
      linarith
  have N_add : ∀ v w, N (v + w) ≤ N v + N w := by
    intro v w
    have h1 : ∀ k₂ ∈ K, N (v + w) - (M * ‖w + k₂‖ - φ k₂) ≤ N v := by
      intro k₂ hk₂
      apply hNge
      intro k₁ hk₁
      have := hNle (v + w) (k₁ + k₂) (hKadd k₁ hk₁ k₂ hk₂)
      have htri : ‖v + w + (k₁ + k₂)‖ ≤ ‖v + k₁‖ + ‖w + k₂‖ := by
        calc ‖v + w + (k₁ + k₂)‖ = ‖(v + k₁) + (w + k₂)‖ := by abel_nf
          _ ≤ ‖v + k₁‖ + ‖w + k₂‖ := norm_add_le _ _
      rw [map_add] at this
      nlinarith
    have h2 : N (v + w) - N v ≤ N w := by
      apply hNge
      intro k₂ hk₂
      have := h1 k₂ hk₂
      linarith
    linarith
  let f0 : E →ₗ.[ℝ] ℝ := ⟨⊥, 0⟩
  have hf0 : ∀ x : f0.domain, f0 x ≤ N x := by
    rintro ⟨x, hx⟩
    have hx0 : x = 0 := (Submodule.mem_bot ℝ).1 hx
    subst hx0
    change (0 : ℝ) ≤ N 0
    apply hNge
    intro k hk
    have := hφK k hk
    simp only [zero_add]
    linarith
  obtain ⟨ψ, -, hψ⟩ := exists_extension_of_le_sublinear f0 N N_hom N_add hf0
  have hψup : ∀ v, ψ v ≤ M * ‖v‖ := by
    intro v
    have := hNle v 0 hK0
    simp only [add_zero, map_zero, sub_zero] at this
    exact (hψ v).trans this
  have hψnorm : ∀ v, ‖ψ v‖ ≤ M * ‖v‖ := by
    intro v
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, hψup v⟩
    have := hψup (-v)
    rw [map_neg, norm_neg] at this
    linarith
  have hψK : ∀ k ∈ K, φ k ≤ ψ k := by
    intro k hk
    have h1 := hψ (-k)
    have h2 := hNle (-k) k hk
    simp only [neg_add_cancel, norm_zero, mul_zero, zero_sub] at h2
    rw [map_neg] at h1
    linarith
  let ψc : E →L[ℝ] ℝ := ψ.mkContinuous M hψnorm
  refine ⟨φ - ψc, ?_, ?_⟩
  · intro z hz
    have hk : z - q ∈ K := ⟨1, zero_le_one, z, hz, by simp⟩
    have := hψK _ hk
    simp only [sub_apply, ψc, LinearMap.mkContinuous_apply]
    linarith
  · rw [sub_sub_cancel]
    exact LinearMap.mkContinuous_norm_le ψ hM hψnorm

lemma stationarity_le {f : E → ℝ} {C : Set E} {x : E} {n : E →L[ℝ] ℝ}
    (hn : n ∈ normalCone C x) : stationarity f C x ≤ ‖fderiv ℝ f x + n‖ :=
  csInf_le ⟨0, by rintro _ ⟨m, -, rfl⟩; exact norm_nonneg _⟩ ⟨n, hn, rfl⟩

lemma stationarity_nonneg (f : E → ℝ) (C : Set E) (x : E) : 0 ≤ stationarity f C x := by
  have hne : ((fun n => ‖fderiv ℝ f x + n‖) '' normalCone C x).Nonempty :=
    ⟨_, 0, fun z _ => by simp, rfl⟩
  exact le_csInf hne (by rintro _ ⟨m, -, rfl⟩; exact norm_nonneg _)

lemma certificate {f : E → ℝ} {C : Set E} {L : ℝ} (hC : Convex ℝ C) (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ C, ∀ y ∈ C, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖)
    {x q : E} {r : ℝ} (hx : x ∈ C) (hq : q ∈ C) (hr : 0 < r) (hqr : ‖q - x‖ ≤ r)
    (hopt : ∀ z ∈ C, ‖z - x‖ ≤ r → fderiv ℝ f x q ≤ fderiv ℝ f x z) :
    stationarity f C q ≤ L * r + -fderiv ℝ f x (q - x) / r := by
  set g := fderiv ℝ f x
  have hd : 0 ≤ -g (q - x) := by
    have := hopt x hx (by simp; exact hr.le)
    rw [map_sub]
    linarith
  have hM : 0 ≤ -g (q - x) / r := div_nonneg hd hr.le
  obtain ⟨n, hn, hnorm⟩ := normal_cone_approx hC hq (-g) hM (by
    intro z hz
    have := lmo_slope hC hx hr hqr hopt hz
    rw [neg_apply, div_mul_eq_mul_div, le_div_iff₀ hr]
    linarith)
  have hLq := hL x hx q hq
  calc stationarity f C q ≤ ‖fderiv ℝ f q + n‖ := stationarity_le hn
    _ = ‖(fderiv ℝ f q - g) - (-g - n)‖ := by congr 1; abel
    _ ≤ ‖fderiv ℝ f q - g‖ + ‖-g - n‖ := norm_sub_le _ _
    _ ≤ L * ‖q - x‖ + -g (q - x) / r := add_le_add hLq hnorm
    _ ≤ L * r + -g (q - x) / r := by gcongr

lemma stationary_of_zero {f : E → ℝ} {C : Set E} (hC : Convex ℝ C)
    {x q : E} {r : ℝ} (hx : x ∈ C) (hr : 0 < r) (hqr : ‖q - x‖ ≤ r)
    (hopt : ∀ z ∈ C, ‖z - x‖ ≤ r → fderiv ℝ f x q ≤ fderiv ℝ f x z)
    (hzero : fderiv ℝ f x (q - x) = 0) : stationarity f C x ≤ 0 := by
  have hn : -fderiv ℝ f x ∈ normalCone C x := by
    intro z hz
    have h1 := lmo_slope hC hx hr hqr hopt hz
    rw [hzero, neg_zero, zero_mul] at h1
    have h2 : fderiv ℝ f x (z - x) = fderiv ℝ f x (z - q) + fderiv ℝ f x (q - x) := by
      rw [← map_add, sub_add_sub_cancel]
    rw [neg_apply, h2, hzero]
    nlinarith
  have := stationarity_le (f := f) hn
  simpa using this

end OracleTemplate.WarmHalvingBrox
