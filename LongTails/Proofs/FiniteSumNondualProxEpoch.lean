import LongTails.Proofs.FiniteSumNondualProxStep
import LongTails.Proofs.FiniteSumNondualProxVariance

open Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualProxEpoch

open FiniteSumNondualProxGeometry FiniteSumNondualProxStep FiniteSumNondualProxVariance
open RecursiveEnvelopeGeometry (Model)
open LongTails.Algorithms.FiniteSumNondualProx
open OracleTemplate.FiniteSum (expect_inner_left estimator_unbiased estimator fullGradient expect_tape_succ)
open LongTails.Setups.FiniteSumSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [NeZero n]

lemma mean_error_inner (g : Fin n × E → E) (z x u : E) :
    (𝔼 i, ⟪estimator g z x i - fullGradient g x, x - u⟫) = 0 := by
  rw [expect_inner_left]
  have he : (n : ℝ)⁻¹ • ∑ i, (estimator g z x i - fullGradient g x) = 0 := by
    rw [Finset.sum_sub_distrib, smul_sub, estimator_unbiased]
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_ne_zero.mpr (NeZero.ne n)]
  rw [he, inner_zero_left]

lemma expected_step {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x)))
    (hμ : 0 ≤ μ) (hη : 0 < η) (hηL : η * L ≤ 1 / 2)
    (c u z x : E) (hu : u ∈ C) (hz : z ∈ C) (hx : x ∈ C)
    (hmin : IsMinOn (regularized (objective f) μ c) C u) :
    let H := regularized (objective f) μ c
    let w := fun i => step C μ η c x (estimator g z x i)
    (𝔼 i, ‖w i - u‖ ^ 2) + 2 * η * (𝔼 i, H (w i) - H u) ≤
      ‖x - u‖ ^ 2 + 8 * η ^ 2 * L * ((H x - H u) + (H z - H u)) := by
  have hs := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    stochastic_step_bound hne hco hcv (OracleTemplate.ComponentEnvelope.finiteSum_model hm)
      hμ hη hηL c x (estimator g z x i) u hu)
  dsimp only at hs ⊢
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Fintype.expect_const, mean_error_inner, mul_zero, sub_zero] at hs
  have hv := estimator_variance hcv hm hμ c u z x hu hz hx hmin
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * η ^ 2 by positivity)
  nlinarith

omit [NeZero n] in
lemma innerRun_length (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c z x : E)
    (seed : List (Fin n)) : (innerRun g C μ η c z x seed).2.length = seed.length := by
  induction seed generalizing x with
  | nil => rfl
  | cons i tail ih => simp only [innerRun, List.length_cons, ih]

omit [NeZero n] in
lemma innerRun_mem {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (g : Fin n × E → E) (μ η : ℝ) (c z x : E) (hx : x ∈ C) (seed : List (Fin n)) :
    (innerRun g C μ η c z x seed).1 ∈ C ∧
      ∀ y ∈ (innerRun g C μ η c z x seed).2, y ∈ C := by
  induction seed generalizing x with
  | nil => simp [innerRun, hx]
  | cons i tail ih =>
    have hw := step_mem hne hco hcv μ η c x (estimator g z x i)
    have ht := ih _ hw
    simp only [innerRun, List.mem_cons]
    exact ⟨ht.1, fun y hy => hy.elim (fun he => he ▸ hw) (ht.2 y)⟩

lemma expected_run {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x)))
    (hμ : 0 ≤ μ) (hη : 0 < η) (hηL : η * L ≤ 1 / 2)
    (c u z : E) (hu : u ∈ C) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (objective f) μ c) C u) (m : ℕ) (x : E) (hx : x ∈ C) :
    let H := regularized (objective f) μ c
    let b := 8 * η ^ 2 * L
    (𝔼 seed : Fin m → Fin n,
      let r := innerRun g C μ η c z x (List.ofFn seed)
      ‖r.1 - u‖ ^ 2 + b * (H r.1 - H u) +
        (2 * η - b) * (r.2.map (fun y => H y - H u)).sum) ≤
      ‖x - u‖ ^ 2 + b * (H x - H u) + (m : ℝ) * b * (H z - H u) := by
  let H := regularized (objective f) μ c
  let b := 8 * η ^ 2 * L
  change (𝔼 seed : Fin m → Fin n,
    let r := innerRun g C μ η c z x (List.ofFn seed)
    ‖r.1 - u‖ ^ 2 + b * (H r.1 - H u) +
      (2 * η - b) * (r.2.map (fun y => H y - H u)).sum) ≤
    ‖x - u‖ ^ 2 + b * (H x - H u) + (m : ℝ) * b * (H z - H u)
  induction m generalizing x with
  | zero => simp [innerRun]
  | succ m ih =>
    rw [expect_tape_succ (fun seed =>
      let r := innerRun g C μ η c z x seed
      ‖r.1 - u‖ ^ 2 + b * (H r.1 - H u) +
        (2 * η - b) * (r.2.map (fun y => H y - H u)).sum)]
    simp only [innerRun, List.map_cons, List.sum_cons, mul_add, ← add_assoc]
    have ht := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      add_le_add_right (ih (step C μ η c x (estimator g z x i))
        (step_mem hne hco hcv μ η c x (estimator g z x i)))
          ((2 * η - b) * (H (step C μ η c x (estimator g z x i)) - H u)))
    have hs := expected_step hne hco hcv hm hμ hη hηL c u z x hu hz hx hmin
    change (𝔼 i, ‖step C μ η c x (estimator g z x i) - u‖ ^ 2) +
      2 * η * (𝔼 i, H (step C μ η c x (estimator g z x i)) - H u) ≤
      ‖x - u‖ ^ 2 + b * ((H x - H u) + (H z - H u)) at hs
    simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
      Fintype.expect_const, Nat.cast_add, Nat.cast_one] at ht hs ⊢
    nlinarith

omit [NeZero n] in
lemma list_average_mem {C : Set E} (hcv : Convex ℝ C) (xs : List E)
    (hne : xs.length ≠ 0) (hx : ∀ x ∈ xs, x ∈ C) : (xs.length : ℝ)⁻¹ • xs.sum ∈ C := by
  have hn : (xs.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne
  have hsum : ∑ _i : Fin xs.length, (xs.length : ℝ)⁻¹ = 1 := by simp [hn]
  have h := hcv.sum_mem (t := Finset.univ) (w := fun _ : Fin xs.length => (xs.length : ℝ)⁻¹)
    (z := xs.get) (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hsum
    (fun i _ => hx _ (xs.get_mem i))
  simpa only [← Finset.smul_sum, ← List.sum_ofFn, List.ofFn_get] using h

omit [NeZero n] in
lemma model_list_average {L : ℝ} {f : E → ℝ} {g : E → E} (hf : Model L f g)
    (u : E) (xs : List E) (hne : xs.length ≠ 0) :
    (xs.length : ℝ) * (f ((xs.length : ℝ)⁻¹ • xs.sum) - f u) ≤
      (xs.map (fun x => f x - f u)).sum := by
  have hs : ∀ (xs : List E) (a : E),
      ⟪g a, xs.sum - (xs.length : ℝ) • a⟫ ≤
        (xs.map (fun x => f x - f u)).sum - (xs.length : ℝ) * (f a - f u) := by
    intro xs a
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hh := hf.lower a x
      have he : x + xs.sum - ((xs.length : ℝ) + 1) • a =
          (x - a) + (xs.sum - (xs.length : ℝ) • a) := by module
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        List.map_cons, he, inner_add_right]
      linarith
  have h := hs xs ((xs.length : ℝ)⁻¹ • xs.sum)
  have hn : (xs.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne
  simp only [smul_smul, mul_inv_cancel₀ hn, one_smul, sub_self, inner_zero_right] at h
  linarith

lemma expected_epoch {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x)))
    (hμ : 0 ≤ μ) (hη : 0 < η) (hηL : η * L < 1 / 4)
    (c u z : E) (hu : u ∈ C) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (objective f) μ c) C u) {m : ℕ} (hmpos : 0 < m) :
    let H := regularized (objective f) μ c
    (2 * η - 8 * η ^ 2 * L) * (m : ℝ) *
      (𝔼 seed : Fin m → Fin n, H (epoch g C μ η c z (List.ofFn seed)) - H u) ≤
        ‖z - u‖ ^ 2 + ((m : ℝ) + 1) * (8 * η ^ 2 * L) * (H z - H u) := by
  let H := regularized (objective f) μ c
  let b := 8 * η ^ 2 * L
  have hb : 0 ≤ b := by dsimp [b]; positivity [(hm 0).pos]
  have ha : 0 ≤ 2 * η - b := by
    have hh := mul_lt_mul_of_pos_left hηL hη
    dsimp [b]
    nlinarith
  have ht := expected_run hne hco hcv hm hμ hη (by linarith) c u z hu hz hmin m z hz
  have hj := Finset.expect_le_expect (s := Finset.univ) (fun (seed : Fin m → Fin n) _ => show
    (2 * η - b) * (m : ℝ) * (H (epoch g C μ η c z (List.ofFn seed)) - H u) ≤
      let r := innerRun g C μ η c z z (List.ofFn seed)
      ‖r.1 - u‖ ^ 2 + b * (H r.1 - H u) +
        (2 * η - b) * (r.2.map (fun y => H y - H u)).sum from by
      let r := innerRun g C μ η c z z (List.ofFn seed)
      have hlen : r.2.length = m := by simp [r, innerRun_length]
      have hav := model_list_average
        (regularized_model (OracleTemplate.ComponentEnvelope.finiteSum_model hm) hμ c)
        u r.2 (by omega)
      rw [hlen] at hav
      have hmem := (innerRun_mem hne hco hcv g μ η c z z hz (List.ofFn seed)).1
      have hgap := hmin hmem
      change H u ≤ H r.1 at hgap
      have hmul := mul_le_mul_of_nonneg_left hav ha
      change (2 * η - b) * (m : ℝ) * (H (epoch g C μ η c z (List.ofFn seed)) - H u) ≤
        ‖r.1 - u‖ ^ 2 + b * (H r.1 - H u) +
          (2 * η - b) * (r.2.map (fun y => H y - H u)).sum
      simp only [epoch, List.length_ofFn]
      change (2 * η - b) * (m : ℝ) * (H ((m : ℝ)⁻¹ • r.2.sum) - H u) ≤ _
      change (2 * η - b) * ((m : ℝ) * (H ((m : ℝ)⁻¹ • r.2.sum) - H u)) ≤ _ at hmul
      nlinarith [sq_nonneg ‖r.1 - u‖, mul_nonneg hb (sub_nonneg.mpr hgap)])
  simp only [← Finset.mul_expect] at hj
  dsimp only at ht ⊢
  dsimp only [H, b] at hj
  simp only [Finset.expect_sub_distrib, Fintype.expect_const] at hj ht ⊢
  nlinarith

lemma epoch_contraction {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ η ρ : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x)))
    (hμ : 0 < μ) (hη : 0 < η) (hηL : η * L < 1 / 4)
    (c u z : E) (hu : u ∈ C) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (objective f) μ c) C u) {m : ℕ} (hmpos : 0 < m)
    (hcoeff : 2 + μ * ((m : ℝ) + 1) * (8 * η ^ 2 * L) ≤
      ρ * μ * (2 * η - 8 * η ^ 2 * L) * (m : ℝ)) :
    let H := regularized (objective f) μ c
    (𝔼 seed : Fin m → Fin n, H (epoch g C μ η c z (List.ofFn seed)) - H u) ≤
      ρ * (H z - H u) := by
  have ht := expected_epoch hne hco hcv hm hμ.le hη hηL c u z hu hz hmin hmpos
  have hd := exact_prox_lower hcv (OracleTemplate.ComponentEnvelope.finiteSum_model hm)
    hμ.le c u hu hmin z hz
  have hg := hmin hz
  change regularized (objective f) μ c u ≤ regularized (objective f) μ c z at hg
  have hmul := mul_le_mul_of_nonneg_left ht hμ.le
  have hcoef := mul_le_mul_of_nonneg_right hcoeff (sub_nonneg.mpr hg)
  have ha : 0 < 2 * η - 8 * η ^ 2 * L := by
    have hh := mul_lt_mul_of_pos_left hηL hη
    nlinarith
  have hp : 0 < μ * (2 * η - 8 * η ^ 2 * L) * (m : ℝ) :=
    mul_pos (mul_pos hμ ha) (Nat.cast_pos.mpr hmpos)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

lemma tuned_coefficient {L : ℝ} (hL : 0 < L) :
    2 + (L / n) * ((144 * n : ℕ) + 1 : ℝ) * (8 * (1 / (12 * L)) ^ 2 * L) ≤
      (3 / 4 : ℝ) * (L / n) * (2 * (1 / (12 * L)) - 8 * (1 / (12 * L)) ^ 2 * L) *
        (144 * n : ℕ) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  push_cast
  field_simp
  nlinarith

omit [NeZero n] in
lemma epoch_mem {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (g : Fin n × E → E) (μ η : ℝ) (c z : E) (hz : z ∈ C)
    (seed : List (Fin n)) (hseed : seed.length ≠ 0) : epoch g C μ η c z seed ∈ C := by
  have hlen := innerRun_length g C μ η c z z seed
  have hh := list_average_mem hcv (innerRun g C μ η c z z seed).2 (by omega)
    (innerRun_mem hne hco hcv g μ η c z z hz seed).2
  simpa only [hlen, epoch] using hh

lemma tuned_epoch_contraction {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x)))
    (c u z : E) (hu : u ∈ C) (hz : z ∈ C)
    (hmin : IsMinOn (regularized (objective f) (L / n) c) C u) :
    let H := regularized (objective f) (L / n) c
    (𝔼 seed : Fin (144 * n) → Fin n,
      H (epoch g C (L / n) (1 / (12 * L)) c z (List.ofFn seed)) - H u) ≤
      (3 / 4 : ℝ) * (H z - H u) := by
  have hL := (hm 0).pos
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  apply epoch_contraction hne hco hcv hm (div_pos hL hn) (by positivity)
    (show (1 / (12 * L)) * L < 1 / 4 by field_simp; nlinarith)
    c u z hu hz hmin (Nat.mul_pos (by norm_num) (NeZero.pos n)) (tuned_coefficient hL)

omit [NeZero n] in
lemma epochRun_mem {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (g : Fin n × E → E) (μ η : ℝ) (c : E) {m : ℕ} (hm : 0 < m)
    (s : ℕ) (z : E) (hz : z ∈ C) (seed : Fin s → Fin m → Fin n) :
    epochRun g C μ η c s z seed ∈ C := by
  induction s generalizing z with
  | zero => exact hz
  | succ s ih =>
    exact ih _ (epoch_mem hne hco hcv g μ η c z hz _ (by simp; omega)) _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero n] in
lemma expect_fin_succ {α : Type*} [Fintype α] {s : ℕ} (h : (Fin (s + 1) → α) → ℝ) :
    (𝔼 seed, h seed) = 𝔼 a, 𝔼 tail, h (Fin.cons a tail) := by
  rw [Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => α)).symm
    h (fun seed => h (Fin.cons seed.1 seed.2))]
  · exact Finset.expect_product Finset.univ Finset.univ _
  · intro seed
    change h seed = h (Fin.cons (seed 0) (fun j => seed j.succ))
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma tuned_run_contraction {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x)))
    (c u : E) (hu : u ∈ C)
    (hmin : IsMinOn (regularized (objective f) (L / n) c) C u)
    (s : ℕ) (z : E) (hz : z ∈ C) :
    let H := regularized (objective f) (L / n) c
    (𝔼 seed : Fin s → Fin (144 * n) → Fin n,
      H (epochRun g C (L / n) (1 / (12 * L)) c s z seed) - H u) ≤
      (3 / 4 : ℝ) ^ s * (H z - H u) := by
  let H := regularized (objective f) (L / n) c
  change (𝔼 seed : Fin s → Fin (144 * n) → Fin n,
    H (epochRun g C (L / n) (1 / (12 * L)) c s z seed) - H u) ≤
    (3 / 4 : ℝ) ^ s * (H z - H u)
  induction s generalizing z with
  | zero => simp [epochRun]
  | succ s ih =>
    rw [expect_fin_succ]
    simp only [epochRun, Fin.cons_zero, Fin.cons_succ]
    have ht := Finset.expect_le_expect (s := Finset.univ)
      (fun (seed : Fin (144 * n) → Fin n) _ => ih
        (epoch g C (L / n) (1 / (12 * L)) c z (List.ofFn seed))
        (epoch_mem hne hco hcv g (L / n) (1 / (12 * L)) c z hz (List.ofFn seed) (by
          simpa using Nat.ne_of_gt (Nat.mul_pos (by decide : 0 < 144) (NeZero.pos n)))))
    have he := tuned_epoch_contraction hne hco hcv hm c u z hu hz hmin
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ (3 / 4 : ℝ) ^ s by positivity)
    simp only [← Finset.mul_expect, Finset.expect_sub_distrib, Fintype.expect_const] at ht
    change (3 / 4 : ℝ) ^ s *
      (𝔼 seed : Fin (144 * n) → Fin n,
        H (epoch g C (L / n) (1 / (12 * L)) c z (List.ofFn seed)) - H u) ≤
      (3 / 4 : ℝ) ^ s * ((3 / 4 : ℝ) * (H z - H u)) at hh
    simpa only [pow_succ, mul_assoc] using ht.trans hh

end LongTails.Proofs.FiniteSumNondualProxEpoch
