import LongTails.Proofs.RecoveryFractalLocal

namespace LongTails.Proofs.RecoveryFractalEnergy

open scoped RealInnerProductSpace
open LongTails.Proofs.AdaptiveSilverSplit

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

noncomputable def maskEnergy (Q H : E →L[ℝ] E) (g d : E) : ℝ :=
  ⟪g, Q d⟫ + ⟪Q d, H (Q d)⟫ / 2

lemma mask_energy_difference (Q H : E →L[ℝ] E)
    (hidem : ∀ v, Q (Q v) = Q v)
    (hself : ∀ u v, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hcomm : ∀ v, H (Q v) = Q (H v))
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (g d e : E) :
    maskEnergy Q H g d ≤ maskEnergy Q H g e +
      (‖Q (g + H d)‖ + ‖Q (g + H e)‖) / 2 * ‖Q (d - e)‖ := by
  let δ := Q (d - e)
  let v := Q e
  have hd : Q d = v + δ := by dsimp [v, δ]; rw [map_sub]; abel
  have hδ : Q δ = δ := hidem (d - e)
  have hge : Q (g + H e) = Q g + H v := by
    rw [map_add, ← hcomm]
  have hgd : Q (g + H d) = Q (g + H e) + H δ := by
    rw [map_add, ← hcomm, hd, map_add, hge]
    abel
  have hlin : ⟪g, δ⟫ + ⟪δ, H v⟫ = ⟪δ, Q (g + H e)⟫ := by
    rw [hge, inner_add_right, ← hself δ g, hδ, real_inner_comm δ g]
  have hcross : ⟪v, H δ⟫ = ⟪δ, H v⟫ := by
    rw [← hsym v δ]
    exact real_inner_comm _ _
  have heq : maskEnergy Q H g d - maskEnergy Q H g e =
      ⟪δ, Q (g + H d) + Q (g + H e)⟫ / 2 := by
    unfold maskEnergy
    rw [hd]
    change (⟪g, v + δ⟫ + ⟪v + δ, H (v + δ)⟫ / 2) -
      (⟪g, v⟫ + ⟪v, H v⟫ / 2) = _
    rw [hgd, map_add]
    simp only [inner_add_left, inner_add_right]
    rw [hcross]
    linarith [hlin]
  have hn := norm_add_le (Q (g + H d)) (Q (g + H e))
  have hi := real_inner_le_norm δ (Q (g + H d) + Q (g + H e))
  have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg δ)
  change maskEnergy Q H g d ≤ maskEnergy Q H g e +
    (‖Q (g + H d)‖ + ‖Q (g + H e)‖) / 2 * ‖δ‖
  nlinarith [heq]

lemma mask_energy_shift (Q H : E →L[ℝ] E)
    (hidem : ∀ v, Q (Q v) = Q v)
    (hself : ∀ u v, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hcomm : ∀ v, H (Q v) = Q (H v))
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (g d y : E) :
    maskEnergy Q H g (d + y) - maskEnergy Q H g d =
      maskEnergy Q H (g + H d) y := by
  have hcross : ⟪Q d, H (Q y)⟫ = ⟪H d, Q y⟫ := by
    rw [← hsym, hcomm, hself, hidem]
  have hcross' : ⟪Q y, H (Q d)⟫ = ⟪H d, Q y⟫ := by
    rw [real_inner_comm, hcomm, hself, hidem]
  unfold maskEnergy
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hcross, hcross']
  ring

lemma mask_idem (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ)
    (hc : ∀ j, c j * c j = c j) (v : E) : proj b c (proj b c v) = proj b c v := by
  apply eq_of_coords b
  intro j
  rw [proj_coord, proj_coord, ← mul_assoc, hc]

lemma mask_self (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (u v : E) :
    ⟪proj b c u, v⟫ = ⟪u, proj b c v⟫ := by
  rw [inner_coords b, inner_coords b u]
  exact Finset.sum_congr rfl (fun i _ => by rw [proj_coord, proj_coord]; ring)

lemma mask_comm (b : OrthonormalBasis ι ℝ E) (c eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (v : E) :
    H (proj b c v) = proj b c (H v) := by
  apply eq_of_coords b
  intro j
  rw [hc, proj_coord, proj_coord, hc]
  ring

lemma mask_norm_le (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ)
    (hc : ∀ j, |c j| ≤ 1) (v : E) : ‖proj b c v‖ ≤ ‖v‖ := by
  have h : ‖proj b c v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_coords b, norm_sq_coords b v]
    apply Finset.sum_le_sum
    intro j _
    rw [proj_coord, mul_pow]
    have hs : c j ^ 2 ≤ 1 := by nlinarith [sq_abs (c j), hc j, abs_nonneg (c j)]
    nlinarith [sq_nonneg ⟪b j, v⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h


open OracleTemplate.ScheduleBlock OracleTemplate.FractalChebyshev

lemma stable_filter_relation (a : ℕ → ℝ) (lam : ℝ) (hl : 0 ≤ lam) (n : ℕ)
    (ha : ∀ i < n, 0 ≤ a i) (hfac : ∀ i < n, 0 ≤ 1 - a i * lam) :
    (1 + 2 * lam * ssum a n) * pr a lam n ^ 2 ≤ 1 := by
  have hS : 0 ≤ ssum a n := Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
  obtain ⟨hp0, hp⟩ := pr_le_exp n hfac
  have hp2 : pr a lam n ^ 2 ≤ Real.exp (-(2 * lam * ssum a n)) := by
    calc
      _ ≤ Real.exp (-(lam * ssum a n)) ^ 2 := pow_le_pow_left₀ hp0 hp 2
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have he := Real.add_one_le_exp (2 * lam * ssum a n)
  calc
    _ ≤ (1 + 2 * lam * ssum a n) * Real.exp (-(2 * lam * ssum a n)) :=
      mul_le_mul_of_nonneg_left hp2 (by positivity)
    _ ≤ Real.exp (2 * lam * ssum a n) * Real.exp (-(2 * lam * ssum a n)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma low_ideal_drop (a : ℕ → ℝ) (μ lam : ℝ) (hμ : 0 < μ) (hl0 : 0 ≤ lam)
    (hlμ : lam ≤ μ) (n : ℕ) (ha : ∀ i < n, 0 ≤ a i)
    (hcap : ∀ i < n, a i ≤ 1 / μ) (hS : 1 / (2 * μ) ≤ ssum a n) :
    1 / (4 * μ) ≤ resp a lam n - lam * resp a lam n ^ 2 / 2 := by
  have hS0 : 0 ≤ ssum a n := Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
  rcases eq_or_lt_of_le hl0 with he | hl
  · rw [← he, resp_zero]
    have hdiv : 1 / (4 * μ) ≤ 1 / (2 * μ) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    simpa using hdiv.trans hS
  · have hfac (i : ℕ) (hi : i < n) : 0 ≤ 1 - a i * lam := by
      have hh := mul_le_mul (hcap i hi) hlμ hl0 (by positivity : 0 ≤ 1 / μ)
      rw [one_div_mul_cancel hμ.ne'] at hh
      linarith
    have hrel := stable_filter_relation a lam hl0 n ha hfac
    have hid := lam_mul_resp a lam n
    have hsquare := congrArg (fun x : ℝ => x ^ 2) hid
    let D := resp a lam n - lam * resp a lam n ^ 2 / 2
    have hid2 : 2 * lam * D = 1 - pr a lam n ^ 2 := by
      dsimp [D]
      nlinarith [hsquare]
    have hf : 0 < 1 + 2 * lam * ssum a n := by positivity
    have hD : ssum a n ≤ D * (1 + 2 * lam * ssum a n) := by
      apply (mul_le_mul_iff_right₀ (show 0 < 2 * lam by positivity)).mp
      have heq := congrArg (fun x : ℝ => (1 + 2 * lam * ssum a n) * x) hid2
      nlinarith only [heq, hrel]
    have hratio : ssum a n / (1 + 2 * lam * ssum a n) ≤ D :=
      (div_le_iff₀ hf).mpr hD
    have hs : 1 ≤ ssum a n * (2 * μ) := (div_le_iff₀ (by positivity)).mp hS
    have hls := mul_le_mul_of_nonneg_right hlμ hS0
    have hlow : 1 / (4 * μ) ≤ ssum a n / (1 + 2 * lam * ssum a n) := by
      rw [div_le_div_iff₀ (by positivity) hf]
      nlinarith only [hs, hls]
    exact hlow.trans hratio

open LongTails.Proofs.RecoveryFractalLocal

lemma low_mask_ideal_energy (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (μ : ℝ) (hμ : 0 < μ) (a : ℕ → ℝ) (g : E) (n : ℕ)
    (ha : ∀ i < n, 0 ≤ a i) (hcap : ∀ i < n, a i ≤ 1 / μ)
    (hS : 1 / (2 * μ) ≤ ssum a n) :
    let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
    maskEnergy (proj b c) H g (idealDisplacement b eig a g n) ≤
      -(‖proj b c g‖ ^ 2) / (4 * μ) := by
  dsimp only
  unfold maskEnergy
  rw [inner_coords b, inner_coords b, norm_sq_coords b, Finset.sum_div,
    ← Finset.sum_add_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  simp only [proj_coord, hc, idealDisplacement]
  by_cases hj : 0 ≤ eig j ∧ eig j ≤ μ
  · simp only [hj, and_self, ite_true, one_mul]
    have hh := low_ideal_drop a μ (eig j) hμ hj.1 hj.2 n ha hcap hS
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ⟪b j, g⟫)
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]
  · simp [hj]



open scoped RealInnerProductSpace
open LongTails.Proofs.AdaptiveSilverSplit LongTails.Proofs.GdSnapshotDynamics
open OracleTemplate.ScheduleBlock



lemma mask_forcing_error (b : OrthonormalBasis ι ℝ E) (c eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hmask : ∀ j, c j = 0 ∨ c j = 1) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u e : ℕ → E) (n : ℕ) (h0 : u 0 = 0)
    (hu : ∀ i < n, u (i + 1) = u i - a i • H (u i) + a i • e i)
    (hwin : ∀ j, c j = 1 → ∀ i < n, |win a (eig j) (i + 1) n| ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (he : ∀ i < n, ‖e i‖ ≤ B) :
    ‖proj b c (u n)‖ ≤ ssum a n * B := by
  have hcoord (j : ι) : ⟪b j, u n⟫ = errResp a (eig j) (fun i => ⟪b j, e i⟫) n := by
    have hh := scalar_forced_solution_prefix a (fun i => ⟪b j, u i⟫)
      (fun i => ⟪b j, e i⟫) (eig j) n (fun i hi => by
        rw [hu i hi]
        simp only [inner_add_right, inner_sub_right, inner_smul_right, hc]
        ring)
    simpa [h0] using hh
  have hbound (j : ι) : |⟪b j, proj b c (u n)⟫| ≤
      wsum a (fun i => b.repr (e i) j) n := by
    rw [proj_coord]
    rcases hmask j with hj | hj
    · simp only [hj, zero_mul, abs_zero]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (abs_nonneg _))
    · rw [hj, one_mul, hcoord]
      have hh := errResp_pos_le ha (fun i => ⟪b j, e i⟫) n (hwin j hj)
      simpa [wsum, OrthonormalBasis.repr_apply_apply] using hh
  have hs : ‖proj b c (u n)‖ ^ 2 ≤ (ssum a n * B) ^ 2 := by
    rw [norm_sq_coords b]
    calc
      _ ≤ ∑ j, wsum a (fun i => b.repr (e i) j) n ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa using pow_le_pow_left₀ (abs_nonneg _) (hbound j) 2
      _ ≤ ssum a n ^ 2 * B ^ 2 := wsum_sq_sum b a ha e n he
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (Finset.sum_nonneg fun i _ => ha i) hB)).mp hs



open OracleTemplate.ScheduleBlock


lemma stable_window_bound (a : ℕ → ℝ) (μ lam : ℝ) (hμ : 0 < μ)
    (hl0 : 0 ≤ lam) (hlμ : lam ≤ μ) (s t : ℕ)
    (ha : ∀ i < t, 0 ≤ a i) (hcap : ∀ i < t, a i ≤ 1 / μ) :
    |win a lam s t| ≤ 1 := by
  unfold win
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    exact abs_nonneg _
  · intro i hi
    have hit := (Finset.mem_Ico.mp hi).2
    have hh := mul_le_mul (hcap i hit) hlμ hl0 (by positivity : 0 ≤ 1 / μ)
    rw [one_div_mul_cancel hμ.ne'] at hh
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - a i * lam)]
    linarith [mul_nonneg (ha i hit) hl0]

lemma low_displacement_error (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (μ : ℝ) (hμ : 0 < μ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (g : E) (d e : ℕ → E) (n : ℕ) (h0 : d 0 = 0)
    (hd : ∀ i < n, d (i + 1) = d i - a i • (g + H (d i) + e i))
    (hcap : ∀ i < n, a i ≤ 1 / μ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ i < n, ‖e i‖ ≤ B) :
    let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
    ‖proj b c (d n - idealDisplacement b eig a g n)‖ ≤ ssum a n * B := by
  let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
  let u := fun i => d i - idealDisplacement b eig a g i
  apply mask_forcing_error b c eig H hc
    (fun j => by by_cases hj : 0 ≤ eig j ∧ eig j ≤ μ <;> simp [c, hj]) a ha
    u (fun i => -e i) n
  · simp [u, h0, idealDisplacement_zero]
  · intro i hi
    dsimp [u]
    rw [hd i hi, idealDisplacement_succ b eig H hc]
    simp only [map_sub]
    module
  · intro j hj i hi
    have hmem : 0 ≤ eig j ∧ eig j ≤ μ := by
      by_contra hn
      simp [c, hn] at hj
    exact stable_window_bound a μ (eig j) hμ hmem.1 hmem.2 (i + 1) n
      (fun i _ => ha i) hcap
  · exact hB
  · intro i hi
    simpa using he i hi

lemma mask_ideal_gradient (b : OrthonormalBasis ι ℝ E) (c eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (a : ℕ → ℝ) (g : E) (n : ℕ) :
    proj b c (g + H (idealDisplacement b eig a g n)) =
      proj b (fun j => c j * pr a (eig j) n) g := by
  apply eq_of_coords b
  intro j
  simp only [proj_coord, inner_add_right, hc, idealDisplacement]
  have hh := lam_mul_resp a (eig j) n
  linear_combination -(c j * ⟪b j, g⟫) * hh

lemma mask_ideal_gradient_norm (b : OrthonormalBasis ι ℝ E) (c eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (a : ℕ → ℝ) (g : E) (n : ℕ)
    (hp : ∀ j, c j ≠ 0 → |pr a (eig j) n| ≤ 1) :
    ‖proj b c (g + H (idealDisplacement b eig a g n))‖ ≤ ‖proj b c g‖ := by
  rw [mask_ideal_gradient b c eig H hc]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_coords b, norm_sq_coords b]
  apply Finset.sum_le_sum
  intro j _
  simp only [proj_coord]
  by_cases hj : c j = 0
  · simp [hj]
  · have hh : pr a (eig j) n ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) (hp j hj) 2
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (c j * ⟪b j, g⟫))
    nlinarith [hm]

lemma low_epoch_energy (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (μ : ℝ) (hμ : 0 < μ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (g : E) (d e : ℕ → E) (n : ℕ) (h0 : d 0 = 0)
    (hd : ∀ i < n, d (i + 1) = d i - a i • (g + H (d i) + e i))
    (hcap : ∀ i < n, a i ≤ 1 / μ) (hS : 1 / (2 * μ) ≤ ssum a n)
    (B : ℝ) (hB : 0 ≤ B) (he : ∀ i < n, ‖e i‖ ≤ B) (A : ℝ)
    (hA : ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0)
      (g + H (d n))‖ ≤ A) :
    let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
    maskEnergy (proj b c) H g (d n) ≤ -(‖proj b c g‖ ^ 2) / (4 * μ) +
      (A + ‖proj b c g‖) / 2 * (ssum a n * B) := by
  let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
  let y := idealDisplacement b eig a g n
  have hid : ∀ j, c j * c j = c j := by
    intro j
    by_cases hj : 0 ≤ eig j ∧ eig j ≤ μ <;> simp [c, hj]
  have hdiff := mask_energy_difference (proj b c) H (mask_idem b c hid)
    (mask_self b c) (mask_comm b c eig H hc) hsym g (d n) y
  have herr := low_displacement_error b eig H hc μ hμ a ha g d e n h0 hd hcap B hB he
  have hideal := low_mask_ideal_energy b eig H hc μ hμ a g n
    (fun i _ => ha i) hcap hS
  have hn := mask_ideal_gradient_norm b c eig H hc a g n (fun j hj => by
    have hmem : 0 ≤ eig j ∧ eig j ≤ μ := by
      by_contra hh
      simp [c, hh] at hj
    exact stable_window_bound a μ (eig j) hμ hmem.1 hmem.2 0 n (fun i _ => ha i) hcap)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hp := mul_le_mul (show (‖proj b c (g + H (d n))‖ +
      ‖proj b c (g + H y)‖) / 2 ≤ (A + ‖proj b c g‖) / 2 by linarith)
    herr (norm_nonneg _) (by positivity : 0 ≤ (A + ‖proj b c g‖) / 2)
  change maskEnergy (proj b c) H g (d n) ≤ _
  linarith

lemma low_two_epoch_energy (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (μ : ℝ) (hμ : 0 < μ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (g : E) (d e : ℕ → E) (n : ℕ) (h0 : d 0 = 0)
    (hd : ∀ i < 2 * n, d (i + 1) = d i - a i • (g + H (d i) + e i))
    (hperiod : ∀ i < n, a (n + i) = a i)
    (hcap : ∀ i < n, a i ≤ 1 / μ) (hS : 1 / (2 * μ) ≤ ssum a n)
    (B G : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (he : ∀ i < 2 * n, ‖e i‖ ≤ B)
    (hg : ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0) g‖ ≤ G)
    (hm : ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0)
      (g + H (d n))‖ ≤ 2 * G)
    (hf : ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0)
      (g + H (d (2 * n)))‖ ≤ 2 * G) :
    let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
    maskEnergy (proj b c) H g (d (2 * n)) ≤
      -(‖proj b c (g + H (d n))‖ ^ 2) / (4 * μ) + 4 * G * ssum a n * B := by
  let c := fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0
  let gm := g + H (d n)
  let D := fun i => d (n + i) - d n
  let E := fun i => e (n + i)
  have hD0 : D 0 = 0 := by simp [D]
  have hD (i : ℕ) (hi : i < n) : D (i + 1) = D i - a i • (gm + H (D i) + E i) := by
    dsimp [D, gm, E]
    rw [← Nat.add_assoc, hd (n + i) (by omega), hperiod i hi, map_sub]
    module
  have hDn : D n = d (2 * n) - d n := by simp [D, two_mul]
  have hEnd : gm + H (D n) = g + H (d (2 * n)) := by
    rw [hDn, map_sub]
    dsimp [gm]
    abel
  have hfirst := low_epoch_energy b eig H hc hsym μ hμ a ha g d e n h0
    (fun i hi => hd i (by omega)) hcap hS B hB (fun i hi => he i (by omega)) (2 * G) hm
  have hsecond := low_epoch_energy b eig H hc hsym μ hμ a ha gm D E n hD0 hD hcap hS B hB
    (fun i hi => he (n + i) (by omega)) (2 * G) (by rw [hEnd]; exact hf)
  have hid : ∀ j, c j * c j = c j := by
    intro j
    by_cases hj : 0 ≤ eig j ∧ eig j ≤ μ <;> simp [c, hj]
  have hshift := mask_energy_shift (proj b c) H (mask_idem b c hid) (mask_self b c)
    (mask_comm b c eig H hc) hsym g (d n) (D n)
  have hadd : d n + D n = d (2 * n) := by rw [hDn]; abel
  rw [hadd] at hshift
  have hSB : 0 ≤ ssum a n * B := mul_nonneg (Finset.sum_nonneg fun i _ => ha i) hB
  have hc1 := mul_le_mul_of_nonneg_right hg hSB
  have hc2 := mul_le_mul_of_nonneg_right hm hSB
  have hneg : 0 ≤ ‖proj b c g‖ ^ 2 / (4 * μ) := by positivity
  change maskEnergy (proj b c) H g (d (2 * n)) ≤ _
  dsimp only [gm] at hsecond hshift
  have hGS := mul_nonneg hG hSB
  dsimp only [c] at hfirst hshift hneg ⊢
  simp only [div_eq_mul_inv] at hfirst hsecond hneg ⊢
  nlinarith only [hfirst, hsecond, hshift, hneg, hc1, hc2, hGS]

lemma positive_scalar_energy_upper (μ lam g d : ℝ) (hμ : 0 < μ) (hl : μ ≤ lam) :
    g * d + lam * d ^ 2 / 2 ≤ (g + lam * d) ^ 2 / (2 * μ) := by
  have hlam : 0 < lam := hμ.trans_le hl
  calc
    _ ≤ (g + lam * d) ^ 2 / (2 * lam) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg g]
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)

lemma high_energy_upper (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (μ : ℝ) (hμ : 0 < μ) (g d : E) :
    let Q := proj b (fun j => if μ < eig j then (1 : ℝ) else 0)
    ⟪g, Q d⟫ + ⟪Q d, H (Q d)⟫ / 2 ≤ ‖Q (g + H d)‖ ^ 2 / (2 * μ) := by
  dsimp only
  rw [inner_coords b, inner_coords b, norm_sq_coords b, Finset.sum_div,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  simp only [proj_coord, hc, inner_add_right]
  by_cases hj : μ < eig j
  · simp only [hj, ite_true, one_mul]
    nlinarith [positive_scalar_energy_upper μ (eig j) ⟪b j, g⟫ ⟪b j, d⟫ hμ hj.le]
  · simp [hj]

open LongTails.Proofs.AdaptiveSilverDynamics

lemma positive_energy_split (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (μ : ℝ) (hμ : 0 ≤ μ) (g d : E) :
    phiPart b eig H g d =
      maskEnergy (proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0)) H g d +
      maskEnergy (proj b (fun j => if μ < eig j then (1 : ℝ) else 0)) H g d := by
  unfold phiPart maskEnergy
  conv_lhs => rw [inner_coords b, inner_coords b, Finset.sum_div, ← Finset.sum_add_distrib]
  conv_rhs => lhs; rw [inner_coords b, inner_coords b, Finset.sum_div, ← Finset.sum_add_distrib]
  conv_rhs => rhs; rw [inner_coords b, inner_coords b, Finset.sum_div, ← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [P_coord', proj_coord, hc]
  by_cases h0 : 0 ≤ eig j
  · by_cases hm : eig j ≤ μ
    · simp [cpos, h0, hm, not_lt.mpr hm]
    · simp [cpos, h0, hm, lt_of_not_ge hm]
  · have hm : eig j ≤ μ := (le_of_not_ge h0).trans hμ
    simp [cpos, h0, not_lt.mpr hm]

lemma negative_energy_descent (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (a : ℕ → ℝ) (g : E) (d e : ℕ → E) (q : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (ha : ∀ i < n, 0 ≤ a i)
    (hd : ∀ i < n, d (i + 1) = d i - a i • (g + H (d i) + e i))
    (he : ∀ i < n, ‖e i‖ ≤ B)
    (hq : ∀ i < n, q i ≤ ‖(g + H (d i)) - P b eig (g + H (d i))‖ ^ 2) :
    psiPart b eig H g (d n) ≤ psiPart b eig H g (d 0) -
      (∑ i ∈ Finset.range n, a i * q i) / 2 + ssum a n * B ^ 2 / 2 := by
  induction n with
  | zero => simp [ssum]
  | succ n ih =>
    have hi := ih (fun i hi => ha i (by omega)) (fun i hi => hd i (by omega))
      (fun i hi => he i (by omega)) (fun i hi => hq i (by omega))
    have hp := psi_step b eig H hc hsym g (d n) (e n) (ha n (by omega))
    have hn := pow_le_pow_left₀ (norm_nonneg _) (he n (by omega)) 2
    have hm := mul_le_mul_of_nonneg_left hn (ha n (by omega))
    have hqm := mul_le_mul_of_nonneg_left (hq n (by omega)) (ha n (by omega))
    rw [hd n (by omega), ssum_succ, Finset.sum_range_succ]
    nlinarith

lemma negative_two_epoch_energy (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (a : ℕ → ℝ) (g : E) (d e : ℕ → E) (n : ℕ) (B C : ℝ)
    (h0 : d 0 = 0) (ha : ∀ i < 2 * n, 0 ≤ a i)
    (hd : ∀ i < 2 * n, d (i + 1) = d i - a i • (g + H (d i) + e i))
    (he : ∀ i < 2 * n, ‖e i‖ ≤ B)
    (hperiod : ∀ i < n, a (n + i) = a i)
    (hq : ∀ i, n ≤ i → i < 2 * n → C ≤ ‖(g + H (d i)) - P b eig (g + H (d i))‖ ^ 2) :
    psiPart b eig H g (d (2 * n)) ≤ -ssum a n * C / 2 + ssum a n * B ^ 2 := by
  let q := fun i => if n ≤ i then C else 0
  have hh := negative_energy_descent b eig H hc hsym a g d e q (2 * n) B ha hd he
    (fun i hi => by
      dsimp [q]
      split_ifs with hni
      · exact hq i hni hi
      · exact sq_nonneg _)
  have hs : ssum a (2 * n) = 2 * ssum a n := by
    unfold ssum
    rw [two_mul, Finset.sum_range_add]
    have hp : (∑ i ∈ Finset.range n, a (n + i)) = ∑ i ∈ Finset.range n, a i :=
      Finset.sum_congr rfl (fun i hi => hperiod i (Finset.mem_range.mp hi))
    rw [hp]
    ring
  have hqsum : (∑ i ∈ Finset.range (2 * n), a i * q i) = ssum a n * C := by
    rw [two_mul, Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range n, a i * q i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [q, not_le.mpr (Finset.mem_range.mp hi)]
    rw [hz, zero_add]
    calc
      _ = ∑ i ∈ Finset.range n, a i * C := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hperiod i (Finset.mem_range.mp hi)]
        simp [q]
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hz : psiPart b eig H g (d 0) = 0 := by simp [h0, psiPart]
  rw [hz] at hh
  rw [hs, hqsum] at hh
  linarith

lemma mask_mul (b : OrthonormalBasis ι ℝ E) (c d : ι → ℝ) (v : E) :
    proj b c (proj b d v) = proj b (fun j => c j * d j) v := by
  apply eq_of_coords b
  intro j
  simp only [proj_coord]
  ring

lemma mask_bound (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ j, |c j| ≤ C) (v : E) : ‖proj b c v‖ ≤ C * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_coords b, norm_sq_coords b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [proj_coord, mul_pow]
  have hh : c j ^ 2 ≤ C ^ 2 := by simpa using pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
  exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)

lemma mask_norm_mono (b : OrthonormalBasis ι ℝ E) (c d : ι → ℝ)
    (hc : ∀ j, |c j| ≤ |d j|) (v : E) : ‖proj b c v‖ ≤ ‖proj b d v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_coords b, norm_sq_coords b]
  apply Finset.sum_le_sum
  intro j _
  simp only [proj_coord, mul_pow]
  have hh : c j ^ 2 ≤ d j ^ 2 := by simpa using pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
  exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)

lemma low_mask_norm_le (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (μ : ℝ) (v : E) :
    ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0) v‖ ≤ ‖P b eig v‖ := by
  apply mask_norm_mono
  intro j
  by_cases h0 : 0 ≤ eig j
  · by_cases hm : eig j ≤ μ <;> simp [cpos, h0, hm]
  · simp [cpos, h0]

lemma high_mask_norm_le (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (v : E) :
    ‖proj b (fun j => if μ < eig j then (1 : ℝ) else 0) v‖ ≤ ‖P b eig v‖ := by
  apply mask_norm_mono
  intro j
  by_cases hm : μ < eig j
  · simp [cpos, hm, hμ.trans hm.le]
  · simp [cpos, hm]

lemma high_filter_transfer (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (a : ℕ → ℝ) (t : ℕ) (g v : E) (D q : ℝ)
    (hq : 0 ≤ q)
    (herr : ‖P b eig v - proj b (fun j => cpos eig j * pr a (eig j) t) g‖ ≤ D)
    (hp : ∀ j, μ < eig j → |pr a (eig j) t| ≤ q) :
    ‖proj b (fun j => if μ < eig j then (1 : ℝ) else 0) v‖ ≤ q * ‖g‖ + D := by
  let c := fun j => if μ < eig j then (1 : ℝ) else 0
  let w := P b eig v - proj b (fun j => cpos eig j * pr a (eig j) t) g
  have hc : ∀ j, |c j| ≤ 1 := by intro j; by_cases hj : μ < eig j <;> simp [c, hj]
  have hcp (j : ι) : c j * cpos eig j = c j := by
    by_cases hj : μ < eig j
    · simp [c, cpos, hj, hμ.trans hj.le]
    · simp [c, hj]
  have heq : proj b c v = proj b c w + proj b (fun j => c j * pr a (eig j) t) g := by
    apply eq_of_coords b
    intro j
    dsimp [w]
    simp only [inner_add_right, proj_coord, inner_sub_right, P_coord']
    have he := hcp j
    linear_combination -(⟪b j, v⟫ - pr a (eig j) t * ⟪b j, g⟫) * he
  have hw : ‖proj b c w‖ ≤ D := by
    have hh := mask_bound b c 1 (by norm_num) hc w
    simp only [one_mul] at hh
    exact hh.trans herr
  have hf : ‖proj b (fun j => c j * pr a (eig j) t) g‖ ≤ q * ‖g‖ := by
    apply mask_bound b _ q hq
    intro j
    by_cases hj : μ < eig j
    · simpa [c, hj] using hp j hj
    · simp [c, hj, hq]
  change ‖proj b c v‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

lemma positive_vector_split (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (v : E) :
    P b eig v =
      proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0) v +
      proj b (fun j => if μ < eig j then (1 : ℝ) else 0) v := by
  apply eq_of_coords b
  intro j
  simp only [inner_add_right, P_coord', proj_coord]
  by_cases h0 : 0 ≤ eig j
  · by_cases hm : eig j ≤ μ
    · simp [cpos, h0, hm, not_lt.mpr hm]
    · simp [cpos, h0, hm, lt_of_not_ge hm]
  · have hm : eig j ≤ μ := (le_of_not_ge h0).trans hμ
    simp [cpos, h0, not_lt.mpr hm]

lemma model_split_norm (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (v : E) :
    ‖v‖ ≤ ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0) v‖ +
      ‖proj b (fun j => if μ < eig j then (1 : ℝ) else 0) v‖ + ‖v - P b eig v‖ := by
  have hh := norm_le_norm_sub_add v (P b eig v)
  have hp := norm_add_le
    (proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0) v)
    (proj b (fun j => if μ < eig j then (1 : ℝ) else 0) v)
  rw [← positive_vector_split b eig μ hμ v] at hp
  linarith

lemma midpoint_model_dichotomy (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (actual model : E) (ε : ℝ)
    (ha : ε < ‖actual‖) (herr : ‖actual - model‖ ≤ ε / 4)
    (hhigh : ‖proj b (fun j => if μ < eig j then (1 : ℝ) else 0) model‖ ≤ ε / 4) :
    ε / 4 ≤ ‖proj b (fun j => if 0 ≤ eig j ∧ eig j ≤ μ then (1 : ℝ) else 0) model‖ ∨
      ε / 4 ≤ ‖model - P b eig model‖ := by
  by_contra hh
  push Not at hh
  have htri := norm_le_norm_sub_add actual model
  have hsplit := model_split_norm b eig μ hμ model
  linarith

lemma completed_energy_arithmetic (μ ε l r low high neg A B J : ℝ)
    (hμ : 0 < μ) (hε : 0 ≤ ε)
    (hcase : ε / 4 ≤ l ∨ ε / 4 ≤ r)
    (hlow : low ≤ -(l ^ 2) / (4 * μ) + A)
    (hneg : neg ≤ B)
    (hstrong : ε / 4 ≤ r → neg ≤ -(ε ^ 2) / (256 * μ) + B)
    (hhigh : high ≤ 9 * ε ^ 2 / (131072 * μ))
    (herror : A + B + J ≤ ε ^ 2 / (1024 * μ)) :
    low + high + neg + J ≤ -(ε ^ 2) / (512 * μ) := by
  have hc : low + neg ≤ -(ε ^ 2) / (256 * μ) + A + B := by
    rcases hcase with hl | hr
    · have hs := pow_le_pow_left₀ (show 0 ≤ ε / 4 by positivity) hl 2
      have hd := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hμ.le)
      have he := mul_nonneg (sq_nonneg ε) (inv_nonneg.mpr hμ.le)
      simp only [div_eq_mul_inv, mul_inv_rev] at hlow ⊢
      norm_num at hlow ⊢
      nlinarith
    · have hn := hstrong hr
      have hs := mul_nonneg (sq_nonneg l) (inv_nonneg.mpr hμ.le)
      simp only [div_eq_mul_inv, mul_inv_rev] at hlow hn ⊢
      norm_num at hlow hn ⊢
      nlinarith
  have he := mul_nonneg (sq_nonneg ε) (inv_nonneg.mpr hμ.le)
  simp only [div_eq_mul_inv, mul_inv_rev] at hc hhigh herror ⊢
  norm_num at hc hhigh herror ⊢
  nlinarith

end LongTails.Proofs.RecoveryFractalEnergy
