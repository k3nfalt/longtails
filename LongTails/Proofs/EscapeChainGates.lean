import LongTails.Proofs.EscapeChainProfiles
import LongTails.Proofs.RelativeHessianArctan

namespace LongTails.Proofs.EscapeChainGates

open EscapeChainProfiles

noncomputable def ag (α β t : ℝ) : ℝ := unit (α * t + β)
noncomputable def ag1 (α β t : ℝ) : ℝ := α * unit1 (α * t + β)
noncomputable def ag2 (α β t : ℝ) : ℝ := α ^ 2 * unit2 (α * t + β)
noncomputable def ag3 (α β t : ℝ) : ℝ := α ^ 3 * unit3 (α * t + β)

lemma ag_contDiff (α β : ℝ) : ContDiff ℝ 3 (ag α β) := by
  have h := unit_contDiff
  unfold ag
  fun_prop

lemma affine_hasDerivAt (α β t : ℝ) : HasDerivAt (fun s => α * s + β) α t := by
  simpa using ((hasDerivAt_id t).const_mul α).add_const β

lemma ag_hasDerivAt (α β t : ℝ) : HasDerivAt (ag α β) (ag1 α β t) t := by
  have h := (unit_hasDerivAt (α * t + β)).comp t (affine_hasDerivAt α β t)
  exact h.congr_deriv (by unfold ag1; ring)

lemma ag1_hasDerivAt (α β t : ℝ) : HasDerivAt (ag1 α β) (ag2 α β t) t := by
  have h := ((unit1_hasDerivAt (α * t + β)).comp t (affine_hasDerivAt α β t)).const_mul α
  exact h.congr_deriv (by unfold ag2; ring)

lemma ag2_hasDerivAt (α β t : ℝ) : HasDerivAt (ag2 α β) (ag3 α β t) t := by
  have h := ((unit2_hasDerivAt (α * t + β)).comp t (affine_hasDerivAt α β t)).const_mul (α ^ 2)
  exact h.congr_deriv (by unfold ag3; ring)

lemma ag_flat {α β t : ℝ} (h : α * t + β ≤ 0) :
    ag α β t = 0 ∧ ag1 α β t = 0 ∧ ag2 α β t = 0 ∧ ag3 α β t = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_flat h
  simp [ag, ag1, ag2, ag3, h0, h1, h2, h3]

lemma ag_full {α β t : ℝ} (h : 4 ≤ α * t + β) :
    ag α β t = 1 ∧ ag1 α β t = 0 ∧ ag2 α β t = 0 ∧ ag3 α β t = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_full h
  simp [ag, ag1, ag2, ag3, h0, h1, h2, h3]

lemma ag_bounds {α : ℝ} (hα : 0 ≤ α) (β t : ℝ) :
    0 ≤ ag α β t ∧ ag α β t ≤ 1 ∧ 0 ≤ ag1 α β t ∧ ag1 α β t ≤ 2 / 3 * α ∧
      |ag2 α β t| ≤ 2 / 3 * α ^ 2 ∧ |ag3 α β t| ≤ 2 * α ^ 3 := by
  obtain ⟨b0, b1⟩ := unit_bounds (α * t + β)
  obtain ⟨j1, j2, j3⟩ := jets_bound (α * t + β)
  have n1 := unit1_nonneg (α * t + β)
  refine ⟨b0, b1, mul_nonneg hα n1, ?_, ?_, ?_⟩
  · unfold ag1; nlinarith
  · unfold ag2; rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
    nlinarith [sq_nonneg α]
  · unfold ag3; rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 3)]
    nlinarith [pow_nonneg hα 3]

noncomputable abbrev psi : ℝ → ℝ := ag 8 (-4)
noncomputable abbrev psi1 : ℝ → ℝ := ag1 8 (-4)
noncomputable abbrev psi2 : ℝ → ℝ := ag2 8 (-4)
noncomputable abbrev psi3 : ℝ → ℝ := ag3 8 (-4)
noncomputable abbrev gam : ℝ → ℝ := ag 20 (-12)
noncomputable abbrev gam1 : ℝ → ℝ := ag1 20 (-12)
noncomputable abbrev gam2 : ℝ → ℝ := ag2 20 (-12)
noncomputable abbrev gam3 : ℝ → ℝ := ag3 20 (-12)

lemma psi_flat {a : ℝ} (h : a ≤ 1 / 2) : psi a = 0 ∧ psi1 a = 0 ∧ psi2 a = 0 ∧ psi3 a = 0 :=
  ag_flat (by linarith)

lemma psi_full {a : ℝ} (h : 1 ≤ a) : psi a = 1 ∧ psi1 a = 0 ∧ psi2 a = 0 ∧ psi3 a = 0 :=
  ag_full (by linarith)

lemma gam_flat {a : ℝ} (h : a ≤ 3 / 5) : gam a = 0 ∧ gam1 a = 0 ∧ gam2 a = 0 ∧ gam3 a = 0 :=
  ag_flat (by linarith)

lemma gam_full {a : ℝ} (h : 4 / 5 ≤ a) : gam a = 1 ∧ gam1 a = 0 ∧ gam2 a = 0 ∧ gam3 a = 0 :=
  ag_full (by linarith)

lemma psi_mono : Monotone psi := fun s t h => unit_monotone (by linarith)

lemma psi_of_gt {a : ℝ} (h : 3 / 5 ≤ a) : 1 / 60 ≤ psi a := by
  have hm : psi (3 / 5) ≤ psi a := psi_mono h
  have he : psi (3 / 5) = unit (4 / 5) := by
    show unit (8 * (3 / 5) + -4) = unit (4 / 5); norm_num
  linarith [unit_at_eight_tenths]

lemma psi_onset {a : ℝ} (h0 : 1 / 2 ≤ a) (h1 : a ≤ 5 / 8) :
    psi a = (8 * a - 4) ^ 4 / 24 ∧ psi2 a = 32 * (8 * a - 4) ^ 2 := by
  obtain ⟨e0, -, e2, -⟩ := piece0 (t := 8 * a + -4) (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · show unit (8 * a + -4) = _; rw [e0]; ring
  · show 8 ^ 2 * unit2 (8 * a + -4) = _; rw [e2]; ring

lemma psi_onset_sq {a : ℝ} (h0 : 1 / 2 ≤ a) (h1 : a ≤ 5 / 8) : psi2 a ^ 2 = 24576 * psi a := by
  obtain ⟨e0, e2⟩ := psi_onset h0 h1
  rw [e0, e2]; ring

noncomputable def lam (c : ℝ) : ℝ := unit (16384 * c ^ 2 - 4)
noncomputable def lam1 (c : ℝ) : ℝ := unit1 (16384 * c ^ 2 - 4) * (32768 * c)
noncomputable def lam2 (c : ℝ) : ℝ :=
  unit2 (16384 * c ^ 2 - 4) * (32768 * c) ^ 2 + unit1 (16384 * c ^ 2 - 4) * 32768
noncomputable def lam3 (c : ℝ) : ℝ :=
  unit3 (16384 * c ^ 2 - 4) * (32768 * c) ^ 3 + 3 * unit2 (16384 * c ^ 2 - 4) * (32768 * c) * 32768

lemma square_hasDerivAt (α β c : ℝ) : HasDerivAt (fun s => α * s ^ 2 + β) (2 * α * c) c := by
  have h := ((hasDerivAt_pow 2 c).const_mul α).add_const β
  convert h using 1
  ring

lemma lam_contDiff : ContDiff ℝ 3 lam := by
  have h := unit_contDiff
  unfold lam
  fun_prop

lemma lam_hasDerivAt (c : ℝ) : HasDerivAt lam (lam1 c) c := by
  have h := (unit_hasDerivAt (16384 * c ^ 2 + -4)).comp c (square_hasDerivAt 16384 (-4) c)
  have he : lam = fun s => unit (16384 * s ^ 2 + -4) := by funext s; simp [lam, sub_eq_add_neg]
  rw [he]
  exact h.congr_deriv (by unfold lam1; simp only [sub_eq_add_neg]; ring)

lemma lam1_hasDerivAt (c : ℝ) : HasDerivAt lam1 (lam2 c) c := by
  have hu := (unit1_hasDerivAt (16384 * c ^ 2 + -4)).comp c (square_hasDerivAt 16384 (-4) c)
  have hl : HasDerivAt (fun s : ℝ => 32768 * s) 32768 c := by
    simpa using (hasDerivAt_id c).const_mul (32768 : ℝ)
  have h := hu.mul hl
  have he : lam1 = fun s => unit1 (16384 * s ^ 2 + -4) * (32768 * s) := by
    funext s; simp [lam1, sub_eq_add_neg]
  rw [he]
  exact h.congr_deriv (by unfold lam2; simp only [sub_eq_add_neg, Function.comp_apply]; ring)

lemma lam2_hasDerivAt (c : ℝ) : HasDerivAt lam2 (lam3 c) c := by
  have h2 := (unit2_hasDerivAt (16384 * c ^ 2 + -4)).comp c (square_hasDerivAt 16384 (-4) c)
  have h1 := (unit1_hasDerivAt (16384 * c ^ 2 + -4)).comp c (square_hasDerivAt 16384 (-4) c)
  have hs : HasDerivAt (fun s : ℝ => (32768 * s) ^ 2) (2 * 32768 * (32768 * c)) c := by
    have h0 : HasDerivAt (fun s : ℝ => 32768 * s) 32768 c := by
      simpa using (hasDerivAt_id c).const_mul (32768 : ℝ)
    exact (h0.pow 2).congr_deriv (by ring)
  have h := (h2.mul hs).add (h1.mul_const 32768)
  have he : lam2 = fun s => unit2 (16384 * s ^ 2 + -4) * (32768 * s) ^ 2 +
      unit1 (16384 * s ^ 2 + -4) * 32768 := by
    funext s; simp [lam2, sub_eq_add_neg]
  rw [he]
  exact h.congr_deriv (by unfold lam3; simp only [sub_eq_add_neg, Function.comp_apply]; ring)

lemma lam_flat {c : ℝ} (h : c ^ 2 ≤ 1 / 4096) :
    lam c = 0 ∧ lam1 c = 0 ∧ lam2 c = 0 ∧ lam3 c = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_flat (t := 16384 * c ^ 2 - 4) (by linarith)
  simp [lam, lam1, lam2, lam3, h0, h1, h2, h3]

lemma lam_full {c : ℝ} (h : 1 / 2048 ≤ c ^ 2) :
    lam c = 1 ∧ lam1 c = 0 ∧ lam2 c = 0 ∧ lam3 c = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_full (t := 16384 * c ^ 2 - 4) (by linarith)
  simp [lam, lam1, lam2, lam3, h0, h1, h2, h3]

lemma lam_bounds (c : ℝ) : 0 ≤ lam c ∧ lam c ≤ 1 := unit_bounds _

noncomputable def sad (c : ℝ) : ℝ := -2 * c ^ 2 * (1 - unit (12288 * c ^ 2 - 8))

lemma sad_contDiff : ContDiff ℝ 3 sad := by
  have h := unit_contDiff
  unfold sad
  fun_prop

lemma sad_inner {c : ℝ} (h : c ^ 2 ≤ 1 / 1536) : sad c = -2 * c ^ 2 := by
  have h0 := (unit_flat (t := 12288 * c ^ 2 - 8) (by linarith)).1
  unfold sad; rw [h0]; ring

lemma sad_outer {c : ℝ} (h : 1 / 1024 ≤ c ^ 2) : sad c = 0 := by
  have h0 := (unit_full (t := 12288 * c ^ 2 - 8) (by linarith)).1
  unfold sad; rw [h0]; ring

lemma sad_nonpos (c : ℝ) : sad c ≤ 0 := by
  have h := unit_bounds (12288 * c ^ 2 - 8)
  unfold sad
  nlinarith [sq_nonneg c]

lemma sad_abs_le (c : ℝ) : |sad c| ≤ 2 * c ^ 2 := by
  have h := unit_bounds (12288 * c ^ 2 - 8)
  rw [abs_of_nonpos (sad_nonpos c)]
  unfold sad
  nlinarith [sq_nonneg c]

lemma sad_abs_small (c : ℝ) : |sad c| ≤ 1 / 512 := by
  rcases le_or_gt (1 / 1024) (c ^ 2) with h | h
  · rw [sad_outer h]; norm_num
  · exact (sad_abs_le c).trans (by linarith)

noncomputable def loc (t : ℝ) : ℝ := 1 - unit ((4 * t - 4) / 3)
noncomputable def loc1 (t : ℝ) : ℝ := -(4 / 3) * unit1 ((4 * t - 4) / 3)
noncomputable def loc2 (t : ℝ) : ℝ := -(16 / 9) * unit2 ((4 * t - 4) / 3)
noncomputable def loc3 (t : ℝ) : ℝ := -(64 / 27) * unit3 ((4 * t - 4) / 3)

lemma loc_contDiff : ContDiff ℝ 3 loc := by
  have h := unit_contDiff
  unfold loc
  fun_prop

lemma loc_affine (t : ℝ) : HasDerivAt (fun s : ℝ => (4 * s - 4) / 3) (4 / 3) t := by
  have h := (((hasDerivAt_id t).const_mul (4 : ℝ)).sub_const 4).div_const 3
  exact h.congr_deriv (by norm_num)

lemma loc_hasDerivAt (t : ℝ) : HasDerivAt loc (loc1 t) t := by
  have h := ((unit_hasDerivAt ((4 * t - 4) / 3)).comp t (loc_affine t)).const_sub 1
  exact h.congr_deriv (by unfold loc1; ring)

lemma loc1_hasDerivAt (t : ℝ) : HasDerivAt loc1 (loc2 t) t := by
  have h := ((unit1_hasDerivAt ((4 * t - 4) / 3)).comp t (loc_affine t)).const_mul (-(4 / 3) : ℝ)
  exact h.congr_deriv (by unfold loc2; ring)

lemma loc2_hasDerivAt (t : ℝ) : HasDerivAt loc2 (loc3 t) t := by
  have h := ((unit2_hasDerivAt ((4 * t - 4) / 3)).comp t (loc_affine t)).const_mul (-(16 / 9) : ℝ)
  exact h.congr_deriv (by unfold loc3; ring)

lemma loc_one {t : ℝ} (h : t ≤ 1) : loc t = 1 ∧ loc1 t = 0 ∧ loc2 t = 0 ∧ loc3 t = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_flat (t := (4 * t - 4) / 3) (by linarith)
  simp [loc, loc1, loc2, loc3, h0, h1, h2, h3]

lemma loc_zero {t : ℝ} (h : 4 ≤ t) : loc t = 0 ∧ loc1 t = 0 ∧ loc2 t = 0 ∧ loc3 t = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_full (t := (4 * t - 4) / 3) (by linarith)
  simp [loc, loc1, loc2, loc3, h0, h1, h2, h3]

lemma loc_bounds (t : ℝ) : 0 ≤ loc t ∧ loc t ≤ 1 ∧ loc1 t ≤ 0 ∧ -(8 / 9) ≤ loc1 t ∧
    |loc2 t| ≤ 32 / 27 ∧ |loc3 t| ≤ 128 / 27 := by
  obtain ⟨b0, b1⟩ := unit_bounds ((4 * t - 4) / 3)
  obtain ⟨j1, j2, j3⟩ := jets_bound ((4 * t - 4) / 3)
  have n1 := unit1_nonneg ((4 * t - 4) / 3)
  refine ⟨by unfold loc; linarith, by unfold loc; linarith, by unfold loc1; linarith,
    by unfold loc1; linarith, ?_, ?_⟩
  · unfold loc2; rw [abs_mul]; norm_num; linarith
  · unfold loc3; rw [abs_mul]; norm_num; linarith

noncomputable def hump (c : ℝ) : ℝ := 1 - unit (12288 * c ^ 2 - 8)
noncomputable def hump1 (c : ℝ) : ℝ := -(unit1 (12288 * c ^ 2 - 8) * (24576 * c))
noncomputable def hump2 (c : ℝ) : ℝ :=
  -(unit2 (12288 * c ^ 2 - 8) * (24576 * c) ^ 2 + unit1 (12288 * c ^ 2 - 8) * 24576)
noncomputable def hump3 (c : ℝ) : ℝ :=
  -(unit3 (12288 * c ^ 2 - 8) * (24576 * c) ^ 3 + 3 * unit2 (12288 * c ^ 2 - 8) * (24576 * c) * 24576)

lemma hump_hasDerivAt (c : ℝ) : HasDerivAt hump (hump1 c) c := by
  have h := ((unit_hasDerivAt (12288 * c ^ 2 + -8)).comp c (square_hasDerivAt 12288 (-8) c)).const_sub 1
  have he : hump = fun s => 1 - unit (12288 * s ^ 2 + -8) := by funext s; simp [hump, sub_eq_add_neg]
  rw [he]
  exact h.congr_deriv (by unfold hump1; simp only [sub_eq_add_neg]; ring)

lemma hump1_hasDerivAt (c : ℝ) : HasDerivAt hump1 (hump2 c) c := by
  have hu := (unit1_hasDerivAt (12288 * c ^ 2 + -8)).comp c (square_hasDerivAt 12288 (-8) c)
  have hl : HasDerivAt (fun s : ℝ => 24576 * s) 24576 c := by
    simpa using (hasDerivAt_id c).const_mul (24576 : ℝ)
  have h := (hu.mul hl).neg
  have he : hump1 = fun s => -(unit1 (12288 * s ^ 2 + -8) * (24576 * s)) := by
    funext s; simp [hump1, sub_eq_add_neg]
  rw [he]
  exact h.congr_deriv (by unfold hump2; simp only [sub_eq_add_neg, Function.comp_apply]; ring)

lemma hump2_hasDerivAt (c : ℝ) : HasDerivAt hump2 (hump3 c) c := by
  have h2 := (unit2_hasDerivAt (12288 * c ^ 2 + -8)).comp c (square_hasDerivAt 12288 (-8) c)
  have h1 := (unit1_hasDerivAt (12288 * c ^ 2 + -8)).comp c (square_hasDerivAt 12288 (-8) c)
  have hs : HasDerivAt (fun s : ℝ => (24576 * s) ^ 2) (2 * 24576 * (24576 * c)) c := by
    have h0 : HasDerivAt (fun s : ℝ => 24576 * s) 24576 c := by
      simpa using (hasDerivAt_id c).const_mul (24576 : ℝ)
    exact (h0.pow 2).congr_deriv (by ring)
  have h := ((h2.mul hs).add (h1.mul_const 24576)).neg
  have he : hump2 = fun s => -(unit2 (12288 * s ^ 2 + -8) * (24576 * s) ^ 2 +
      unit1 (12288 * s ^ 2 + -8) * 24576) := by
    funext s; simp [hump2, sub_eq_add_neg]
  rw [he]
  exact h.congr_deriv (by unfold hump3; simp only [sub_eq_add_neg, Function.comp_apply]; ring)

noncomputable def sad1 (c : ℝ) : ℝ := -4 * c * hump c - 2 * c ^ 2 * hump1 c
noncomputable def sad2 (c : ℝ) : ℝ := -4 * hump c - 8 * c * hump1 c - 2 * c ^ 2 * hump2 c
noncomputable def sad3 (c : ℝ) : ℝ := -12 * hump1 c - 12 * c * hump2 c - 2 * c ^ 2 * hump3 c

lemma sad_eq (c : ℝ) : sad c = -2 * c ^ 2 * hump c := rfl

lemma sad_hasDerivAt (c : ℝ) : HasDerivAt sad (sad1 c) c := by
  have hq : HasDerivAt (fun s : ℝ => -2 * s ^ 2) (-4 * c) c :=
    ((hasDerivAt_pow 2 c).const_mul (-2 : ℝ)).congr_deriv (by ring)
  have h := hq.mul (hump_hasDerivAt c)
  have he : sad = fun s => -2 * s ^ 2 * hump s := rfl
  rw [he]
  exact h.congr_deriv (by unfold sad1; ring)

lemma sad1_hasDerivAt (c : ℝ) : HasDerivAt sad1 (sad2 c) c := by
  have hl : HasDerivAt (fun s : ℝ => -4 * s) (-4) c := by
    simpa using (hasDerivAt_id c).const_mul (-4 : ℝ)
  have hq : HasDerivAt (fun s : ℝ => 2 * s ^ 2) (4 * c) c :=
    ((hasDerivAt_pow 2 c).const_mul (2 : ℝ)).congr_deriv (by ring)
  have h := (hl.mul (hump_hasDerivAt c)).sub (hq.mul (hump1_hasDerivAt c))
  have he : sad1 = fun s => -4 * s * hump s - 2 * s ^ 2 * hump1 s := rfl
  rw [he]
  exact h.congr_deriv (by unfold sad2; ring)

lemma sad2_hasDerivAt (c : ℝ) : HasDerivAt sad2 (sad3 c) c := by
  have hl : HasDerivAt (fun s : ℝ => 8 * s) 8 c := by
    simpa using (hasDerivAt_id c).const_mul (8 : ℝ)
  have hq : HasDerivAt (fun s : ℝ => 2 * s ^ 2) (4 * c) c :=
    ((hasDerivAt_pow 2 c).const_mul (2 : ℝ)).congr_deriv (by ring)
  have h := (((hump_hasDerivAt c).const_mul (-4 : ℝ)).sub (hl.mul (hump1_hasDerivAt c))).sub
    (hq.mul (hump2_hasDerivAt c))
  have he : sad2 = fun s => -4 * hump s - 8 * s * hump1 s - 2 * s ^ 2 * hump2 s := rfl
  rw [he]
  exact h.congr_deriv (by unfold sad3; ring)

lemma hump_outer {c : ℝ} (h : 1 / 1024 ≤ c ^ 2) :
    hump c = 0 ∧ hump1 c = 0 ∧ hump2 c = 0 ∧ hump3 c = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_full (t := 12288 * c ^ 2 - 8) (by linarith)
  simp [hump, hump1, hump2, hump3, h0, h1, h2, h3]

lemma hump_inner {c : ℝ} (h : c ^ 2 ≤ 1 / 1536) :
    hump c = 1 ∧ hump1 c = 0 ∧ hump2 c = 0 ∧ hump3 c = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := unit_flat (t := 12288 * c ^ 2 - 8) (by linarith)
  simp [hump, hump1, hump2, hump3, h0, h1, h2, h3]

lemma sad_jets_inner {c : ℝ} (h : c ^ 2 ≤ 1 / 1536) :
    sad c = -2 * c ^ 2 ∧ sad1 c = -4 * c ∧ sad2 c = -4 ∧ sad3 c = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := hump_inner h
  refine ⟨by rw [sad_eq, h0]; ring, by unfold sad1; rw [h0, h1]; ring,
    by unfold sad2; rw [h0, h1, h2]; ring, by unfold sad3; rw [h1, h2, h3]; ring⟩

lemma sad_jets_outer {c : ℝ} (h : 1 / 1024 ≤ c ^ 2) :
    sad c = 0 ∧ sad1 c = 0 ∧ sad2 c = 0 ∧ sad3 c = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := hump_outer h
  refine ⟨by rw [sad_eq, h0]; ring, by unfold sad1; rw [h0, h1]; ring,
    by unfold sad2; rw [h0, h1, h2]; ring, by unfold sad3; rw [h1, h2, h3]; ring⟩

lemma hump_bounds {c : ℝ} (h : c ^ 2 ≤ 1 / 1024) :
    |hump c| ≤ 1 ∧ |hump1 c| ≤ 512 ∧ |hump2 c| ≤ 409600 ∧ |hump3 c| ≤ 2 ^ 30 := by
  have hc : |c| ≤ 1 / 32 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (c ^ 2) ≤ Real.sqrt (1 / 1024) := Real.sqrt_le_sqrt h
      _ = 1 / 32 := by rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨b0, b1⟩ := unit_bounds (12288 * c ^ 2 - 8)
  obtain ⟨j1, j2, j3⟩ := jets_bound (12288 * c ^ 2 - 8)
  have n1 := unit1_nonneg (12288 * c ^ 2 - 8)
  have hc0 := abs_nonneg c
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold hump; rw [abs_le]; constructor <;> linarith
  · unfold hump1; rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg n1]
    norm_num; nlinarith
  · unfold hump2; rw [abs_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg n1, abs_pow, abs_mul]
    norm_num
    have h2 : |c| ^ 2 ≤ 1 / 1024 := by rw [sq_abs]; exact h
    nlinarith [abs_nonneg (unit2 (12288 * c ^ 2 - 8)), mul_le_mul j2 h2 (by positivity) (by norm_num)]
  · unfold hump3; rw [abs_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_mul]
    norm_num
    have h2 : |c| ^ 2 ≤ 1 / 1024 := by rw [sq_abs]; exact h
    have h3 : |c| ^ 3 ≤ 1 / 32768 := by
      calc |c| ^ 3 = |c| * |c| ^ 2 := by ring
        _ ≤ (1 / 32) * (1 / 1024) := mul_le_mul hc h2 (by positivity) (by norm_num)
        _ = 1 / 32768 := by norm_num
    nlinarith [abs_nonneg (unit2 (12288 * c ^ 2 - 8)), abs_nonneg (unit3 (12288 * c ^ 2 - 8)),
      mul_le_mul j3 h3 (by positivity) (by norm_num), mul_le_mul j2 hc (by positivity) (by norm_num)]

lemma sad_jet_bounds (c : ℝ) : |sad c| ≤ 1 ∧ |sad1 c| ≤ 36 * |c| ∧ |sad1 c| ≤ 2 ^ 21 ∧
    |sad2 c| ≤ 2 ^ 22 ∧ |sad3 c| ≤ 2 ^ 22 := by
  rcases le_or_gt (1 / 1024) (c ^ 2) with h | h
  · obtain ⟨e0, e1, e2, e3⟩ := sad_jets_outer h
    rw [e0, e1, e2, e3]
    simp only [abs_zero]
    refine ⟨by norm_num, by positivity, by positivity, by positivity, by positivity⟩
  have hle := h.le
  have hc : |c| ≤ 1 / 32 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (c ^ 2) ≤ Real.sqrt (1 / 1024) := Real.sqrt_le_sqrt hle
      _ = 1 / 32 := by rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq : |c| ^ 2 ≤ 1 / 1024 := by rw [sq_abs]; exact hle
  obtain ⟨b0, b1, b2, b3⟩ := hump_bounds hle
  have hc0 := abs_nonneg c
  have hs : |sad c| ≤ 1 := (sad_abs_small c).trans (by norm_num)
  have hs1 : |sad1 c| ≤ 36 * |c| := by
    have hu := unit1_nonneg (12288 * c ^ 2 - 8)
    have hj := (jets_bound (12288 * c ^ 2 - 8)).1
    have he : sad1 c = c * (-4 * hump c + 49152 * c ^ 2 * unit1 (12288 * c ^ 2 - 8)) := by
      unfold sad1 hump1; ring
    have hin : |-4 * hump c + 49152 * c ^ 2 * unit1 (12288 * c ^ 2 - 8)| ≤ 36 := by
      have h1 : |-4 * hump c| ≤ 4 := by rw [abs_mul]; norm_num; linarith
      have h2 : |49152 * c ^ 2 * unit1 (12288 * c ^ 2 - 8)| ≤ 32 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg (sq_nonneg c)]
        norm_num
        nlinarith [mul_le_mul hle hj hu (by norm_num)]
      exact (abs_add_le _ _).trans (by linarith)
    rw [he, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hin hc0
  have hb1 : |c| * |hump1 c| ≤ 1 / 32 * 512 := mul_le_mul hc b1 (abs_nonneg _) (by norm_num)
  have hb2 : |c| * |hump2 c| ≤ 1 / 32 * 409600 := mul_le_mul hc b2 (abs_nonneg _) (by norm_num)
  have hb2' : |c| ^ 2 * |hump2 c| ≤ 1 / 1024 * 409600 :=
    mul_le_mul hsq b2 (abs_nonneg _) (by norm_num)
  have hb3 : |c| ^ 2 * |hump3 c| ≤ 1 / 1024 * 2 ^ 30 :=
    mul_le_mul hsq b3 (abs_nonneg _) (by norm_num)
  refine ⟨hs, hs1, hs1.trans (by nlinarith), ?_, ?_⟩
  · have e : |sad2 c| ≤ 4 * |hump c| + 8 * (|c| * |hump1 c|) + 2 * (|c| ^ 2 * |hump2 c|) := by
      unfold sad2
      have t1 : |-4 * hump c| = 4 * |hump c| := by rw [abs_mul]; norm_num
      have t2 : |8 * c * hump1 c| = 8 * (|c| * |hump1 c|) := by rw [abs_mul, abs_mul]; norm_num; ring
      have t3 : |2 * c ^ 2 * hump2 c| = 2 * (|c| ^ 2 * |hump2 c|) := by
        rw [abs_mul, abs_mul, abs_pow]; norm_num; ring
      calc _ ≤ |-4 * hump c| + |8 * c * hump1 c| + |2 * c ^ 2 * hump2 c| := by
            refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans le_rfl) le_rfl)
        _ = _ := by rw [t1, t2, t3]
    linarith
  · have e : |sad3 c| ≤ 12 * |hump1 c| + 12 * (|c| * |hump2 c|) + 2 * (|c| ^ 2 * |hump3 c|) := by
      unfold sad3
      have t1 : |-12 * hump1 c| = 12 * |hump1 c| := by rw [abs_mul]; norm_num
      have t2 : |12 * c * hump2 c| = 12 * (|c| * |hump2 c|) := by rw [abs_mul, abs_mul]; norm_num; ring
      have t3 : |2 * c ^ 2 * hump3 c| = 2 * (|c| ^ 2 * |hump3 c|) := by
        rw [abs_mul, abs_mul, abs_pow]; norm_num; ring
      calc _ ≤ |-12 * hump1 c| + |12 * c * hump2 c| + |2 * c ^ 2 * hump3 c| := by
            refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans le_rfl) le_rfl)
        _ = _ := by rw [t1, t2, t3]
    linarith

end LongTails.Proofs.EscapeChainGates
