import LongTails.Proofs.ComparisonBox
import LongTails.Proofs.ComparisonFrame
import LongTails.Proofs.PLHessianGeometry

open scoped RealInnerProductSpace

namespace OracleTemplate.ComparisonOrth

open QueryPlan

variable {n : ℕ}

noncomputable def boxErr (m : ℕ) (M w R : ℝ) : ℝ :=
  (m + 1) * ((m + 1) * (M * ((2 / 3) ^ m * (R - -R))) + M * ((2 / 3) ^ m * (R - -R))) +
    M * ((2 / 3) ^ m * (w - -w))

structure Inv (f : Pt n → ℝ) (x0 : Pt n) (R η : ℝ) (k : ℕ) (s : OrthState n) : Prop where
  frame : Frame s.u1 s.u2 s.u3
  xspan : InSpan s.u1 s.u2 s.u3 (s.x - x0)
  dspan : InSpan s.u1 s.u2 s.u3 s.d
  dnorm : ‖s.d‖ ^ 2 ≤ k
  xnorm : ‖s.x - x0‖ ^ 2 ≤ (2 * k + 1) * R ^ 2
  opt : ∃ w, R ≤ w ∧ ∃ a b c, |a| ≤ w ∧ |b| ≤ R ∧ |c| ≤ R ∧
    s.x = affine3 x0 s.u1 s.u2 s.u3 a b c ∧
    ∀ a' b' c', |a'| ≤ w → |b'| ≤ R → |c'| ≤ R →
      f s.x ≤ f (affine3 x0 s.u1 s.u2 s.u3 a' b' c') + η
  mono : f s.x ≤ f x0

lemma inv_init (f : Pt n → ℝ) (x0 : Pt n) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 ≤ η) :
    Inv f x0 R η 0 (initState x0) := by
  have hf : Frame (0 : Pt n) 0 0 :=
    ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, inner_zero_left _, inner_zero_left _,
      inner_zero_left _⟩
  have haff : ∀ a b c : ℝ, affine3 x0 (0 : Pt n) 0 0 a b c = x0 := by
    intro a b c; simp [affine3]
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, le_rfl⟩
  · simp [InSpan, proj3, initState]
  · simp [InSpan, proj3, initState]
  · simp [initState]
  · simp only [initState, sub_self, norm_zero]; push_cast; nlinarith [sq_nonneg R]
  · refine ⟨R, le_rfl, 0, 0, 0, by simpa using hR, by simpa using hR, by simpa using hR,
      (haff 0 0 0).symm, ?_⟩
    intro a' b' c' _ _ _
    simp only [initState]
    rw [haff]
    linarith

lemma eval_orthStep (f : Pt n → ℝ) (x0 : Pt n) (R h : ℝ) (m : ℕ) (s : OrthState n) :
    eval (cmp f) (orthStepPlan x0 R h m s) =
      newState x0 s (eval (cmp f) (dirPlan s.x h m))
        (if decide (f (eval (cmp f) (boxPlan m (boxPoint x0 s (eval (cmp f) (dirPlan s.x h m)))
            (max R ‖s.x - x0‖) R R)) ≤ f s.x) = true
          then eval (cmp f) (boxPlan m (boxPoint x0 s (eval (cmp f) (dirPlan s.x h m)))
            (max R ‖s.x - x0‖) R R) else s.x) := by
  simp only [orthStepPlan, eval_bind]
  rfl

lemma boxPoint_eq (x0 : Pt n) (s : OrthState n) (ghat : Pt n) :
    boxPoint x0 s ghat = affine3 x0 (newState x0 s ghat s.x).u1 (newState x0 s ghat s.x).u2
      (newState x0 s ghat s.x).u3 := rfl

lemma projOut_eq (s : OrthState n) (v : Pt n) :
    projOut s v = v - proj3 s.u1 s.u2 s.u3 v := rfl

lemma proj3_sub (u1 u2 u3 v w : Pt n) :
    proj3 u1 u2 u3 (v - w) = proj3 u1 u2 u3 v - proj3 u1 u2 u3 w := by
  simp only [proj3, inner_sub_left, sub_smul]; abel

lemma proj3_smul (u1 u2 u3 v : Pt n) (c : ℝ) :
    proj3 u1 u2 u3 (c • v) = c • proj3 u1 u2 u3 v := by
  simp only [proj3, inner_smul_left, RCLike.conj_to_real, smul_add, smul_smul]

lemma norm_comb_le {u1 u2 u3 : Pt n} (F : Frame u1 u2 u3) (a b c : ℝ) :
    ‖a • u1 + b • u2 + c • u3‖ ≤ |a| + |b| + |c| := by
  calc ‖a • u1 + b • u2 + c • u3‖ ≤ ‖a • u1‖ + ‖b • u2‖ + ‖c • u3‖ := norm_add₃_le
    _ ≤ |a| + |b| + |c| := by
        simp only [norm_smul, Real.norm_eq_abs]
        gcongr
        · nlinarith [F.h1.norm_le, abs_nonneg a]
        · nlinarith [F.h2.norm_le, abs_nonneg b]
        · nlinarith [F.h3.norm_le, abs_nonneg c]

lemma vi_of_opt {X D2 L η e1 : ℝ} (hη : 0 < η) (he1 : 0 < e1) (h2η : 2 * η ≤ e1)
    (hD : 2 * L * η * D2 ≤ e1 ^ 2)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * X + L / 2 * t ^ 2 * D2 + η) : -e1 ≤ X := by
  have ht : 0 < 2 * η / e1 := by positivity
  have ht1 : 2 * η / e1 ≤ 1 := by rw [div_le_one he1]; exact h2η
  have hh := h _ ht ht1
  have key : 0 ≤ X + L * η * D2 / e1 + e1 / 2 := by
    have : 0 ≤ (2 * η / e1) * (X + L * η * D2 / e1 + e1 / 2) := by
      have e : (2 * η / e1) * (X + L * η * D2 / e1 + e1 / 2) =
          2 * η / e1 * X + L / 2 * (2 * η / e1) ^ 2 * D2 + η := by
        field_simp
      rw [e]; exact hh
    exact (mul_nonneg_iff_of_pos_left ht).mp this
  have : L * η * D2 / e1 ≤ e1 / 2 := by
    rw [div_le_iff₀ he1]; nlinarith
  linarith

lemma Frame.norm_proj_le {u1 u2 u3 : Pt n} (F : Frame u1 u2 u3) (v : Pt n) :
    ‖proj3 u1 u2 u3 v‖ ≤ ‖v‖ := by
  have hspan : InSpan u1 u2 u3 (proj3 u1 u2 u3 v) := F.inSpan_comb _ _ _
  have horth := inner_projOut_of_inSpan v _ hspan
  have hsq : ‖v‖ ^ 2 = ‖v - proj3 u1 u2 u3 v‖ ^ 2 + ‖proj3 u1 u2 u3 v‖ ^ 2 := by
    have := norm_add_sq_real (v - proj3 u1 u2 u3 v) (proj3 u1 u2 u3 v)
    rw [sub_add_cancel, horth] at this
    linarith
  nlinarith [norm_nonneg v, norm_nonneg (proj3 u1 u2 u3 v),
    sq_nonneg ‖v - proj3 u1 u2 u3 v‖]

lemma inner_unit_of_dist {a b : Pt n} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ⟪a, b⟫ = 1 - ‖a - b‖ ^ 2 / 2 := by
  have := norm_sub_sq_real a b
  rw [ha, hb] at this
  linarith

section Step

variable {f : Pt n → ℝ} {L : ℝ}
  (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
  (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
include hc hg hlip

set_option maxHeartbeats 1000000 in
theorem orth_step {x0 xs : Pt n} (hmin : IsMinOn f Set.univ xs) {R h η ε θ θg : ℝ}
    {m k K : ℕ} (hL : 0 < L) (hR : 0 < R) (hη : 0 < η) (hε : 0 < ε) (hθ : θ ≤ 1 / 2)
    (hx0 : ‖x0 - xs‖ ≤ R) (hkK : k + 1 ≤ K)
    {s : OrthState n} (hs : Inv f x0 R η k s)
    (hbox : boxErr m (L * (max R ‖s.x - x0‖ + 3 * R)) (max R ‖s.x - x0‖) R ≤ η) :
    Inv f x0 R η (k + 1) (eval (cmp f) (orthStepPlan x0 R h m s)) ∧
      f (eval (cmp f) (orthStepPlan x0 R h m s)).x ≤ f s.x ∧
      (eval (cmp f) (orthStepPlan x0 R h m s)).d =
        s.d + (eval (cmp f) (orthStepPlan x0 R h m s)).u3 ∧
      (ε ≤ f s.x - f xs → 2 * η ≤ ε / 4 → 8 * L * η * K * R ^ 2 ≤ ε ^ 2 / 16 →
        25 * L * R ^ 2 * η ≤ ε ^ 2 → 8 * θg * L * R ^ 2 ≤ 3 * ε * θ →
        (∀ x, 3 * ε / (4 * R) ≤ ‖gradient f x‖ →
          ‖eval (cmp f) (dirPlan x h m) - nrm (gradient f x)‖ ≤ θg) →
        0 < ⟪(eval (cmp f) (orthStepPlan x0 R h m s)).u3, x0 - xs⟫ + θ * R ∧
        ⟪(eval (cmp f) (orthStepPlan x0 R h m s)).u3, x0 - xs⟫ + θ * R ≤ 3 / 2 * R ∧
        f (eval (cmp f) (orthStepPlan x0 R h m s)).x - f xs ≤ (f s.x - f xs) -
          (f s.x - f xs) ^ 2 /
            (8 * L * (⟪(eval (cmp f) (orthStepPlan x0 R h m s)).u3, x0 - xs⟫ + θ * R) ^ 2)) := by
  have hmin' : ∀ y, f xs ≤ f y := fun y => hmin (Set.mem_univ y)
  have hg0 : gradient f xs = 0 := PLHessian.grad_zero_of_min hL hg hlip hmin
  obtain ⟨hF, hxspan, hdspan, hdnorm, hxnorm, ⟨w, hRw, a0, b0, c0, ha0, hb0, hc0, hsx, hopt⟩,
    hmono⟩ := hs
  set ghat := eval (cmp f) (dirPlan s.x h m) with hghat
  set u1 := nrm (s.x - x0) with hu1
  set r := s.d - ⟪s.d, u1⟫ • u1 with hr
  set u2 := nrm r with hu2
  set G := nrm (projOut s ghat) with hG
  set w1 := max R ‖s.x - x0‖ with hw1
  set M := L * (w1 + 3 * R) with hM
  have hw1R : R ≤ w1 := le_max_left _ _
  have hw1x : ‖s.x - x0‖ ≤ w1 := le_max_right _ _
  have hspan_u1 : InSpan s.u1 s.u2 s.u3 u1 := inSpan_smul hxspan _
  have hspan_r : InSpan s.u1 s.u2 s.u3 r := inSpan_sub hdspan (inSpan_smul hspan_u1 _)
  have hspan_u2 : InSpan s.u1 s.u2 s.u3 u2 := inSpan_smul hspan_r _
  have hG_u : ∀ v, InSpan s.u1 s.u2 s.u3 v → ⟪G, v⟫ = 0 := by
    intro v hv
    rw [hG, inner_nrm_left, projOut_eq, inner_projOut_of_inSpan _ _ hv, mul_zero]
  have hu1u : UnitOrZero u1 := unitOrZero_nrm _
  have hu1r : ⟪u1, r⟫ = 0 := by
    rw [hr, inner_sub_right, inner_smul_right, hu1u.inner_mul_self, real_inner_comm, sub_self]
  have hF' : Frame u1 u2 G := by
    refine ⟨hu1u, unitOrZero_nrm _, unitOrZero_nrm _, ?_, ?_, ?_⟩
    · rw [hu2, real_inner_comm, inner_nrm_left, real_inner_comm, hu1r, mul_zero]
    · rw [real_inner_comm]; exact hG_u u1 hspan_u1
    · rw [real_inner_comm]; exact hG_u u2 hspan_u2
  have hsx_dec : s.x - x0 = ‖s.x - x0‖ • u1 := nrm_decomp _
  have hgradM : ∀ a b c, a ∈ Set.Icc (-w1) w1 → b ∈ Set.Icc (-R) R → c ∈ Set.Icc (-R) R →
      ‖gradient f (affine3 x0 u1 u2 G a b c)‖ ≤ M := by
    intro a b c ha hb hcc
    have h1 := hlip (affine3 x0 u1 u2 G a b c) xs
    rw [hg0, sub_zero] at h1
    have h2 : ‖affine3 x0 u1 u2 G a b c - xs‖ ≤ (|a| + |b| + |c|) + R := by
      calc ‖affine3 x0 u1 u2 G a b c - xs‖ = ‖(a • u1 + b • u2 + c • G) + (x0 - xs)‖ := by
            congr 1; simp only [affine3]; abel
        _ ≤ ‖a • u1 + b • u2 + c • G‖ + ‖x0 - xs‖ := norm_add_le _ _
        _ ≤ (|a| + |b| + |c|) + R := add_le_add (norm_comb_le hF' a b c) hx0
    have ha' : |a| ≤ w1 := abs_le.mpr ha
    have hb' : |b| ≤ R := abs_le.mpr hb
    have hc' : |c| ≤ R := abs_le.mpr hcc
    calc ‖gradient f (affine3 x0 u1 u2 G a b c)‖ ≤ L * ‖affine3 x0 u1 u2 G a b c - xs‖ := h1
      _ ≤ L * ((|a| + |b| + |c|) + R) := mul_le_mul_of_nonneg_left h2 hL.le
      _ ≤ M := by rw [hM]; apply mul_le_mul_of_nonneg_left _ hL.le; linarith
  have hM0 : 0 ≤ M := by rw [hM]; have := hR.le; positivity
  obtain ⟨a, ha, b, hb, c, hcc, hxt, hxtopt⟩ := box_guarantee hc hg hmin' x0 u1 u2 G
    hF'.h1.norm_le hF'.h2.norm_le hF'.h3.norm_le (hR.le.trans hw1R) hR.le hR.le hM0 hgradM m
  obtain ⟨xt, hxtdef⟩ : ∃ xt, xt = eval (cmp f) (boxPlan m (affine3 x0 u1 u2 G) w1 R R) :=
    ⟨_, rfl⟩
  rw [← hxtdef] at hxt hxtopt
  have hxtE : ∀ a' b' c', |a'| ≤ w1 → |b'| ≤ R → |c'| ≤ R →
      f xt ≤ f (affine3 x0 u1 u2 G a' b' c') + η := by
    intro a' b' c' ha' hb' hc'
    have := hxtopt a' (abs_le.mp ha') b' (abs_le.mp hb') c' (abs_le.mp hc')
    have hE : (m + 1) * ((m + 1) * (M * ((2 / 3) ^ m * (R - -R))) +
        M * ((2 / 3) ^ m * (R - -R))) + M * ((2 / 3) ^ m * (w1 - -w1)) ≤ η := hbox
    linarith
  have hstep := eval_orthStep f x0 R h m s
  rw [boxPoint_eq] at hstep
  obtain ⟨xn, hxn⟩ : ∃ xn, xn = if decide (f xt ≤ f s.x) = true then xt else s.x :=
    ⟨_, rfl⟩
  have hxn_xt : f xn ≤ f xt := by
    by_cases hb' : f xt ≤ f s.x
    · simp [hxn, hb']
    · simp only [hxn, hb', decide_false, Bool.false_eq_true, ite_false]
      push Not at hb'; exact hb'.le
  have hxn_sx : f xn ≤ f s.x := by
    by_cases hb' : f xt ≤ f s.x
    · simp [hxn, hb']
    · simp [hxn, hb']
  have hxn_cases : xn = xt ∨ xn = s.x := by
    by_cases hb' : f xt ≤ f s.x
    · left; simp [hxn, hb']
    · right; simp [hxn, hb']
  have hs' : eval (cmp f) (orthStepPlan x0 R h m s) =
      ⟨xn, s.d + G, u1, u2, G⟩ := by
    rw [hstep, hxn, hxtdef]; rfl
  rw [hs']
  clear_value ghat G u1 u2 r w1 M
  clear hstep hs'
  have hsx_aff : s.x = affine3 x0 u1 u2 G ‖s.x - x0‖ 0 0 := by
    simp only [affine3, zero_smul, add_zero]
    rw [← hsx_dec]; abel
  have hd_dec : s.d = ⟪s.d, u1⟫ • u1 + ‖r‖ • u2 := by
    rw [hu2, ← nrm_decomp r, hr]; abel
  refine ⟨⟨hF', ?_, ?_, ?_, ?_, ?_, ?_⟩, hxn_sx, rfl, ?_⟩
  · show InSpan u1 u2 G (xn - x0)
    rcases hxn_cases with h' | h'
    · rw [h', hxt]
      have : affine3 x0 u1 u2 G a b c - x0 = a • u1 + b • u2 + c • G := by
        simp only [affine3]; abel
      rw [this]; exact hF'.inSpan_comb a b c
    · rw [h', hsx_dec]
      have := hF'.inSpan_comb ‖s.x - x0‖ 0 0
      simpa using this
  · show InSpan u1 u2 G (s.d + G)
    rw [hd_dec, show ⟪s.d, u1⟫ • u1 + ‖r‖ • u2 + G = ⟪s.d, u1⟫ • u1 + ‖r‖ • u2 + (1 : ℝ) • G by
      rw [one_smul]]
    exact hF'.inSpan_comb _ _ _
  · show ‖s.d + G‖ ^ 2 ≤ ((k + 1 : ℕ) : ℝ)
    have hdG : ⟪s.d, G⟫ = 0 := by rw [real_inner_comm]; exact hG_u s.d hdspan
    have hG1 : ‖G‖ ≤ 1 := hF'.h3.norm_le
    rw [norm_add_sq_real, hdG]
    push_cast
    nlinarith [norm_nonneg G]
  · show ‖xn - x0‖ ^ 2 ≤ (2 * ((k + 1 : ℕ) : ℝ) + 1) * R ^ 2
    push_cast
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rcases hxn_cases with h' | h'
    · rw [h', hxt]
      have e : affine3 x0 u1 u2 G a b c - x0 = a • u1 + b • u2 + c • G := by
        simp only [affine3]; abel
      rw [e]
      have h1 := hF'.norm_comb_sq a b c
      have ha2 : a ^ 2 ≤ w1 ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) (abs_le.mpr ha) 2
      have hb2 : b ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg b) (abs_le.mpr hb) 2
      have hc2 : c ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg c) (abs_le.mpr hcc) 2
      have hw12 : w1 ^ 2 ≤ (2 * k + 1) * R ^ 2 := by
        rcases le_total R ‖s.x - x0‖ with hle | hle
        · rw [hw1, max_eq_right hle]; exact hxnorm
        · rw [hw1, max_eq_left hle]; nlinarith [sq_nonneg R]
      nlinarith
    · rw [h']; nlinarith [sq_nonneg R]
  · refine ⟨w1, hw1R, ?_⟩
    rcases hxn_cases with h' | h'
    · refine ⟨a, b, c, abs_le.mpr ha, abs_le.mpr hb, abs_le.mpr hcc, by rw [h', hxt], ?_⟩
      intro a' b' c' ha' hb' hc'
      have := hxtE a' b' c' ha' hb' hc'
      linarith
    · refine ⟨‖s.x - x0‖, 0, 0, by rw [abs_of_nonneg (norm_nonneg _)]; exact hw1x,
        by simp [hR.le], by simp [hR.le], by rw [h']; exact hsx_aff, ?_⟩
      intro a' b' c' ha' hb' hc'
      have := hxtE a' b' c' ha' hb' hc'
      linarith
  · exact hxn_sx.trans hmono
  intro hδ h2η hDη h25 hθg hdir
  set δ := f s.x - f xs with hδdef
  set g := gradient f s.x with hgdef
  set P := proj3 s.u1 s.u2 s.u3 with hP
  set Gv := g - P g with hGv
  set y := affine3 x0 s.u1 s.u2 s.u3 ⟪xs - x0, s.u1⟫ ⟪xs - x0, s.u2⟫ ⟪xs - x0, s.u3⟫ with hy
  have hy_eq : y = x0 + P (xs - x0) := by simp only [hy, hP, affine3, proj3]; abel
  have hcoord : ∀ u : Pt n, UnitOrZero u → |⟪xs - x0, u⟫| ≤ R := by
    intro u hu
    calc |⟪xs - x0, u⟫| ≤ ‖xs - x0‖ := abs_inner_le_of_unitOrZero hu _
      _ = ‖x0 - xs‖ := norm_sub_rev _ _
      _ ≤ R := hx0
  have hy1 := hcoord s.u1 hF.h1
  have hy2 := hcoord s.u2 hF.h2
  have hy3 := hcoord s.u3 hF.h3
  have hyx : ‖y - x0‖ ≤ R := by
    rw [hy_eq, add_sub_cancel_left]
    calc ‖P (xs - x0)‖ ≤ ‖xs - x0‖ := hF.norm_proj_le _
      _ = ‖x0 - xs‖ := norm_sub_rev _ _
      _ ≤ R := hx0
  have hD2 : ‖y - s.x‖ ^ 2 ≤ 4 * K * R ^ 2 := by
    have h1 : ‖y - s.x‖ ≤ ‖y - x0‖ + ‖s.x - x0‖ := by
      calc ‖y - s.x‖ = ‖(y - x0) - (s.x - x0)‖ := by congr 1; abel
        _ ≤ ‖y - x0‖ + ‖s.x - x0‖ := norm_sub_le _ _
    have hK : ((k : ℝ) + 1) ≤ K := by exact_mod_cast hkK
    have ha2 : ‖y - x0‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyx 2
    have hs2 : ‖y - s.x‖ ^ 2 ≤ (‖y - x0‖ + ‖s.x - x0‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hab : (‖y - x0‖ + ‖s.x - x0‖) ^ 2 ≤ 2 * ‖y - x0‖ ^ 2 + 2 * ‖s.x - x0‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖y - x0‖ - ‖s.x - x0‖)]
    have hKR := mul_le_mul_of_nonneg_right hK (sq_nonneg R)
    nlinarith only [hs2, hab, ha2, hxnorm, hKR]
  have hvi : -(ε / 4) ≤ ⟪g, y - s.x⟫ := by
    apply vi_of_opt hη (by positivity) h2η (D2 := ‖y - s.x‖ ^ 2) (L := L)
    · have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      nlinarith [mul_le_mul_of_nonneg_left hD2 (by positivity : (0 : ℝ) ≤ 2 * L * η)]
    intro t ht0 ht1
    set z := affine3 x0 s.u1 s.u2 s.u3 ((1 - t) * a0 + t * ⟪xs - x0, s.u1⟫)
      ((1 - t) * b0 + t * ⟪xs - x0, s.u2⟫) ((1 - t) * c0 + t * ⟪xs - x0, s.u3⟫) with hz
    have hzmix : z = (1 - t) • s.x + t • y := by
      rw [hz, affine3_mix x0 s.u1 s.u2 s.u3 _ _ _ _ _ _ (1 - t) t (by ring), ← hsx]
    have hbound : ∀ p q W : ℝ, |p| ≤ W → |q| ≤ W → |(1 - t) * p + t * q| ≤ W := by
      intro p q W hp hq
      calc |(1 - t) * p + t * q| ≤ |(1 - t) * p| + |t * q| := abs_add_le _ _
        _ = (1 - t) * |p| + t * |q| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t),
              abs_of_nonneg ht0.le]
        _ ≤ (1 - t) * W + t * W := by
            gcongr
        _ = W := by ring
    have hopt' := hopt _ _ _ (hbound _ _ w ha0 (hy1.trans hRw))
      (hbound _ _ R hb0 hy2) (hbound _ _ R hc0 hy3)
    rw [← hz] at hopt'
    have hup := Gradient.smooth_upper_bound hg hlip s.x z
    rw [← hgdef] at hup
    have hzs : z - s.x = t • (y - s.x) := by rw [hzmix]; module
    rw [hzs, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hup
    nlinarith
  have hsupp := Gradient.convex_support hc hg s.x xs
  rw [← hgdef] at hsupp
  have hyxs : ⟪g, y - xs⟫ = ⟪Gv, x0 - xs⟫ := by
    have e1 : y - xs = (x0 - xs) - P (x0 - xs) := by
      rw [hy_eq, show xs - x0 = -(x0 - xs) by abel, show P (-(x0 - xs)) = -P (x0 - xs) by
        rw [hP, ← neg_one_smul ℝ (x0 - xs), proj3_smul, neg_one_smul]]
      abel
    rw [e1, inner_sub_right, hGv, inner_sub_left, hP, inner_proj_comm]
  have hmain : δ - ε / 4 ≤ ⟪Gv, x0 - xs⟫ := by
    have : ⟪g, s.x - xs⟫ = ⟪g, s.x - y⟫ + ⟪g, y - xs⟫ := by
      rw [← inner_add_right]; congr 1; abel
    rw [show xs - s.x = -(s.x - xs) by abel, inner_neg_right] at hsupp
    rw [show s.x - y = -(y - s.x) by abel, inner_neg_right] at this
    rw [hδdef]; linarith
  have hGv_pos : 3 * ε / (4 * R) ≤ ‖Gv‖ := by
    have := hmain.trans (real_inner_le_norm Gv (x0 - xs))
    have h2 : ‖Gv‖ * ‖x0 - xs‖ ≤ ‖Gv‖ * R := mul_le_mul_of_nonneg_left hx0 (norm_nonneg _)
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hGv0 : 0 < ‖Gv‖ := lt_of_lt_of_le (by positivity) hGv_pos
  have hgGv : ‖Gv‖ ≤ ‖g‖ := hF.norm_projOut_le g
  have hgLR : ‖g‖ ≤ L * R := by
    have h1 := PLHessian.grad_sq_le hL hg hlip hmin s.x
    rw [← hgdef] at h1
    have h2 := Gradient.smooth_upper_bound hg hlip xs x0
    rw [hg0, inner_zero_left, add_zero] at h2
    have h3 : ‖x0 - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx0 2
    have h5 : f s.x - f xs ≤ L / 2 * R ^ 2 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ L / 2)
      linarith only [this, h2, hmono]
    have h4 : ‖g‖ ^ 2 ≤ (L * R) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * L)
      nlinarith only [this, h1]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h4
  have hdir' := hdir s.x (hGv_pos.trans hgGv)
  rw [← hghat] at hdir'
  have hproj_diff : projOut s ghat - ‖g‖⁻¹ • Gv = projOut s (ghat - nrm g) := by
    rw [projOut_eq, projOut_eq, proj3_sub, nrm, proj3_smul, hGv, hP, smul_sub]; abel
  have hpd : ‖projOut s ghat - ‖g‖⁻¹ • Gv‖ ≤ θg := by
    rw [hproj_diff, projOut_eq]; exact (hF.norm_projOut_le _).trans hdir'
  have hg_pos : 0 < ‖g‖ := lt_of_lt_of_le hGv0 hgGv
  have hscale : nrm (‖g‖⁻¹ • Gv) = nrm Gv := nrm_smul_pos Gv (inv_pos.mpr hg_pos)
  have hGv_ne : ‖g‖⁻¹ • Gv ≠ 0 :=
    smul_ne_zero (inv_ne_zero hg_pos.ne') (norm_pos_iff.mp hGv0)
  have hθ' : ‖G - nrm Gv‖ ≤ θ := by
    have h1 := nrm_sub_le (projOut s ghat) (‖g‖⁻¹ • Gv) hGv_ne
    rw [hscale] at h1
    rw [hG]
    have hn : ‖‖g‖⁻¹ • Gv‖ = ‖Gv‖ / ‖g‖ := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    rw [hn] at h1
    calc ‖nrm (projOut s ghat) - nrm Gv‖ ≤ 2 * ‖projOut s ghat - ‖g‖⁻¹ • Gv‖ / (‖Gv‖ / ‖g‖) := h1
      _ ≤ 2 * θg / (‖Gv‖ / ‖g‖) := by gcongr
      _ = 2 * θg * ‖g‖ / ‖Gv‖ := by field_simp
      _ ≤ θ := by
          rw [div_le_iff₀ hGv0]
          have hθg0 : 0 ≤ θg := (norm_nonneg _).trans hdir'
          have hθ0 : 0 ≤ θ := by
            have h8 : 0 ≤ 8 * θg * L * R ^ 2 := by positivity
            exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 3 * ε)).mp
              (h8.trans hθg)
          have ha := mul_le_mul_of_nonneg_left hgLR (by positivity : (0 : ℝ) ≤ 2 * θg)
          have hb := mul_le_mul_of_nonneg_left hGv_pos hθ0
          have hcc : 2 * θg * (L * R) ≤ θ * (3 * ε / (4 * R)) := by
            rw [show θ * (3 * ε / (4 * R)) = 3 * ε * θ / (4 * R) by ring,
              le_div_iff₀ (by positivity)]
            nlinarith
          linarith
  have hnGv : ‖nrm Gv‖ = 1 := by
    rcases unitOrZero_nrm Gv with h0 | h1
    · have := nrm_decomp Gv; rw [h0, smul_zero] at this
      rw [this, norm_zero] at hGv0; exact (lt_irrefl _ hGv0).elim
    · exact h1
  have hG1 : ‖G‖ = 1 := by
    rcases (unitOrZero_nrm (projOut s ghat)) with h0 | h1
    · rw [← hG] at h0
      rw [h0, zero_sub, norm_neg, hnGv] at hθ'; linarith only [hθ', hθ]
    · rw [← hG] at h1; exact h1
  have hinner_unit := inner_unit_of_dist hnGv hG1
  have hθ0 : 0 ≤ ‖nrm Gv - G‖ := norm_nonneg _
  have hθ'' : ‖nrm Gv - G‖ ≤ θ := by rw [norm_sub_rev]; exact hθ'
  have hGvG : ⟪Gv, G⟫ ≥ 7 / 8 * ‖Gv‖ := by
    have hdec : Gv = ‖Gv‖ • nrm Gv := nrm_decomp Gv
    have : ⟪Gv, G⟫ = ‖Gv‖ * ⟪nrm Gv, G⟫ := by
      conv_lhs => rw [hdec]
      rw [real_inner_smul_left]
    rw [this, hinner_unit]
    have h4 : ‖nrm Gv - G‖ ^ 2 ≤ 1 / 4 := by nlinarith only [hθ'', hθ0, hθ]
    nlinarith only [mul_nonneg (norm_nonneg Gv)
      (show (0 : ℝ) ≤ 1 / 8 - ‖nrm Gv - G‖ ^ 2 / 2 by linarith only [h4])]
  have hPgG : ⟪P g, G⟫ = 0 := by
    rw [real_inner_comm]; exact hG_u _ (hF.inSpan_comb _ _ _)
  have hgG : ⟪g, G⟫ = ⟪Gv, G⟫ := by
    rw [hGv, inner_sub_left, hPgG, sub_zero]
  set ρ := ⟪G, x0 - xs⟫ + θ * R with hρ
  have hGvρ : ⟪Gv, x0 - xs⟫ ≤ ‖Gv‖ * ρ := by
    have hdec : Gv = ‖Gv‖ • nrm Gv := nrm_decomp Gv
    have : ⟪Gv, x0 - xs⟫ = ‖Gv‖ * ⟪nrm Gv, x0 - xs⟫ := by
      conv_lhs => rw [hdec]
      rw [real_inner_smul_left]
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h1 : ⟪nrm Gv, x0 - xs⟫ = ⟪G, x0 - xs⟫ + ⟪nrm Gv - G, x0 - xs⟫ := by
      rw [inner_sub_left]; ring
    have h2 : ⟪nrm Gv - G, x0 - xs⟫ ≤ θ * R :=
      (real_inner_le_norm _ _).trans (mul_le_mul hθ'' hx0 (norm_nonneg _)
        (le_trans hθ0 hθ''))
    rw [h1, hρ]; linarith only [h2]
  have hρpos : 0 < ρ := by
    by_contra hneg; push Not at hneg
    have : ‖Gv‖ * ρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hneg
    linarith only [hmain, hGvρ, this, hδ, hε]
  have hρle : ρ ≤ 3 / 2 * R := by
    have h1 : ⟪G, x0 - xs⟫ ≤ R := (real_inner_le_norm _ _).trans (by rw [hG1, one_mul]; exact hx0)
    have h2 := mul_le_mul_of_nonneg_right hθ hR.le
    rw [hρ]; linarith only [h1, h2]
  refine ⟨hρpos, hρle, ?_⟩
  set τ := ⟪g, G⟫ / L with hτ
  have hτ0 : 0 ≤ τ := by
    rw [hτ, hgG]; apply div_nonneg _ hL.le; linarith only [hGvG, norm_nonneg Gv]
  have hτR : τ ≤ R := by
    rw [hτ, div_le_iff₀ hL]
    have h1 : ‖g‖ * ‖G‖ ≤ L * R := by rw [hG1, mul_one]; exact hgLR
    have := (real_inner_le_norm g G).trans h1
    linarith only [this]
  have hp_aff : affine3 x0 u1 u2 G ‖s.x - x0‖ 0 (-τ) = s.x - τ • G := by
    simp only [affine3, zero_smul, add_zero, neg_smul]
    rw [← hsx_dec]; abel
  have hp := hxtE ‖s.x - x0‖ 0 (-τ) (by rw [abs_of_nonneg (norm_nonneg _)]; exact hw1x)
    (by simp [hR.le]) (by rw [abs_neg, abs_of_nonneg hτ0]; exact hτR)
  rw [hp_aff] at hp
  have hup := Gradient.smooth_upper_bound hg hlip s.x (s.x - τ • G)
  rw [show s.x - τ • G - s.x = -(τ • G) by abel, inner_neg_right, inner_smul_right, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, hG1, mul_one] at hup
  rw [← hgdef] at hup
  have hdesc : f (s.x - τ • G) ≤ f s.x - ⟪g, G⟫ ^ 2 / (2 * L) := by
    have e : τ * ⟪g, G⟫ - L / 2 * τ ^ 2 = ⟪g, G⟫ ^ 2 / (2 * L) := by
      rw [hτ]; field_simp; ring
    linarith only [hup, e]
  show f xn - f xs ≤ δ - δ ^ 2 / (8 * L * ρ ^ 2)
  have hgG2 : 49 / 64 * ‖Gv‖ ^ 2 ≤ ⟪g, G⟫ ^ 2 := by
    rw [hgG]; nlinarith only [hGvG, norm_nonneg Gv]
  have hGvρ2 : 9 / 16 * δ ^ 2 ≤ ‖Gv‖ ^ 2 * ρ ^ 2 := by
    have h1 : 3 / 4 * δ ≤ ‖Gv‖ * ρ := by linarith only [hmain, hGvρ, hδ]
    have h0 : 0 ≤ 3 / 4 * δ := by linarith only [hδ, hε]
    nlinarith only [h1, h0]
  have hQ : 441 / 2048 * (δ ^ 2 / (L * ρ ^ 2)) ≤ ⟪g, G⟫ ^ 2 / (2 * L) := by
    have h1 : δ ^ 2 / (L * ρ ^ 2) ≤ 16 / 9 * ‖Gv‖ ^ 2 / L := by
      rw [div_le_div_iff₀ (by positivity) hL]
      have := mul_le_mul_of_nonneg_left hGvρ2 hL.le
      linarith only [this]
    have h2 : 49 / 64 * ‖Gv‖ ^ 2 / (2 * L) ≤ ⟪g, G⟫ ^ 2 / (2 * L) :=
      div_le_div_of_nonneg_right hgG2 (by positivity)
    calc 441 / 2048 * (δ ^ 2 / (L * ρ ^ 2)) ≤ 441 / 2048 * (16 / 9 * ‖Gv‖ ^ 2 / L) := by
          gcongr
      _ = 49 / 64 * ‖Gv‖ ^ 2 / (2 * L) := by ring
      _ ≤ ⟪g, G⟫ ^ 2 / (2 * L) := h2
  have hηQ : η ≤ 185 / 2048 * (δ ^ 2 / (L * ρ ^ 2)) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have hρ2 : ρ ^ 2 ≤ 9 / 4 * R ^ 2 := by nlinarith only [hρpos, hρle]
    have hεδ : ε ^ 2 ≤ δ ^ 2 := by nlinarith only [hδ, hε]
    have h3 := mul_le_mul_of_nonneg_left hρ2 (by positivity : (0 : ℝ) ≤ L * η)
    linarith only [h3, h25, hεδ, sq_nonneg δ]
  have hfin : δ ^ 2 / (8 * L * ρ ^ 2) = 1 / 8 * (δ ^ 2 / (L * ρ ^ 2)) := by
    field_simp
  rw [hfin]
  have : f xn ≤ f s.x - ⟪g, G⟫ ^ 2 / (2 * L) + η := by linarith only [hxn_xt, hp, hdesc]
  rw [hδdef] at hQ hηQ ⊢
  linarith only [this, hQ, hηQ]

end Step

end OracleTemplate.ComparisonOrth
