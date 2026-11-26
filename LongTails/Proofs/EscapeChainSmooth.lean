import LongTails.Proofs.EscapeChainJets

namespace LongTails.Proofs.EscapeChainSmooth

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds EscapeChainJets RelativeHessianArctan
open ThirdOrderJetDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

noncomputable def projL (u v : ℕ → E) (l : ℕ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ∑ m ∈ Finset.range l,
    ((innerSL ℝ (u m)).smulRight (u m) + (innerSL ℝ (v m)).smulRight (v m))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma projL_apply (l : ℕ) (x : E) :
    projL u v l x = x - ∑ m ∈ Finset.range l, (⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m) := by
  simp [projL, sum_apply]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma projL_inner (l : ℕ) (x e : E) :
    ⟪projL u v l x, e⟫ = ⟪x, e⟫ - ∑ m ∈ Finset.range l, (⟪u m, x⟫ * ⟪u m, e⟫ + ⟪v m, x⟫ * ⟪v m, e⟫) := by
  rw [projL_apply, inner_sub_left, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma projL_norm (fr : Frame K u v) {l : ℕ} (hl : l ≤ K) (x : E) :
    ‖projL u v l x‖ ^ 2 = resid u v l x := by
  rw [EscapeChainCount.resid_eq, ← real_inner_self_eq_norm_sq, projL_inner]
  have h1 : ∀ m ∈ Finset.range l, ⟪u m, projL u v l x⟫ = 0 ∧ ⟪v m, projL u v l x⟫ = 0 := by
    intro m hm
    have hml := Finset.mem_range.1 hm
    have hmK : m < K := lt_of_lt_of_le hml hl
    constructor
    · rw [real_inner_comm, projL_inner]
      have h2 : ∀ m' ∈ Finset.range l, (⟪u m', x⟫ * ⟪u m', u m⟫ + ⟪v m', x⟫ * ⟪v m', u m⟫) =
          ⟪u m', x⟫ * (if m' = m then 1 else 0) := by
        intro m' hm'
        have hm'K : m' < K := lt_of_lt_of_le (Finset.mem_range.1 hm') hl
        rw [fr.uu m' m hm'K hmK, fr.vu hm'K hmK]; ring
      rw [Finset.sum_congr rfl h2, sum_delta (fun m' => ⟪u m', x⟫), ite_eq_left hml, real_inner_comm]
      ring
    · rw [real_inner_comm, projL_inner]
      have h2 : ∀ m' ∈ Finset.range l, (⟪u m', x⟫ * ⟪u m', v m⟫ + ⟪v m', x⟫ * ⟪v m', v m⟫) =
          ⟪v m', x⟫ * (if m' = m then 1 else 0) := by
        intro m' hm'
        have hm'K : m' < K := lt_of_lt_of_le (Finset.mem_range.1 hm') hl
        rw [fr.uv m' m hm'K hmK, fr.vv m' m hm'K hmK]; ring
      rw [Finset.sum_congr rfl h2, sum_delta (fun m' => ⟪v m', x⟫), ite_eq_left hml, real_inner_comm]
      ring
  have hx : ⟪x, projL u v l x⟫ = ‖x‖ ^ 2 - ∑ m ∈ Finset.range l, (⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2) := by
    rw [real_inner_comm, projL_inner, real_inner_self_eq_norm_sq]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hsum : ∑ m ∈ Finset.range l, (⟪u m, x⟫ * ⟪u m, projL u v l x⟫ +
      ⟪v m, x⟫ * ⟪v m, projL u v l x⟫) = 0 :=
    Finset.sum_eq_zero fun m hm => by rw [(h1 m hm).1, (h1 m hm).2]; ring
  rw [hsum, sub_zero, hx]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma projL_le (fr : Frame K u v) {l : ℕ} (hl : l ≤ K) (x : E) : ‖projL u v l x‖ ≤ ‖x‖ := by
  have h := projL_norm fr hl x
  rw [EscapeChainCount.resid_eq] at h
  have : 0 ≤ ∑ m ∈ Finset.range l, (⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2) :=
    Finset.sum_nonneg fun _ _ => by positivity
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0) |>.1
    (by linarith)

lemma resid_gradient (l : ℕ) (x : E) : gradient (resid u v l) x = (2 : ℝ) • projL u v l x := by
  apply ext_inner_right ℝ
  intro e
  have h := D_resid (u := u) (v := v) l x e
  unfold D at h
  rw [h, real_inner_smul_left, projL_inner, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma resid_hessian (l : ℕ) (x : E) :
    fderiv ℝ (gradient (resid u v l)) x = (2 : ℝ) • projL u v l := by
  have h : gradient (resid u v l) = fun y => (2 : ℝ) • projL u v l y := funext (resid_gradient l)
  rw [h]
  exact ((projL u v l).hasFDerivAt.const_smul (2 : ℝ)).fderiv

lemma resid_third (l : ℕ) (x : E) : fderiv ℝ (fderiv ℝ (gradient (resid u v l))) x = 0 := by
  have h : fderiv ℝ (gradient (resid u v l)) = fun _ => (2 : ℝ) • projL u v l :=
    funext (resid_hessian l)
  rw [h]
  exact fderiv_const_apply _

lemma quarter_jets (l : ℕ) (x : E) :
    gradient (quarter u v l) x = (1 / 2 : ℝ) • projL u v l x ∧
      fderiv ℝ (gradient (quarter u v l)) x = (1 / 2 : ℝ) • projL u v l ∧
      fderiv ℝ (fderiv ℝ (gradient (quarter u v l))) x = 0 := by
  have hq : quarter u v l = fun y => (1 / 4 : ℝ) * resid u v l y := rfl
  have hs := resid_smooth u v l
  refine ⟨?_, ?_, ?_⟩
  · rw [hq, cmul_gradient hs]; simp only [resid_gradient, smul_smul]; norm_num
  · rw [hq, cmul_hessian hs]; simp only [resid_hessian, smul_smul]; norm_num
  · rw [hq, cmul_third hs, resid_third, smul_zero]

lemma window_jet (fr : Frame K u v) {l : ℕ} (hl : l ≤ K) (z w w' : E) :
    JetBound (window u v l) z w w' 64 64 64 64 ‖w‖ ‖w'‖ := by
  have hqs := quarter_smooth u v l
  obtain ⟨hg, hH, hT⟩ := quarter_jets (u := u) (v := v) l z
  have hW : window u v l = loc ∘ quarter u v l := rfl
  obtain ⟨b0, b1, c1a, c1b, c2, c3⟩ := loc_bounds (quarter u v l z)
  have hPn : ‖projL u v l‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact projL_le fr hl x
  have hHq : ‖fderiv ℝ (gradient (quarter u v l)) z‖ ≤ 1 / 2 := by
    rw [hH, norm_smul, Real.norm_eq_abs]; norm_num; linarith
  have hTq : ‖fderiv ℝ (fderiv ℝ (gradient (quarter u v l))) z‖ = 0 := by
    rw [hT]; exact ContinuousLinearMap.opNorm_zero
  rcases le_or_gt 4 (quarter u v l z) with h4 | h4
  · obtain ⟨e0, e1, e2, e3⟩ := loc_zero h4
    refine norm_bound _ z w w' ?_ ?_ ?_ ?_
    · rw [hW]; simp [e0]
    · rw [hW, ScalarCompositionJets.comp_gradient hqs loc_hasDerivAt, e1, zero_smul, norm_zero]
      norm_num
    · refine (ScalarCompositionJets.comp_hessian_norm hqs loc_contDiff loc_hasDerivAt
        loc1_hasDerivAt z).trans ?_
      rw [e1, e2]; norm_num
    · refine (ScalarCompositionJets.comp_third_norm hqs loc_contDiff loc_hasDerivAt
        loc1_hasDerivAt loc2_hasDerivAt z).trans ?_
      rw [e1, e2, e3]; norm_num
  · have hres : resid u v l z < 16 := by unfold quarter at h4; linarith
    have hpn : ‖projL u v l z‖ ≤ 4 := by
      have h := projL_norm fr hl z
      nlinarith [norm_nonneg (projL u v l z)]
    have hgq : ‖gradient (quarter u v l) z‖ ≤ 2 := by
      rw [hg, norm_smul, Real.norm_eq_abs]; norm_num; linarith
    have hg0 := norm_nonneg (gradient (quarter u v l) z)
    refine norm_bound _ z w w' ?_ ?_ ?_ ?_
    · rw [hW]; simp only [Function.comp]; rw [abs_of_nonneg b0]; linarith
    · rw [hW, ScalarCompositionJets.comp_gradient hqs loc_hasDerivAt, norm_smul, Real.norm_eq_abs]
      have : |loc1 (quarter u v l z)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (loc1 (quarter u v l z))]
    · refine (ScalarCompositionJets.comp_hessian_norm hqs loc_contDiff loc_hasDerivAt
        loc1_hasDerivAt z).trans ?_
      have : |loc1 (quarter u v l z)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hg2 : ‖gradient (quarter u v l) z‖ ^ 2 ≤ 4 := by nlinarith
      nlinarith [abs_nonneg (loc1 (quarter u v l z)), abs_nonneg (loc2 (quarter u v l z)),
        norm_nonneg (fderiv ℝ (gradient (quarter u v l)) z)]
    · refine (ScalarCompositionJets.comp_third_norm hqs loc_contDiff loc_hasDerivAt
        loc1_hasDerivAt loc2_hasDerivAt z).trans ?_
      rw [hTq]
      have hg3 : ‖gradient (quarter u v l) z‖ ^ 3 ≤ 8 := by
        have := pow_le_pow_left₀ hg0 hgq 3; norm_num at this; linarith
      have h3 : |loc2 (quarter u v l z)| * ‖gradient (quarter u v l) z‖ *
          ‖fderiv ℝ (gradient (quarter u v l)) z‖ ≤ (32 / 27) * 2 * (1 / 2) := by
        gcongr
      nlinarith [abs_nonneg (loc3 (quarter u v l z))]

lemma window_jet_zero (_fr : Frame K u v) {l : ℕ} (z w w' : E) (h4 : 4 ≤ quarter u v l z) :
    JetBound (window u v l) z w w' 0 0 0 0 ‖w‖ ‖w'‖ := by
  have hqs := quarter_smooth u v l
  have hW : window u v l = loc ∘ quarter u v l := rfl
  obtain ⟨e0, e1, e2, e3⟩ := loc_zero h4
  refine norm_bound _ z w w' ?_ ?_ ?_ ?_
  · rw [hW]; simp [e0]
  · rw [hW, ScalarCompositionJets.comp_gradient hqs loc_hasDerivAt, e1, zero_smul, norm_zero]
  · refine (ScalarCompositionJets.comp_hessian_norm hqs loc_contDiff loc_hasDerivAt
      loc1_hasDerivAt z).trans ?_
    rw [e1, e2]; norm_num
  · refine (ScalarCompositionJets.comp_third_norm hqs loc_contDiff loc_hasDerivAt
      loc1_hasDerivAt loc2_hasDerivAt z).trans ?_
    rw [e1, e2, e3]; norm_num

lemma add_hessian {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    fderiv ℝ (gradient (fun z => f z + g z)) x = fderiv ℝ (gradient f) x + fderiv ℝ (gradient g) x := by
  simpa only [one_mul, one_smul] using ThirdOrderAffineCalculus.combination_hessian hf hg 1 1 x

lemma add_third {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun z => f z + g z))) x =
      fderiv ℝ (fderiv ℝ (gradient f)) x + fderiv ℝ (fderiv ℝ (gradient g)) x := by
  simpa only [one_mul, one_smul] using ThirdOrderAffineCalculus.combination_third hf hg 1 1 x

lemma add_gradient {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    gradient (fun z => f z + g z) x = gradient f x + gradient g x := by
  simpa only [one_mul, one_smul] using ThirdOrderAffineCalculus.combination_gradient hf hg 1 1 x

lemma gam_jets (t : ℝ) : |gam t| ≤ 2 ^ 15 ∧ |gam1 t| ≤ 2 ^ 15 ∧ |gam2 t| ≤ 2 ^ 15 ∧
    |gam3 t| ≤ 2 ^ 15 := by
  obtain ⟨h0, h1, h2, h3⟩ := ag_jet_bounds (show (0 : ℝ) ≤ 20 by norm_num) (-12) t
  norm_num at h0 h1 h2 h3
  exact ⟨h0.trans (by norm_num), h1.trans (by norm_num), h2.trans (by norm_num),
    h3.trans (by norm_num)⟩

lemma sad_jets (t : ℝ) : |sad t| ≤ 2 ^ 22 ∧ |sad1 t| ≤ 2 ^ 22 ∧ |sad2 t| ≤ 2 ^ 22 ∧
    |sad3 t| ≤ 2 ^ 22 := by
  obtain ⟨h0, -, h1, h2, h3⟩ := sad_jet_bounds t
  exact ⟨h0.trans (by norm_num), h1.trans (by norm_num), h2, h3⟩

lemma prevGam_jet (fr : Frame K u v) {l : ℕ} (hl : l < K) (z w w' : E) :
    JetBound (prevGam u l) z w w' (2 ^ 15) (2 ^ 15) (2 ^ 15) (2 ^ 15) ‖w‖ ‖w'‖ := by
  cases l with
  | zero =>
    have h := jet_const (1 : ℝ) z w w' (U := ‖w‖) (V := ‖w'‖)
    exact jet_mono (norm_nonneg _) (norm_nonneg _) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h
  | succ l =>
    have hn : ‖u l‖ ≤ 1 := by
      have h := fr.uu l l (by omega) (by omega)
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
      nlinarith [norm_nonneg (u l)]
    have hu : |⟪u l, w⟫| ≤ ‖w‖ :=
      (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg w])
    have hv : |⟪u l, w'⟫| ≤ ‖w'‖ :=
      (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg w'])
    exact jet_ridge (ag_contDiff 20 (-12)) (ag_hasDerivAt 20 (-12)) (ag1_hasDerivAt 20 (-12))
      (ag2_hasDerivAt 20 (-12)) (by norm_num) gam_jets (u l) z w w' (norm_nonneg _) (norm_nonneg _)
      hn hu hv

lemma prevGam_jet_zero {l : ℕ} (z w w' : E) (hl : l ≠ 0) (ha : ⟪u (l - 1), z⟫ ≤ 3 / 5) :
    JetBound (prevGam u l) z w w' 0 0 0 0 ‖w‖ ‖w'‖ := by
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  simp only [Nat.succ_sub_one] at ha
  obtain ⟨e0, e1, e2, e3⟩ := gam_flat ha
  have e1' : ag1 20 (-12) ⟪u l', z⟫ = 0 := e1
  have e2' : ag2 20 (-12) ⟪u l', z⟫ = 0 := e2
  have e3' : ag3 20 (-12) ⟪u l', z⟫ = 0 := e3
  have hg : gradient (RidgeJets.value gam (u l')) z = 0 := by
    rw [RidgeJets.gradient_eq (ag_hasDerivAt 20 (-12)), e1', zero_smul]
  have hH : ∀ y, fderiv ℝ (gradient (RidgeJets.value gam (u l'))) z y = 0 := fun y => by
    rw [RidgeJets.hessian_apply (ag_contDiff 20 (-12)) (ag_hasDerivAt 20 (-12))
      (ag1_hasDerivAt 20 (-12)), e2', zero_mul, zero_smul]
  have hT : ∀ y y', fderiv ℝ (fderiv ℝ (gradient (RidgeJets.value gam (u l')))) z y y' = 0 :=
    fun y y' => by
      rw [RidgeJets.third_apply (ag_contDiff 20 (-12)) (ag_hasDerivAt 20 (-12))
        (ag1_hasDerivAt 20 (-12)) (ag2_hasDerivAt 20 (-12)), e3', zero_mul, zero_mul, zero_smul]
  show JetBound (RidgeJets.value gam (u l')) z w w' 0 0 0 0 ‖w‖ ‖w'‖
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [RidgeJets.value, e0, hg, hH, hT]

lemma sad_jet (fr : Frame K u v) {l : ℕ} (hl : l < K) (z w w' : E) :
    JetBound (RidgeJets.value sad (v l)) z w w' (2 ^ 22) (2 ^ 22) (2 ^ 22) (2 ^ 22) ‖w‖ ‖w'‖ := by
  have hn : ‖v l‖ ≤ 1 := by
    have h := fr.vv l l hl hl
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (v l)]
  have hu : |⟪v l, w⟫| ≤ ‖w‖ := (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg w])
  have hv : |⟪v l, w'⟫| ≤ ‖w'‖ := (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg w'])
  exact jet_ridge sad_contDiff sad_hasDerivAt sad1_hasDerivAt sad2_hasDerivAt (by norm_num) sad_jets
    (v l) z w w' (norm_nonneg _) (norm_nonneg _) hn hu hv

noncomputable def sadConst (u v : ℕ → E) (z : E) (l : ℕ) : ℝ :=
  open Classical in if active u v z l then 2 ^ 49 else 0

lemma saddle_jet (fr : Frame K u v) {l : ℕ} (hl : l < K) (z w w' : E) :
    JetBound (saddle u v l) z w w' (sadConst u v z l) (sadConst u v z l) (sadConst u v z l)
      (sadConst u v z l) ‖w‖ ‖w'‖ := by
  classical
  have hU := norm_nonneg w
  have hV := norm_nonneg w'
  have hS := sad_jet fr hl z w w'
  have hSW := jet_prod (sadR_smooth (v l)) (window_smooth u v l) hU hV
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ hS (window_jet fr hl.le z w w')
  have hSW' := jet_mono (b₀ := 2 ^ 31) (b₁ := 2 ^ 31) (b₂ := 2 ^ 31) (b₃ := 2 ^ 31) hU hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hSW
  unfold sadConst
  by_cases hact : active u v z l
  · rw [ite_eq_left hact]
    have h := jet_prod (prevGam_smooth u l) (inner_smooth u v l) hU hV
      ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ (prevGam_jet fr hl z w w') hSW'
    exact jet_mono hU hV (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  · rw [ite_eq_right hact]
    unfold active at hact
    rw [not_and_or] at hact
    rcases hact with h | h
    · rw [not_or] at h
      obtain ⟨h0, h1⟩ := h
      have h := jet_prod (prevGam_smooth u l) (inner_smooth u v l) hU hV
        ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩ ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
        (prevGam_jet_zero z w w' h0 (le_of_not_gt h1)) hSW'
      exact jet_mono hU hV (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
    · have hq : 4 ≤ quarter u v l z := by unfold quarter; linarith [lt_of_not_ge h]
      have hSW0 := jet_prod (sadR_smooth (v l)) (window_smooth u v l) hU hV
        ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩ hS
        (window_jet_zero fr z w w' hq)
      have hSW0' := jet_mono (b₀ := 0) (b₁ := 0) (b₂ := 0) (b₃ := 0) hU hV
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hSW0
      have h := jet_prod (prevGam_smooth u l) (inner_smooth u v l) hU hV
        ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
        (prevGam_jet fr hl z w w') hSW0'
      exact jet_mono hU hV (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sadConst_sum (fr : Frame K u v) (z : E) :
    ∑ l ∈ Finset.range K, sadConst u v z l ≤ 2 ^ 49 * 45 := by
  classical
  unfold sadConst
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have := active_card fr z K le_rfl
  rw [mul_comm]
  gcongr
  exact_mod_cast this

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_sq_sum (fr : Frame K u v) (w : E) :
    ∑ l ∈ Finset.range K, energy u v l w ^ 2 ≤ 6 * ‖w‖ ^ 2 := by
  have hb := bessel fr w
  have hsq : ∀ l, energy u v l w ^ 2 ≤ 3 * (⟪v l, w⟫ ^ 2 + ⟪u l, w⟫ ^ 2 + prevEnergy u l w ^ 2) := by
    intro l
    unfold energy
    have h1 : |⟪v l, w⟫| ^ 2 = ⟪v l, w⟫ ^ 2 := sq_abs _
    have h2 : |⟪u l, w⟫| ^ 2 = ⟪u l, w⟫ ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|⟪v l, w⟫| - |⟪u l, w⟫|), sq_nonneg (|⟪v l, w⟫| - prevEnergy u l w),
      sq_nonneg (|⟪u l, w⟫| - prevEnergy u l w)]
  have hprev : ∑ l ∈ Finset.range K, prevEnergy u l w ^ 2 ≤ ∑ m ∈ Finset.range K, ⟪u m, w⟫ ^ 2 := by
    rcases K with _ | K
    · simp
    rw [Finset.sum_range_succ']
    simp only [prevEnergy, ite_eq_right (Nat.succ_ne_zero _), Nat.succ_sub_one, sq_abs]
    norm_num
    rw [Finset.sum_range_succ]
    have := sq_nonneg ⟪u K, w⟫
    linarith
  calc _ ≤ ∑ l ∈ Finset.range K, 3 * (⟪v l, w⟫ ^ 2 + ⟪u l, w⟫ ^ 2 + prevEnergy u l w ^ 2) :=
        Finset.sum_le_sum fun l _ => hsq l
    _ = 3 * (∑ l ∈ Finset.range K, (⟪u l, w⟫ ^ 2 + ⟪v l, w⟫ ^ 2) +
          ∑ l ∈ Finset.range K, prevEnergy u l w ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 3 * (‖w‖ ^ 2 + ‖w‖ ^ 2) := by
        have h0 : ∑ m ∈ Finset.range K, ⟪u m, w⟫ ^ 2 ≤ ∑ m ∈ Finset.range K, (⟪u m, w⟫ ^ 2 + ⟪v m, w⟫ ^ 2) :=
          Finset.sum_le_sum fun m _ => le_add_of_nonneg_right (sq_nonneg _)
        linarith
    _ = 6 * ‖w‖ ^ 2 := by ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_pair_sum (fr : Frame K u v) (w w' : E) :
    ∑ l ∈ Finset.range K, energy u v l w * energy u v l w' ≤ 6 * (‖w‖ * ‖w'‖) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range K) (fun l => energy u v l w)
    (fun l => energy u v l w')
  have h1 := energy_sq_sum fr w
  have h2 := energy_sq_sum fr w'
  have hA : Real.sqrt (∑ l ∈ Finset.range K, energy u v l w ^ 2) ≤ Real.sqrt 6 * ‖w‖ := by
    rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h1
  have hB : Real.sqrt (∑ l ∈ Finset.range K, energy u v l w' ^ 2) ≤ Real.sqrt 6 * ‖w'‖ := by
    rw [← Real.sqrt_sq (norm_nonneg w'), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h2
  calc _ ≤ Real.sqrt (∑ l ∈ Finset.range K, energy u v l w ^ 2) *
        Real.sqrt (∑ l ∈ Finset.range K, energy u v l w' ^ 2) := hcs
    _ ≤ (Real.sqrt 6 * ‖w‖) * (Real.sqrt 6 * ‖w'‖) :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (by positivity)
    _ = 6 * (‖w‖ * ‖w'‖) := by
        rw [show Real.sqrt 6 * ‖w‖ * (Real.sqrt 6 * ‖w'‖) = (Real.sqrt 6) ^ 2 * (‖w‖ * ‖w'‖) by ring,
          Real.sq_sqrt (by norm_num)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_sum (fr : Frame K u v) (w : E) :
    ∑ l ∈ Finset.range K, energy u v l w ≤ Real.sqrt (6 * K) * ‖w‖ := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range K) (fun _ => (1 : ℝ))
    (fun l => energy u v l w)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  have h1 := energy_sq_sum fr w
  calc _ ≤ Real.sqrt K * Real.sqrt (∑ l ∈ Finset.range K, energy u v l w ^ 2) := hcs
    _ ≤ Real.sqrt K * (Real.sqrt 6 * ‖w‖) := by
        gcongr
        rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt h1
    _ = Real.sqrt (6 * K) * ‖w‖ := by
        rw [Real.sqrt_mul (by norm_num), mul_comm (Real.sqrt 6)]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma frame_norms (fr : Frame K u v) {l : ℕ} (hl : l < K) :
    ‖u l‖ ≤ 1 ∧ ‖v l‖ ≤ 1 ∧ (l ≠ 0 → ‖u (l - 1)‖ ≤ 1) := by
  have hn (w : E) (h : ⟪w, w⟫ = 1) : ‖w‖ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq] at h; nlinarith [norm_nonneg w]
  refine ⟨hn _ (by rw [fr.uu l l hl hl, ite_eq_left rfl]), hn _ (by rw [fr.vv l l hl hl, ite_eq_left rfl]), ?_⟩
  intro h0
  exact hn _ (by rw [fr.uu (l - 1) (l - 1) (by omega) (by omega), ite_eq_left rfl])

lemma hidden_third_bound (fr : Frame K u v) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (hidden K u v))) z‖ ≤ 2 ^ 124 := by
  have hT : fderiv ℝ (fderiv ℝ (gradient (hidden K u v))) z =
      ∑ l ∈ Finset.range K, (fderiv ℝ (fderiv ℝ (gradient (link u v l))) z +
        fderiv ℝ (fderiv ℝ (gradient (saddle u v l))) z) := by
    have h : hidden K u v = fun y => ∑ l ∈ Finset.range K, (link u v l y + saddle u v l y) := rfl
    rw [h, ThirdOrderAffineCalculus.sum_third _ (fun l _ => term_smooth u v l)]
    exact Finset.sum_congr rfl fun l _ => add_third (link_smooth u v l) (saddle_smooth u v l) z
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w'
  rw [hT]
  simp only [sum_apply, add_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ l ∈ Finset.range K,
      ‖fderiv ℝ (fderiv ℝ (gradient (link u v l))) z w w' +
        fderiv ℝ (fderiv ℝ (gradient (saddle u v l))) z w w'‖ ≤
      2 ^ 120 * (energy u v l w * energy u v l w') + sadConst u v z l * (‖w‖ * ‖w'‖) := by
    intro l hl
    have hlK := Finset.mem_range.1 hl
    obtain ⟨n1, n2, n3⟩ := frame_norms fr hlK
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have := (link_jet u v l z w w' n1 n2 n3).third
      linarith [show 2 ^ 120 * energy u v l w * energy u v l w' =
        2 ^ 120 * (energy u v l w * energy u v l w') by ring]
    · have := (saddle_jet fr hlK z w w').third
      linarith [show sadConst u v z l * ‖w‖ * ‖w'‖ = sadConst u v z l * (‖w‖ * ‖w'‖) by ring]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have h1 := energy_pair_sum fr w w'
  have h2 := sadConst_sum fr z
  have hww : 0 ≤ ‖w‖ * ‖w'‖ := by positivity
  calc _ ≤ 2 ^ 120 * (6 * (‖w‖ * ‖w'‖)) + 2 ^ 49 * 45 * (‖w‖ * ‖w'‖) := by gcongr
    _ ≤ 2 ^ 124 * ‖w‖ * ‖w'‖ := by nlinarith

lemma hidden_hessian_bound (fr : Frame K u v) (z : E) :
    ‖fderiv ℝ (gradient (hidden K u v)) z‖ ≤ 2 ^ 124 := by
  have hH : fderiv ℝ (gradient (hidden K u v)) z =
      ∑ l ∈ Finset.range K, (fderiv ℝ (gradient (link u v l)) z +
        fderiv ℝ (gradient (saddle u v l)) z) := by
    have h : hidden K u v = fun y => ∑ l ∈ Finset.range K, (link u v l y + saddle u v l y) := rfl
    rw [h, ThirdOrderAffineCalculus.sum_hessian _ (fun l _ => term_smooth u v l)]
    exact Finset.sum_congr rfl fun l _ => add_hessian (link_smooth u v l) (saddle_smooth u v l) z
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  set y := fderiv ℝ (gradient (hidden K u v)) z w with hy
  have hbil : ⟪y, y⟫ ≤ 2 ^ 124 * ‖w‖ * ‖y‖ := by
    have hexp : ⟪y, y⟫ = ∑ l ∈ Finset.range K, (⟪fderiv ℝ (gradient (link u v l)) z w, y⟫ +
        ⟪fderiv ℝ (gradient (saddle u v l)) z w, y⟫) := by
      nth_rewrite 1 [hy]
      rw [hH]
      simp only [sum_apply, add_apply, sum_inner, inner_add_left]
    rw [hexp]
    have hterm : ∀ l ∈ Finset.range K,
        ⟪fderiv ℝ (gradient (link u v l)) z w, y⟫ + ⟪fderiv ℝ (gradient (saddle u v l)) z w, y⟫ ≤
        2 ^ 120 * (energy u v l w * energy u v l y) + sadConst u v z l * (‖w‖ * ‖y‖) := by
      intro l hl
      have hlK := Finset.mem_range.1 hl
      obtain ⟨n1, n2, n3⟩ := frame_norms fr hlK
      have a1 := (link_jet u v l z w y n1 n2 n3).huv
      have a2 := (saddle_jet fr hlK z w y).huv
      have b1 := le_abs_self ⟪fderiv ℝ (gradient (link u v l)) z w, y⟫
      have b2 := le_abs_self ⟪fderiv ℝ (gradient (saddle u v l)) z w, y⟫
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have h1 := energy_pair_sum fr w y
    have h2 := sadConst_sum fr z
    have hww : 0 ≤ ‖w‖ * ‖y‖ := by positivity
    have hnum : (2 : ℝ) ^ 120 * 6 + 2 ^ 49 * 45 ≤ 2 ^ 124 := by norm_num
    calc _ ≤ 2 ^ 120 * (6 * (‖w‖ * ‖y‖)) + 2 ^ 49 * 45 * (‖w‖ * ‖y‖) := by gcongr
      _ = (2 ^ 120 * 6 + 2 ^ 49 * 45) * (‖w‖ * ‖y‖) := by ring
      _ ≤ 2 ^ 124 * (‖w‖ * ‖y‖) := by gcongr
      _ = 2 ^ 124 * ‖w‖ * ‖y‖ := by ring
  rw [real_inner_self_eq_norm_sq] at hbil
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hpos
  · have : (0 : ℝ) ≤ 2 ^ 124 * ‖w‖ := mul_nonneg (by norm_num) (norm_nonneg w)
    linarith
  · have h' : ‖y‖ * ‖y‖ ≤ (2 ^ 124 * ‖w‖) * ‖y‖ := by rw [← sq]; linarith [hbil]
    exact le_of_mul_le_mul_right h' hpos

lemma hidden_gradient_bound (fr : Frame K u v) (z : E) :
    ‖gradient (hidden K u v) z‖ ≤ 2 ^ 123 * Real.sqrt (K + 1) := by
  have hG : gradient (hidden K u v) z = ∑ l ∈ Finset.range K,
      (gradient (link u v l) z + gradient (saddle u v l) z) := by
    have h : hidden K u v = fun y => ∑ l ∈ Finset.range K, (link u v l y + saddle u v l y) := rfl
    rw [h, ThirdOrderAffineCalculus.sum_gradient _ (fun l _ => term_smooth u v l)]
    exact Finset.sum_congr rfl fun l _ => add_gradient (link_smooth u v l) (saddle_smooth u v l) z
  set y := gradient (hidden K u v) z with hy
  have hbil : ⟪y, y⟫ ≤ (2 ^ 120 * Real.sqrt (6 * K) + 2 ^ 49 * 45) * ‖y‖ := by
    have hexp : ⟪y, y⟫ = ∑ l ∈ Finset.range K, (⟪gradient (link u v l) z, y⟫ +
        ⟪gradient (saddle u v l) z, y⟫) := by
      nth_rewrite 1 [hG]
      simp only [sum_inner, inner_add_left]
    rw [hexp]
    have hterm : ∀ l ∈ Finset.range K,
        ⟪gradient (link u v l) z, y⟫ + ⟪gradient (saddle u v l) z, y⟫ ≤
        2 ^ 120 * energy u v l y + sadConst u v z l * ‖y‖ := by
      intro l hl
      have hlK := Finset.mem_range.1 hl
      obtain ⟨n1, n2, n3⟩ := frame_norms fr hlK
      have a1 := (link_jet u v l z y y n1 n2 n3).du
      have a2 := (saddle_jet fr hlK z y y).du
      have b1 := le_abs_self ⟪gradient (link u v l) z, y⟫
      have b2 := le_abs_self ⟪gradient (saddle u v l) z, y⟫
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have h1 := energy_sum fr y
    have h2 := sadConst_sum fr z
    calc _ ≤ 2 ^ 120 * (Real.sqrt (6 * K) * ‖y‖) + 2 ^ 49 * 45 * ‖y‖ := by gcongr
      _ = _ := by ring
  rw [real_inner_self_eq_norm_sq] at hbil
  have hy0 := norm_nonneg y
  have hb : ‖y‖ ≤ 2 ^ 120 * Real.sqrt (6 * K) + 2 ^ 49 * 45 := by
    rcases eq_or_lt_of_le hy0 with h0 | hpos
    · rw [← h0]; positivity
    · nlinarith
  have hs : Real.sqrt (6 * K) ≤ 3 * Real.sqrt (K + 1) := by
    rw [show (3 : ℝ) * Real.sqrt (K + 1) = Real.sqrt (9 * (K + 1)) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : 1 ≤ Real.sqrt (K + 1) := by
    exact Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) K])
  have e1 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 ^ 120 by positivity)
  have e2 : (2 : ℝ) ^ 49 * 45 ≤ 2 ^ 55 * Real.sqrt (K + 1) := by
    calc (2 : ℝ) ^ 49 * 45 ≤ 2 ^ 55 * 1 := by norm_num
      _ ≤ 2 ^ 55 * Real.sqrt (K + 1) := by gcongr
  have e3 : (2 : ℝ) ^ 120 * (3 * Real.sqrt (K + 1)) + 2 ^ 55 * Real.sqrt (K + 1) ≤
      2 ^ 123 * Real.sqrt (K + 1) := by
    have : (0 : ℝ) ≤ Real.sqrt (K + 1) := Real.sqrt_nonneg _
    linarith
  linarith

lemma hidden_value_bound (fr : Frame K u v) (z : E) : |hidden K u v z| ≤ 2 ^ 121 * (K + 1) := by
  unfold EscapeChainFunction.hidden
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ l ∈ Finset.range K, |link u v l z + saddle u v l z| ≤ 2 ^ 120 + sadConst u v z l := by
    intro l hl
    have hlK := Finset.mem_range.1 hl
    obtain ⟨n1, n2, n3⟩ := frame_norms fr hlK
    exact (abs_add_le _ _).trans (add_le_add (link_jet u v l z 0 0 n1 n2 n3).val
      (saddle_jet fr hlK z 0 0).val)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 := sadConst_sum fr z
  nlinarith [Nat.cast_nonneg (α := ℝ) K]

end LongTails.Proofs.EscapeChainSmooth
