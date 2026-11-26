import LongTails.Proofs.EscapeChainBounds
import LongTails.Proofs.ThirdOrderJetDifference

namespace LongTails.Proofs.EscapeChainJets

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds RelativeHessianArctan
open ThirdOrderJetDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smul_le {c A B : ℝ} {w : E} (hc : |c| ≤ A) (hw : ‖w‖ ≤ B) (hA : 0 ≤ A) :
    ‖c • w‖ ≤ A * B := by
  rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul hc hw (norm_nonneg w) hA

lemma jet_prod {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) {z u v : E}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (ha : 0 ≤ a₀ ∧ 0 ≤ a₁ ∧ 0 ≤ a₂ ∧ 0 ≤ a₃) (hb : 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ 0 ≤ b₂ ∧ 0 ≤ b₃)
    (fj : JetBound f z u v a₀ a₁ a₂ a₃ U V) (gj : JetBound g z u v b₀ b₁ b₂ b₃ U V) :
    JetBound (fun y => f y * g y) z u v (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) (a₀ * b₃ + 3 * (a₁ * b₂) + 3 * (a₂ * b₁) + a₃ * b₀) U V := by
  obtain ⟨ha₀, ha₁, ha₂, ha₃⟩ := ha
  obtain ⟨hb₀, hb₁, hb₂, hb₃⟩ := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul fj.val gj.val (abs_nonneg _) ha₀
  · rw [ProductCompositionJets.product_gradient hf hg]
    calc _ ≤ ‖f z • gradient g z‖ + ‖g z • gradient f z‖ := norm_add_le _ _
      _ ≤ a₀ * b₁ + b₀ * a₁ := add_le_add (smul_le fj.val gj.grad ha₀) (smul_le gj.val fj.grad hb₀)
      _ = _ := by ring
  · have h := D_mul hf hg z u
    unfold D at h; rw [h]
    calc _ ≤ |f z * ⟪gradient g z, u⟫| + |g z * ⟪gradient f z, u⟫| := abs_add_le _ _
      _ ≤ a₀ * (b₁ * U) + b₀ * (a₁ * U) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul fj.val gj.du (abs_nonneg _) ha₀)
            (mul_le_mul gj.val fj.du (abs_nonneg _) hb₀)
      _ = _ := by ring
  · have h := D_mul hf hg z v
    unfold D at h; rw [h]
    calc _ ≤ |f z * ⟪gradient g z, v⟫| + |g z * ⟪gradient f z, v⟫| := abs_add_le _ _
      _ ≤ a₀ * (b₁ * V) + b₀ * (a₁ * V) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul fj.val gj.dv (abs_nonneg _) ha₀)
            (mul_le_mul gj.val fj.dv (abs_nonneg _) hb₀)
      _ = _ := by ring
  · rw [ProductCompositionJets.product_hessian_apply hf hg]
    calc _ ≤ ‖f z • fderiv ℝ (gradient g) z u‖ + ‖⟪gradient f z, u⟫ • gradient g z‖ +
          ‖g z • fderiv ℝ (gradient f) z u‖ + ‖⟪gradient g z, u⟫ • gradient f z‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
      _ ≤ a₀ * (b₂ * U) + (a₁ * U) * b₁ + b₀ * (a₂ * U) + (b₁ * U) * a₁ :=
          add_le_add (add_le_add (add_le_add (smul_le fj.val gj.hu ha₀)
            (smul_le fj.du gj.grad (by positivity))) (smul_le gj.val fj.hu hb₀))
            (smul_le gj.du fj.grad (by positivity))
      _ = _ := by ring
  · rw [ProductCompositionJets.product_hessian_apply hf hg]
    calc _ ≤ ‖f z • fderiv ℝ (gradient g) z v‖ + ‖⟪gradient f z, v⟫ • gradient g z‖ +
          ‖g z • fderiv ℝ (gradient f) z v‖ + ‖⟪gradient g z, v⟫ • gradient f z‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
      _ ≤ a₀ * (b₂ * V) + (a₁ * V) * b₁ + b₀ * (a₂ * V) + (b₁ * V) * a₁ :=
          add_le_add (add_le_add (add_le_add (smul_le fj.val gj.hv ha₀)
            (smul_le fj.dv gj.grad (by positivity))) (smul_le gj.val fj.hv hb₀))
            (smul_le gj.dv fj.grad (by positivity))
      _ = _ := by ring
  · exact product_hessian_bilinear hf hg z u v hU ⟨ha₀, ha₁⟩ ⟨hb₀, hb₁⟩ fj gj
  · rw [ProductCompositionJets.product_third_apply hf hg]
    calc _ ≤ ‖f z • fderiv ℝ (fderiv ℝ (gradient g)) z u v‖ +
          ‖⟪gradient f z, u⟫ • fderiv ℝ (gradient g) z v‖ +
          ‖⟪gradient f z, v⟫ • fderiv ℝ (gradient g) z u‖ +
          ‖⟪fderiv ℝ (gradient f) z u, v⟫ • gradient g z‖ +
          ‖g z • fderiv ℝ (fderiv ℝ (gradient f)) z u v‖ +
          ‖⟪gradient g z, u⟫ • fderiv ℝ (gradient f) z v‖ +
          ‖⟪gradient g z, v⟫ • fderiv ℝ (gradient f) z u‖ +
          ‖⟪fderiv ℝ (gradient g) z u, v⟫ • gradient f z‖ := by
          grw [norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le,
            norm_add_le]
      _ ≤ a₀ * (b₃ * U * V) + (a₁ * U) * (b₂ * V) + (a₁ * V) * (b₂ * U) + (a₂ * U * V) * b₁ +
          b₀ * (a₃ * U * V) + (b₁ * U) * (a₂ * V) + (b₁ * V) * (a₂ * U) + (b₂ * U * V) * a₁ := by
          gcongr
          · exact smul_le fj.val gj.third ha₀
          · exact smul_le fj.du gj.hv (by positivity)
          · exact smul_le fj.dv gj.hu (by positivity)
          · exact smul_le fj.huv gj.grad (by positivity)
          · exact smul_le gj.val fj.third hb₀
          · exact smul_le gj.du fj.hv (by positivity)
          · exact smul_le gj.dv fj.hu (by positivity)
          · exact smul_le gj.huv fj.grad (by positivity)
      _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma jet_mono {f : E → ℝ} {z u v : E} {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ U V : ℝ} (hU : 0 ≤ U)
    (hV : 0 ≤ V) (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (fj : JetBound f z u v a₀ a₁ a₂ a₃ U V) : JetBound f z u v b₀ b₁ b₂ b₃ U V :=
  ⟨fj.val.trans h₀, fj.grad.trans h₁, fj.du.trans (by gcongr), fj.dv.trans (by gcongr),
    fj.hu.trans (by gcongr), fj.hv.trans (by gcongr), fj.huv.trans (by gcongr),
    fj.third.trans (by gcongr)⟩

omit [FiniteDimensional ℝ E] in
lemma jet_const (c : ℝ) (z u v : E) {U V : ℝ} :
    JetBound (fun _ : E => c) z u v |c| 0 0 0 U V := by
  have h1 : gradient (fun _ : E => c) = fun _ => 0 := gradient_fun_const' c
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h1]

lemma cmul_gradient {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c : ℝ) :
    gradient (fun y => c * f y) = fun y => c • gradient f y := by
  funext x
  have h := ((GradientDependentLocal.derivative_chain hf).1 x).const_mul c
  have hg : HasGradientAt (fun y => c * f y) (c • gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext w
    simp
  exact hg.gradient

lemma cmul_hessian {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c : ℝ) :
    fderiv ℝ (gradient (fun y => c * f y)) = fun y => c • fderiv ℝ (gradient f) y := by
  funext x
  rw [cmul_gradient hf c]
  exact ((GradientDependentLocal.derivative_chain hf).2.1 x).const_smul c |>.fderiv

lemma cmul_third {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun y => c * f y))) x = c • fderiv ℝ (fderiv ℝ (gradient f)) x := by
  rw [cmul_hessian hf c]
  exact ((GradientDependentLocal.derivative_chain hf).2.2 x).const_smul c |>.fderiv

lemma jet_cmul {f : E → ℝ} (hf : ContDiff ℝ 3 f) (c : ℝ) {z u v : E}
    {a₀ a₁ a₂ a₃ U V : ℝ} (_hU : 0 ≤ U) (_hV : 0 ≤ V) (fj : JetBound f z u v a₀ a₁ a₂ a₃ U V) :
    JetBound (fun y => c * f y) z u v (|c| * a₀) (|c| * a₁) (|c| * a₂) (|c| * a₃) U V := by
  have hc := abs_nonneg c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left fj.val hc
  · rw [cmul_gradient hf, norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left fj.grad hc
  · rw [cmul_gradient hf]; simp only [real_inner_smul_left, abs_mul]
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left fj.du hc
  · rw [cmul_gradient hf]; simp only [real_inner_smul_left, abs_mul]
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left fj.dv hc
  · rw [cmul_hessian hf]; simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left fj.hu hc
  · rw [cmul_hessian hf]; simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left fj.hv hc
  · rw [cmul_hessian hf]; simp only [smul_apply, real_inner_smul_left, abs_mul]
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using fj.huv) hc
  · rw [cmul_third hf]; simp only [smul_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using fj.third) hc

lemma jet_ridge {φ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφc : ContDiff ℝ 3 φ)
    (hφ : ∀ t, HasDerivAt φ (φ₁ t) t) (hφ₁ : ∀ t, HasDerivAt φ₁ (φ₂ t) t)
    (hφ₂ : ∀ t, HasDerivAt φ₂ (φ₃ t) t) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, |φ t| ≤ M ∧ |φ₁ t| ≤ M ∧ |φ₂ t| ≤ M ∧ |φ₃ t| ≤ M) (a z u v : E) {U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1) (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V) :
    JetBound (RidgeJets.value φ a) z u v M M M M U V := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hb ⟪a, z⟫
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ :=
    RidgeJets.jet_bounds hφc hφ hφ₁ hφ₂ a z u v hM hU hV ha hu hv h₀ h₁ h₂ h₃
  exact ⟨b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩

lemma lam_jet_bounds (c : ℝ) : |lam c| ≤ 2 ^ 30 ∧ |lam1 c| ≤ 2 ^ 30 ∧ |lam2 c| ≤ 2 ^ 30 ∧
    |lam3 c| ≤ 2 ^ 30 := by
  rcases le_or_gt (1 / 2048) (c ^ 2) with h | h
  · obtain ⟨e0, e1, e2, e3⟩ := lam_full h
    rw [e0, e1, e2, e3]; norm_num
  have hc : |c| ≤ 1 / 45 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (c ^ 2) ≤ Real.sqrt ((1 / 45) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 / 45 := Real.sqrt_sq (by norm_num)
  have hc0 := abs_nonneg c
  obtain ⟨b0, b1⟩ := unit_bounds (16384 * c ^ 2 - 4)
  obtain ⟨j1, j2, j3⟩ := jets_bound (16384 * c ^ 2 - 4)
  have n1 := unit1_nonneg (16384 * c ^ 2 - 4)
  have hX : |32768 * c| ≤ 32768 / 45 := by rw [abs_mul]; norm_num; linarith
  have hX0 := abs_nonneg (32768 * c)
  have hX2 : |32768 * c| ^ 2 ≤ (32768 / 45) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have hX3 : |32768 * c| ^ 3 ≤ (32768 / 45) ^ 3 := pow_le_pow_left₀ hX0 hX 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · show |unit (16384 * c ^ 2 - 4)| ≤ _
    rw [abs_of_nonneg b0]; linarith
  · unfold lam1; rw [abs_mul, abs_of_nonneg n1]
    nlinarith
  · unfold lam2
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg n1, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 32768)]
    have p2 := mul_le_mul j2 hX2 (by positivity) (by norm_num : (0 : ℝ) ≤ 2 / 3)
    nlinarith [p2]
  · unfold lam3
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_mul]
    norm_num
    have hY : 32768 * |c| ≤ 32768 / 45 := by linarith
    have hY3 := pow_le_pow_left₀ (by positivity) hY 3
    have p3 := mul_le_mul j3 hY3 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
    have p4 := mul_le_mul j2 hY (by positivity) (by norm_num : (0 : ℝ) ≤ 2 / 3)
    nlinarith [p3, p4]

lemma ag_jet_bounds {α : ℝ} (hα : 0 ≤ α) (β t : ℝ) :
    |ag α β t| ≤ 2 * (1 + α) ^ 3 ∧ |ag1 α β t| ≤ 2 * (1 + α) ^ 3 ∧ |ag2 α β t| ≤ 2 * (1 + α) ^ 3 ∧
      |ag3 α β t| ≤ 2 * (1 + α) ^ 3 := by
  obtain ⟨b0, b1, c0, c1, d2, d3⟩ := ag_bounds hα β t
  have h1 : 1 ≤ (1 + α) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : α ≤ (1 + α) ^ 3 := by nlinarith [pow_le_pow_left₀ (show 0 ≤ α by linarith) (show α ≤ 1 + α by linarith) 3,
    show α ≤ α ^ 3 ∨ α ^ 3 ≤ α from le_total _ _]
  have h3 : α ^ 2 ≤ (1 + α) ^ 3 := by nlinarith [sq_nonneg α]
  have h4 : α ^ 3 ≤ (1 + α) ^ 3 := pow_le_pow_left₀ hα (by linarith) 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg b0]; linarith
  · rw [abs_of_nonneg c0]; nlinarith
  · nlinarith
  · nlinarith

lemma profile_jets (t : ℝ) : |profile t| ≤ 8 ∧ |density t| ≤ 8 ∧ |densitySlope t| ≤ 8 ∧
    |densityCurvature t| ≤ 8 := by
  obtain ⟨p0, p1⟩ := profile_bounds t
  obtain ⟨h1, h2, h3⟩ := profile_jet_bounds t
  refine ⟨?_, by linarith, by linarith, h3⟩
  rw [abs_of_pos p0]; linarith [Real.pi_lt_four]

noncomputable def prevEnergy (u : ℕ → E) (l : ℕ) (w : E) : ℝ := if l = 0 then 0 else |⟪u (l - 1), w⟫|

noncomputable def energy (u v : ℕ → E) (l : ℕ) (w : E) : ℝ :=
  |⟪v l, w⟫| + |⟪u l, w⟫| + prevEnergy u l w

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_nonneg (u v : ℕ → E) (l : ℕ) (w : E) : 0 ≤ energy u v l w := by
  unfold energy prevEnergy; split_ifs <;> positivity

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_ge (u v : ℕ → E) (l : ℕ) (w : E) :
    |⟪v l, w⟫| ≤ energy u v l w ∧ |⟪u l, w⟫| ≤ energy u v l w ∧ prevEnergy u l w ≤ energy u v l w := by
  have h0 : 0 ≤ prevEnergy u l w := by unfold prevEnergy; split_ifs <;> positivity
  unfold energy
  refine ⟨by linarith [abs_nonneg ⟪u l, w⟫], by linarith [abs_nonneg ⟪v l, w⟫], by
    linarith [abs_nonneg ⟪u l, w⟫, abs_nonneg ⟪v l, w⟫]⟩

lemma prevPsi_jet (u : ℕ → E) (l : ℕ) (z w w' : E) (hn : l ≠ 0 → ‖u (l - 1)‖ ≤ 1) :
    JetBound (prevPsi u l) z w w' (2 ^ 30) (2 ^ 30) (2 ^ 30) (2 ^ 30)
      (prevEnergy u l w) (prevEnergy u l w') := by
  have hU : 0 ≤ prevEnergy u l w := by unfold prevEnergy; split_ifs <;> positivity
  have hV : 0 ≤ prevEnergy u l w' := by unfold prevEnergy; split_ifs <;> positivity
  cases l with
  | zero =>
    have h := jet_const (1 : ℝ) z w w' (U := prevEnergy u 0 w) (V := prevEnergy u 0 w')
    exact jet_mono hU hV (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  | succ l =>
    have hb : ∀ t, |psi t| ≤ 2 ^ 30 ∧ |psi1 t| ≤ 2 ^ 30 ∧ |psi2 t| ≤ 2 ^ 30 ∧ |psi3 t| ≤ 2 ^ 30 := by
      intro t
      obtain ⟨h0, h1, h2, h3⟩ := ag_jet_bounds (show (0 : ℝ) ≤ 8 by norm_num) (-4) t
      norm_num at h0 h1 h2 h3
      exact ⟨h0.trans (by norm_num), h1.trans (by norm_num), h2.trans (by norm_num),
        h3.trans (by norm_num)⟩
    have hu : |⟪u l, w⟫| ≤ prevEnergy u (l + 1) w := by simp [prevEnergy]
    have hv : |⟪u l, w'⟫| ≤ prevEnergy u (l + 1) w' := by simp [prevEnergy]
    exact jet_ridge (ag_contDiff 8 (-4)) (ag_hasDerivAt 8 (-4)) (ag1_hasDerivAt 8 (-4))
      (ag2_hasDerivAt 8 (-4)) (by norm_num) hb (u l) z w w' hU hV (hn (by omega)) hu hv

lemma link_jet (u v : ℕ → E) (l : ℕ) (z w w' : E) (hu : ‖u l‖ ≤ 1) (hv : ‖v l‖ ≤ 1)
    (hp : l ≠ 0 → ‖u (l - 1)‖ ≤ 1) :
    JetBound (link u v l) z w w' (2 ^ 120) (2 ^ 120) (2 ^ 120) (2 ^ 120)
      (energy u v l w) (energy u v l w') := by
  have hU := energy_nonneg u v l w
  have hV := energy_nonneg u v l w'
  obtain ⟨e1, e2, e3⟩ := energy_ge u v l w
  obtain ⟨f1, f2, f3⟩ := energy_ge u v l w'
  have hP := jet_mono hU hV le_rfl le_rfl le_rfl le_rfl
    (show JetBound (prevPsi u l) z w w' (2 ^ 30) (2 ^ 30) (2 ^ 30) (2 ^ 30)
      (energy u v l w) (energy u v l w') from by
      have h := prevPsi_jet u l z w w' hp
      have hP0 : 0 ≤ prevEnergy u l w := by unfold prevEnergy; split_ifs <;> positivity
      have hP0' : 0 ≤ prevEnergy u l w' := by unfold prevEnergy; split_ifs <;> positivity
      exact ⟨h.val, h.grad, h.du.trans (by gcongr), h.dv.trans (by gcongr), h.hu.trans (by gcongr),
        h.hv.trans (by gcongr), h.huv.trans (by gcongr), h.third.trans (by gcongr)⟩)
  have hΦb : ∀ t, |profile t| ≤ 2 ^ 30 ∧ |density t| ≤ 2 ^ 30 ∧ |densitySlope t| ≤ 2 ^ 30 ∧
      |densityCurvature t| ≤ 2 ^ 30 := by
    intro t
    obtain ⟨h0, h1, h2, h3⟩ := profile_jets t
    exact ⟨h0.trans (by norm_num), h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num)⟩
  have hΦ := jet_ridge profile_contDiff profile_derivative density_derivative
    densitySlope_derivative (by norm_num) hΦb (u l) z w w' hU hV hu e2 f2
  have hΛ := jet_ridge lam_contDiff lam_hasDerivAt lam1_hasDerivAt lam2_hasDerivAt (by norm_num)
    lam_jet_bounds (v l) z w w' hU hV hv e1 f1
  have hPΦ := jet_prod (prevPsi_smooth u l) (phiR_smooth (u l)) hU hV
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ hP hΦ
  have hPΦ' := jet_mono (b₀ := 2 ^ 63) (b₁ := 2 ^ 63) (b₂ := 2 ^ 63) (b₃ := 2 ^ 63) hU hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hPΦ
  have hcore := jet_prod (lamR_smooth (v l)) (pair_smooth u l) hU hV
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ hΛ hPΦ'
  have hcore' := jet_mono (b₀ := 2 ^ 96) (b₁ := 2 ^ 96) (b₂ := 2 ^ 96) (b₃ := 2 ^ 96) hU hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcore
  have h := jet_cmul (core_smooth u v l) (-strength) hU hV hcore'
  have hs : |-strength| * 2 ^ 96 = 2 ^ 120 := by
    unfold strength; norm_num
  rw [hs] at h
  exact h

end LongTails.Proofs.EscapeChainJets
