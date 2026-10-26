import LongTails.Proofs.BFGSMatrix
import LongTails.Proofs.BFGSInequalities

open Matrix Finset
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BFGSRate

open LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSMatrix
open LongTails.Proofs.BFGSInequalities

variable {d : ℕ}

lemma inner_eq_dot (u v : Space d) : ⟪u, v⟫ = WithLp.ofLp u ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma norm_sq_eq_dot (u : Space d) : ‖u‖ ^ 2 = WithLp.ofLp u ⬝ᵥ WithLp.ofLp u := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dot]

lemma bfgsUpdate_zero (B : Matrix (Fin d) (Fin d) ℝ) : bfgsUpdate B 0 0 = B := by
  simp [bfgsUpdate]

lemma direction_zero (B : Matrix (Fin d) (Fin d) ℝ) : direction B 0 = 0 := by
  simp [direction]

lemma ofLp_direction (B : Matrix (Fin d) (Fin d) ℝ) (g : Space d) :
    WithLp.ofLp (direction B g) = -(B⁻¹ *ᵥ WithLp.ofLp g) := by
  simp [direction]

lemma posDef_smul_one {c : ℝ} (hc : 0 < c) : (c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_smul, transpose_one]
  · simp only [star_trivial, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    have : 0 < v ⬝ᵥ v := by
      rcases Function.ne_iff.mp hv with ⟨i, hi⟩
      simp only [dotProduct]
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, mem_univ _, mul_self_pos.mpr hi⟩
    positivity

lemma inv_quad_pos {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) {g : Fin d → ℝ} (hg : g ≠ 0) :
    0 < g ⬝ᵥ (B⁻¹ *ᵥ g) := by
  simpa using hB.inv.dotProduct_mulVec_pos hg

structure Traj (f : Space d → ℝ) (x g : ℕ → Space d) (B : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (α : ℕ → ℝ) (c1 c2 : ℝ) : Prop where
  grad : ∀ i, HasGradientAt f (g i) (x i)
  step : ∀ i, x (i + 1) = x i + α i • direction (B i) (g i)
  upd : ∀ i, B (i + 1) = bfgsUpdate (B i) (WithLp.ofLp (α i • direction (B i) (g i)))
    (WithLp.ofLp (g (i + 1) - g i))
  ls : ∀ i, ⟪g i, direction (B i) (g i)⟫ < 0 →
    0 < α i ∧ f (x (i + 1)) ≤ f (x i) + c1 * α i * ⟪g i, direction (B i) (g i)⟫ ∧
      c2 * ⟪g i, direction (B i) (g i)⟫ ≤ ⟪g (i + 1), direction (B i) (g i)⟫

structure Prob (f : Space d → ℝ) (xs x0 : Space d) (L κ : ℝ) : Prop where
  min : ∀ x, f xs ≤ f x
  conv : ∀ x gx, HasGradientAt f gx x → f x - f xs ≤ ⟪gx, x - xs⟫
  coco : ∀ x gx z gz, HasGradientAt f gx x → HasGradientAt f gz z →
    ‖gz - gx‖ ^ 2 ≤ L * ⟪gz - gx, z - x⟫
  cross : ∀ x gx z gz, HasGradientAt f gx x → HasGradientAt f gz z → f z ≤ f x0 →
    ⟪gz - gx, z - xs⟫ ^ 2 ≤ 2 * κ * ⟪gz - gx, z - x⟫ * (f z - f xs)

section

variable {f : Space d → ℝ} {x g : ℕ → Space d} {B : ℕ → Matrix (Fin d) (Fin d) ℝ} {α : ℕ → ℝ}
  {c1 c2 L κ : ℝ} {xs : Space d}

lemma descent_inner (Bi : Matrix (Fin d) (Fin d) ℝ) (gi : Space d) :
    ⟪gi, direction Bi gi⟫ = -(WithLp.ofLp gi ⬝ᵥ (Bi⁻¹ *ᵥ WithLp.ofLp gi)) := by
  rw [inner_eq_dot, ofLp_direction, dotProduct_neg]

lemma ofLp_ne_zero {v : Space d} (hv : v ≠ 0) : WithLp.ofLp v ≠ 0 := by
  intro h0
  apply hv
  rw [← WithLp.toLp_ofLp 2 v, h0]
  rfl

lemma descent_neg {Bi : Matrix (Fin d) (Fin d) ℝ} (hB : Bi.PosDef) {gi : Space d} (hg : gi ≠ 0) :
    ⟪gi, direction Bi gi⟫ < 0 := by
  rw [descent_inner]
  linarith [inv_quad_pos hB (ofLp_ne_zero hg)]

end

section steps

variable {f : Space d → ℝ} {x g : ℕ → Space d} {B : ℕ → Matrix (Fin d) (Fin d) ℝ} {α : ℕ → ℝ}
  {c1 c2 L κ : ℝ} {xs : Space d}

lemma stay (T : Traj f x g B α c1 c2) {i : ℕ} (hg : g i = 0) :
    x (i + 1) = x i ∧ g (i + 1) = g i ∧ B (i + 1) = B i := by
  have hx : x (i + 1) = x i := by rw [T.step, hg, direction_zero, smul_zero, add_zero]
  have hg' : g (i + 1) = g i := by
    have h1 := T.grad (i + 1)
    rw [hx] at h1
    exact h1.unique (T.grad i)
  refine ⟨hx, hg', ?_⟩
  rw [T.upd, hg', sub_self, hg, direction_zero, smul_zero]
  simpa using bfgsUpdate_zero (B i)

lemma sv_eq (B : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) (gi : Space d) :
    WithLp.ofLp (a • direction B gi) = a • -(B⁻¹ *ᵥ WithLp.ofLp gi) := by
  rw [WithLp.ofLp_smul, ofLp_direction]

lemma Bs_eq {Bi : Matrix (Fin d) (Fin d) ℝ} (hB : Bi.PosDef) (a : ℝ) (gi : Space d) :
    Bi *ᵥ WithLp.ofLp (a • direction Bi gi) = -(a • WithLp.ofLp gi) := by
  rw [sv_eq, mulVec_smul, mulVec_neg, mulVec_inv_mulVec hB, smul_neg]

lemma sBs_eq {Bi : Matrix (Fin d) (Fin d) ℝ} (hB : Bi.PosDef) (a : ℝ) (gi : Space d) :
    WithLp.ofLp (a • direction Bi gi) ⬝ᵥ (Bi *ᵥ WithLp.ofLp (a • direction Bi gi)) =
      a ^ 2 * (WithLp.ofLp gi ⬝ᵥ (Bi⁻¹ *ᵥ WithLp.ofLp gi)) := by
  rw [Bs_eq hB, sv_eq, dotProduct_neg, smul_dotProduct, neg_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm (Bi⁻¹ *ᵥ WithLp.ofLp gi)]
  ring

lemma ys_eq (gi gj : Space d) (Bi : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) :
    WithLp.ofLp (gj - gi) ⬝ᵥ WithLp.ofLp (a • direction Bi gi) =
      a * (⟪gj, direction Bi gi⟫ - ⟪gi, direction Bi gi⟫) := by
  rw [← inner_eq_dot, inner_smul_right, inner_sub_left]

lemma posDef_all (T : Traj f x g B α c1 c2) (hB0 : (B 0).PosDef) (hc2 : c2 < 1) :
    ∀ i, (B i).PosDef := by
  intro i
  induction i with
  | zero => exact hB0
  | succ i ih =>
    by_cases hg : g i = 0
    · rw [(stay T hg).2.2]
      exact ih
    · have hneg := descent_neg ih hg
      obtain ⟨hα, -, hw⟩ := T.ls i hneg
      rw [T.upd]
      apply upd_posDef ih
      · rw [sv_eq]
        intro h0
        have hv := ofLp_ne_zero hg
        have : (B i)⁻¹ *ᵥ WithLp.ofLp (g i) = 0 := by
          have h1 := congrArg (fun v => (α i)⁻¹ • v) h0
          simp only [smul_neg, smul_smul, inv_mul_cancel₀ hα.ne', one_smul, smul_zero,
            neg_eq_zero] at h1
          exact h1
        have h2 := inv_quad_pos ih hv
        rw [this, dotProduct_zero] at h2
        exact lt_irrefl _ h2
      · rw [ys_eq]
        apply mul_pos hα
        nlinarith
end steps

section quant

variable {f : Space d → ℝ} {x g : ℕ → Space d} {B : ℕ → Matrix (Fin d) (Fin d) ℝ} {α : ℕ → ℝ}
  {c1 c2 L κ : ℝ} {xs : Space d}

noncomputable def aq (g : ℕ → Space d) (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  WithLp.ofLp (g i) ⬝ᵥ ((B i)⁻¹ *ᵥ WithLp.ofLp (g i))

noncomputable def ys (g : ℕ → Space d) (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (α : ℕ → ℝ) (i : ℕ) : ℝ :=
  WithLp.ofLp (g (i + 1) - g i) ⬝ᵥ WithLp.ofLp (α i • direction (B i) (g i))

noncomputable def vd (x : ℕ → Space d) (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (xs : Space d) (i : ℕ) :
    ℝ :=
  WithLp.ofLp (x i - xs) ⬝ᵥ (B i *ᵥ WithLp.ofLp (x i - xs))

lemma mono (T : Traj f x g B α c1 c2) (hPD : ∀ i, (B i).PosDef) (hc1 : 0 < c1) (i : ℕ) :
    f (x (i + 1)) ≤ f (x i) := by
  by_cases hg : g i = 0
  · rw [(stay T hg).1]
  · have hneg := descent_neg (hPD i) hg
    obtain ⟨hα, harm, -⟩ := T.ls i hneg
    have : c1 * α i * ⟪g i, direction (B i) (g i)⟫ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hc1 hα).le hneg.le
    linarith

lemma below_start (T : Traj f x g B α c1 c2) (hPD : ∀ i, (B i).PosDef) (hc1 : 0 < c1) :
    ∀ i, f (x i) ≤ f (x 0) := by
  intro i
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (mono T hPD hc1 i).trans ih

lemma step_facts (T : Traj f x g B α c1 c2) (hPD : ∀ i, (B i).PosDef) {i : ℕ} (hg : g i ≠ 0) :
    0 < aq g B i ∧ 0 < α i ∧ (1 - c2) * α i * aq g B i ≤ ys g B α i ∧
      f (x (i + 1)) ≤ f (x i) - c1 * α i * aq g B i := by
  have ha : 0 < aq g B i := inv_quad_pos (hPD i) (ofLp_ne_zero hg)
  have hneg := descent_neg (hPD i) hg
  obtain ⟨hα, harm, hw⟩ := T.ls i hneg
  have hi : ⟪g i, direction (B i) (g i)⟫ = -aq g B i := descent_inner (B i) (g i)
  refine ⟨ha, hα, ?_, ?_⟩
  · rw [ys, ys_eq, hi]
    rw [hi] at hw
    nlinarith
  · rw [hi] at harm
    linarith

lemma s_ne_zero (hPD : ∀ i, (B i).PosDef) {i : ℕ} (hg : g i ≠ 0) (hα : 0 < α i) :
    WithLp.ofLp (α i • direction (B i) (g i)) ≠ 0 := by
  rw [sv_eq]
  intro h0
  have h1 := congrArg (fun v => (α i)⁻¹ • v) h0
  simp only [smul_neg, smul_smul, inv_mul_cancel₀ hα.ne', one_smul, smul_zero, neg_eq_zero] at h1
  have h2 := inv_quad_pos (hPD i) (ofLp_ne_zero hg)
  rw [h1, dotProduct_zero] at h2
  exact lt_irrefl _ h2

lemma recip_step (T : Traj f x g B α c1 c2) (hPD : ∀ i, (B i).PosDef) {i : ℕ} (hg : g i ≠ 0)
    (hc1 : 0 < c1) (hc2 : c2 < 1) (h0 : 0 < f (x i) - f xs) (h1 : 0 < f (x (i + 1)) - f xs) :
    c1 * (1 - c2) * ((α i * aq g B i) ^ 2 / (ys g B α i * (f (x i) - f xs) ^ 2)) ≤
      1 / (f (x (i + 1)) - f xs) - 1 / (f (x i) - f xs) := by
  obtain ⟨ha, hα, hy, harm⟩ := step_facts T hPD hg
  set D0 := f (x i) - f xs
  set D1 := f (x (i + 1)) - f xs
  set a := aq g B i
  set Y := ys g B α i
  have hc2' : 0 < 1 - c2 := by linarith
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) hy
  have hdec : c1 * α i * a ≤ D0 - D1 := by simp only [D0, D1]; linarith
  have hD : D1 ≤ D0 := by nlinarith [mul_pos (mul_pos hc1 hα) ha]
  have e1 : 1 / D1 - 1 / D0 = (D0 - D1) / (D0 * D1) := by field_simp
  rw [e1]
  have h2 : c1 * (1 - c2) * ((α i * a) ^ 2 / (Y * D0 ^ 2)) ≤ c1 * α i * a / D0 ^ 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : c1 * (1 - c2) * (α i * a) ^ 2 ≤ c1 * α i * a * Y := by
      have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ c1 * α i * a)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ D0 ^ 2)]
  have h3 : c1 * α i * a / D0 ^ 2 ≤ (D0 - D1) / D0 ^ 2 :=
    div_le_div_of_nonneg_right hdec (by positivity)
  have h4 : (D0 - D1) / D0 ^ 2 ≤ (D0 - D1) / (D0 * D1) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  linarith

lemma det_step (T : Traj f x g B α c1 c2) (hPD : ∀ i, (B i).PosDef) {i : ℕ} (hg : g i ≠ 0)
    (hc2 : c2 < 1) :
    det (B (i + 1)) = det (B i) * (ys g B α i / (α i ^ 2 * aq g B i)) := by
  obtain ⟨ha, hα, hy, -⟩ := step_facts T hPD hg
  have hY : 0 < ys g B α i :=
    lt_of_lt_of_le (mul_pos (mul_pos (by linarith) hα) ha) hy
  rw [T.upd, upd_det (hPD i) (s_ne_zero hPD hg hα) hY, sBs_eq (hPD i)]
  rfl

lemma trace_step (T : Traj f x g B α c1 c2) (P : Prob f xs (x 0) L κ) (hPD : ∀ i, (B i).PosDef)
    {i : ℕ} (hg : g i ≠ 0) (hc2 : c2 < 1) :
    trace (B (i + 1)) ≤ trace (B i) + L := by
  obtain ⟨ha, hα, hy, -⟩ := step_facts T hPD hg
  have hY : 0 < ys g B α i :=
    lt_of_lt_of_le (mul_pos (mul_pos (by linarith) hα) ha) hy
  rw [T.upd]
  refine (upd_trace_le (hPD i) (s_ne_zero hPD hg hα)).trans ?_
  have hc := P.coco (x i) (g i) (x (i + 1)) (g (i + 1)) (T.grad i) (T.grad (i + 1))
  have hstep : x (i + 1) - x i = α i • direction (B i) (g i) := by rw [T.step]; abel
  rw [hstep, norm_sq_eq_dot, inner_eq_dot] at hc
  have hY' : 0 < WithLp.ofLp (g (i + 1) - g i) ⬝ᵥ WithLp.ofLp (α i • direction (B i) (g i)) := hY
  have : WithLp.ofLp (g (i + 1) - g i) ⬝ᵥ WithLp.ofLp (g (i + 1) - g i) /
      (WithLp.ofLp (g (i + 1) - g i) ⬝ᵥ WithLp.ofLp (α i • direction (B i) (g i))) ≤ L := by
    rw [div_le_iff₀ hY']
    exact hc
  linarith

lemma vd_step (T : Traj f x g B α c1 c2) (P : Prob f xs (x 0) L κ) (hPD : ∀ i, (B i).PosDef)
    (hc1 : 0 < c1) {i : ℕ} (hg : g i ≠ 0) (hc2 : c2 < 1) (h0 : 0 < f (x i) - f xs) :
    (f (x i) - f xs) ^ 2 / aq g B i ≤
      vd x B xs i - vd x B xs (i + 1) + 2 * κ * (f (x (i + 1)) - f xs) := by
  obtain ⟨ha, hα, hy, -⟩ := step_facts T hPD hg
  have hY : 0 < ys g B α i :=
    lt_of_lt_of_le (mul_pos (mul_pos (by linarith) hα) ha) hy
  have hBt : (B i)ᵀ = B i := by
    have h := (hPD i).isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  set s := WithLp.ofLp (α i • direction (B i) (g i))
  set e := WithLp.ofLp (x i - xs)
  set y := WithLp.ofLp (g (i + 1) - g i)
  have hsBs : s ⬝ᵥ (B i *ᵥ s) = α i ^ 2 * aq g B i := sBs_eq (hPD i) (α i) (g i)
  have hsB0 : s ⬝ᵥ (B i *ᵥ s) ≠ 0 := by rw [hsBs]; positivity
  have hes : WithLp.ofLp (x (i + 1) - xs) = e + s := by
    rw [T.step, show x i + α i • direction (B i) (g i) - xs = (x i - xs) + α i • direction (B i) (g i)
      by abel, WithLp.ofLp_add]
  have hid := upd_distance hBt s y e hsB0
  have hV1 : vd x B xs (i + 1) = (e + s) ⬝ᵥ (bfgsUpdate (B i) s y *ᵥ (e + s)) := by
    rw [vd, hes, T.upd]
  have hsBe : s ⬝ᵥ (B i *ᵥ e) = -(α i * (WithLp.ofLp (g i) ⬝ᵥ e)) := by
    rw [← symm_dot hBt s e, Bs_eq (hPD i), neg_dotProduct, smul_dotProduct, smul_eq_mul]
  have hge : WithLp.ofLp (g i) ⬝ᵥ e = ⟪g i, x i - xs⟫ := (inner_eq_dot _ _).symm
  have hconv := P.conv (x i) (g i) (T.grad i)
  have hQ : (f (x i) - f xs) ^ 2 / aq g B i ≤ (s ⬝ᵥ (B i *ᵥ e)) ^ 2 / (s ⬝ᵥ (B i *ᵥ s)) := by
    rw [hsBe, hsBs, neg_sq, mul_pow, mul_div_mul_left _ _ (by positivity : α i ^ 2 ≠ 0), hge]
    apply div_le_div_of_nonneg_right _ ha.le
    exact pow_le_pow_left₀ h0.le hconv 2
  have hcross := P.cross (x i) (g i) (x (i + 1)) (g (i + 1)) (T.grad i) (T.grad (i + 1))
    (below_start T hPD hc1 (i + 1))
  have hG : (y ⬝ᵥ (e + s)) ^ 2 / (y ⬝ᵥ s) ≤ 2 * κ * (f (x (i + 1)) - f xs) := by
    have hstep : x (i + 1) - x i = α i • direction (B i) (g i) := by rw [T.step]; abel
    rw [hstep, inner_eq_dot, inner_eq_dot, hes] at hcross
    have hY' : 0 < y ⬝ᵥ s := hY
    rw [div_le_iff₀ hY']
    linarith [hcross]
  have hV0 : vd x B xs i = e ⬝ᵥ (B i *ᵥ e) := rfl
  rw [hV1, hid, hV0]
  linarith

end quant

section assembly

variable {f : Space d → ℝ} {x g : ℕ → Space d} {B : ℕ → Matrix (Fin d) (Fin d) ℝ} {α : ℕ → ℝ}
  {c1 c2 L κ : ℝ} {xs : Space d}

theorem main_bound (T : Traj f x g B α c1 c2) (P : Prob f xs (x 0) L κ) (hB0 : B 0 = L • 1)
    (hL : 0 < L) (hκ : 0 ≤ κ) (hc1 : 0 < c1) (hc2 : c2 < 1) (k : ℕ) (hk : 1 ≤ k) :
    f (x k) - f xs ≤ Real.exp 1 * (L * ‖x 0 - xs‖ ^ 2 +
      2 * κ * ∑ i ∈ range k, (f (x (i + 1)) - f xs)) / (c1 * (1 - c2) * (k : ℝ) ^ 2) := by
  have hPD := posDef_all T (by rw [hB0]; exact posDef_smul_one hL) hc2
  set D : ℕ → ℝ := fun i => f (x i) - f xs with hDdef
  have hDn : ∀ i, 0 ≤ D i := fun i => sub_nonneg.mpr (P.min _)
  have hDm : ∀ i, D (i + 1) ≤ D i := fun i => by simp only [D]; linarith [mono T hPD hc1 i]
  have hc2' : 0 < 1 - c2 := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hRHS : 0 ≤ Real.exp 1 * (L * ‖x 0 - xs‖ ^ 2 + 2 * κ * ∑ i ∈ range k, D (i + 1)) /
      (c1 * (1 - c2) * (k : ℝ) ^ 2) := by
    have hs := Finset.sum_nonneg fun i (_ : i ∈ range k) => hDn (i + 1)
    positivity
  change D k ≤ _
  by_cases hall : ∀ j ≤ k, 0 < D j
  · have hg : ∀ i < k, g i ≠ 0 := by
      intro i hi hgi
      have h1 := P.conv (x i) (g i) (T.grad i)
      rw [hgi, inner_zero_left] at h1
      have h2 := hall i hi.le
      simp only [D] at h2
      linarith
    set ζ : ℕ → ℝ := fun i => ys g B α i / (α i ^ 2 * aq g B i) with hζdef
    set Q : ℕ → ℝ := fun i => D i ^ 2 / aq g B i with hQdef
    have hζ : ∀ i < k, 0 < ζ i := by
      intro i hi
      obtain ⟨ha, hα, hy, -⟩ := step_facts T hPD (hg i hi)
      have hY : 0 < ys g B α i := lt_of_lt_of_le (by positivity) hy
      positivity
    have hQ : ∀ i < k, 0 < Q i := by
      intro i hi
      obtain ⟨ha, -, -, -⟩ := step_facts T hPD (hg i hi)
      have := hall i hi.le
      positivity
    have hrec : ∑ i ∈ range k, c1 * (1 - c2) * (1 / (ζ i * Q i)) ≤ 1 / D k - 1 / D 0 := by
      rw [← Finset.sum_range_sub (fun i => 1 / D i)]
      apply Finset.sum_le_sum
      intro i hi
      have hik := mem_range.mp hi
      obtain ⟨ha, hα, hy, -⟩ := step_facts T hPD (hg i hik)
      have hY : 0 < ys g B α i := lt_of_lt_of_le (by positivity) hy
      have hDi := hall i hik.le
      have e : 1 / (ζ i * Q i) = (α i * aq g B i) ^ 2 / (ys g B α i * D i ^ 2) := by
        simp only [ζ, Q]
        field_simp
      rw [e]
      exact recip_step T hPD (hg i hik) hc1 hc2 hDi (hall (i + 1) hik)
    have hdetk : ∀ n ≤ k, det (B n) = det (B 0) * ∏ i ∈ range n, ζ i := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        rw [prod_range_succ, det_step T hPD (hg n (by omega)) hc2, ih (by omega)]
        ring
    have htrk : ∀ n ≤ k, trace (B n) ≤ trace (B 0) + n * L := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        have := trace_step T P hPD (hg n (by omega)) hc2
        push_cast
        linarith [ih (by omega)]
    have hdet0 : det (B 0) = L ^ d := by
      rw [hB0, det_smul, det_one, Fintype.card_fin, mul_one]
    have htr0 : trace (B 0) = d * L := by
      rw [hB0, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
      ring
    have hdetpos : 0 < det (B k) := (hPD k).det_pos
    have hprod : ∏ i ∈ range k, ζ i ≤ Real.exp k := by
      have hlog := log_det_le (hPD k) hL
      have h1 : Real.log (det (B k)) ≤ d * Real.log L + k := by
        have h2 := htrk k le_rfl
        rw [htr0] at h2
        have h3 : trace (B k) / L ≤ d + k := by
          rw [div_le_iff₀ hL]
          linarith
        linarith
      have h3 : det (B k) ≤ L ^ d * Real.exp k := by
        rw [← Real.exp_log hdetpos]
        calc Real.exp (Real.log (det (B k))) ≤ Real.exp (d * Real.log L + k) :=
              Real.exp_le_exp.mpr h1
          _ = L ^ d * Real.exp k := by
            rw [Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]
      have h4 := hdetk k le_rfl
      rw [hdet0] at h4
      rw [h4] at h3
      exact le_of_mul_le_mul_left h3 (by positivity)
    have hQsum : ∑ i ∈ range k, Q i ≤ L * ‖x 0 - xs‖ ^ 2 + 2 * κ * ∑ i ∈ range k, D (i + 1) := by
      have h1 : ∑ i ∈ range k, Q i ≤
          ∑ i ∈ range k, (vd x B xs i - vd x B xs (i + 1) + 2 * κ * D (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hik := mem_range.mp hi
        exact vd_step T P hPD hc1 (hg i hik) hc2 (hall i hik.le)
      rw [sum_add_distrib, Finset.sum_range_sub', ← mul_sum] at h1
      have hVk : 0 ≤ vd x B xs k := by
        have := (hPD k).posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp (x k - xs))
        simp only [star_trivial] at this
        exact this
      have hV0 : vd x B xs 0 = L * ‖x 0 - xs‖ ^ 2 := by
        rw [vd, hB0, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, ← norm_sq_eq_dot]
      linarith
    have hamgm := sum_inv_ge (by omega : 0 < k) ζ Q hζ hQ hprod
    have hQs : 0 < ∑ i ∈ range k, Q i :=
      sum_pos (fun i hi => hQ i (mem_range.mp hi)) (nonempty_range_iff.mpr (by omega))
    have hDk := hall k le_rfl
    have hD0 := hall 0 (Nat.zero_le _)
    have key : c1 * (1 - c2) * ((k : ℝ) ^ 2 / (Real.exp 1 * ∑ i ∈ range k, Q i)) ≤ 1 / D k := by
      have h1 := mul_le_mul_of_nonneg_left hamgm (by positivity : (0 : ℝ) ≤ c1 * (1 - c2))
      have h3 : c1 * (1 - c2) * ∑ i ∈ range k, 1 / (ζ i * Q i) =
          ∑ i ∈ range k, c1 * (1 - c2) * (1 / (ζ i * Q i)) := Finset.mul_sum _ _ _
      have h2 : 0 < 1 / D 0 := by positivity
      linarith
    have hfin : D k ≤ Real.exp 1 * (∑ i ∈ range k, Q i) / (c1 * (1 - c2) * (k : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hDk] at key
      linarith
    calc D k ≤ Real.exp 1 * (∑ i ∈ range k, Q i) / (c1 * (1 - c2) * (k : ℝ) ^ 2) := hfin
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hQsum (Real.exp_pos 1).le
  · push Not at hall
    obtain ⟨j, hjk, hj⟩ := hall
    have hDj : D j = 0 := le_antisymm hj (hDn j)
    have hanti : ∀ n, D (j + n) ≤ D j := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => exact (hDm (j + n)).trans ih
    have h1 := hanti (k - j)
    rw [Nat.add_sub_cancel' hjk] at h1
    have hDk : D k = 0 := le_antisymm (h1.trans hDj.le) (hDn k)
    rw [hDk]
    exact hRHS

end assembly

end LongTails.Proofs.BFGSRate
