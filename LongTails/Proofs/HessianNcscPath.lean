import LongTails.Proofs.HessianNcscLocal
import LongTails.Proofs.HessianNcscNormalization

open scoped RealInnerProductSpace

namespace OracleTemplate.HessianNcsc

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

structure PathRel (H : Hyp f gx gy Hx Hy L μ ρ) (α γ η lam : ℝ) (w u xt : ℕ → E) (y : ℕ → F)
    (ξx : ℕ → E) (ζ : ℕ → F) : Prop where
  w_succ : ∀ t, w (t + 1) = w t + nphi η lam (u t)
  xt_eq : ∀ t, xt (t + 1) = w (t + 1) + ((1 - α) / α) • nphi η lam (u t)
  u_succ : ∀ t, u (t + 1) = (1 - α) • u t + α • (gx (xt (t + 1), y (t + 1)) + ξx (t + 1))
  y_succ : ∀ t, y (t + 2) = y (t + 1) + γ • (gy (xt (t + 1), y (t + 1)) + ζ (t + 1))

section defs
variable (H : Hyp f gx gy Hx Hy L μ ρ) (α γ : ℝ) (w u xt : ℕ → E) (y : ℕ → F)

noncomputable def eh (t : ℕ) : E := u t - Gs H (w t)

noncomputable def ee (t : ℕ) : F := y t - ystar H (xt t)

noncomputable def psi (t : ℕ) : E := eh H w u t - (α / γ) • Mm H (w t) (ee H xt y (t + 1))

noncomputable def Dterm (t : ℕ) : E :=
  (1 - α) • Gs H (w t) + α • Gs H (xt (t + 1)) - Gs H (w (t + 1))

noncomputable def rr (t : ℕ) : E :=
  gx (xt t, y t) - Gs H (xt t) - Bb H (xt t) (ee H xt y t)

noncomputable def ss (t : ℕ) : F := gy (xt t, y t) - Jb H (xt t) (ee H xt y t)

noncomputable def mis (t : ℕ) : E :=
  Bb H (xt t) (ee H xt y t) - Mm H (w t) (Jb H (xt t) (ee H xt y t))

noncomputable def dd (t : ℕ) : F := ystar H (xt (t + 1)) - ystar H (xt t)

noncomputable def Qterm (t : ℕ) : E :=
  Dterm H α w xt t + α • mis H w xt y (t + 1) + α • rr H xt y (t + 1) -
    α • Mm H (w (t + 1)) (ss H xt y (t + 1)) + (α / γ) • Mm H (w (t + 1)) (dd H xt (t + 1)) +
    (α / γ) • ((1 - α) • Mm H (w t) (ee H xt y (t + 1)) - Mm H (w (t + 1)) (ee H xt y (t + 1)))

end defs

variable {H : Hyp f gx gy Hx Hy L μ ρ} {α γ η lam : ℝ} {w u xt : ℕ → E} {y : ℕ → F}
  {ξx : ℕ → E} {ζ : ℕ → F}

omit [FiniteDimensional ℝ F] in
lemma PathRel.eh_succ (R : PathRel H α γ η lam w u xt y ξx ζ) (t : ℕ) :
    eh H w u (t + 1) = (1 - α) • eh H w u t + Dterm H α w xt t +
      α • Bb H (xt (t + 1)) (ee H xt y (t + 1)) + α • rr H xt y (t + 1) + α • ξx (t + 1) := by
  simp only [eh, Dterm, rr, R.u_succ t]
  simp only [smul_sub, smul_add, sub_smul, one_smul]
  abel

omit [FiniteDimensional ℝ F] in
lemma PathRel.ee_succ (R : PathRel H α γ η lam w u xt y ξx ζ) (t : ℕ) :
    ee H xt y (t + 2) = ee H xt y (t + 1) + γ • Jb H (xt (t + 1)) (ee H xt y (t + 1)) +
      γ • ss H xt y (t + 1) + γ • ζ (t + 1) - dd H xt (t + 1) := by
  simp only [ee, ss, dd, R.y_succ t]
  simp only [smul_sub, smul_add]
  abel

lemma PathRel.psi_succ (R : PathRel H α γ η lam w u xt y ξx ζ) (hγ : γ ≠ 0) (t : ℕ) :
    psi H α γ w u xt y (t + 1) = (1 - α) • psi H α γ w u xt y t +
      α • (ξx (t + 1) - Mm H (w (t + 1)) (ζ (t + 1))) + Qterm H α γ w xt y t := by
  have h1 := R.eh_succ t
  have h2 := R.ee_succ t
  have hM : ∀ v v' : F, Mm H (w (t + 1)) (v + v') = Mm H (w (t + 1)) v + Mm H (w (t + 1)) v' :=
    fun v v' => H.Mm_add _ v v'
  have hMs : ∀ (c : ℝ) (v : F), Mm H (w (t + 1)) (c • v) = c • Mm H (w (t + 1)) v :=
    fun c v => H.Mm_smul _ c v
  have hMsub : ∀ v v' : F, Mm H (w (t + 1)) (v - v') = Mm H (w (t + 1)) v - Mm H (w (t + 1)) v' :=
    fun v v' => H.Mm_sub _ v v'
  have hMJ : Mm H (w (t + 1)) (Jb H (xt (t + 1)) (ee H xt y (t + 1))) =
      Bb H (xt (t + 1)) (ee H xt y (t + 1)) - mis H w xt y (t + 1) := by
    simp [mis]
  simp only [psi, Qterm]
  rw [show t + 1 + 1 = t + 2 by ring, h2, h1]
  rw [hMsub, hM, hM, hM, hMs, hMs, hMs, hMJ]
  simp only [smul_sub, smul_add, smul_smul]
  have e1 : α / γ * γ = α := by field_simp
  rw [e1]

  module
section bounds

variable (R : PathRel H α γ η lam w u xt y ξx ζ)
include R

omit [FiniteDimensional ℝ F] in
lemma PathRel.xt_sub_w0 (hα : α ≠ 0) (t : ℕ) : xt (t + 1) - w t = (1 / α) • nphi η lam (u t) := by
  rw [R.xt_eq t, R.w_succ t]
  have : (1 / α) = 1 + (1 - α) / α := by field_simp; ring
  rw [this, add_smul, one_smul]; abel

omit [FiniteDimensional ℝ F] in
lemma PathRel.w_conv (hα : α ≠ 0) (t : ℕ) : w (t + 1) = (1 - α) • w t + α • xt (t + 1) := by
  have h := R.xt_sub_w0 hα t
  have h2 : xt (t + 1) = w t + (1 / α) • nphi η lam (u t) := by rw [← h]; abel
  rw [h2, R.w_succ t, smul_add, smul_smul, mul_one_div_cancel hα, one_smul]
  simp only [sub_smul, one_smul]; abel

omit [FiniteDimensional ℝ F] in
lemma PathRel.w_step (hl : 0 < lam) (hη : 0 ≤ η) (t : ℕ) : ‖w (t + 1) - w t‖ ≤ η := by
  rw [R.w_succ t, add_sub_cancel_left]; exact nphi_norm hl hη _

omit [FiniteDimensional ℝ F] in
lemma PathRel.w_dist (hl : 0 < lam) (hη : 0 ≤ η) (s n : ℕ) : ‖w (s + n) - w s‖ ≤ n * η := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 := R.w_step hl hη (s + n)
      calc ‖w (s + (n + 1)) - w s‖ = ‖(w (s + n + 1) - w (s + n)) + (w (s + n) - w s)‖ := by
            rw [show s + (n + 1) = s + n + 1 by ring]; congr 1; abel
        _ ≤ η + n * η := (norm_add_le _ _).trans (add_le_add h2 ih)
        _ = (↑(n + 1) : ℝ) * η := by push_cast; ring

omit [FiniteDimensional ℝ F] in
lemma PathRel.xt_sub_w (hα0 : 0 < α) (hα1 : α ≤ 1) (hl : 0 < lam) (hη : 0 ≤ η) (t : ℕ) :
    ‖xt (t + 1) - w (t + 1)‖ ≤ η / α := by
  rw [R.xt_eq t, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (div_nonneg (by linarith) hα0.le)]
  have h := nphi_norm hl hη (u t)
  calc (1 - α) / α * ‖nphi η lam (u t)‖ ≤ 1 / α * η := by
        apply mul_le_mul _ h (norm_nonneg _) (by positivity)
        rw [div_le_div_iff_of_pos_right hα0]; linarith
    _ = η / α := by ring

omit [FiniteDimensional ℝ F] in
lemma PathRel.xt_dist (hα0 : 0 < α) (hα1 : α ≤ 1) (hl : 0 < lam) (hη : 0 ≤ η) (s n : ℕ) :
    ‖xt (s + n + 1) - xt (s + 1)‖ ≤ 2 * η / α + n * η := by
  have h1 := R.xt_sub_w hα0 hα1 hl hη (s + n)
  have h2 := R.xt_sub_w hα0 hα1 hl hη s
  have h3 := R.w_dist hl hη (s + 1) n
  rw [show s + 1 + n = s + n + 1 by ring] at h3
  calc ‖xt (s + n + 1) - xt (s + 1)‖ =
      ‖(xt (s + n + 1) - w (s + n + 1)) + (w (s + n + 1) - w (s + 1)) - (xt (s + 1) - w (s + 1))‖ := by
        congr 1; abel
    _ ≤ η / α + n * η + η / α := by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add ((norm_add_le _ _).trans (add_le_add h1 h3)) h2
    _ = 2 * η / α + n * η := by ring

omit [FiniteDimensional ℝ F] in
lemma PathRel.Dterm_bound (hα0 : 0 < α) (hα1 : α ≤ 1) (hl : 0 < lam) (hη : 0 ≤ η) (t : ℕ) :
    ‖Dterm H α w xt t‖ ≤ ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * η ^ 2 / α := by
  have hd := H.Gs_defect (w t) (xt (t + 1)) hα0.le hα1
  rw [← R.w_conv hα0.ne' t] at hd
  have hsq := H.zs_sq (w t) (xt (t + 1))
  have hsub : ‖w t - xt (t + 1)‖ ≤ η / α := by
    rw [norm_sub_rev, R.xt_sub_w0 hα0.ne' t, norm_smul, Real.norm_of_nonneg (by positivity)]
    have := nphi_norm hl hη (u t)
    calc 1 / α * ‖nphi η lam (u t)‖ ≤ 1 / α * η := mul_le_mul_of_nonneg_left this (by positivity)
      _ = η / α := by ring
  have hsub2 : ‖w t - xt (t + 1)‖ ^ 2 ≤ (η / α) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hρ := H.ρnn
  have hμ := H.μpos
  have hk : 0 ≤ 1 + L / μ := by have := H.L_pos; positivity
  have ha1 : 0 ≤ α * (1 - α) := mul_nonneg hα0.le (by linarith)
  calc ‖Dterm H α w xt t‖ ≤ ρ * (1 + L / μ) * (α * (1 - α)) * sq (zs H (w t) - zs H (xt (t + 1))) := hd
    _ ≤ ρ * (1 + L / μ) * (α * (1 - α)) * ((1 + (L / μ) ^ 2) * (η / α) ^ 2) := by
        gcongr
        exact hsq.trans (mul_le_mul_of_nonneg_left hsub2 (by positivity))
    _ ≤ ρ * (1 + L / μ) * (α * 1) * ((1 + (L / μ) ^ 2) * (η / α) ^ 2) := by
        gcongr; linarith
    _ = ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * η ^ 2 / α := by field_simp

noncomputable def Yv (t : ℕ) : F := ystar H (xt t)

noncomputable def Zs (α : ℝ) (xt : ℕ → E) : ℕ → F
  | 0 => ystar H (xt 1)
  | r + 1 => (1 - α) • Zs α xt r + α • ystar H (xt (r + 1))

omit R in
omit [FiniteDimensional ℝ F] in
lemma Zs_succ (r : ℕ) : Zs (H := H) α xt (r + 1) = (1 - α) • Zs (H := H) α xt r + α • ystar H (xt (r + 1)) := rfl

omit [FiniteDimensional ℝ F] in
lemma PathRel.Z_close (hα0 : 0 < α) (hα1 : α ≤ 1) (hl : 0 < lam) (hη : 0 ≤ η) (t : ℕ) :
    ∀ r, r ≤ t → ‖ystar H (xt (t + 1)) - Zs (H := H) α xt r‖ ≤ (L / μ) * (3 * η / α + (t + 1 - r) * η) := by
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  intro r
  induction r with
  | zero =>
    intro _
    have h1 := H.ystar_lip (xt (t + 1)) (xt 1)
    have h2 := R.xt_dist hα0 hα1 hl hη 0 t
    simp only [zero_add] at h2
    simp only [Zs, CharP.cast_eq_zero, sub_zero]
    calc ‖ystar H (xt (t + 1)) - ystar H (xt 1)‖ ≤ L / μ * ‖xt (t + 1) - xt 1‖ := h1
      _ ≤ L / μ * (2 * η / α + t * η) := mul_le_mul_of_nonneg_left h2 hk
      _ ≤ L / μ * (3 * η / α + (t + 1) * η) := by
          apply mul_le_mul_of_nonneg_left _ hk
          have : 0 ≤ η / α := by positivity
          have e3 : 3 * η / α = 2 * η / α + η / α := by ring
          rw [e3]; linarith
  | succ r ih =>
    intro hr
    have hprev := ih (by omega)
    have h1 := H.ystar_lip (xt (t + 1)) (xt (r + 1))
    obtain ⟨n, hn⟩ : ∃ n, t = r + n := ⟨t - r, by omega⟩
    have h2 := R.xt_dist hα0 hα1 hl hη r n
    rw [← hn] at h2
    have e : ystar H (xt (t + 1)) - Zs (H := H) α xt (r + 1) =
        (1 - α) • (ystar H (xt (t + 1)) - Zs (H := H) α xt r) +
          α • (ystar H (xt (t + 1)) - ystar H (xt (r + 1))) := by
      rw [Zs_succ]; simp only [smul_sub, sub_smul, one_smul]; abel
    rw [e]
    have hn' : (n : ℝ) = (t : ℝ) - r := by rw [hn]; push_cast; ring
    calc ‖(1 - α) • (ystar H (xt (t + 1)) - Zs (H := H) α xt r) +
          α • (ystar H (xt (t + 1)) - ystar H (xt (r + 1)))‖
        ≤ (1 - α) * ((L / μ) * (3 * η / α + (t + 1 - r) * η)) +
            α * (L / μ * (2 * η / α + n * η)) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_of_nonneg (by linarith)]
            exact mul_le_mul_of_nonneg_left hprev (by linarith)
          · rw [norm_smul, Real.norm_of_nonneg hα0.le]
            exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hk)) hα0.le
      _ ≤ (L / μ) * (3 * η / α + (t + 1 - (↑(r + 1) : ℝ)) * η) := by
          rw [hn']; push_cast
          have e2 : (1 - α) * (L / μ * (3 * η / α + (↑t + 1 - ↑r) * η)) + α * (L / μ * (2 * η / α + (↑t - ↑r) * η)) =
              L / μ * (3 * η / α + (↑t + 1 - (↑r + 1)) * η) - L / μ * (α * η) := by
            field_simp; ring
          rw [e2]
          have : 0 ≤ L / μ * (α * η) := by positivity
          linarith

omit [FiniteDimensional ℝ F] in
lemma PathRel.Z_close_t (hα0 : 0 < α) (hα1 : α ≤ 1) (hl : 0 < lam) (hη : 0 ≤ η) (t : ℕ) :
    ‖ystar H (xt (t + 1)) - Zs (H := H) α xt t‖ ≤ 4 * (L / μ) * η / α := by
  have h := R.Z_close hα0 hα1 hl hη t t le_rfl
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  have : η ≤ η / α := by rw [le_div_iff₀ hα0]; nlinarith
  calc ‖ystar H (xt (t + 1)) - Zs (H := H) α xt t‖ ≤ (L / μ) * (3 * η / α + (t + 1 - t) * η) := h
    _ = (L / μ) * (3 * η / α + η) := by ring
    _ ≤ (L / μ) * (3 * η / α + η / α) := by gcongr
    _ = 4 * (L / μ) * η / α := by ring

omit R in
omit [FiniteDimensional ℝ F] in
lemma sqrt_zs_le (a b : E) :
    Real.sqrt (sq (zs H a - zs H b)) ≤ Real.sqrt (1 + (L / μ) ^ 2) * ‖a - b‖ := by
  have h := H.zs_sq a b
  rw [← Real.sqrt_sq (norm_nonneg (a - b)), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h

noncomputable def chi (t : ℕ) : E :=
  psi H α γ w u xt y t - (α / γ) • Mm H (w t) (ystar H (xt (t + 1)) - Zs (H := H) α xt t)

noncomputable def Qp (t : ℕ) : E :=
  Dterm H α w xt t + α • mis H w xt y (t + 1) + α • rr H xt y (t + 1) -
    α • Mm H (w (t + 1)) (ss H xt y (t + 1)) +
    (α / γ) • ((1 - α) • Mm H (w t) (ee H xt y (t + 1)) - Mm H (w (t + 1)) (ee H xt y (t + 1))) +
    ((1 - α) * (α / γ)) • (Mm H (w t) (ystar H (xt (t + 1)) - Zs (H := H) α xt t) -
      Mm H (w (t + 1)) (ystar H (xt (t + 1)) - Zs (H := H) α xt t))

lemma PathRel.chi_succ (hγ : γ ≠ 0) (t : ℕ) :
    chi (H := H) (α := α) (γ := γ) (w := w) (u := u) (xt := xt) (y := y) (t + 1) =
      (1 - α) • chi (H := H) (α := α) (γ := γ) (w := w) (u := u) (xt := xt) (y := y) t +
      α • (ξx (t + 1) - Mm H (w (t + 1)) (ζ (t + 1))) +
      Qp (H := H) (α := α) (γ := γ) (w := w) (xt := xt) (y := y) t := by
  have hp := R.psi_succ hγ t
  set V := ystar H (xt (t + 1)) - Zs (H := H) α xt t
  have hV : ystar H (xt (t + 1 + 1)) - Zs (H := H) α xt (t + 1) = dd H xt (t + 1) + (1 - α) • V := by
    simp only [V, dd, Zs_succ, smul_sub, sub_smul, one_smul]; abel
  have hM1 : Mm H (w (t + 1)) (dd H xt (t + 1) + (1 - α) • V) =
      Mm H (w (t + 1)) (dd H xt (t + 1)) + (1 - α) • Mm H (w (t + 1)) V := by
    rw [H.Mm_add, H.Mm_smul]
  simp only [chi, Qp]
  rw [hp, hV, hM1]
  simp only [Qterm, smul_add, smul_sub, smul_smul]
  module

lemma PathRel.Qp_bound (hα0 : 0 < α) (hα1 : α ≤ 1) (hγ : 0 < γ) (hl : 0 < lam) (hη : 0 ≤ η) (t : ℕ) :
    ‖Qp (H := H) (α := α) (γ := γ) (w := w) (xt := xt) (y := y) t‖ ≤
      ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * η ^ 2 / α +
      ρ * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * η * ‖ee H xt y (t + 1)‖ +
      α * (ρ * (1 + L / μ)) * ‖ee H xt y (t + 1)‖ ^ 2 +
      (α / γ) * ((ρ / μ) * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * η + α * (L / μ)) *
        ‖ee H xt y (t + 1)‖ +
      (α / γ) * ((ρ / μ) * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * η) * (4 * (L / μ) * η / α) := by
  set e := ee H xt y (t + 1)
  set V := ystar H (xt (t + 1)) - Zs (H := H) α xt t
  have hμ := H.μpos
  have hL := H.L_pos
  have hρ := H.ρnn
  have hk : 0 ≤ L / μ := by positivity
  set s2 := Real.sqrt (1 + (L / μ) ^ 2)
  have hs2 : 0 ≤ s2 := Real.sqrt_nonneg _
  have hD := R.Dterm_bound hα0 hα1 hl hη t
  have hmis : ‖mis H w xt y (t + 1)‖ ≤ ρ * (1 + L / μ) * s2 * (η / α) * ‖e‖ := by
    have h := H.mismatch (xt (t + 1)) (w (t + 1)) e
    have h2 := sqrt_zs_le (H := H) (xt (t + 1)) (w (t + 1))
    have h3 := R.xt_sub_w hα0 hα1 hl hη t
    calc ‖mis H w xt y (t + 1)‖ ≤ ρ * (1 + L / μ) * Real.sqrt (sq (zs H (xt (t + 1)) - zs H (w (t + 1)))) * ‖e‖ := h
      _ ≤ ρ * (1 + L / μ) * (s2 * ‖xt (t + 1) - w (t + 1)‖) * ‖e‖ := by gcongr
      _ ≤ ρ * (1 + L / μ) * (s2 * (η / α)) * ‖e‖ := by gcongr
      _ = ρ * (1 + L / μ) * s2 * (η / α) * ‖e‖ := by ring
  have hy : y (t + 1) = ystar H (xt (t + 1)) + e := by simp [e, ee]
  have hrr : ‖rr H xt y (t + 1)‖ ≤ ρ * ‖e‖ ^ 2 := by
    have h := H.lin_x (xt (t + 1)) e
    rw [← hy] at h; simpa [rr, e] using h
  have hss : ‖ss H xt y (t + 1)‖ ≤ ρ * ‖e‖ ^ 2 := by
    have h := H.lin_y (xt (t + 1)) e
    rw [← hy] at h; simpa [ss, e] using h
  have hMss : ‖Mm H (w (t + 1)) (ss H xt y (t + 1))‖ ≤ (L / μ) * (ρ * ‖e‖ ^ 2) :=
    (H.Mm_norm _ _).trans (mul_le_mul_of_nonneg_left hss hk)
  have hMd : ∀ v : F, ‖Mm H (w t) v - Mm H (w (t + 1)) v‖ ≤ (ρ / μ) * (1 + L / μ) * s2 * η * ‖v‖ := by
    intro v
    have h := H.Mm_diff (w t) (w (t + 1)) v
    have h2 := sqrt_zs_le (H := H) (w t) (w (t + 1))
    have h3 : ‖w t - w (t + 1)‖ ≤ η := by rw [norm_sub_rev]; exact R.w_step hl hη t
    calc ‖Mm H (w t) v - Mm H (w (t + 1)) v‖
        ≤ (ρ / μ) * (1 + L / μ) * Real.sqrt (sq (zs H (w t) - zs H (w (t + 1)))) * ‖v‖ := h
      _ ≤ (ρ / μ) * (1 + L / μ) * (s2 * ‖w t - w (t + 1)‖) * ‖v‖ := by gcongr
      _ ≤ (ρ / μ) * (1 + L / μ) * (s2 * η) * ‖v‖ := by gcongr
      _ = (ρ / μ) * (1 + L / μ) * s2 * η * ‖v‖ := by ring
  have hcorr : ‖(1 - α) • Mm H (w t) e - Mm H (w (t + 1)) e‖ ≤
      ((ρ / μ) * (1 + L / μ) * s2 * η + α * (L / μ)) * ‖e‖ := by
    have e1 : (1 - α) • Mm H (w t) e - Mm H (w (t + 1)) e =
        (Mm H (w t) e - Mm H (w (t + 1)) e) - α • Mm H (w t) e := by
      simp only [sub_smul, one_smul]; abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hα0.le]
    have := H.Mm_norm (w t) e
    nlinarith [hMd e]
  have hVb := R.Z_close_t hα0 hα1 hl hη t
  have hlast : ‖Mm H (w t) V - Mm H (w (t + 1)) V‖ ≤
      (ρ / μ) * (1 + L / μ) * s2 * η * (4 * (L / μ) * η / α) :=
    (hMd V).trans (mul_le_mul_of_nonneg_left hVb (by positivity))
  have hc : 0 ≤ 1 - α := by linarith
  simp only [Qp]
  have hag : 0 ≤ α / γ := by positivity
  calc ‖Dterm H α w xt t + α • mis H w xt y (t + 1) + α • rr H xt y (t + 1) -
        α • Mm H (w (t + 1)) (ss H xt y (t + 1)) +
        (α / γ) • ((1 - α) • Mm H (w t) e - Mm H (w (t + 1)) e) +
        ((1 - α) * (α / γ)) • (Mm H (w t) V - Mm H (w (t + 1)) V)‖
      ≤ ‖Dterm H α w xt t‖ + α * ‖mis H w xt y (t + 1)‖ + α * ‖rr H xt y (t + 1)‖ +
          α * ‖Mm H (w (t + 1)) (ss H xt y (t + 1))‖ +
          (α / γ) * ‖(1 - α) • Mm H (w t) e - Mm H (w (t + 1)) e‖ +
          (α / γ) * ‖Mm H (w t) V - Mm H (w (t + 1)) V‖ := by
        have h6 : ‖((1 - α) * (α / γ)) • (Mm H (w t) V - Mm H (w (t + 1)) V)‖ ≤
            (α / γ) * ‖Mm H (w t) V - Mm H (w (t + 1)) V‖ := by
          rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hc hag)]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          nlinarith
        refine (norm_add_le _ _).trans (add_le_add ?_ h6)
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [norm_smul, Real.norm_of_nonneg hα0.le]
            · rw [norm_smul, Real.norm_of_nonneg hα0.le]
          · rw [norm_smul, Real.norm_of_nonneg hα0.le]
        · rw [norm_smul, Real.norm_of_nonneg hag]
    _ ≤ ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * η ^ 2 / α +
          α * (ρ * (1 + L / μ) * s2 * (η / α) * ‖e‖) + α * (ρ * ‖e‖ ^ 2) +
          α * ((L / μ) * (ρ * ‖e‖ ^ 2)) +
          (α / γ) * (((ρ / μ) * (1 + L / μ) * s2 * η + α * (L / μ)) * ‖e‖) +
          (α / γ) * ((ρ / μ) * (1 + L / μ) * s2 * η * (4 * (L / μ) * η / α)) := by
        gcongr
    _ = _ := by field_simp; ring

end bounds

end OracleTemplate.HessianNcsc
