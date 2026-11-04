import LongTails.Proofs.InexactJacobianGeometry
import LongTails.Proofs.LazyAnchoredLyapunov

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InexactJacobianPhase

open LazyAnchoredLyapunov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma anchor_residual_bound (x0 z g : E) {A r : ℝ} (hr : 0 ≤ r)
    (hV : potential x0 A z g ≤ 0) (hz : ‖z - x0‖ ≤ 3 * r) :
    ‖x0 - z - A • g‖ ≤ 3 * r := by
  have he : ‖x0 - z - A • g‖ ^ 2 = ‖z - x0‖ ^ 2 + 2 * potential x0 A z g := by
    unfold potential
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
    have hi : ⟪x0 - z, g⟫ = -⟪g, z - x0⟫ := by
      rw [real_inner_comm, ← inner_neg_right]
      congr 1
      abel
    rw [hi, norm_sub_rev x0 z]
    ring
  nlinarith [norm_nonneg (x0 - z - A • g), norm_nonneg (z - x0)]

lemma extrapolation_bound (x0 xs z g : E) {A a r : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hr : 0 ≤ r) (hx : ‖x0 - xs‖ ≤ r)
    (hz : ‖z - x0‖ ≤ 3 * r) (hV : potential x0 A z g ≤ 0) :
    let b := (a / (A + a)) • x0 + (A / (A + a)) • z
    let c := b - (a * A / (A + a)) • g
    ‖b - xs‖ ≤ 4 * r ∧ ‖c - xs‖ ≤ 7 * r := by
  dsimp only
  have hden : 0 < A + a := by positivity
  have hα : 0 ≤ a / (A + a) := by positivity
  have hα₁ : a / (A + a) ≤ 1 := by rw [div_le_one hden]; linarith
  have hβ : 0 ≤ A / (A + a) := by positivity
  have hβ₁ : A / (A + a) ≤ 1 := by rw [div_le_one hden]; linarith
  have he : a / (A + a) + A / (A + a) = 1 := by field_simp; ring
  have hb : (a / (A + a)) • x0 + (A / (A + a)) • z - xs =
      (x0 - xs) + (A / (A + a)) • (z - x0) := by
    have he' : a / (A + a) = 1 - A / (A + a) := by linarith
    rw [he']; module
  have hc : ((a / (A + a)) • x0 + (A / (A + a)) • z -
      (a * A / (A + a)) • g) - xs =
      (z - x0) + (x0 - xs) + (a / (A + a)) • (x0 - z - A • g) := by
    have he' : A / (A + a) = 1 - a / (A + a) := by linarith
    have he'' : a * A / (A + a) = (a / (A + a)) * A := by ring
    rw [he', he'']; module
  have hnormα : ∀ v : E, ‖(a / (A + a)) • v‖ ≤ ‖v‖ := by
    intro v
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
    exact mul_le_of_le_one_left (norm_nonneg v) hα₁
  have hnormβ : ∀ v : E, ‖(A / (A + a)) • v‖ ≤ ‖v‖ := by
    intro v
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
    exact mul_le_of_le_one_left (norm_nonneg v) hβ₁
  constructor
  · rw [hb]
    have h := norm_add_le (x0 - xs) ((A / (A + a)) • (z - x0))
    linarith [hnormβ (z - x0)]
  · rw [hc]
    have h₁ := norm_add_le ((z - x0) + (x0 - xs))
      ((a / (A + a)) • (x0 - z - A • g))
    have h₂ := norm_add_le (z - x0) (x0 - xs)
    have h₃ := anchor_residual_bound x0 z g hr hV hz
    linarith [hnormα (x0 - z - A • g)]

lemma accepted_descent (x0 z y g gy e c : E) {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a)
    (hy : y - x0 = (A / (A + a)) • (z - x0) - a • gy + e)
    (hc : c = (a / (A + a)) • x0 + (A / (A + a)) • z -
      (a * A / (A + a)) • g)
    (hm : A = 0 ∨ 0 ≤ ⟪gy - g, y - z⟫) (he : ‖e‖ ≤ ‖y - c‖ / 2) :
    potential x0 (A + a) y gy ≤ potential x0 A z g -
      3 / 8 * ((A + a) / a) ^ 2 * ‖y - c‖ ^ 2 := by
  have h : potential x0 (A + a) y gy ≤ potential x0 A z g +
      (A + a) ^ 2 / (2 * a ^ 2) *
        (‖e‖ ^ 2 - ‖y - (((a / (A + a)) • x0 + (A / (A + a)) • z) -
          (a * A / (A + a)) • g)‖ ^ 2) := by
    rcases hm with hzero | hm
    · subst A
      have h := descent x0 z y gy gy e a 0 ha (by rfl) hy (by simp)
      simpa [potential] using h
    · exact descent x0 z y g gy e a A ha hA hy hm
  rw [← hc] at h
  have he' : ‖e‖ ^ 2 ≤ ‖y - c‖ ^ 2 / 4 := by
    nlinarith [norm_nonneg e, norm_nonneg (y - c)]
  have hcoef : 0 ≤ (A + a) ^ 2 / (2 * a ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left he' hcoef
  have hid : (A + a) ^ 2 / (2 * a ^ 2) * (‖y - c‖ ^ 2 / 4) -
      (A + a) ^ 2 / (2 * a ^ 2) * ‖y - c‖ ^ 2 =
      -(3 / 8 * ((A + a) / a) ^ 2 * ‖y - c‖ ^ 2) := by ring
  nlinarith

lemma accepted_invariant (x0 xs z y g gy e c : E) {A a r : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hr : 0 ≤ r) (hx : ‖x0 - xs‖ ≤ r)
    (hz : ‖z - x0‖ ≤ 3 * r) (hV : potential x0 A z g ≤ 0)
    (hy : y - x0 = (A / (A + a)) • (z - x0) - a • gy + e)
    (hc : c = (a / (A + a)) • x0 + (A / (A + a)) • z -
      (a * A / (A + a)) • g)
    (hm : A = 0 ∨ 0 ≤ ⟪gy - g, y - z⟫) (hg : 0 ≤ ⟪gy, y - xs⟫)
    (he : ‖e‖ ≤ ‖y - c‖ / 2) :
    potential x0 (A + a) y gy ≤ 0 ∧ ‖y - x0‖ ≤ 3 * r ∧
      ‖gy‖ ≤ 2 * r / (A + a) := by
  have hden : 0 < A + a := by positivity
  have hd := accepted_descent x0 z y g gy e c hA ha hy hc hm he
  have hv : potential x0 (A + a) y gy ≤ 0 := by
    have : 0 ≤ 3 / 8 * ((A + a) / a) ^ 2 * ‖y - c‖ ^ 2 := by positivity
    linarith
  have hlo := potential_lower x0 xs y gy (A + a) r hden.le hx hg
  have hres := residual_bound x0 xs y gy (A + a) r hden hx hg hv
  have hq : 0 < (A + a) / a := div_pos hden ha
  have hs : ((A + a) / a) * ‖y - c‖ ≤ 2 * r := by
    nlinarith [sq_nonneg (((A + a) / a) * ‖y - c‖ - 2 * r)]
  have hs' : ‖y - c‖ ≤ 2 * r * a / (A + a) := by
    apply (le_div_iff₀ hden).2
    have h := (div_le_iff₀ ha).1 (show (A + a) * ‖y - c‖ / a ≤ 2 * r by
      simpa only [div_mul_eq_mul_div] using hs)
    nlinarith
  have he' : ‖e‖ ≤ r * a / (A + a) := by
    have hid : 2 * r * a / (A + a) = 2 * (r * a / (A + a)) := by ring
    rw [hid] at hs'
    linarith
  have hb : 0 ≤ A / (A + a) := by positivity
  have hnorm : ‖y - x0‖ ≤ A / (A + a) * ‖z - x0‖ + a * ‖gy‖ + ‖e‖ := by
    rw [hy]
    calc
      _ ≤ ‖(A / (A + a)) • (z - x0) - a • gy‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖(A / (A + a)) • (z - x0)‖ + ‖a • gy‖) + ‖e‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb,
        abs_of_pos ha]
  refine ⟨hv, ?_, hres⟩
  have hz' := mul_le_mul_of_nonneg_left hz hb
  have hg' := mul_le_mul_of_nonneg_left hres ha.le
  have hid : A / (A + a) * (3 * r) + a * (2 * r / (A + a)) +
      r * a / (A + a) = 3 * r := by field_simp; ring
  linarith

lemma local_model_invariant {G : E → E} {D J : E →L[ℝ] E}
    (x0 xs z y g : E) {A δ M r ρ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hM : 0 < M) (hr : 0 ≤ r)
    (hρ : 0 < ρ) (hrρ : r ≤ ρ) (hx : ‖x0 - xs‖ ≤ r)
    (hz : ‖z - x0‖ ≤ 3 * r) (hV : potential x0 A z g ≤ 0)
    (hzero : G xs = 0) (hmono : ∀ v w, 0 ≤ ⟪G v - G w, v - w⟫)
    (hg : A = 0 ∨ g = G z)
    (hD : ∀ v, 0 ≤ ⟪D v, v⟫) (herr : ‖J - D‖ ≤ δ)
    (b c : E)
    (hb : b = ((1 / (128 * δ + 512 * M * ρ)) / (A + 1 / (128 * δ + 512 * M * ρ))) • x0 +
      (A / (A + 1 / (128 * δ + 512 * M * ρ))) • z)
    (hc : c = b - ((1 / (128 * δ + 512 * M * ρ)) * A /
      (A + 1 / (128 * δ + 512 * M * ρ))) • g)
    (htaylor : ∀ v, ‖G v - G c - D (v - c)‖ ≤ M * ‖v - c‖ ^ 2)
    (hy : y + (1 / (128 * δ + 512 * M * ρ)) •
      (G c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c)) = b) :
    potential x0 (A + 1 / (128 * δ + 512 * M * ρ)) y (G y) ≤ 0 ∧
      ‖y - x0‖ ≤ 3 * r ∧
      ‖G y‖ ≤ 2 * r / (A + 1 / (128 * δ + 512 * M * ρ)) := by
  let t := 1 / (128 * δ + 512 * M * ρ)
  have ht : 0 < t := (InexactJacobianGeometry.local_step_bounds hδ hM hρ).1
  have hb' : b = (t / (A + t)) • x0 + (A / (A + t)) • z := hb
  have hc' : c = (t / (A + t)) • x0 + (A / (A + t)) • z -
      (t * A / (A + t)) • g := by rw [hc, hb]
  have hbounds := extrapolation_bound x0 xs z g hA ht hr hx hz hV
  change ‖(t / (A + t)) • x0 + (A / (A + t)) • z - xs‖ ≤ 4 * r ∧
    ‖((t / (A + t)) • x0 + (A / (A + t)) • z -
      (t * A / (A + t)) • g) - xs‖ ≤ 7 * r at hbounds
  rw [← hc', ← hb'] at hbounds
  obtain ⟨_, he⟩ := InexactJacobianGeometry.local_trial_control hδ hM hr hρ hrρ
    hD herr c b y xs hzero hbounds.2 hbounds.1 htaylor hy
  let e := t • (G y - (G c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c)))
  have hrec : y - x0 = (A / (A + t)) • (z - x0) - t • G y + e := by
    have heq : t / (A + t) = 1 - A / (A + t) := by field_simp; ring
    have hy' : y = b - t • (G c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c)) := by
      change y + t • _ = b at hy
      rw [← hy]; abel
    calc
      y - x0 = (b - t • (G c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c))) - x0 :=
        congrArg (fun v => v - x0) hy'
      _ = _ := by
        dsimp only [e]
        rw [hb', heq]
        module
  have hpair : A = 0 ∨ 0 ≤ ⟪G y - g, y - z⟫ := by
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact hmono y z)
  have hroot : 0 ≤ ⟪G y, y - xs⟫ := by simpa [hzero] using hmono y xs
  exact accepted_invariant x0 xs z y g (G y) e c hA ht hr hx hz hV hrec hc' hpair hroot he

lemma phase_invariant {G : E → E} (x0 xs : E) {δ M r ρ : ℝ}
    (hδ : 0 ≤ δ) (hM : 0 < M) (hr : 0 ≤ r) (hρ : 0 < ρ) (hrρ : r ≤ ρ)
    (hx : ‖x0 - xs‖ ≤ r) (hzero : G xs = 0)
    (hmono : ∀ v w, 0 ≤ ⟪G v - G w, v - w⟫)
    (u g b c : ℕ → E) (D J : ℕ → E →L[ℝ] E) (N : ℕ)
    (hu0 : u 0 = x0) (hg : ∀ n, g (n + 1) = G (u (n + 1)))
    (hD : ∀ n < N, ∀ v, 0 ≤ ⟪D n v, v⟫)
    (herr : ∀ n < N, ‖J n - D n‖ ≤ δ)
    (hb : ∀ n < N, b n =
      (1 / ((n : ℝ) + 1)) • x0 + ((n : ℝ) / ((n : ℝ) + 1)) • u n)
    (hc : ∀ n < N, c n = b n -
      ((1 / (128 * δ + 512 * M * ρ)) * (n : ℝ) / ((n : ℝ) + 1)) • g n)
    (htaylor : ∀ n < N, ∀ v, ‖G v - G (c n) - D n (v - c n)‖ ≤ M * ‖v - c n‖ ^ 2)
    (hy : ∀ n < N, u (n + 1) + (1 / (128 * δ + 512 * M * ρ)) •
      (G (c n) + (J n + δ • ContinuousLinearMap.id ℝ E) (u (n + 1) - c n)) = b n) :
    ∀ n ≤ N,
      potential x0 ((n : ℝ) * (1 / (128 * δ + 512 * M * ρ))) (u n) (g n) ≤ 0 ∧
      ‖u n - x0‖ ≤ 3 * r ∧
      (0 < n → ‖G (u n)‖ ≤ 2 * r / ((n : ℝ) * (1 / (128 * δ + 512 * M * ρ)))) := by
  let t := 1 / (128 * δ + 512 * M * ρ)
  have ht : 0 < t := (InexactJacobianGeometry.local_step_bounds hδ hM hρ).1
  intro n hn
  induction n with
  | zero => simp [potential, hu0, hr]
  | succ n ih =>
    have hnN : n < N := by omega
    obtain ⟨hv, hz, _⟩ := ih (by omega)
    have hA : 0 ≤ (n : ℝ) * t := by positivity
    have hgn : (n : ℝ) * t = 0 ∨ g n = G (u n) := by
      cases n with
      | zero => exact Or.inl (by simp)
      | succ n => exact Or.inr (hg n)
    have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
    have he₁ : t / ((n : ℝ) * t + t) = 1 / ((n : ℝ) + 1) := by
      field_simp
    have he₂ : (n : ℝ) * t / ((n : ℝ) * t + t) = (n : ℝ) / ((n : ℝ) + 1) := by
      field_simp
    have he₃ : t * ((n : ℝ) * t) / ((n : ℝ) * t + t) =
        t * (n : ℝ) / ((n : ℝ) + 1) := by field_simp
    have hbn : b n = (t / ((n : ℝ) * t + t)) • x0 +
        ((n : ℝ) * t / ((n : ℝ) * t + t)) • u n := by rw [he₁, he₂]; exact hb n hnN
    have hcn : c n = b n - (t * ((n : ℝ) * t) / ((n : ℝ) * t + t)) • g n := by
      rw [he₃]; exact hc n hnN
    have h := local_model_invariant x0 xs (u n) (u (n + 1)) (g n)
      hA hδ hM hr hρ hrρ hx hz hv hzero hmono hgn (hD n hnN) (herr n hnN)
      (b n) (c n) hbn hcn (htaylor n hnN) (hy n hnN)
    have he : ((n + 1 : ℕ) : ℝ) * t = (n : ℝ) * t + t := by push_cast; ring
    change potential x0 (((n + 1 : ℕ) : ℝ) * t) (u (n + 1)) (g (n + 1)) ≤ 0 ∧
      ‖u (n + 1) - x0‖ ≤ 3 * r ∧
      (0 < n + 1 → ‖G (u (n + 1))‖ ≤ 2 * r / (((n + 1 : ℕ) : ℝ) * t))
    rw [he, hg n]
    exact ⟨h.1, h.2.1, fun _ => h.2.2⟩

lemma phase_certificate {G : E → E} {μ B : ℝ} {xs x0 y : E}
    (hμ : 0 < μ) (hB : 0 < B) (hsize : 8 ≤ B * μ)
    (hzero : G xs = 0)
    (hstrong : ∀ x z, μ * ‖x - z‖ ^ 2 ≤ ⟪G x - G z, x - z⟫)
    (hres : ‖G y‖ ≤ 2 * ‖x0 - xs‖ / B) :
    ‖G y‖ / μ ≤ ‖y - x0‖ / 2 := by
  apply InexactJacobianGeometry.relative_certificate_of_residual hμ hzero hstrong rfl
  have h := mul_le_mul_of_nonneg_right hsize (norm_nonneg (x0 - xs))
  have hb : 2 * ‖x0 - xs‖ / B ≤ μ * ‖x0 - xs‖ / 4 := by
    rw [div_le_iff₀ hB]
    nlinarith
  exact hres.trans hb

end LongTails.Proofs.InexactJacobianPhase
