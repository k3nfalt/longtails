import LongTails.Proofs.AcceleratedMarkovStep
import LongTails.Proofs.HeavyTailedError

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedMarkovGradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clippedRun_index (g : E → Ω → E) (D R C : ℝ) (m : ℕ) (x0 : E)
    (ξ : ℕ → Ω) (k : ℕ) : (clippedRun g D R C m x0 ξ k).1 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [clippedRun, projectedClippedUpdate] using congrArg Nat.succ ih

lemma query_ball {R : ℝ} {x0 x z : E} (hx : ‖x - x0‖ ≤ R) (hz : ‖z - x0‖ ≤ R)
    (k : ℕ) : ‖Gradient.acceleratedQuery (k, x, z) - x0‖ ≤ R := by
  let A := (k : ℝ) * ((k : ℝ) + 1) / 4
  let a := ((k : ℝ) + 1) / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : 0 < A + a := by dsimp [A, a]; positivity
  have hw : A / (A + a) + a / (A + a) = 1 := by rw [← add_div, div_self hB.ne']
  have he : Gradient.acceleratedQuery (k, x, z) - x0 =
      (A / (A + a)) • (x - x0) + (a / (A + a)) • (z - x0) := by
    dsimp [Gradient.acceleratedQuery]
    change (A / (A + a)) • x + (a / (A + a)) • z - x0 = _
    calc
      _ = (A / (A + a)) • x + (a / (A + a)) • z -
          ((A / (A + a)) • x0 + (a / (A + a)) • x0) := by rw [← add_smul, hw, one_smul]
      _ = _ := by module
  rw [he]
  calc
    _ ≤ ‖(A / (A + a)) • (x - x0)‖ + ‖(a / (A + a)) • (z - x0)‖ := norm_add_le _ _
    _ = A / (A + a) * ‖x - x0‖ + a / (A + a) * ‖z - x0‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hA hB.le), abs_of_nonneg (div_nonneg ha hB.le)]
    _ ≤ A / (A + a) * R + a / (A + a) * R :=
      add_le_add (mul_le_mul_of_nonneg_left hx (div_nonneg hA hB.le))
        (mul_le_mul_of_nonneg_left hz (div_nonneg ha hB.le))
    _ = R := by rw [← add_mul, hw, one_mul]

lemma clippedRun_ball (g : E → Ω → E) (D C : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (x0 : E) (ξ : ℕ → Ω) (k : ℕ) :
    ‖(clippedRun g D R C m x0 ξ k).2.1 - x0‖ ≤ R ∧
      ‖(clippedRun g D R C m x0 ξ k).2.2 - x0‖ ≤ R := by
  induction k with
  | zero => simpa only [clippedRun, sub_self, norm_zero, and_self] using hR
  | succ k ih =>
    let s := clippedRun g D R C m x0 ξ k
    let reply := g (Gradient.acceleratedQuery s) (ξ (k * m))
    let next := x0 + clip R (s.2.2 - (((s.1 : ℝ) + 1) / 2 / D) • clip C reply - x0)
    have hn : ‖next - x0‖ ≤ R := by
      simpa only [next, add_sub_cancel_left] using norm_clip_le hR
        (s.2.2 - (((s.1 : ℝ) + 1) / 2 / D) • clip C reply - x0)
    exact ⟨query_ball ih.1 hn s.1, hn⟩

lemma clippedRun_query_ball (g : E → Ω → E) (D C : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (x0 : E) (ξ : ℕ → Ω) (k : ℕ) :
    ‖Gradient.acceleratedQuery (clippedRun g D R C m x0 ξ k) - x0‖ ≤ R := by
  have h := clippedRun_ball g D C hR m x0 ξ k
  exact query_ball h.1 h.2 _

lemma clippedRun_congr (g : E → Ω → E) (D R C : ℝ) (m : ℕ) (x0 : E)
    {ξ ζ : ℕ → Ω} (k : ℕ) (h : ∀ j < k, ξ (j * m) = ζ (j * m)) :
    clippedRun g D R C m x0 ξ k = clippedRun g D R C m x0 ζ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [clippedRun, ih (fun j hj => h j (by omega)), h k (by omega)]

set_option maxHeartbeats 800000 in
lemma measurable_clippedRun [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (D R C : ℝ) (m : ℕ) (x0 : E) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => (clippedRun g D R C m x0 ξ k).2) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    let s := fun ξ => clippedRun g D R C m x0 ξ k
    have hy : Measurable (fun ξ => Gradient.acceleratedQuery (s ξ)) := by
      change Measurable (fun ξ => Gradient.acceleratedQuery ((s ξ).1, (s ξ).2.1, (s ξ).2.2))
      simp only [s, clippedRun_index, Gradient.acceleratedQuery]
      exact (ih.fst.const_smul _).add (ih.snd.const_smul _)
    have hr : Measurable (fun ξ => clip C (g (Gradient.acceleratedQuery (s ξ)) (ξ (k * m)))) :=
      (measurable_clip C).comp (hg.comp (hy.prodMk (measurable_pi_apply _)))
    have hn : Measurable (fun ξ => x0 + clip R ((s ξ).2.2 -
        (((k : ℝ) + 1) / 2 / D) • clip C (g (Gradient.acceleratedQuery (s ξ)) (ξ (k * m))) - x0)) :=
      measurable_const.add ((measurable_clip R).comp ((ih.snd.sub (hr.const_smul _)).sub_const x0))
    simp only [clippedRun, projectedClippedUpdate, clippedRun_index, Gradient.acceleratedQuery]

    simpa only [s, Gradient.acceleratedQuery, clippedRun_index, Pi.add_apply, Pi.smul_apply] using
      ((ih.fst.const_smul (((k : ℝ) * ((k : ℝ) + 1) / 4) /
      ((k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2))).add
      (hn.const_smul ((((k : ℝ) + 1) / 2) /
        ((k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2)))).prodMk hn

lemma gradient_minimizer_zero [CompleteSpace E] {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) : gradient f u = 0 := by
  have hd := Gradient.descent hL hg hlip u
  have hh := hm (show u - (1 / L) • gradient f u ∈ univ from trivial)
  change f u ≤ f (u - (1 / L) • gradient f u) at hh
  have hsq : ‖gradient f u‖ ^ 2 / (2 * L) ≤ 0 := by linarith
  have hz := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hsq
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient f u)])

lemma gradient_ball [CompleteSpace E] {f : E → ℝ} {L R : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u x0 x : E} (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R)
    (hx : ‖x - x0‖ ≤ R) : ‖gradient f x‖ ≤ 2 * L * R := by
  have hd : ‖x - u‖ ≤ 2 * R := by
    calc
      _ ≤ ‖x - x0‖ + ‖x0 - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * R := by rw [norm_sub_rev x0 u]; linarith
  have hh := hlip x u
  rw [gradient_minimizer_zero hL hg hlip hm, sub_zero] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hd hL.le])

lemma smooth_gap_ball [CompleteSpace E] {f : E → ℝ} {L R : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u x0 x : E} (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R)
    (hx : ‖x - x0‖ ≤ R) : 0 ≤ f x - f u ∧ f x - f u ≤ 2 * L * R ^ 2 := by
  have hd : ‖x - u‖ ≤ 2 * R := by
    calc
      _ ≤ ‖x - x0‖ + ‖x0 - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * R := by rw [norm_sub_rev x0 u]; linarith
  have hh := Gradient.smooth_upper_bound hg hlip u x
  rw [gradient_minimizer_zero hL hg hlip hm, inner_zero_left, add_zero] at hh
  have hs : ‖x - u‖ ^ 2 ≤ (2 * R) ^ 2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hd
  exact ⟨sub_nonneg.mpr (hm trivial), by nlinarith [mul_le_mul_of_nonneg_left hs hL.le]⟩

end OracleTemplate.HeavyTailedMarkovGradient
