import LongTails.Proofs.ManySampleConvolutionalPerceptronDynamics
import LongTails.Proofs.ManySampleConvolutionalPerceptronConstants

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronTrajectory

open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronStability

structure Gains (E : Type*) (n : ℕ) where
  reference : ℝ
  longitudinal : Fin n → ℝ
  plus : Fin n → E
  minus : Fin n → E
  contrast : ℝ
  kick : ℝ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

noncomputable def next (g : Gains E n) : Option (Fin n) → State E → State E
  | none, x => positive g.reference g.kick x
  | some i, x => negative (g.longitudinal i) g.contrast (g.plus i) (g.minus i) x

def Permitted (g : Gains E n) : Option (Fin n) → State E → Prop
  | none, x => x.a * x.q ≤ 0
  | some i, x => 0 < x.a * x.q ∧
      0 ≤ g.longitudinal i * x.a * x.q +
        g.contrast * (x.a * ⟪g.plus i, x.z⟫ + x.t * ⟪g.minus i, x.z⟫)

def coefficient (g : Gains E n) : Option (Fin n) → ℝ
  | none => g.reference
  | some i => g.longitudinal i

noncomputable def forcing (g : Gains E n) : Option (Fin n) → State E → ℝ
  | none, x => escapeKick g.kick (x.a + x.q)
  | some i, x => -(g.contrast * ⟪g.plus i, x.z⟫)

lemma next_coordinates {g : Gains E n} {e : Option (Fin n)} {x : State E}
    (he : Permitted g e x) :
    coordinates (next g e x) =
      ((scalarStep (coefficient g e) (coordinates x).1 (coordinates x).2).1 + forcing g e x,
       (scalarStep (coefficient g e) (coordinates x).1 (coordinates x).2).2 + forcing g e x) := by
  cases e with
  | none => exact positive_coordinates he
  | some i => simpa only [next, coefficient, forcing, sub_eq_add_neg] using negative_coordinates he.1

lemma forcing_bound {g : Gains E n} {e : Option (Fin n)} {x : State E} {H : ℝ}
    (hδ : 0 ≤ g.contrast) (hσ : 0 ≤ g.kick) (hH : 0 ≤ H)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hx : ‖x.z‖ ≤ H) :
    |forcing g e x| ≤ g.contrast * H + g.kick := by
  cases e with
  | none =>
    simp only [forcing, escapeKick_abs hσ]
    nlinarith
  | some i =>
    have hf := negative_forcing (x := x) hδ (hp i)
    change |-(g.contrast * ⟪g.plus i, x.z⟫)| ≤ _
    nlinarith

lemma finite_stability {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {ρ H : ℝ} {K : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 ≤ g.contrast) (hσ : 0 ≤ g.kick) (hH : 0 ≤ H)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1)
    (hc : ∀ j, ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1)
    (hzero : |(coordinates (x 0)).1| + |(coordinates (x 0)).2| ≤ 3)
    (hone : 1 ≤ K → |(coordinates (x 1)).1| + |(coordinates (x 1)).2| ≤ 3)
    (hheight : ∀ j, j < K → ‖(x j).z‖ ≤ H)
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j))
    (hpermit : ∀ j, j < K → Permitted g (e j) (x j)) :
    ∀ j, j ≤ K → |(coordinates (x j)).1| + |(coordinates (x j)).2| ≤
      3 * (1 - ρ ^ 2 / 2) ^ (j / 2) + 12 * (g.contrast * H + g.kick) / ρ ^ 2 := by
  apply trajectory_bound hρ hρ1 (by positivity) hzero hone
    (fun j _ => hc (e j)) (fun j _ => hc1 (e j))
    (fun j hj => forcing_bound hδ hσ hH hp (hheight j hj))
  · intro j hj
    rw [hstep j hj, next_coordinates (hpermit j hj)]
  · intro j hj
    rw [hstep j hj, next_coordinates (hpermit j hj)]

def negativeCount (e : ℕ → Option (Fin n)) : ℕ → ℕ
  | 0 => 0
  | k + 1 => negativeCount e k + if (e k).isSome then 1 else 0

lemma negativeCount_mono (e : ℕ → Option (Fin n)) : Monotone (negativeCount e) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [negativeCount]
  omega

lemma negativeCount_le (e : ℕ → Option (Fin n)) (k : ℕ) : negativeCount e k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [negativeCount]
    split_ifs <;> omega

lemma count_telescope {e : ℕ → Option (Fin n)} {v : ℕ → ℝ} {C : ℝ} {B K : ℕ}
    (hBK : B ≤ K)
    (hstep : ∀ j, B ≤ j → j < K →
      v (j + 1) ≤ v j + C * ((negativeCount e (j + 1) : ℝ) - negativeCount e j)) :
    v K ≤ v B + C * ((negativeCount e K : ℝ) - negativeCount e B) := by
  have h : ∀ j, B ≤ j → j ≤ K →
      v j ≤ v B + C * ((negativeCount e j : ℝ) - negativeCount e B) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; ring_nf; exact le_refl _
    | succ j hj ih =>
      intro hjK
      have hi := ih (by omega)
      have hs := hstep j hj (by omega)
      linarith
  exact h K hBK le_rfl

lemma signal_drift_bound {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {H : ℝ} {K : ℕ} (hδ : 0 ≤ g.contrast)
    (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hheight : ∀ j, j < K → ‖(x j).z‖ ≤ H)
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j)) :
    |(x K).t - (x 0).t| ≤ g.contrast * H * negativeCount e K := by
  have htel := count_telescope (e := e) (v := fun j => |(x j).t - (x 0).t|)
    (C := g.contrast * H) (B := 0) (K := K) (Nat.zero_le K)
  simp only [negativeCount, Nat.cast_zero, sub_zero, sub_self, abs_zero, zero_add] at htel
  apply htel
  intro j _ hj
  rw [hstep j hj]
  cases he : e j with
  | none => simp [next, positive]
  | some i =>
    have hd := negative_signal_drift (x := x j) (c := g.longitudinal i)
      (p := g.plus i) hδ (hr i)
    have hh := hheight j hj
    have ht := abs_add_le ((negative (g.longitudinal i) g.contrast (g.plus i) (g.minus i) (x j)).t -
      (x j).t) ((x j).t - (x 0).t)
    rw [show (negative (g.longitudinal i) g.contrast (g.plus i) (g.minus i) (x j)).t -
      (x j).t + ((x j).t - (x 0).t) =
      (negative (g.longitudinal i) g.contrast (g.plus i) (g.minus i) (x j)).t - (x 0).t by ring] at ht
    simp only [next, Option.isSome_some, ite_true, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma coarse_residual_bound {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {K : ℕ} (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hzero : (x 0).z = 0)
    (ha : ∀ j, j < K → |(x j).a| ≤ 2) (ht : ∀ j, j < K → |(x j).t| ≤ 3 / 2)
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j)) :
    ‖(x K).z‖ ≤ 4 * negativeCount e K := by
  have htel := count_telescope (e := e) (v := fun j => ‖(x j).z‖)
    (C := 4) (B := 0) (K := K) (Nat.zero_le K)
  simp only [negativeCount, Nat.cast_zero, sub_zero, hzero, norm_zero, zero_add] at htel
  apply htel
  intro j _ hj
  rw [hstep j hj]
  cases he : e j with
  | none => simp [next, positive]
  | some i =>
    have hnorm := residual_step_norm (a := (x j).a) (t := (x j).t) (hp i) (hr i)
    have ha' := ha j hj
    have ht' := ht j hj
    have hn := norm_sub_le ((x j).z) ((x j).a • g.plus i + (x j).t • g.minus i)
    simp only [next, negative, Option.isSome_some, ite_true,
      Nat.cast_add, Nat.cast_one]
    linarith

lemma projection_accumulation {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {κ Z : ℝ} {w : E} {B K : ℕ} (hκ : 0 ≤ κ) (hBK : B ≤ K)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hw : ‖w‖ = 1)
    (hmargin : ∀ i, κ ≤ -⟪g.minus i, w⟫) (hstart : ‖(x B).z‖ ≤ Z)
    (ha : ∀ j, B ≤ j → j < K → |(x j).a| ≤ κ / 4)
    (ht : ∀ j, B ≤ j → j < K → 1 / 2 ≤ (x j).t)
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j)) :
    -Z + κ / 4 * ((negativeCount e K : ℝ) - negativeCount e B) ≤ ⟪(x K).z, w⟫ := by
  have htel := count_telescope (e := e) (v := fun j => -⟪(x j).z, w⟫)
    (C := -(κ / 4)) hBK
  have hincr : ∀ j, B ≤ j → j < K →
      -⟪(x (j + 1)).z, w⟫ ≤ -⟪(x j).z, w⟫ +
        -(κ / 4) * ((negativeCount e (j + 1) : ℝ) - negativeCount e j) := by
    intro j hj hjK
    rw [hstep j hjK]
    cases he : e j with
    | none => simp [next, positive, negativeCount, he]
    | some i =>
      have ht' := ht j hj hjK
      have ha' := ha j hj hjK
      have hn := negative_projection (c := g.longitudinal i) (δ := g.contrast)
        (x := x j) (hp i) hw (hmargin i) (by linarith : 0 ≤ (x j).t)
      simp only [next, negativeCount, he, Option.isSome_some, ite_true, Nat.cast_add, Nat.cast_one]
      nlinarith
  have hz := htel hincr
  have hinner := abs_real_inner_le_norm (x B).z w
  rw [hw, mul_one] at hinner
  have hl := neg_le_abs ⟪(x B).z, w⟫
  linarith

end LongTails.Proofs.ManySampleConvolutionalPerceptronTrajectory
