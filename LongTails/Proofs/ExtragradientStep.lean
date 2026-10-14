import LongTails.Algorithms.Extragradient
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.SaddlePoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
lemma project_spec {X : Set E} (hne : X.Nonempty) (hcl : IsCompact X)
    (hc : Convex ℝ X) (x : E) :
    project X x ∈ X ∧ ∀ u ∈ X, ⟪x - project X x, u - project X x⟫ ≤ 0 := by
  have h := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc x
  rw [project, dite_eq_left h]
  exact ⟨h.choose_spec.1,
    (norm_eq_iInf_iff_real_inner_le_zero hc h.choose_spec.1).mp h.choose_spec.2⟩

omit [CompleteSpace E] in
lemma project_inequality {X : Set E} (hne : X.Nonempty) (hcl : IsCompact X)
    (hc : Convex ℝ X) (η : ℝ) (z g u : E) (hu : u ∈ X) :
    2 * η * ⟪g, project X (z - η • g) - u⟫ ≤
      ‖z - u‖ ^ 2 - ‖project X (z - η • g) - u‖ ^ 2 -
      ‖z - project X (z - η • g)‖ ^ 2 := by
  let p := project X (z - η • g)
  have h := (project_spec hne hcl hc (z - η • g)).2 u hu
  change ⟪z - η • g - p, u - p⟫ ≤ 0 at h
  have he : z - η • g - p = (z - p) - η • g := by module
  have hn : z - u = (z - p) + (p - u) := by module
  rw [he, inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at h
  change 2 * η * ⟪g, p - u⟫ ≤ ‖z - u‖ ^ 2 - ‖p - u‖ ^ 2 - ‖z - p‖ ^ 2
  rw [hn, norm_add_sq_real]
  have hi : u - p = -(p - u) := by module
  rw [hi, inner_neg_right, inner_neg_right] at h
  linarith

def energy (z u : E × F) : ℝ := ‖z.1 - u.1‖ ^ 2 + ‖z.2 - u.2‖ ^ 2

def pairing (g d : E × F) : ℝ := ⟪g.1, d.1⟫ + ⟪g.2, d.2⟫

omit [CompleteSpace E] [CompleteSpace F] in
lemma prox_mem {X : Set E} {Y : Set F} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hxc : IsCompact X) (hyc : IsCompact Y) (hxv : Convex ℝ X) (hyv : Convex ℝ Y)
    (η : ℝ) (z g : E × F) : prox X Y η z g ∈ X ×ˢ Y :=
  ⟨(project_spec hx hxc hxv _).1, (project_spec hy hyc hyv _).1⟩

omit [CompleteSpace E] [CompleteSpace F] in
lemma prox_inequality {X : Set E} {Y : Set F} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hxc : IsCompact X) (hyc : IsCompact Y) (hxv : Convex ℝ X) (hyv : Convex ℝ Y)
    (η : ℝ) (z g u : E × F) (hu : u ∈ X ×ˢ Y) :
    2 * η * pairing g (prox X Y η z g - u) ≤
      energy z u - energy (prox X Y η z g) u - energy z (prox X Y η z g) := by
  have h1 := project_inequality hx hxc hxv η z.1 g.1 u.1 hu.1
  have h2 := project_inequality hy hyc hyv η z.2 g.2 u.2 hu.2
  dsimp [pairing, energy, prox]
  linarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma pairing_sub (a b c : E × F) : pairing a (b - c) =
    pairing a b - pairing a c := by simp [pairing, inner_sub_right]; ring

omit [CompleteSpace E] [CompleteSpace F] in
lemma pairing_sub_left (a b c : E × F) : pairing (a - b) c =
    pairing a c - pairing b c := by simp [pairing, inner_sub_left]; ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma energy_nonneg (z u : E × F) : 0 ≤ energy z u :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma energy_comm (z u : E × F) : energy z u = energy u z := by
  simp only [energy, norm_sub_rev]

omit [CompleteSpace E] [CompleteSpace F] in
lemma pairing_error (a b c : E × F) (η : ℝ) :
    2 * η * pairing a (b - c) ≤
      2 * η ^ 2 * (‖a.1‖ ^ 2 + ‖a.2‖ ^ 2) + energy b c / 2 := by
  have h1 := real_inner_le_norm (η • a.1) (b.1 - c.1)
  have h2 := real_inner_le_norm (η • a.2) (b.2 - c.2)
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs, starRingEnd_apply, star_trivial] at h1 h2
  have s1 := sq_nonneg (2 * |η| * ‖a.1‖ - ‖b.1 - c.1‖)
  have s2 := sq_nonneg (2 * |η| * ‖a.2‖ - ‖b.2 - c.2‖)
  dsimp [pairing, energy]
  nlinarith [sq_abs η]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma energy_lipschitz (g : E × F → E × F) {L : ℝ}
    (hlip : ∀ z w, ‖g z - g w‖ ≤ L * ‖z - w‖) (z w : E × F) :
    energy (g z) (g w) ≤ 2 * L ^ 2 * energy z w := by
  have h := hlip z w
  have hf := norm_fst_le (g z - g w)
  have hs := norm_snd_le (g z - g w)
  have hn : ‖z - w‖ ^ 2 ≤ energy z w := by
    rw [Prod.norm_def]
    dsimp [energy]
    rcases le_total ‖z.1 - w.1‖ ‖z.2 - w.2‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖z.1 - w.1‖]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖z.2 - w.2‖]
  have hh := mul_self_le_mul_self (norm_nonneg (g z - g w)) h
  have hff := mul_self_le_mul_self (norm_nonneg (g z - g w).1) hf
  have hss := mul_self_le_mul_self (norm_nonneg (g z - g w).2) hs
  have ht := mul_le_mul_of_nonneg_left hn (sq_nonneg L)
  dsimp [energy] at *
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
lemma extragradient_step {X : Set E} {Y : Set F} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hxc : IsCompact X) (hyc : IsCompact Y) (hxv : Convex ℝ X) (hyv : Convex ℝ Y)
    (g : E × F → E × F) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ z w, ‖g z - g w‖ ≤ L * ‖z - w‖)
    (z u : E × F) (hu : u ∈ X ×ˢ Y) :
    let η := 1 / (2 * L)
    let w := prox X Y η z (g z)
    let v := prox X Y η z (g w)
    2 * η * pairing (g w) (w - u) ≤ energy z u - energy v u := by
  dsimp only
  let η := 1 / (2 * L)
  let w := prox X Y η z (g z)
  let v := prox X Y η z (g w)
  change 2 * η * pairing (g w) (w - u) ≤ energy z u - energy v u
  have hv := prox_mem hx hy hxc hyc hxv hyv η z (g w)
  have h1 := prox_inequality hx hy hxc hyc hxv hyv η z (g w) u hu
  have h2 := prox_inequality hx hy hxc hyc hxv hyv η z (g z) v hv
  change 2 * η * pairing (g w) (v - u) ≤ energy z u - energy v u - energy z v at h1
  change 2 * η * pairing (g z) (w - v) ≤ energy z v - energy w v - energy z w at h2
  have he := pairing_error (g w - g z) w v η
  change 2 * η * pairing (g w - g z) (w - v) ≤
    2 * η ^ 2 * energy (g w) (g z) + energy w v / 2 at he
  have hl := energy_lipschitz g hlip w z
  rw [energy_comm w z] at hl
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * η ^ 2)
  have hη : 4 * η ^ 2 * L ^ 2 = 1 := by dsimp [η]; field_simp; ring
  have hηe : 2 * η ^ 2 * (2 * L ^ 2 * energy z w) = energy z w := by
    calc
      _ = (4 * η ^ 2 * L ^ 2) * energy z w := by ring
      _ = energy z w := by rw [hη, one_mul]
  rw [hηe] at hh
  have hneg := energy_nonneg w v
  rw [pairing_sub_left] at he
  simp only [pairing_sub] at h1 h2
  simp only [pairing_sub] at he
  rw [pairing_sub]
  nlinarith

end OracleTemplate.SaddlePoint
