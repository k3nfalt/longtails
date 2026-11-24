import LongTails.Proofs.NcConcaveTransitionBounds

open scoped BigOperators

namespace LongTails.Proofs.NcConcavePsi

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds

variable {n : ℕ}

noncomputable def cη : ℝ := 10000

noncomputable def rb (u : Fin (n + 1) → ℝ) (i : Fin n) : ℝ := rr (u i.succ)

noncomputable def hpart (u : Fin (n + 1) → ℝ) : ℝ :=
  -cη * u 0 - cη * ∑ j : Fin n, nu (u j.succ) + cη / 2 * ∑ j, rr (u j) ^ 2

noncomputable def psi (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) : ℝ :=
  hpart u + (1 / 2) * ∑ i, (a i - rho u i) ^ 2 + (1 / 2) * ∑ i, (b i - rb u i) ^ 2 +
    (1 / 2) * ∑ i, a i ^ 2 + (1 / 2) * ∑ i, b i ^ 2 + (1 / 2) * ∑ i, (a i - b i / 2) ^ 2

noncomputable def dhpart (u v : Fin (n + 1) → ℝ) : ℝ :=
  -cη * v 0 - cη * ∑ j : Fin n, dnu (u j.succ) * v j.succ + cη * ∑ j, rr (u j) * drr (u j) * v j

noncomputable def dpsiU (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  dhpart u v - ∑ i, (a i - rho u i) * drho u v i - ∑ i, (b i - rb u i) * (drr (u i.succ) * v i.succ)

lemma dpsiU_add (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (v w : Fin (n + 1) → ℝ) :
    dpsiU u a b (v + w) = dpsiU u a b v + dpsiU u a b w := by
  simp only [dpsiU, dhpart, drho_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma dpsiU_smul (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (c : ℝ) (v : Fin (n + 1) → ℝ) :
    dpsiU u a b (c • v) = c * dpsiU u a b v := by
  simp only [dpsiU, dhpart, drho_smul, Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ j : Fin n, dnu (u j.succ) * (c * v j.succ) = c * ∑ j : Fin n, dnu (u j.succ) * v j.succ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, rr (u j) * drr (u j) * (c * v j) = c * ∑ j, rr (u j) * drr (u j) * v j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i, (a i - rho u i) * (c * drho u v i) = c * ∑ i, (a i - rho u i) * drho u v i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ i, (b i - rb u i) * (drr (u i.succ) * (c * v i.succ)) =
      c * ∑ i, (b i - rb u i) * (drr (u i.succ) * v i.succ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, e4]; ring

noncomputable def dpsiUL (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun := dpsiU u a b
  map_add' := dpsiU_add u a b
  map_smul' c v := by simp only [dpsiU_smul, smul_eq_mul, RingHom.id_apply]

noncomputable def gu (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  dpsiU u a b (fun k => if j = k then 1 else 0)

lemma dpsiU_eq_sum (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    dpsiU u a b v = ∑ j, v j * gu u a b j := by
  have h := LinearMap.pi_apply_eq_sum_univ (dpsiUL u a b) v
  simpa [dpsiUL, gu, smul_eq_mul] using h

noncomputable def gab (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (i : Fin n) : ℝ × ℝ :=
  (3 * a i - b i / 2 - rho u i, -(a i) / 2 + 9 / 4 * b i - rb u i)

noncomputable def astar (u : Fin (n + 1) → ℝ) (i : Fin n) : ℝ := 9 / 26 * rho u i + 1 / 13 * rb u i

noncomputable def bstar (u : Fin (n + 1) → ℝ) (i : Fin n) : ℝ := 1 / 13 * rho u i + 6 / 13 * rb u i

lemma gab_star (u : Fin (n + 1) → ℝ) (i : Fin n) :
    gab u (astar u) (bstar u) i = (0, 0) := by
  simp only [gab, astar, bstar, Prod.mk.injEq]
  constructor <;> ring

end LongTails.Proofs.NcConcavePsi
