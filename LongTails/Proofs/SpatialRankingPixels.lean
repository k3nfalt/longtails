import LongTails.Proofs.SpatialRankingGradients

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingPixels

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

noncomputable def pixel (d i : ℕ) : Features d :=
  if h : i<d then EuclideanSpace.single ⟨i,h⟩ 1 else 0

lemma pixel_dot {d i j : ℕ} (hi : i<d) (hj : j<d) :
    ⟪pixel d i, pixel d j⟫ = if i=j then 1 else 0 := by
  simp [pixel, hi, hj, EuclideanSpace.inner_single_left, PiLp.single_apply]

lemma shift_pixel {d i : ℕ} (hi : i+1<d) : shift (pixel d i) = pixel d (i+1) := by
  obtain ⟨d,rfl⟩ : ∃ k, d=k+1 := ⟨d-1,by omega⟩
  let a : Fin (d+1) := ⟨i,by omega⟩
  let b : Fin (d+1) := ⟨i+1,hi⟩
  have hab : finRotate (d+1) a = b := Fin.ext (coe_finRotate_of_ne_last (by
    intro he
    have hh := congrArg Fin.val he
    change i=d at hh
    omega))
  ext j
  have hh : (finRotate (d+1)).symm j = a ↔ j=b := by rw [Equiv.symm_apply_eq, hab]
  simp [shift, pixel, show i<d+1 by omega, hi, PiLp.single_apply, a, b] at hh ⊢
  exact if_congr hh rfl rfl

noncomputable def block (d b : ℕ) (x : ℕ → ℤ) : Features d :=
  ∑ j ∈ Finset.range 31, (x j : ℝ) • pixel d (32*b+j)

lemma block_pixel {d b c j : ℕ} (hb : 32*b+31 < d) (hc : 32*c+31 < d) (hj : j<32)
    (x : ℕ → ℤ) : ⟪block d b x, pixel d (32*c+j)⟫ =
      if b=c ∧ j<31 then (x j : ℝ) else 0 := by
  unfold block
  simp only [sum_inner, real_inner_smul_left]
  by_cases H : b=c ∧ j<31
  · rw [ite_eq_left H, Finset.sum_eq_single j]
    · rw [H.1, pixel_dot (by omega) (by omega), ite_eq_left rfl, mul_one]
    · intro k hk hk'
      have := Finset.mem_range.mp hk
      rw [pixel_dot (by omega) (by omega), ite_eq_right (by omega), mul_zero]
    · simp [H.2]
  · rw [ite_eq_right H]
    apply Finset.sum_eq_zero
    intro k hk
    have := Finset.mem_range.mp hk
    rw [pixel_dot (by omega) (by omega), ite_eq_right (by omega), mul_zero]

noncomputable def spatialLag {d : ℕ} (lag : Bool) : Features d →ₗ[ℝ] Features d :=
  if lag then
    { toFun := shift
      map_add' := shift_add
      map_smul' := fun k x => shift_smul k x }
  else LinearMap.id

def offset (lag : Bool) : ℕ := if lag then 1 else 0

def correlation (lag : Bool) (x y : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range 31, y j * (if j+offset lag < 31 then x (j+offset lag) else 0)

lemma block_inner {d b c : ℕ} (hb : 32*b+31 < d) (hc : 32*c+31 < d) (lag : Bool)
    (x y : ℕ → ℤ) : ⟪block d b x, spatialLag lag (block d c y)⟫ =
    if b=c then (correlation lag x y : ℝ) else 0 := by
  have hs (j : ℕ) (hj : j<31) : spatialLag lag (pixel d (32*c+j)) =
      pixel d (32*c+(j+offset lag)) := by
    cases lag
    · simp [spatialLag, offset]
    · simp [spatialLag, offset, shift_pixel (by omega : 32*c+j+1<d), Nat.add_assoc]
  have hsum : spatialLag lag (block d c y) =
      ∑ j ∈ Finset.range 31, (y j:ℝ) • pixel d (32*c+(j+offset lag)) := by
    unfold block
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, hs _ (Finset.mem_range.mp hj)]
  rw [hsum, inner_sum]
  have hL : offset lag ≤ 1 := by cases lag <;> decide
  by_cases H : b=c
  · rw [ite_eq_left H]
    unfold correlation
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    rw [real_inner_smul_right, block_pixel hb hc (by omega)]
    by_cases e : j+offset lag < 31 <;> simp [H, e]
  · rw [ite_eq_right H]
    apply Finset.sum_eq_zero
    intro j hj
    have := Finset.mem_range.mp hj
    rw [real_inner_smul_right, block_pixel hb hc (by omega)]
    simp [H]

inductive Packet where
  | before | after | run | cap | isolated
  deriving DecidableEq

def pattern (g : Bool) (p : Packet) (i : ℕ) : ℤ :=
  let a := if g then 22 else 3
  let L := if g then 2 else 6
  match p with
  | .before => if i+1=a then 1 else 0
  | .after => if i=a+2*L then 1 else 0
  | .run => if a ≤ i ∧ i < a+L then 1 else if a+L ≤ i ∧ i < a+2*L then -1 else 0
  | .cap => if i=a ∨ i=a+2 then 1 else if i=a+1 then (if g then 1 else -1) else 0
  | .isolated => if i=a+5 then 1 else 0

def energy (g : Bool) : ℤ := if g then 4 else 12
def capSign (g : Bool) : ℤ := if g then 1 else -1

lemma cross_table (lag g : Bool) (p q : Packet) :
    correlation lag (pattern g p) (pattern (!g) q) = 0 := by
  cases lag <;> cases g <;> cases p <;> cases q <;> decide

def anchor (last : Bool) : Packet := if last then .after else .before

lemma packet_table (g lag e f : Bool) :
    let C := fun α β => correlation lag (pattern g α) (pattern g β)
    C .run .run = (if lag then energy g - 3 else energy g) ∧
    C .run (anchor e) = (if lag ∧ !e then 1 else 0) ∧
    C (anchor e) .run = (if lag ∧ e then -1 else 0) ∧
    C (anchor e) (anchor f) = (if !lag ∧ e=f then 1 else 0) ∧
    C .cap .cap = (if lag then 2*capSign g else 3) ∧
    C .cap .isolated = 0 ∧ C .isolated .cap = 0 ∧
    C .isolated .isolated = (if lag then 0 else 1) := by
  cases g <;> cases lag <;> cases e <;> cases f <;> decide

end LongTails.Proofs.SpatialRankingPixels
