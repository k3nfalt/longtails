import LongTails.Proofs.SpatialRankingPixels
import LongTails.Proofs.SpatialRankingMargins

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingDictionary

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.SpatialRankingPixels
open LongTails.Proofs.SpatialRankingMargins (u v trace_step right_eq)

noncomputable def form {d : ℕ} (r : Bool) (x y : Features d) : ℝ := ⟪x,spatialLag r y⟫

lemma form_add_left {d : ℕ} (r : Bool) (x y z : Features d) :
    form r (x+y) z = form r x z + form r y z := inner_add_left _ _ _

lemma form_add_right {d : ℕ} (r : Bool) (x y z : Features d) :
    form r x (y+z) = form r x y + form r x z := by simp [form, inner_add_right]

lemma form_smul_left {d : ℕ} (r : Bool) (s : ℝ) (x y : Features d) :
    form r (s • x) y = s*form r x y := real_inner_smul_left _ _ _

lemma form_smul_right {d : ℕ} (r : Bool) (s : ℝ) (x y : Features d) :
    form r x (s • y) = s*form r x y := by simp [form, real_inner_smul_right]

noncomputable def atom (p : Params) (g : Bool) (a : Packet) (j : ℕ) : Features p.d :=
  block p.d j (pattern g a)

def cov (r g h : Bool) (a b : Packet) : ℝ :=
  (correlation r (pattern g a) (pattern h b) : ℤ)

lemma atom_form {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h : Bool) (a b : Packet)
    {i j : ℕ} (hi : i ≤ p.n) (hj : j ≤ p.n) :
    form r (atom p g a i) (atom p h b j) = if i=j then cov r g h a b else 0 :=
  block_inner (by omega) (by omega) r _ _

noncomputable def spine (p : Params) (g : Bool) (a : Packet) (x : ℕ → ℝ) : Features p.d :=
  ∑ i ∈ Finset.range (p.n-1), x i • atom p g a i

lemma spine_atom {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h : Bool) (a b : Packet)
    (x : ℕ → ℝ) {j : ℕ} (hj : j ≤ p.n) :
    form r (spine p g a x) (atom p h b j) =
      if j < p.n-1 then x j * cov r g h a b else 0 := by
  unfold spine form
  rw [sum_inner]
  change ∑ i ∈ _, form r (x i • atom p g a i) (atom p h b j) = _
  simp only [form_smul_left]
  by_cases H : j<p.n-1
  · rw [ite_eq_left H, Finset.sum_eq_single j, atom_form hd _ _ _ _ _ hj hj, ite_eq_left rfl]
    · intro i hi he
      have := Finset.mem_range.mp hi
      rw [atom_form hd _ _ _ _ _ (by omega) hj, ite_eq_right he, mul_zero]
    · simp [H]
  · rw [ite_eq_right H]
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    rw [atom_form hd _ _ _ _ _ (by omega) hj, ite_eq_right (by omega), mul_zero]

lemma atom_spine {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h : Bool) (a b : Packet)
    (x : ℕ → ℝ) {i : ℕ} (hi : i ≤ p.n) :
    form r (atom p g a i) (spine p h b x) =
      if i < p.n-1 then x i * cov r g h a b else 0 := by
  unfold spine form
  rw [map_sum, inner_sum]
  change ∑ j ∈ _, form r (atom p g a i) (x j • atom p h b j) = _
  simp only [form_smul_right]
  by_cases H : i<p.n-1
  · rw [ite_eq_left H, Finset.sum_eq_single i, atom_form hd _ _ _ _ _ hi hi, ite_eq_left rfl]
    · intro j hj he
      have := Finset.mem_range.mp hj
      rw [atom_form hd _ _ _ _ _ hi (by omega), ite_eq_right (Ne.symm he), mul_zero]
    · simp [H]
  · rw [ite_eq_right H]
    apply Finset.sum_eq_zero
    intro j hj
    have := Finset.mem_range.mp hj
    rw [atom_form hd _ _ _ _ _ hi (by omega), ite_eq_right (by omega), mul_zero]

lemma spine_form {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h : Bool) (a b : Packet)
    (x y : ℕ → ℝ) : form r (spine p g a x) (spine p h b y) =
      (∑ j ∈ Finset.range (p.n-1), x j * y j) * cov r g h a b := by
  change ⟪spine p g a x, spatialLag r (∑ j ∈ Finset.range (p.n-1), y j • atom p h b j)⟫ = _
  rw [map_sum, inner_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have H := Finset.mem_range.mp hj
  change form r (spine p g a x) (y j • atom p h b j) = _
  rw [form_smul_right, spine_atom hd _ _ _ _ _ _ (by omega), ite_eq_left H]
  ring

noncomputable def width (g : Bool) : ℝ := Real.sqrt (energy g)

noncomputable def amp (n : ℕ) (g : Bool) (j : ℕ) : ℝ := traceValue n g (j+1) * width g

noncomputable def power (n : ℕ) (g : Bool) : ℝ :=
  ∑ j ∈ Finset.range (n-1), amp n g j * amp n g j

noncomputable def remnant (n : ℕ) (g : Bool) : ℝ := Real.sqrt (1/4-power n g)

def privateBlock (n : ℕ) (last : Bool) : ℕ := if last then n else n-1

noncomputable def filler (p : Params) (g e : Bool) : Features p.d :=
  (1/2:ℝ) • atom p g .cap (privateBlock p.n e) +
  remnant p.n g • atom p g .isolated (privateBlock p.n e)

noncomputable def endpoint (p : Params) (g e : Bool) : Features p.d :=
  spine p g (anchor e) (amp p.n g) + filler p g e

noncomputable def item (p : Params) (g : Bool) (i : ℕ) : Features p.d :=
  (width g)⁻¹ • atom p g .run (i-1)

noncomputable def dictionary (p : Params) : Items p := fun g i =>
  if i.val=0 then endpoint p g false else if i.val=p.n then endpoint p g true else item p g i.val

lemma width_pos (g : Bool) : 0 < width g := by cases g <;> norm_num [width, energy]

lemma width_sq (g : Bool) : width g ^2 = energy g := by
  unfold width
  apply Real.sq_sqrt
  cases g <;> norm_num [energy]

lemma tracing {n : ℕ} (hn : 8 ≤ n) (g : Bool) {j : ℕ} (hj : j < n-1) :
    0 ≤ traceValue n g (j+1) ∧ traceValue n g (j+1) ≤ (1/8:ℝ)/Real.sqrt n := by
  have ht : (0:ℝ) < ((n-2:ℕ):ℝ) := by exact_mod_cast (show 0 < n-2 by omega)
  have hj' : (j:ℝ) / (n-2:ℕ) ≤ 1 := (div_le_one ht).mpr (by exact_mod_cast (show j ≤ n-2 by omega))
  have hj₀ : (0:ℝ) ≤ (j:ℝ) / (n-2:ℕ) := by positivity
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  cases g <;> simp only [traceValue, population, first, second, Nat.add_sub_cancel,
    mul_div_assoc, div_le_div_iff_of_pos_right hs] <;>
    constructor <;> first | exact div_nonneg (by linarith) hs.le | linarith

lemma remnant_sq {n : ℕ} (hn : 8 ≤ n) (g : Bool) : remnant n g ^2 = 1/4-power n g := by
  unfold remnant
  apply Real.sq_sqrt
  have hn₀ : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hs := Real.sq_sqrt hn₀.le
  have hw : (energy g : ℝ) ≤ 12 := by cases g <;> norm_num [energy]
  have H (j : ℕ) (hj : j<n-1) : amp n g j * amp n g j ≤ (12/64:ℝ)/n := by
    obtain ⟨hl,hr⟩ := tracing hn g hj
    have hq := mul_self_le_mul_self hl hr
    have he : ((1/8:ℝ)/Real.sqrt n)^2 = (1/64:ℝ)/n := by rw [div_pow, hs]; norm_num
    rw [← sq, ← sq, he] at hq
    unfold amp
    calc _ = traceValue n g (j+1)^2 * (energy g : ℝ) := by rw [← width_sq g]; ring
         _ ≤ ((1/64:ℝ)/n)*12 := mul_le_mul hq hw (by cases g <;> norm_num [energy]) (by positivity)
         _ = _ := by ring
  have hb := Finset.sum_le_sum (s := Finset.range (n-1)) (fun j hj => H j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
  have hc : ((n-1:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hr : (n:ℝ)*((12/64:ℝ)/n) = 12/64 := by field_simp
  have he := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (12/64:ℝ)/n)
  unfold power
  linarith

end LongTails.Proofs.SpatialRankingDictionary
