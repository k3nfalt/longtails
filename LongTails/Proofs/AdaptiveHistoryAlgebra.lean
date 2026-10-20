import Mathlib.Data.Fin.Rev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.AdaptiveHistoryAlgebra

lemma normalized_difference {a b r s δ C D : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hC : 0 ≤ C)
    (ha : |a| ≤ C * r) (hab : |a - b| ≤ C * D) (hrs : |r - s| ≤ D) :
    |a / (δ + r) - b / (δ + s)| ≤ 2 * C * D / (δ + s) := by
  have hpr : 0 < δ + r := by positivity
  have hps : 0 < δ + s := by positivity
  have he : a / (δ + r) - b / (δ + s) =
      (a - b) / (δ + s) + (a / (δ + r)) * ((s - r) / (δ + s)) := by
    field_simp
    ring
  have han : |a / (δ + r)| ≤ C := by
    rw [abs_div, abs_of_pos hpr, div_le_iff₀ hpr]
    nlinarith
  have hsr : |s - r| ≤ D := by simpa [abs_sub_comm] using hrs
  rw [he]
  calc
    _ ≤ |(a - b) / (δ + s)| + |(a / (δ + r)) * ((s - r) / (δ + s))| := abs_add_le _ _
    _ = |a - b| / (δ + s) + |a / (δ + r)| * (|s - r| / (δ + s)) := by
      rw [abs_mul, abs_div (a - b), abs_div (s - r), abs_of_pos hps]
    _ ≤ (C * D) / (δ + s) + C * (D / (δ + s)) := by
      gcongr
    _ = _ := by ring

lemma head_potential_change {q p d r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (hd : |q - p| ≤ d) :
    η / 2 * ((q ^ 2 - p ^ 2) / r) ≤
      η / 4 * (q ^ 2 / r) + 3 * η / (2 * r) * d ^ 2 := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hsq : (q - p) ^ 2 ≤ d ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (q - p)) hd0).2 hd
  have hbase : 2 * (q ^ 2 - p ^ 2) ≤ q ^ 2 + 6 * d ^ 2 := by
    nlinarith [sq_nonneg (q - 2 * (q - p))]
  have hm := mul_le_mul_of_nonneg_left hbase (show 0 ≤ η / (4 * r) by positivity)
  convert hm using 1 <;> field_simp <;> ring

lemma accumulator_of_energy {r r₀ A N : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A)
    (h : r ≤ r₀ + Real.sqrt (r * A) + N) :
    r ≤ 2 * r₀ + A + 2 * N := by
  have hs := Real.sq_sqrt (mul_nonneg hr hA)
  have hn := sq_nonneg (r - A)
  have hs0 := Real.sqrt_nonneg (r * A)
  have hroot : 2 * Real.sqrt (r * A) ≤ r + A := by
    nlinarith
  linarith

lemma reciprocal_accumulator_increment {r s G : ℝ} (hr : 0 < r) (hs : 0 < s)
    (he : s ^ 2 = r ^ 2 + G ^ 2) :
    G ^ 2 / (r * (s + r) ^ 2) ≤ 1 / r - 1 / s := by
  have hsr : r ≤ s := by nlinarith [sq_nonneg G]
  have hd : 0 < r * (s + r) ^ 2 * s := by positivity
  apply (mul_le_mul_iff_of_pos_right hd).mp
  field_simp
  nlinarith [mul_nonneg (sq_nonneg G) hr.le]


lemma default_momentum_invariant {m v g : ℝ} (hv : 0 ≤ v) (hm : m ^ 2 ≤ 64 * v) :
    ((9 / 10 : ℝ) * m + (1 - 9 / 10) * g) ^ 2 ≤
      64 * ((999 / 1000 : ℝ) * v + (1 - 999 / 1000) * g ^ 2) := by
  nlinarith [sq_nonneg ((2 / 5 : ℝ) * m - (9 / 40 : ℝ) * g), sq_nonneg g]

lemma momentum_sqrt_bound {m v : ℝ} (hv : 0 ≤ v) (hm : m ^ 2 ≤ 64 * v) :
    |m| ≤ 8 * Real.sqrt v := by
  nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v, abs_nonneg m, sq_abs m]

lemma adagrad_direction_bound {v g : ℝ} (hv : 0 ≤ v) :
    |g / Real.sqrt (v + g ^ 2)| ≤ 1 := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt (show 0 ≤ v + g ^ 2 by positivity), Real.sqrt_nonneg (v + g ^ 2),
    abs_nonneg g, sq_abs g]

lemma bias_corrected_direction_bound {m v a c δ : ℝ}
    (hv : 0 ≤ v) (hm : m ^ 2 ≤ 64 * v) (ha : 1 / 10 ≤ a)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) :
    |(m / a) / (δ + Real.sqrt (v / c))| ≤ 80 := by
  have ha0 : 0 < a := by linarith
  have hvc : v ≤ v / c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hroot : Real.sqrt v ≤ Real.sqrt (v / c) := Real.sqrt_le_sqrt hvc
  have hmb := (momentum_sqrt_bound hv hm).trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
  rw [abs_div, abs_div, abs_of_pos ha0,
    abs_of_pos (show 0 < δ + Real.sqrt (v / c) by positivity),
    div_le_iff₀ (by positivity), div_le_iff₀ ha0]
  have hprod := mul_le_mul_of_nonneg_right ha (show 0 ≤ 80 * (δ + Real.sqrt (v / c)) by positivity)
  nlinarith [Real.sqrt_nonneg (v / c)]


lemma affine_history_expansion (v u : ℕ → ℝ) (a : ℝ)
    (hr : ∀ t, v (t+1) = a * v t + u t) (s n : ℕ) :
    v (s+n) = a^n * v s + ∑ i : Fin n, a^(i : ℕ) * u (s+(i.rev : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show s+(n+1) = s+n+1 by omega, hr, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.rev_zero, Fin.val_last, one_mul,
      Fin.val_succ, Fin.rev_succ, Fin.val_castSucc]
    have he : (∑ i : Fin n, a^((i : ℕ)+1) * u (s+(i.rev : ℕ))) =
        a * ∑ i : Fin n, a^(i : ℕ) * u (s+(i.rev : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    rw [he, pow_succ]
    ring

lemma decayed_momentum_bound {α β m v : ℝ} (hv : 0 ≤ v)
    (hm : m^2 ≤ 64*v) (hαβ : α^2 ≤ β) (n : ℕ) :
    |α^n*m| ≤ 8*Real.sqrt (β^n*v) := by
  have hβ : 0 ≤ β := (sq_nonneg α).trans hαβ
  apply momentum_sqrt_bound (mul_nonneg (pow_nonneg hβ _) hv)
  calc
    _ = (α^2)^n * m^2 := by rw [mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul]
    _ ≤ β^n * (64*v) := mul_le_mul (pow_le_pow_left₀ (sq_nonneg α) hαβ n) hm
      (sq_nonneg _) (pow_nonneg hβ _)
    _ = _ := by ring



lemma default_finite_history_invariant {m v : ℝ} (hv : 0 ≤ v) (hm : m^2 ≤ 64*v)
    (n : ℕ) (z : Fin n → ℝ) :
    ((9/10 : ℝ)^n*m + ∑ i : Fin n, (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*z i)^2 ≤
      64*((999/1000 : ℝ)^n*v + ∑ i : Fin n, (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(z i)^2) := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    let M := (9/10 : ℝ)^n*m + ∑ i : Fin n, (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*z i.succ
    let V := (999/1000 : ℝ)^n*v + ∑ i : Fin n, (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(z i.succ)^2
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have hMV : M^2 ≤ 64*V := ih (fun i => z i.succ)
    have hh := default_momentum_invariant (g := z 0) hV hMV
    have hα : (∑ i : Fin n, (1-(9/10 : ℝ))*(9/10 : ℝ)^((i : ℕ)+1)*z i.succ) =
        (9/10 : ℝ) * ∑ i : Fin n, (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*z i.succ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    have hβ : (∑ i : Fin n, (1-(999/1000 : ℝ))*(999/1000 : ℝ)^((i : ℕ)+1)*(z i.succ)^2) =
        (999/1000 : ℝ) * ∑ i : Fin n, (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(z i.succ)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    rw [hα,hβ,pow_succ,pow_succ]
    dsimp [M,V] at hh
    convert hh using 1 <;> ring



lemma sqrt_offset_difference_of_le {R r s : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) (hsr : s ≤ r) :
    Real.sqrt (R+r^2)-Real.sqrt (R+s^2) ≤ r-s := by
  have hb : s ≤ Real.sqrt (R+s^2) := (Real.le_sqrt hs (by positivity)).mpr (by linarith)
  have hp := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hsr)
  have hh : Real.sqrt (R+r^2) ≤ Real.sqrt (R+s^2)+(r-s) := by
    apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hsr))).mpr
    nlinarith [Real.sq_sqrt (show 0 ≤ R+s^2 by positivity)]
  linarith

lemma sqrt_offset_difference {R r s : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |Real.sqrt (R+r^2)-Real.sqrt (R+s^2)| ≤ |r-s| := by
  rcases le_total s r with hsr | hrs
  · have hh := sqrt_offset_difference_of_le hR hs hsr
    have he : Real.sqrt (R+s^2) ≤ Real.sqrt (R+r^2) := Real.sqrt_le_sqrt (by nlinarith)
    simpa only [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonneg (sub_nonneg.mpr hsr)] using hh
  · have hh := sqrt_offset_difference_of_le hR hr hrs
    have he : Real.sqrt (R+r^2) ≤ Real.sqrt (R+s^2) := Real.sqrt_le_sqrt (by nlinarith)
    rw [abs_sub_comm (Real.sqrt (R+r^2)), abs_sub_comm r]
    simpa only [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonneg (sub_nonneg.mpr hrs)] using hh

lemma sqrt_offset_norm_difference {E : Type*} [NormedAddCommGroup E]
    {R : ℝ} (hR : 0 ≤ R) (v w : E) :
    |Real.sqrt (R+‖v‖^2)-Real.sqrt (R+‖w‖^2)| ≤ ‖v-w‖ :=
  (sqrt_offset_difference hR (norm_nonneg _) (norm_nonneg _)).trans (abs_norm_sub_norm_le v w)



lemma accumulator_log_increment {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    (w-v)/w ≤ Real.log w-Real.log v := by
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hw hv)
  rw [Real.log_div hw.ne' hv.ne', inv_div] at hh
  convert hh using 1; field_simp

lemma accumulator_log_sum (v : ℕ → ℝ) (hv : ∀ t,0 < v t) (T : ℕ) :
    (∑ t ∈ Finset.range T,(v (t+1)-v t)/v (t+1)) ≤ Real.log (v T)-Real.log (v 0) := by
  have hh := Finset.sum_le_sum (s := Finset.range T) (fun t _ => accumulator_log_increment (hv t) (hv (t+1)))
  rw [Finset.sum_range_sub (fun t => Real.log (v t)) T] at hh
  exact hh



lemma bias_corrected_direction_identity {m v a c δ : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ) (hv : 0 ≤ v) :
    (m/a)/(δ+Real.sqrt (v/c)) =
      (Real.sqrt c/a)*(m/(δ*Real.sqrt c+Real.sqrt v)) := by
  rw [Real.sqrt_div hv]
  have hroot := Real.sqrt_pos.mpr hc
  have hden : 0 < δ*Real.sqrt c+Real.sqrt v := by positivity
  have hden' : 0 < δ+Real.sqrt v/Real.sqrt c := by positivity
  field_simp



lemma head_potential_telescope (U A C V R : ℕ → ℝ) (η σ : ℝ) (T : ℕ)
    (hstep : ∀ t,t<T → U t ≤ -η/4*A t+η/2*(V t-V (t+1))+
      3*η/2*C t+η*σ^2/2*(R t-R (t+1))) :
    (∑ t ∈ Finset.range T,U t)+η/4*(∑ t ∈ Finset.range T,A t) ≤
      η/2*(V 0-V T)+3*η/2*(∑ t ∈ Finset.range T,C t)+η*σ^2/2*(R 0-R T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hh := ih (fun t ht => hstep t (by omega))
    have ht := hstep T (by omega)
    simp only [Finset.sum_range_succ]
    nlinarith

lemma head_potential_sum (U A C V R : ℕ → ℝ) {η σ : ℝ} (T : ℕ)
    (hη : 0 ≤ η) (hV : 0 ≤ V T) (hR : 0 ≤ R T)
    (hstep : ∀ t,t<T → U t ≤ -η/4*A t+η/2*(V t-V (t+1))+
      3*η/2*C t+η*σ^2/2*(R t-R (t+1))) :
    (∑ t ∈ Finset.range T,U t)+η/4*(∑ t ∈ Finset.range T,A t) ≤
      η/2*V 0+3*η/2*(∑ t ∈ Finset.range T,C t)+η*σ^2/2*R 0 := by
  have hh := head_potential_telescope U A C V R η σ T hstep
  have hp := mul_nonneg hη hV
  have hr := mul_nonneg (mul_nonneg hη (sq_nonneg σ)) hR
  nlinarith


lemma weighted_abs_sum_sq {ι : Type*} [Fintype ι] (q r : ι → ℝ)
    (hr : ∀ i,0 < r i) :
    (∑ i,|q i|)^2 ≤ (∑ i,(q i)^2/r i)*(∑ i,r i) := by
  have he (i) : Real.sqrt ((q i)^2/r i)*Real.sqrt (r i)=|q i| := by
    rw [← Real.sqrt_mul (div_nonneg (sq_nonneg _) (hr i).le),
      div_mul_cancel₀ _ (hr i).ne',Real.sqrt_sq_eq_abs]
  have hh := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
    (f := fun i => (q i)^2/r i) (g := r)
    (fun i => div_nonneg (sq_nonneg _) (hr i).le) (fun i => (hr i).le)
  simp only [he] at hh
  have hs := (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hh
  rw [mul_pow,Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hr i).le),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => (hr i).le)] at hs
  exact hs

lemma quadratic_self_bound {G A N c : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) (hc : 0 ≤ c)
    (hh : G^2 ≤ A*(N+c*G)) : G ≤ c*A+Real.sqrt (A*N) := by
  by_contra h
  have hgt : c*A+Real.sqrt (A*N) < G := lt_of_not_ge h
  have hs := Real.sq_sqrt (mul_nonneg hA hN)
  have hs0 := Real.sqrt_nonneg (A*N)
  have hp := mul_nonneg (mul_nonneg hc hA) (show 0 ≤ G-c*A by linarith)
  nlinarith

lemma weighted_abs_sum_of_denominator_sum {ι : Type*} [Fintype ι] (q r : ι → ℝ)
    {N c : ℝ} (hr : ∀ i,0 < r i) (hN : 0 ≤ N) (hc : 0 ≤ c)
    (hs : (∑ i,r i) ≤ N+c*(∑ i,|q i|)) :
    (∑ i,|q i|) ≤ c*(∑ i,(q i)^2/r i)+Real.sqrt (N*(∑ i,(q i)^2/r i)) := by
  have hA : 0 ≤ ∑ i,(q i)^2/r i := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hr i).le
  have hh := (weighted_abs_sum_sq q r hr).trans (mul_le_mul_of_nonneg_left hs hA)
  simpa only [mul_comm N] using quadratic_self_bound hA hN hc hh


lemma head_time_energy_bound {T h : ℕ} (q r : Fin T → Fin h → ℝ) (R : Fin h → ℝ)
    (hr : ∀ t j,0 < r t j) (hR : ∀ t j,r t j ≤ R j) :
    (∑ t,∑ j,|q t j|)^2 ≤ (∑ t,∑ j,(q t j)^2/r t j)*(T*(∑ j,R j)) := by
  have hh := weighted_abs_sum_sq (fun i : Fin T × Fin h => q i.1 i.2)
    (fun i : Fin T × Fin h => r i.1 i.2) (fun i => hr i.1 i.2)
  simp only [Fintype.sum_prod_type] at hh
  have hsum : (∑ t,∑ j,r t j) ≤ T*(∑ j,R j) := by
    calc
      _ ≤ ∑ _t : Fin T,∑ j,R j := Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ => hR t j
      _ = _ := by simp
  exact hh.trans (mul_le_mul_of_nonneg_left hsum
    (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hr t j).le))


lemma body_abs_sum_energy {ι : Type*} [Fintype ι] (q S d : ι → ℝ) {δ σ : ℝ}
    (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hd : ∀ i,0 < d i) (hdδ : ∀ i,d i ≤ δ)
    (hS : ∀ i,0 ≤ S i) (hSum : (∑ i,S i) ≤ σ) :
    (∑ i,|q i|) ≤ 66*(∑ i,(q i)^2/(d i+66*(|q i|+S i)))+
      Real.sqrt ((Fintype.card ι*δ+66*σ)*(∑ i,(q i)^2/(d i+66*(|q i|+S i)))) := by
  have hr (i) : 0 < d i+66*(|q i|+S i) :=
    add_pos_of_pos_of_nonneg (hd i) (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (hS i)))
  have hN : 0 ≤ Fintype.card ι*δ+66*σ := by positivity
  have hsumd : (∑ i,d i) ≤ Fintype.card ι*δ := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdδ i)
  have hs : (∑ i, (d i + 66 * (|q i| + S i))) ≤ (Fintype.card ι*δ+66*σ)+66*(∑ i,|q i|) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_add_distrib]
    linarith
  exact weighted_abs_sum_of_denominator_sum q (fun i => d i+66*(|q i|+S i)) hr hN (by norm_num) hs


lemma descent_energy_sum (F Ab Ah C V R : ℕ → ℝ) {ηb ηh σ Δ : ℝ} (T : ℕ)
    (hηh : 0 ≤ ηh) (hV : 0 ≤ V T) (hR : 0 ≤ R T) (hgap : F 0-F T ≤ Δ)
    (hstep : ∀ t,t<T → F (t+1)-F t ≤ -ηb*Ab t-ηh/4*Ah t+
      ηh/2*(V t-V (t+1))+C t+ηh*σ^2/2*(R t-R (t+1))) :
    ηb*(∑ t ∈ Finset.range T,Ab t)+ηh/4*(∑ t ∈ Finset.range T,Ah t) ≤
      Δ+ηh/2*V 0+(∑ t ∈ Finset.range T,C t)+ηh*σ^2/2*R 0 := by
  have htelescope (N : ℕ)
      (hs : ∀ t,t<N → F (t+1)-F t ≤ -ηb*Ab t-ηh/4*Ah t+
        ηh/2*(V t-V (t+1))+C t+ηh*σ^2/2*(R t-R (t+1))) :
      F N-F 0+ηb*(∑ t ∈ Finset.range N,Ab t)+ηh/4*(∑ t ∈ Finset.range N,Ah t) ≤
        ηh/2*(V 0-V N)+(∑ t ∈ Finset.range N,C t)+ηh*σ^2/2*(R 0-R N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hh := ih (fun t ht => hs t (by omega))
      have hN := hs N (by omega)
      simp only [Finset.sum_range_succ]
      nlinarith
  have hh := htelescope T hstep
  have hp := mul_nonneg hηh hV
  have hr := mul_nonneg (mul_nonneg hηh (sq_nonneg σ)) hR
  nlinarith


lemma prefix_late_energy_sum (U A E : ℕ → ℝ) {c D : ℝ} (T k : ℕ)
    (hearly : ∀ t,t<T → t<k → U t ≤ D)
    (hlate : ∀ t,t<T → k ≤ t → U t+c*A t ≤ E t) :
    (∑ t ∈ Finset.range T,U t)+c*(∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),A t) ≤
      (min k T : ℕ)*D+∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),E t := by
  have he : (Finset.range T).filter (fun t => ¬ k ≤ t)=Finset.range (min k T) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have hper : (∑ t ∈ Finset.range T,(U t+(if k ≤ t then c*A t else 0))) ≤
      ∑ t ∈ Finset.range T,if k ≤ t then E t else D := by
    apply Finset.sum_le_sum
    intro t ht
    by_cases hk : k ≤ t
    · simpa only [ite_eq_left hk] using hlate t (Finset.mem_range.mp ht) hk
    · simpa only [ite_eq_right hk,add_zero] using hearly t (Finset.mem_range.mp ht) (by omega)
  rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.mul_sum] at hper
  have hr : (∑ t ∈ Finset.range T,if k ≤ t then E t else D)=
      (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),E t)+
        ∑ t ∈ (Finset.range T).filter (fun t => ¬ k ≤ t),D := by
    rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> simp_all
  rw [hr,he] at hper
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,add_comm] using hper

lemma combined_body_head_energy {Δ Ub Uh Ab Ah Eb Eh S L cb ch : ℝ}
    (hobj : -Δ ≤ Ub+Uh+L/2*S)
    (hb : Ub+cb*Ab ≤ Eb) (hh : Uh+ch*Ah ≤ Eh) :
    cb*Ab+ch*Ah ≤ Δ+Eb+Eh+L/2*S := by linarith



lemma constant_block_step_bound {b h a η q : ℝ}
    (hb : 0 ≤ b) (hh : 0 ≤ h) (ha : 0 ≤ a) (hη : 0 ≤ η) (hηa : η ≤ a)
    (hq : 0 ≤ q) (hscale : (b+h)*a^2=q^2) :
    Real.sqrt (6400*b*η^2+h*a^2) ≤ 80*q := by
  have hs : η^2 ≤ a^2 := sq_le_sq₀ hη ha |>.mpr hηa
  have hbs := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6400*b by positivity)
  have hha : 0 ≤ h*a^2 := mul_nonneg hh (sq_nonneg a)
  have hv : 0 ≤ 6400*b*η^2+h*a^2 := by positivity
  have hsqrt := Real.sq_sqrt hv
  nlinarith [Real.sqrt_nonneg (6400*b*η^2+h*a^2)]

lemma preliminary_gradient_envelope {g L q C : ℝ} {n T : ℕ}
    (hL : 0 ≤ L) (hq : 0 ≤ q) (hT : 1 ≤ T) (hn : n ≤ T)
    (hC : C ≤ 80*q) (hg : g ≤ 2*L*q+L*n*C) :
    g ≤ 82*L*q*T := by
  have hn' : (n : ℝ) ≤ T := by exact_mod_cast hn
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h1 := mul_le_mul_of_nonneg_left hC (show 0 ≤ L*n by positivity)
  have h2 := mul_le_mul_of_nonneg_left hn' (show 0 ≤ 80*L*q by positivity)
  have h3 := mul_le_mul_of_nonneg_left hT' (show 0 ≤ 2*L*q by positivity)
  nlinarith

lemma preliminary_head_accumulator_ratio {r B σ H V T : ℝ}
    (hr : 1 ≤ r) (hT : 1 ≤ T)
    (hHr : 2*H ≤ r) (hσr : σ^2 ≤ r)
    (hB : B^2 ≤ 6889*H*T^2) (hV : V ≤ r^2+T*(B^2+σ^2)) :
    V/r^2 ≤ 4000*T^3 := by
  have hr0 : 0 < r := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
  have hB' : B^2 ≤ (6889/2 : ℝ)*r*T^2 := by
    have he := mul_le_mul_of_nonneg_right hHr (show 0 ≤ (6889/2 : ℝ)*T^2 by positivity)
    nlinarith
  have hT0 : 0 ≤ T := by linarith
  have hT2 : 1 ≤ T^2 := by nlinarith
  have hT3 : T ≤ T^3 := by nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hT2)]
  have hr2 : r ≤ r^2 := by nlinarith
  have hBr := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (6889/2 : ℝ)*T^2 by positivity)
  have hVr := mul_le_mul_of_nonneg_left (show B^2+σ^2 ≤ (6889/2 : ℝ)*r^2*T^2+r^2 by nlinarith) hT0
  have hbase := mul_le_mul_of_nonneg_right (show 1+T ≤ 2*T^3 by nlinarith) (sq_nonneg r)
  nlinarith

lemma log_poly_accumulator_bound {X T : ℝ} (hX : 0 < X) (hT : 1 ≤ T)
    (hbound : X ≤ 4000*T^3) : Real.log X ≤ 12*Real.log (10*T) := by
  have hT0 : 0 < T := by linarith
  have he := Real.log_le_log hX hbound
  rw [Real.log_mul (by norm_num : (4000 : ℝ) ≠ 0) (pow_ne_zero _ hT0.ne'),Real.log_pow] at he
  have hc := Real.log_le_log (by norm_num : (0 : ℝ) < 4000) (by norm_num : (4000 : ℝ) ≤ 10^4)
  rw [Real.log_pow] at hc
  rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hT0.ne']
  have ht := Real.log_nonneg hT
  have hten := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10)
  norm_num at he hc
  linarith

lemma preliminary_movement_energy_bound {S b h T η a q ℓ : ℝ}
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hℓ : 1 ≤ ℓ)
    (hscale : (b+h)*a^2=q^2) (hstep : T*η^2=a^2)
    (hS : S ≤ 6400*b*T*η^2+12*h*a^2*ℓ) :
    S ≤ 6500*q^2*ℓ := by
  have he : 6400*b*T*η^2=6400*b*a^2 := by nlinarith [congrArg (fun z => 6400*b*z) hstep]
  rw [he] at hS
  have hp := mul_nonneg (show 0 ≤ 6400*b*a^2 by positivity) (sub_nonneg.mpr hℓ)
  have hp' : 0 ≤ h*a^2*ℓ := by positivity
  have hs := congrArg (fun z => z*ℓ) hscale
  nlinarith [sq_nonneg q]



lemma hybrid_tuning_identities {L Δ d : ℝ} {T : ℕ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hd : 0 < d) (hT : 1 ≤ T) :
    let a := Real.sqrt (Δ/(L*d))
    let q := Real.sqrt (Δ/L)
    let η := a/Real.sqrt T
    0<a ∧ 0<η ∧ η ≤ a ∧ d*a^2=q^2 ∧ (T : ℝ)*η^2=a^2 ∧
      L*q=Real.sqrt (L*Δ) ∧ Real.sqrt (2*L*Δ) ≤ 2*L*q := by
  let a := Real.sqrt (Δ/(L*d))
  let q := Real.sqrt (Δ/L)
  let η := a/Real.sqrt T
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTr : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hTr1 : (1 : ℝ) ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT'
  have hη : 0<η := div_pos ha hTr
  have hηa : η ≤ a := (div_le_iff₀ hTr).mpr (by nlinarith)
  have ha2 : a^2=Δ/(L*d) := Real.sq_sqrt (by positivity)
  have hq2 : q^2=Δ/L := Real.sq_sqrt (by positivity)
  have hscale : d*a^2=q^2 := by rw [ha2,hq2]; field_simp
  have hstep : (T : ℝ)*η^2=a^2 := by
    dsimp only [η]
    rw [div_pow,Real.sq_sqrt (by positivity : 0 ≤ (T : ℝ))]
    field_simp
  have hLq : (L*q)^2=L*Δ := by rw [mul_pow,hq2]; field_simp
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hroot : L*q=Real.sqrt (L*Δ) := by
    have he := congrArg Real.sqrt hLq
    simpa only [Real.sqrt_sq (mul_nonneg hL.le hq0)] using he
  have hinit : Real.sqrt (2*L*Δ) ≤ 2*L*q := by
    have he := Real.sqrt_le_sqrt (show 2*L*Δ ≤ (2*(L*q))^2 by nlinarith [hLq,mul_pos hL hΔ])
    simpa only [Real.sqrt_sq (show 0 ≤ 2*(L*q) by positivity),mul_assoc] using he
  exact ⟨ha,hη,hηa,hscale,hstep,hroot,hinit⟩

lemma hybrid_initial_head_charge {r η G L Δ σ h : ℝ}
    (hη : 0 ≤ η) (hr : 0 < r) (hG : G ≤ 2*L*Δ) (hinit : 2*L*Δ+h*σ^2 ≤ r) :
    η/(2*r)*G+η*h*σ^2/(2*r) ≤ η/2 := by
  have he := mul_le_mul_of_nonneg_left (show G+h*σ^2 ≤ r by linarith) (show 0 ≤ η/(2*r) by positivity)
  have hrn : r ≠ 0 := hr.ne'
  field_simp at he ⊢
  nlinarith



lemma sum_linear_root_energy {ι : Type*} (s : Finset ι) {G A : ι → ℝ} {c N : ℝ}
    (hN : 0 ≤ N) (hA : ∀ i,0 ≤ A i) (hG : ∀ i ∈ s,G i ≤ c*A i+Real.sqrt (N*A i)) :
    (∑ i ∈ s,G i) ≤ c*(∑ i ∈ s,A i)+Real.sqrt ((s.card : ℝ)*N*(∑ i ∈ s,A i)) := by
  have he := Finset.sum_le_sum hG
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at he
  have hs := Real.sum_sqrt_mul_sqrt_le (s := s) (f := fun _ => N) (g := A) (fun _ => hN) hA
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  simp_rw [← Real.sqrt_mul hN] at hs
  rw [← Real.sqrt_mul (show 0 ≤ (s.card : ℝ)*N by positivity)] at hs
  linarith



lemma default_history_tail_exponential (k : ℕ) :
    Real.sqrt ((999/1000 : ℝ)^k) ≤ Real.exp (-(k : ℝ)/2000) := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1-1/1000) (Real.one_sub_le_exp_neg (1/1000 : ℝ)) k
  norm_num only [show (1-1/1000 : ℝ)=999/1000 by norm_num] at he
  rw [← Real.exp_nat_mul] at he
  apply Real.sqrt_le_iff.mpr
  refine ⟨Real.exp_nonneg _,he.trans_eq ?_⟩
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma half_power_exponential (k : ℕ) : (1/2 : ℝ)^k ≤ Real.exp (-(k : ℝ)/2) := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1-1/2) (Real.one_sub_le_exp_neg (1/2 : ℝ)) k
  norm_num only [show (1-1/2 : ℝ)=1/2 by norm_num] at he
  rw [← Real.exp_nat_mul] at he
  convert he using 1
  congr 1
  ring

lemma default_history_log_tail {X : ℝ} {k : ℕ} (hX : 0 < X)
    (hk : 20000*Real.log X ≤ k) : Real.sqrt ((999/1000 : ℝ)^k) ≤ 1/X^10 := by
  have he : Real.exp (-(k : ℝ)/2000) ≤ Real.exp (-(10*Real.log X)) := Real.exp_le_exp.mpr (by linarith)
  have hid : Real.exp (10*Real.log X)=X^10 := by
    rw [show (10 : ℝ)=(10 : ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hX]
  rw [Real.exp_neg,hid] at he
  exact (default_history_tail_exponential k).trans (by simpa only [one_div] using he)

lemma half_power_log_tail {X : ℝ} {k : ℕ} (hX : 1 ≤ X)
    (hk : 20000*Real.log X ≤ k) : (1/2 : ℝ)^k ≤ 1/X^20 := by
  have hX0 : 0 < X := by linarith
  have hlog := Real.log_nonneg hX
  have he : Real.exp (-(k : ℝ)/2) ≤ Real.exp (-(20*Real.log X)) := Real.exp_le_exp.mpr (by linarith)
  have hid : Real.exp (20*Real.log X)=X^20 := by
    rw [show (20 : ℝ)=(20 : ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hX0]
  rw [Real.exp_neg,hid] at he
  exact (half_power_exponential k).trans (by simpa only [one_div] using he)

lemma logarithmic_window_rounding {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    2 ≤ ⌈20000*ℓ⌉₊ ∧ 20000*ℓ ≤ (⌈20000*ℓ⌉₊ : ℕ) ∧
      (⌈20000*ℓ⌉₊ : ℝ) ≤ 20001*ℓ ∧ Real.sqrt ℓ ≤ ℓ := by
  have hlo := Nat.le_ceil (20000*ℓ)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 20000*ℓ by linarith)
  have htwo : (2 : ℝ) ≤ (⌈20000*ℓ⌉₊ : ℕ) := by linarith
  refine ⟨by exact_mod_cast htwo,hlo,by linarith,?_⟩
  exact Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩

lemma half_power_preceding {k : ℕ} (hk : 1 ≤ k) :
    (1/2 : ℝ)^(k-1)=2*(1/2 : ℝ)^k := by
  have he : (1/2 : ℝ)^k=(1/2 : ℝ)^(k-1)*(1/2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  linarith

lemma logarithmic_argument_bounds {σ T : ℝ} (hσ : 0 ≤ σ) (hT : 1 ≤ T) :
    let X := 10*(1+σ)*T
    10 ≤ X ∧ T ≤ X ∧ σ ≤ X ∧ 1 ≤ Real.log X ∧ Real.log (10*T) ≤ Real.log X := by
  let X := 10*(1+σ)*T
  have hT0 : 0 ≤ T := by linarith
  have hprod := mul_nonneg hσ hT0
  have hσT := mul_le_mul_of_nonneg_left hT hσ
  have hX10 : 10 ≤ X := by dsimp [X]; nlinarith
  have hX10T : 10*T ≤ X := by dsimp [X]; nlinarith
  have hten : (1 : ℝ) ≤ Real.log 10 := by
    have he := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)
    norm_num at he
    linarith
  refine ⟨hX10,by nlinarith,by nlinarith,
    hten.trans (Real.log_le_log (by norm_num) hX10),?_⟩
  exact Real.log_le_log (by positivity) hX10T


lemma hybrid_scale_comparisons {b h : ℕ} {L M Δ : ℝ}
    (hd : 0 < b+h) (hL : 0 < L) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    let d := (b : ℝ)+h
    let a := Real.sqrt (Δ/(L*d))
    let q := Real.sqrt (Δ/L)
    let R := 1+d*(L+M)*q
    1 ≤ R ∧ b*Real.sqrt (L*Δ) ≤ R ∧ b*(L+M)*q ≤ R ∧ Δ/a ≤ R := by
  let d := (b : ℝ)+h
  let a := Real.sqrt (Δ/(L*d))
  let q := Real.sqrt (Δ/L)
  let R := 1+d*(L+M)*q
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hd0 : 0 < d := by linarith
  have hbd : (b : ℝ) ≤ d := by dsimp [d]; exact le_add_of_nonneg_right (Nat.cast_nonneg h)
  rcases hybrid_tuning_identities (T := 1) hL hΔ hd0 (by norm_num) with
    ⟨ha,hη,hηa,hscale,hstep,hroot,hinit⟩
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hR : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_right (by positivity)
  have hbq : (b : ℝ)*(L+M)*q ≤ R := by
    have he := mul_le_mul_of_nonneg_right hbd (show 0 ≤ (L+M)*q by positivity)
    dsimp [R]
    nlinarith
  have hbLq : (b : ℝ)*Real.sqrt (L*Δ) ≤ R := by
    rw [← hroot]
    have he : 0 ≤ (b : ℝ)*M*q := by positivity
    nlinarith [hbq]
  have haq : a ≤ q := by
    have he := mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg a)
    apply (sq_le_sq₀ ha.le hq0).mp
    nlinarith [hscale]
  have hΔq : L*q^2=Δ := by
    dsimp only [q]
    rw [Real.sq_sqrt (show 0 ≤ Δ/L by positivity)]
    field_simp
  have hdiv : Δ/a=d*L*a := (div_eq_iff ha.ne').mpr (by
    have he := congrArg (fun z => L*z) hscale
    nlinarith [hΔq])
  have hgap : Δ/a ≤ R := by
    rw [hdiv]
    have he := mul_le_mul_of_nonneg_left haq (show 0 ≤ d*L by positivity)
    have hm : 0 ≤ d*M*q := by positivity
    dsimp [R]
    nlinarith
  exact ⟨hR,hbLq,hbq,hgap⟩

lemma history_tail_charge {X T R C σ z : ℝ} (hX : 10 ≤ X) (hT : 1 ≤ T) (hTX : T ≤ X)
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hCB : C ≤ 83*R*T) (hσ : 0 ≤ σ) (hσX : σ ≤ X)
    (hz : 0 ≤ z) (hzX : z ≤ 1/X^10) :
    1300480*Real.sqrt T*z*(C+σ) ≤ 2*R := by
  have hX0 : 0 < X := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hroot : Real.sqrt T ≤ X := (Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩).trans hTX
  have hCX : C+σ ≤ 84*R*X := by
    have he := mul_le_mul_of_nonneg_left hTX (show 0 ≤ 83*R by positivity)
    have hx := mul_le_mul_of_nonneg_right hR hX0.le
    nlinarith
  have hp := mul_le_mul hroot hCX (show 0 ≤ C+σ by positivity) hX0.le
  have hpz := mul_le_mul hp hzX hz (show 0 ≤ X*(84*R*X) by positivity)
  have hscale := mul_le_mul_of_nonneg_left hpz (show (0 : ℝ) ≤ 1300480 by norm_num)
  have hpow : (100000000 : ℝ) ≤ X^8 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hX 8
    norm_num at he
    exact he
  have hbound : 1300480*(X*(84*R*X)*(1/X^10)) ≤ 2*R := by
    rw [one_div]
    rw [← mul_assoc,← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos hX0 10)).mpr
    have he := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*R*X^2 by positivity)
    have hid : 2*R*X^2*X^8=2*R*X^10 := by ring
    rw [hid] at he
    nlinarith [mul_nonneg hR0 (sq_nonneg X)]
  exact (show 1300480*Real.sqrt T*z*(C+σ) ≤ 1300480*(X*(84*R*X)*(1/X^10)) by nlinarith [hscale]).trans hbound

lemma failure_tail_charge {X T R C K z : ℝ} (hX : 10 ≤ X) (hT : 1 ≤ T) (hTX : T ≤ X)
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hCB : C ≤ 83*R*T) (hK : 0 ≤ K) (hKX : K ≤ 20001*X)
    (hz : 0 ≤ z) (hzX : z ≤ 1/X^20) :
    160*Real.sqrt T*C*(2*K+1)*z ≤ R := by
  have hX0 : 0 < X := by linarith
  have hroot : Real.sqrt T ≤ X := (Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩).trans hTX
  have hCX : C ≤ 83*R*X := hCB.trans (mul_le_mul_of_nonneg_left hTX (by positivity))
  have hK' : 2*K+1 ≤ 40003*X := by linarith
  have hp := mul_le_mul hroot hCX hC hX0.le
  have hpK := mul_le_mul hp hK' (show 0 ≤ 2*K+1 by positivity) (show 0 ≤ X*(83*R*X) by positivity)
  have hpz := mul_le_mul hpK hzX hz (show 0 ≤ X*(83*R*X)*(40003*X) by positivity)
  have hs := mul_le_mul_of_nonneg_left hpz (show (0 : ℝ) ≤ 160 by norm_num)
  have hpow : (100000000000000000 : ℝ) ≤ X^17 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hX 17
    norm_num at he
    exact he
  have hbound : 160*(X*(83*R*X)*(40003*X)*(1/X^20)) ≤ R := by
    rw [one_div,← mul_assoc,← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos hX0 20)).mpr
    have he := mul_le_mul_of_nonneg_left hpow (show 0 ≤ R*X^3 by positivity)
    have hid : R*X^3*X^17=R*X^20 := by ring
    rw [hid] at he
    nlinarith [show 0 ≤ R*X^3 by positivity]
  exact (show 160*Real.sqrt T*C*(2*K+1)*z ≤ 160*(X*(83*R*X)*(40003*X)*(1/X^20)) by nlinarith [hs]).trans hbound

lemma tracking_movement_charge {P q k S R ℓ : ℝ}
    (hP : 0 ≤ P) (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hR : 1 ≤ R) (hℓ : 1 ≤ ℓ) (hPQ : P*q ≤ R)
    (hkℓ : k ≤ 20001*ℓ) (hSQ : S ≤ 6500*q^2*ℓ) :
    1300560*P*k*Real.sqrt S ≤ 2200000000000*R*ℓ^2 := by
  have hs : Real.sqrt S ≤ 81*q*Real.sqrt ℓ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have he := Real.sq_sqrt (show 0 ≤ ℓ by linarith)
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ ℓ by linarith)]
  have hl : Real.sqrt ℓ ≤ ℓ := Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩
  have he := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1300560*P*k by positivity)
  have he2 := mul_le_mul_of_nonneg_right hPQ (show 0 ≤ 105345360*k*Real.sqrt ℓ by positivity)
  have he3 := mul_le_mul hkℓ hl (Real.sqrt_nonneg _) (show 0 ≤ 20001*ℓ by positivity)
  have he4 := mul_le_mul_of_nonneg_left he3 (show 0 ≤ 105345360*R by positivity)
  nlinarith [mul_nonneg (show 0 ≤ R by linarith) (sq_nonneg ℓ)]

lemma prefix_energy_charge {P k u T R ℓ : ℝ}
    (hP : 0 ≤ P) (hk : 1 ≤ k) (hu : 0 ≤ u) (huk : u ≤ k)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hPR : P ≤ R)
    (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ 20001*ℓ) :
    80*P*(2+80*k)*u/Real.sqrt T ≤ 2700000000000*R*ℓ^2 := by
  have ht : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
  have hp := mul_le_mul hPR huk hu (show 0 ≤ R by linarith)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 80*(2+80*k) by positivity)
  have hkk : k^2 ≤ (20001*ℓ)^2 := (sq_le_sq₀ (by linarith) (by positivity)).mpr hkℓ
  have hscale := mul_le_mul_of_nonneg_left hkk (show 0 ≤ 6600*R by positivity)
  have hkr := mul_nonneg (show 0 ≤ R*k by positivity) (show 0 ≤ k-1 by linarith)
  have hnum : 80*P*(2+80*k)*u ≤ 2700000000000*R*ℓ^2 := by
    nlinarith [mul_nonneg (show 0 ≤ R by linarith) (sq_nonneg ℓ)]
  exact (div_le_self (by positivity) ht).trans hnum

lemma smoothness_movement_charge {L Δ a r S R ℓ : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hr : 0 < r)
    (hR : 1 ≤ R) (hℓ : 1 ≤ ℓ) (hgap : Δ/a ≤ R)
    (hrΔ : 2*L*Δ ≤ r) (hS : S ≤ 6500*(Δ/L)*ℓ) :
    (L/2+3*a*L^2/(2*r))*S/a ≤ 8125*R*ℓ^2 := by
  have hs := mul_le_mul_of_nonneg_left hS
    (show 0 ≤ (L/2+3*a*L^2/(2*r))/a by positivity)
  have hfirst := mul_le_mul_of_nonneg_right hgap (show 0 ≤ 3250*ℓ by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hrΔ (show 0 ≤ 4875*ℓ/r by positivity)
  have hid : (L/2+3*a*L^2/(2*r))/a*(6500*(Δ/L)*ℓ)=
      3250*ℓ*(Δ/a)+9750*L*Δ*ℓ/r := by field_simp; ring
  rw [hid] at hs
  have hid2 : r*(4875*ℓ/r)=4875*ℓ := by field_simp
  rw [hid2] at hsecond
  have he : (L/2+3*a*L^2/(2*r))*S/a ≤ 8125*R*ℓ := by
    have hh := mul_le_mul_of_nonneg_right hR (show 0 ≤ 4875*ℓ by positivity)
    simp only [div_eq_mul_inv] at hs hfirst hsecond ⊢
    nlinarith [hs]
  have hl : ℓ ≤ ℓ^2 := by nlinarith
  exact he.trans (mul_le_mul_of_nonneg_left hl (by positivity))

lemma combined_normalized_energy_charge {E G Prefix Track Fail Tail Init Smooth R ℓ : ℝ}
    (hR : 1 ≤ R) (hℓ : 1 ≤ ℓ)
    (he : E ≤ G+Prefix+Track+Fail+Tail+Init+Smooth)
    (hG : G ≤ R) (hP : Prefix ≤ 2700000000000*R*ℓ^2)
    (hTr : Track ≤ 2200000000000*R*ℓ^2) (hF : Fail ≤ R)
    (hTa : Tail ≤ 2*R) (hI : Init ≤ 1/2)
    (hS : Smooth ≤ 8125*R*ℓ^2) : E ≤ 10000000000000*R*ℓ^2 := by
  have hl : 1 ≤ ℓ^2 := by nlinarith
  have hr := mul_le_mul_of_nonneg_left hl (show 0 ≤ R by linarith)
  nlinarith

lemma logarithmic_energy_bound {b h T : ℕ} {L M Δ σ r S E : ℝ}
    (hd : 0 < b+h) (hT : 1 ≤ T) (hL : 0 < L) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hσ : 0 ≤ σ) (hr : 0 < r) (hrΔ : 2*L*Δ ≤ r) :
    let a := Real.sqrt (Δ/(L*((b : ℝ)+h)))
    let q := Real.sqrt (Δ/L)
    let R := 1+((b : ℝ)+h)*(L+M)*q
    let X := 10*(1+σ)*T
    let ℓ := Real.log X
    let k := ⌈20000*ℓ⌉₊
    let C := (b : ℝ)*(83*Real.sqrt (L*Δ)*T)
    S ≤ 6500*(Δ/L)*ℓ →
    E ≤ Δ/a+80*(b*Real.sqrt (L*Δ))*(2+80*k)*(min k T : ℕ)/Real.sqrt T+
      1300560*(b*(L+M))*k*Real.sqrt S+
      160*Real.sqrt T*C*(2*k+1)*(1/2 : ℝ)^k+
      1300480*Real.sqrt T*Real.sqrt ((999/1000 : ℝ)^k)*(C+σ)+1/2+
      (L/2+3*a*L^2/(2*r))*S/a →
    E ≤ 10000000000000*R*ℓ^2 := by
  let a := Real.sqrt (Δ/(L*((b : ℝ)+h)))
  let q := Real.sqrt (Δ/L)
  let R := 1+((b : ℝ)+h)*(L+M)*q
  let X := 10*(1+σ)*T
  let ℓ := Real.log X
  let k := ⌈20000*ℓ⌉₊
  let C := (b : ℝ)*(83*Real.sqrt (L*Δ)*T)
  dsimp only
  intro hS he
  rcases hybrid_scale_comparisons hd hL hM hΔ with ⟨hR,hP,hPQ,hgap⟩
  rcases logarithmic_argument_bounds hσ (show (1 : ℝ) ≤ T by exact_mod_cast hT) with
    ⟨hX,hTX,hσX,hℓ,hlog⟩
  rcases logarithmic_window_rounding hℓ with ⟨hk2,hklo,hkhi,hsqrt⟩
  have hdim : (0 : ℝ) < (b : ℝ)+h := by exact_mod_cast hd
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  change 2 ≤ k at hk2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCB : C ≤ 83*R*T := by
    have hh := mul_le_mul_of_nonneg_right hP (show (0 : ℝ) ≤ 83*T by positivity)
    dsimp [C]; nlinarith
  have hX0 : 0 < X := by linarith
  have hkX : (k : ℝ) ≤ 20001*X := hkhi.trans
    (mul_le_mul_of_nonneg_left (Real.log_le_self hX0.le) (by norm_num))
  have hhistory := history_tail_charge hX (show (1 : ℝ) ≤ T by exact_mod_cast hT)
    hTX hR hC hCB hσ hσX (Real.sqrt_nonneg _)
    (default_history_log_tail hX0 hklo)
  have hfailure := failure_tail_charge hX (show (1 : ℝ) ≤ T by exact_mod_cast hT)
    hTX hR hC hCB hk0 hkX (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^k)
    (half_power_log_tail (by linarith : 1 ≤ X) hklo)
  have hSq : S ≤ 6500*q^2*ℓ := by
    dsimp [q]
    rw [Real.sq_sqrt (show 0 ≤ Δ/L by positivity)]
    exact hS
  have htracking := tracking_movement_charge (show 0 ≤ (b : ℝ)*(L+M) by positivity)
    hq hk0 hR hℓ hPQ hkhi hSq
  have hprefix := prefix_energy_charge (show 0 ≤ (b : ℝ)*Real.sqrt (L*Δ) by positivity)
    hk1 (show (0 : ℝ) ≤ (min k T : ℕ) by positivity)
    (show ((min k T : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.min_le_left k T)
    (show (1 : ℝ) ≤ T by exact_mod_cast hT) hR hP hℓ hkhi
  have hsmooth := smoothness_movement_charge hL ha hr hR hℓ hgap hrΔ hS
  exact combined_normalized_energy_charge hR hℓ he hgap hprefix htracking hfailure hhistory
    (by rfl : (1/2 : ℝ) ≤ 1/2) hsmooth

lemma hybrid_energy_normalization {E Δ Prefix Track Fail Tail Init Smooth a η u T : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hη : η=a/u) (huT : u^2=T)
    (hI : Init ≤ a/2)
    (he : E ≤ Δ+η*Prefix+η*u*Track+η*T*(Fail+Tail)+Init+Smooth) :
    E/a ≤ Δ/a+Prefix/u+Track+u*(Fail+Tail)+1/2+Smooth/a := by
  have hid : (Δ/a+Prefix/u+Track+u*(Fail+Tail)+1/2+Smooth/a)*a=
      Δ+η*Prefix+η*u*Track+η*T*(Fail+Tail)+a/2+Smooth := by
    rw [hη,← huT]
    field_simp
  apply (div_le_iff₀ ha).mpr
  rw [hid]
  linarith

lemma hybrid_energy_block_bounds {Ab Ah R ℓ u : ℝ}
    (hu : 0 < u) (hb : 0 ≤ Ab) (hh : 0 ≤ Ah)
    (he : Ab/(3000*u)+Ah/4 ≤ 10000000000000*R*ℓ^2) :
    Ab ≤ 30000000000000000*R*ℓ^2*u ∧ Ah ≤ 40000000000000*R*ℓ^2 := by
  have hAb : Ab/(3000*u) ≤ 10000000000000*R*ℓ^2 := by linarith
  have hAh : Ah/4 ≤ 10000000000000*R*ℓ^2 := by
    have hpos : 0 ≤ Ab/(3000*u) := by positivity
    linarith
  constructor
  · have hx := (div_le_iff₀ (show 0 < 3000*u by positivity)).mp hAb
    nlinarith
  · linarith

lemma body_gradient_energy_rate {A N R ℓ u : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hR : 0 ≤ R) (hℓ : 0 ≤ ℓ) (hu : 0 ≤ u)
    (hAB : A ≤ 30000000000000000*R*ℓ^2*u) :
    66*A+Real.sqrt (u^2*N*A) ≤ 2000000000000000000*R*ℓ^2*u+
      200000000*Real.sqrt (N*R)*ℓ*u*Real.sqrt u := by
  have hs : Real.sqrt A ≤ 200000000*Real.sqrt R*ℓ*Real.sqrt u := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hr := Real.sq_sqrt hR
    have hu2 := Real.sq_sqrt hu
    have hid : (200000000*Real.sqrt R*ℓ*Real.sqrt u)^2=40000000000000000*R*ℓ^2*u := by
      rw [mul_pow,mul_pow,mul_pow,hr,hu2]
      ring
    rw [hid]
    nlinarith [show 0 ≤ R*ℓ^2*u by positivity]
  have he := mul_le_mul_of_nonneg_left hs (show 0 ≤ u*Real.sqrt N by positivity)
  have hid : Real.sqrt (u^2*N*A)=u*Real.sqrt N*Real.sqrt A := by
    rw [Real.sqrt_mul (mul_nonneg (sq_nonneg u) hN),Real.sqrt_mul (sq_nonneg u),Real.sqrt_sq hu]
  rw [hid]
  have hnr : Real.sqrt (N*R)=Real.sqrt N*Real.sqrt R := Real.sqrt_mul hN R
  rw [hnr]
  nlinarith [show 0 ≤ R*ℓ^2*u by positivity]

lemma head_gradient_energy_rate {B N R H ℓ u : ℝ}
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hR : 1 ≤ R) (hH : 0 ≤ H)
    (hℓ : 1 ≤ ℓ) (hu : 0 ≤ u) (hBB : B ≤ 40000000000000*R*ℓ^2) :
    u*Real.sqrt B*Real.sqrt (2*H+B+2*N*u) ≤
      50000000000000*Real.sqrt (R^2+H*R)*ℓ^2*u+
      20000000*Real.sqrt (N*R)*ℓ*u*Real.sqrt u := by
  have hR0 : 0 ≤ R := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hb2 := Real.sq_sqrt hB
  have hn2 := Real.sq_sqrt hN
  have hr2 := Real.sq_sqrt hR0
  have hh2 := Real.sq_sqrt hH
  have hu2 := Real.sq_sqrt hu
  have hbroot : Real.sqrt B ≤ 10000000*Real.sqrt R*ℓ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hid : (10000000*Real.sqrt R*ℓ)^2=100000000000000*R*ℓ^2 := by
      rw [mul_pow,mul_pow,hr2]; ring
    rw [hid]
    nlinarith [show 0 ≤ R*ℓ^2 by positivity]
  have hsplit : Real.sqrt (2*H+B+2*N*u) ≤ 2*Real.sqrt H+Real.sqrt B+2*Real.sqrt N*Real.sqrt u := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hp : (Real.sqrt N*Real.sqrt u)^2=N*u := by rw [mul_pow,hn2,hu2]
    nlinarith [show 0 ≤ Real.sqrt H*Real.sqrt B by positivity,
      show 0 ≤ Real.sqrt H*(Real.sqrt N*Real.sqrt u) by positivity,
      show 0 ≤ Real.sqrt B*(Real.sqrt N*Real.sqrt u) by positivity]
  let C := Real.sqrt (R^2+H*R)
  have hc2 : C^2=R^2+H*R := Real.sq_sqrt (by positivity)
  have hCR : R ≤ C := (sq_le_sq₀ hR0 (Real.sqrt_nonneg _)).mp (by nlinarith [mul_nonneg hH hR0])
  have hCH : Real.sqrt R*Real.sqrt H ≤ C := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,hr2,hh2,hc2]
    nlinarith [sq_nonneg R]
  have hmain := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ u*Real.sqrt B by positivity)
  have hh := mul_le_mul_of_nonneg_right hbroot (show 0 ≤ 2*u*Real.sqrt H by positivity)
  have hn := mul_le_mul_of_nonneg_right hbroot (show 0 ≤ 2*u*Real.sqrt N*Real.sqrt u by positivity)
  have hHC := mul_le_mul_of_nonneg_right hCH (show 0 ≤ 20000000*ℓ*u by positivity)
  have hRC := mul_le_mul_of_nonneg_right hCR (show 0 ≤ 40000000000000*ℓ^2*u by positivity)
  have hBu := mul_le_mul_of_nonneg_right hBB hu
  have hl : ℓ ≤ ℓ^2 := by nlinarith
  have hCl := mul_le_mul_of_nonneg_right hl (show 0 ≤ 20000000*C*u by positivity)
  have hnr : Real.sqrt (N*R)=Real.sqrt N*Real.sqrt R := Real.sqrt_mul hN R
  rw [hnr]
  change u*Real.sqrt B*Real.sqrt (2*H+B+2*N*u) ≤
    50000000000000*C*ℓ^2*u+20000000*(Real.sqrt N*Real.sqrt R)*ℓ*u*Real.sqrt u
  have hbid : u*Real.sqrt B*Real.sqrt B=u*B := by nlinarith [hb2]
  nlinarith [show 0 ≤ C*ℓ^2*u by positivity]

lemma hybrid_gradient_energy_rate {Ab Ah N H R ℓ u Rest G : ℝ}
    (hb : 0 ≤ Ab) (hh : 0 ≤ Ah) (hN : 0 ≤ N) (hH : 0 ≤ H)
    (hR : 1 ≤ R) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u)
    (he : Ab/(3000*u)+Ah/4 ≤ 10000000000000*R*ℓ^2)
    (hRest : Rest ≤ 100000000000*R*ℓ^2*u)
    (hG : G ≤ Rest+66*Ab+Real.sqrt (u^2*N*Ab)+
      u*Real.sqrt Ah*Real.sqrt (2*H+Ah+2*N*u)) :
    G ≤ 10000000000000000000*(Real.sqrt (N*R)*ℓ*u*Real.sqrt u+
      Real.sqrt (R^2+H*R)*ℓ^2*u) := by
  have hu0 : 0 < u := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  rcases hybrid_energy_block_bounds hu0 hb hh he with ⟨hAb,hAh⟩
  have hbody := body_gradient_energy_rate hb hN hR0 hℓ0 hu0.le hAb
  have hhead := head_gradient_energy_rate hh hN hR hH hℓ hu0.le hAh
  have hCR : R ≤ Real.sqrt (R^2+H*R) := by
    apply (sq_le_sq₀ hR0 (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [mul_nonneg hH hR0]
  have hc := mul_le_mul_of_nonneg_right hCR (show 0 ≤ ℓ^2*u by positivity)
  nlinarith only [hG,hRest,hbody,hhead,hc,show 0 ≤ Real.sqrt (N*R)*ℓ*u*Real.sqrt u by positivity,
    show 0 ≤ Real.sqrt (R^2+H*R)*ℓ^2*u by positivity]

lemma hybrid_gradient_scale {b h : ℕ} {L M Δ : ℝ}
    (hd : 0 < b+h) (hL : 0 < L) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    Real.sqrt (L*Δ) ≤ 1+((b : ℝ)+h)*(L+M)*Real.sqrt (Δ/L) := by
  have he := (hybrid_scale_comparisons (b := b+h) (h := 0) (by omega) hL hM hΔ).2.1
  simp only [Nat.cast_add,Nat.cast_zero,add_zero] at he
  have hd1 : (1 : ℝ) ≤ (b : ℝ)+h := by exact_mod_cast hd
  have hh := mul_le_mul_of_nonneg_right hd1 (Real.sqrt_nonneg (L*Δ))
  nlinarith

lemma output_prefix_charge {G k v u R ℓ : ℝ}
    (hGR : G ≤ R) (hk : 1 ≤ k) (hv : 0 ≤ v) (hvk : v ≤ k)
    (hu : 1 ≤ u) (hR : 1 ≤ R) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ 20001*ℓ) :
    (2+80*k)*G*v ≤ 40000000000*R*ℓ^2*u := by
  have hp := mul_le_mul hGR hvk hv (show 0 ≤ R by linarith)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2+80*k by positivity)
  have hkk : k^2 ≤ (20001*ℓ)^2 := (sq_le_sq₀ (by linarith) (by positivity)).mpr hkℓ
  have hscale := mul_le_mul_of_nonneg_left hkk (show 0 ≤ 82*R by positivity)
  have hkr := mul_nonneg (show 0 ≤ R*k by positivity) (show 0 ≤ k-1 by linarith)
  have he : (2+80*k)*G*v ≤ 40000000000*R*ℓ^2 := by
    nlinarith [show 0 ≤ R*ℓ^2 by positivity]
  exact he.trans (by nlinarith [mul_nonneg (show 0 ≤ 40000000000*R*ℓ^2 by positivity) (sub_nonneg.mpr hu)])

lemma output_lag_charge {P q k S R ℓ u : ℝ}
    (hP : 0 ≤ P) (hq : 0 ≤ q) (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hR : 1 ≤ R) (hℓ : 1 ≤ ℓ) (hPQ : P*q ≤ R)
    (hkℓ : k ≤ 20001*ℓ) (hSQ : S ≤ 6500*q^2*ℓ) :
    P*k*u*Real.sqrt S ≤ 2000000*R*ℓ^2*u := by
  have hs : Real.sqrt S ≤ 81*q*Real.sqrt ℓ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have he := Real.sq_sqrt (show 0 ≤ ℓ by linarith)
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ ℓ by linarith)]
  have hl : Real.sqrt ℓ ≤ ℓ := Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩
  have he := mul_le_mul_of_nonneg_left hs (show 0 ≤ P*k*u by positivity)
  have he2 := mul_le_mul_of_nonneg_right hPQ (show 0 ≤ 81*k*u*Real.sqrt ℓ by positivity)
  have he3 := mul_le_mul hkℓ hl (Real.sqrt_nonneg _) (show 0 ≤ 20001*ℓ by positivity)
  have he4 := mul_le_mul_of_nonneg_left he3 (show 0 ≤ 81*R*u by positivity)
  nlinarith [show 0 ≤ R*ℓ^2*u by positivity]



lemma rounded_log_budget {C Q σ : ℝ} (hC : 20 ≤ C) (hQ : 1 ≤ Q) (hσ : 0 ≤ σ) :
    let z := Real.log (C*(1+σ)*Q)
    let T := ⌈C*Q*z^4⌉₊
    1 ≤ z ∧ 1 ≤ T ∧ C*Q*z^4 ≤ (T : ℝ) ∧
      (T : ℝ) ≤ 2*C*Q*z^4 ∧ Real.log (10*(1+σ)*T) ≤ 6*z := by
  let z := Real.log (C*(1+σ)*Q)
  let T := ⌈C*Q*z^4⌉₊
  have hC0 : 0 < C := by linarith
  have hQ0 : 0 < Q := by linarith
  have hs0 : 0 < 1+σ := by linarith
  have hz1 : 1 ≤ z := by
    have he := (logarithmic_argument_bounds hσ hQ).2.2.2.1
    apply he.trans
    apply Real.log_le_log (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ C-10 by linarith) (show 0 ≤ (1+σ)*Q by positivity)]
  have hz0 : 0 < z := by linarith
  have hz4 : 1 ≤ z^4 := by nlinarith [sq_nonneg (z^2-1),sq_nonneg z]
  have hbase : 1 ≤ C*Q*z^4 := by
    have he := mul_le_mul hQ hz4 (by norm_num : (0 : ℝ) ≤ 1) hQ0.le
    have hh := mul_le_mul_of_nonneg_left he hC0.le
    nlinarith
  have hlo : C*Q*z^4 ≤ (T : ℝ) := Nat.le_ceil _
  have hhi : (T : ℝ) ≤ 2*C*Q*z^4 := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ C*Q*z^4 by positivity)
    change (T : ℝ) < C*Q*z^4+1 at he
    linarith
  have hT : 1 ≤ T := by exact_mod_cast (show (1 : ℝ) ≤ T by linarith)
  have hlogT := Real.log_le_log (show 0 < 10*(1+σ)*(T : ℝ) by positivity)
    (mul_le_mul_of_nonneg_left hhi (show 0 ≤ 10*(1+σ) by positivity))
  have hid : 10*(1+σ)*(2*C*Q*z^4)=20*(C*(1+σ)*Q)*z^4 := by ring
  have hlogid : Real.log (20*(C*(1+σ)*Q)*z^4)=Real.log 20+z+4*Real.log z := by
    rw [Real.log_mul (by positivity : 20*(C*(1+σ)*Q) ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) (by positivity),Real.log_pow]
    rfl
  rw [hid,hlogid] at hlogT
  have hlog20 : Real.log 20 ≤ z := by
    apply Real.log_le_log (by norm_num)
    have hsQ : 1 ≤ (1+σ)*Q := by nlinarith [mul_nonneg hσ hQ0.le]
    have hh := mul_le_mul_of_nonneg_left hsQ hC0.le
    nlinarith
  have hlogz := Real.log_le_self hz0.le
  refine ⟨hz1,hT,hlo,hhi,?_⟩
  change Real.log (10*(1+σ)*(T : ℝ)) ≤ 6*z
  change Real.log (10*(1+σ)*(T : ℝ)) ≤ Real.log 20+z+4*Real.log z at hlogT
  linarith




lemma structured_budget_parameters {A R N N₀ H ε : ℝ}
    (hA : 1 ≤ A) (hN : 0 ≤ N) (hN₀ : 0 ≤ N₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hR2 : R^2 ≤ 2*A) (hRA : R ≤ 2*Real.sqrt A) (hNN : N ≤ 66*N₀) :
    let Q := 1+A*N₀^2/ε^4+(A+H*Real.sqrt A)/ε^2
    1 ≤ Q ∧ N^2*R^2 ≤ 10000*Q*ε^4 ∧ R^2+H*R ≤ 4*Q*ε^2 := by
  let Q := 1+A*N₀^2/ε^4+(A+H*Real.sqrt A)/ε^2
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    linarith only [show 0 ≤ A*N₀^2/ε^4 by positivity,show 0 ≤ (A+H*Real.sqrt A)/ε^2 by positivity]
  have hfirst : A*N₀^2/ε^4 ≤ Q := by
    dsimp [Q]
    linarith only [show 0 ≤ (A+H*Real.sqrt A)/ε^2 by positivity]
  have hsecond : (A+H*Real.sqrt A)/ε^2 ≤ Q := by
    dsimp [Q]
    linarith only [show 0 ≤ A*N₀^2/ε^4 by positivity]
  have h1 := (div_le_iff₀ (pow_pos hε 4)).mp hfirst
  have h2 := (div_le_iff₀ (pow_pos hε 2)).mp hsecond
  have hN2 : N^2 ≤ (66*N₀)^2 := (sq_le_sq₀ hN (by positivity)).mpr hNN
  have hp := mul_le_mul hN2 hR2 (sq_nonneg R) (sq_nonneg (66*N₀))
  have hHR := mul_le_mul_of_nonneg_left hRA hH
  refine ⟨hQ,?_,?_⟩
  · nlinarith only [hp,h1,show 0 ≤ A*N₀^2 by positivity]
  · nlinarith only [hR2,hHR,h2,show 0 ≤ Q*ε^2 by positivity]

lemma dimension_scale_square {d L M Δ : ℝ}
    (hd : 0 ≤ d) (hL : 0 < L) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) :
    let A := 1+d^2*(L+M)^2*Δ/L
    let R := 1+d*(L+M)*Real.sqrt (Δ/L)
    1 ≤ A ∧ 1 ≤ R ∧ R^2 ≤ 2*A ∧ R ≤ 2*Real.sqrt A := by
  let A := 1+d^2*(L+M)^2*Δ/L
  let R := 1+d*(L+M)*Real.sqrt (Δ/L)
  have hA : 1 ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
  have hR : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_right (by positivity)
  have hid : (d*(L+M)*Real.sqrt (Δ/L))^2=A-1 := by
    dsimp [A]
    rw [mul_pow,mul_pow,Real.sq_sqrt (show 0 ≤ Δ/L by positivity)]
    ring
  have hs : R^2 ≤ 2*A := by
    dsimp [R]
    nlinarith only [hid,sq_nonneg (d*(L+M)*Real.sqrt (Δ/L)-1)]
  have hroot : R ≤ 2*Real.sqrt A := by
    apply (sq_le_sq₀ (by linarith) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by linarith : 0 ≤ A)]
    nlinarith only [hs,hA]
  exact ⟨hA,hR,hs,hroot⟩

lemma block_noise_simplification {b h : ℕ} {δ σb σh : ℝ}
    (hδ : 0 ≤ δ) (hh : 0 ≤ σh) :
    (b : ℝ)*δ+66*σb+Real.sqrt h*σh ≤ 66*(b*δ+σb+Real.sqrt h*σh) := by
  nlinarith only [show 0 ≤ (b : ℝ)*δ by positivity,show 0 ≤ Real.sqrt h*σh by positivity]




lemma budget_numerator_roots {N R D Q ε : ℝ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hNR : N^2*R^2 ≤ 10000*Q*ε^4) (hD : D ≤ 4*Q*ε^2) :
    Real.sqrt (N*R) ≤ 10*Real.sqrt (Real.sqrt Q)*ε ∧
      Real.sqrt D ≤ 2*Real.sqrt Q*ε := by
  have hv2 := Real.sq_sqrt (Real.sqrt_nonneg Q)
  have hq2 := Real.sq_sqrt hQ
  have hv4 : (Real.sqrt (Real.sqrt Q))^4=Q := by
    calc
      _=((Real.sqrt (Real.sqrt Q))^2)^2 := by ring
      _=(Real.sqrt Q)^2 := by rw [hv2]
      _=Q := hq2
  constructor
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    apply (sq_le_sq₀ (mul_nonneg hN hR) (sq_nonneg _)).mp
    have hid : ((10*Real.sqrt (Real.sqrt Q)*ε)^2)^2=10000*Q*ε^4 := by
      rw [← pow_mul]
      norm_num only [Nat.reduceMul]
      rw [mul_pow,mul_pow,hv4]
      ring
    rw [mul_pow,hid]
    exact hNR
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hid : (2*Real.sqrt Q*ε)^2=4*Q*ε^2 := by rw [mul_pow,mul_pow,hq2]; ring
    rw [hid]
    exact hD

lemma budget_denominator_roots {T Q z : ℝ} (hQ : 0 ≤ Q) (hz : 0 ≤ z)
    (hT : (1000000000000000000000 : ℝ)^4*Q*z^4 ≤ T) :
    1000000000000000000000000000000000000000000*Real.sqrt Q*z^2 ≤ Real.sqrt T ∧
      1000000000000000000000*Real.sqrt (Real.sqrt Q)*z ≤ Real.sqrt (Real.sqrt T) := by
  have hq2 := Real.sq_sqrt hQ
  have hv2 := Real.sq_sqrt (Real.sqrt_nonneg Q)
  have hfirst : 1000000000000000000000000000000000000000000*Real.sqrt Q*z^2 ≤ Real.sqrt T := by
    have hid : (1000000000000000000000000000000000000000000*Real.sqrt Q*z^2)^2=
        (1000000000000000000000 : ℝ)^4*Q*z^4 := by
      rw [mul_pow,mul_pow,hq2]
      ring
    have he := Real.sqrt_le_sqrt (hid.trans_le hT)
    simpa only [Real.sqrt_sq (show 0 ≤ 1000000000000000000000000000000000000000000*Real.sqrt Q*z^2 by positivity)] using he
  refine ⟨hfirst,?_⟩
  have hid : (1000000000000000000000*Real.sqrt (Real.sqrt Q)*z)^2=
      1000000000000000000000000000000000000000000*Real.sqrt Q*z^2 := by
    rw [mul_pow,mul_pow,hv2]
    ring
  have he := Real.sqrt_le_sqrt (hid.trans_le hfirst)
  simpa only [Real.sqrt_sq (show 0 ≤ 1000000000000000000000*Real.sqrt (Real.sqrt Q)*z by positivity)] using he




lemma gradient_rate_normalization {G A B ℓ T u v K : ℝ}
    (hu : 0 < u) (hv : 0 < v) (huT : u^2=T) (hvu : v^2=u)
    (he : G ≤ K*(A*ℓ*u*v+B*ℓ^2*u)) :
    G/T ≤ K*(A*ℓ/v+B*ℓ^2/u) := by
  have hT : 0 < T := by rw [← huT]; positivity
  apply (div_le_iff₀ hT).mpr
  have hid : K*(A*ℓ/v+B*ℓ^2/u)*T=K*(A*ℓ*u*v+B*ℓ^2*u) := by
    rw [← huT,← hvu]
    field_simp
  rw [hid]
  exact he

lemma explicit_gradient_rate_inversion {A B ℓ u v z q q₄ ε : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hu : 0 < u) (hv : 0 < v)
    (hz : 0 ≤ z) (hq : 0 ≤ q) (hq₄ : 0 ≤ q₄) (hε : 0 < ε)
    (hAn : A ≤ 10*q₄*ε) (hBn : B ≤ 2*q*ε) (hℓ : ℓ ≤ 6*z)
    (huB : 1000000000000000000000000000000000000000000*q*z^2 ≤ u)
    (hvB : 1000000000000000000000*q₄*z ≤ v) :
    10000000000000000000*(A*ℓ/v+B*ℓ^2/u) ≤ ε := by
  have hfirst : 10000000000000000000*A*ℓ/v ≤ 3*ε/5 := by
    apply (div_le_iff₀ hv).mpr
    have hp := mul_le_mul hAn hℓ hℓ0 (show 0 ≤ 10*q₄*ε by positivity)
    have hd := mul_le_mul_of_nonneg_left hvB (show 0 ≤ 3*ε/5 by positivity)
    nlinarith only [hp,hd]
  have hsecond : 10000000000000000000*B*ℓ^2/u ≤ ε/5 := by
    apply (div_le_iff₀ hu).mpr
    have hl2 : ℓ^2 ≤ (6*z)^2 := (sq_le_sq₀ hℓ0 (by positivity)).mpr hℓ
    have hp := mul_le_mul hBn hl2 (sq_nonneg ℓ) (show 0 ≤ 2*q*ε by positivity)
    have hd := mul_le_mul_of_nonneg_left huB (show 0 ≤ ε/5 by positivity)
    nlinarith only [hp,hd,show 0 ≤ q*ε*z^2 by positivity]
  simp only [div_eq_mul_inv] at hfirst hsecond ⊢
  nlinarith only [hfirst,hsecond,hε]




lemma structured_budget_suffices {A R N N₀ H ε σ : ℝ}
    (hA : 1 ≤ A) (hR : 0 ≤ R) (hN : 0 ≤ N) (hN₀ : 0 ≤ N₀) (hH : 0 ≤ H)
    (hε : 0 < ε) (hσ : 0 ≤ σ) (hR2 : R^2 ≤ 2*A) (hRA : R ≤ 2*Real.sqrt A) (hNN : N ≤ 66*N₀) :
    let Q := 1+A*N₀^2/ε^4+(A+H*Real.sqrt A)/ε^2
    let z := Real.log ((10 : ℝ)^84*(1+σ)*Q)
    let T := ⌈(10 : ℝ)^84*Q*z^4⌉₊
    let ℓ := Real.log (10*(1+σ)*T)
    1 ≤ T ∧ 10000000000000000000*(Real.sqrt (N*R)*ℓ/Real.sqrt (Real.sqrt T)+
      Real.sqrt (R^2+H*R)*ℓ^2/Real.sqrt T) ≤ ε := by
  let Q := 1+A*N₀^2/ε^4+(A+H*Real.sqrt A)/ε^2
  let z := Real.log ((10 : ℝ)^84*(1+σ)*Q)
  let T := ⌈(10 : ℝ)^84*Q*z^4⌉₊
  let ℓ := Real.log (10*(1+σ)*T)
  rcases structured_budget_parameters hA hN hN₀ hH hε hR2 hRA hNN with ⟨hQ,hNR,hD⟩
  rcases rounded_log_budget (C := (10 : ℝ)^84) (by norm_num) hQ hσ with
    ⟨hz,hT,hlo,hhi,hlog⟩
  change 1 ≤ Q at hQ
  change 1 ≤ z at hz
  change 1 ≤ T at hT
  change (10 : ℝ)^84*Q*z^4 ≤ (T : ℝ) at hlo
  have hQ0 : 0 ≤ Q := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hu : 0 < Real.sqrt (T : ℝ) := by positivity
  have hv : 0 < Real.sqrt (Real.sqrt (T : ℝ)) := by positivity
  have hℓ0 : 0 ≤ ℓ := by
    have hh := (logarithmic_argument_bounds hσ hTr).2.2.2.1
    linarith
  rcases budget_numerator_roots hN hR hQ0 hε.le hNR hD with ⟨hn,hd⟩
  have hlo' : (1000000000000000000000 : ℝ)^4*Q*z^4 ≤ (T : ℝ) := by
    rw [show (1000000000000000000000 : ℝ)^4=(10 : ℝ)^84 by norm_num]
    exact hlo
  rcases budget_denominator_roots hQ0 hz0 hlo' with ⟨huB,hvB⟩
  exact ⟨hT,explicit_gradient_rate_inversion hℓ0 hu hv hz0 (Real.sqrt_nonneg Q)
    (Real.sqrt_nonneg (Real.sqrt Q)) hε hn hd hlog huB hvB⟩


end LongTails.Proofs.AdaptiveHistoryAlgebra
