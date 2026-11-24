import LongTails.Proofs.NcConcavePsi

open scoped BigOperators

namespace LongTails.Proofs.NcConcavePartTwo

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi

variable {n : ℕ}

noncomputable def cδ : ℝ := 1 / 100

noncomputable def Rab : ℝ := 2

noncomputable def κ : ℝ := (cδ + Rab + 10) / (cη + 1)

lemma κ_eq : κ = 1201 / 1000100 := by norm_num [κ, cδ, Rab, cη]

lemma κ_pos : 0 < κ := by rw [κ_eq]; norm_num

lemma κ_small : κ < 1 / 800 := by rw [κ_eq]; norm_num

def ind (j k : Fin (n + 1)) : ℝ := if j = k then 1 else 0

noncomputable def hvec (u : Fin (n + 1) → ℝ) (a : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  ∑ k, (a k - rho u k) * drho u (ind j) k

lemma l2_triangle3 (r x y z : Fin n → ℝ) (h : ∀ i, |r i| ≤ x i + y i + z i) :
    Real.sqrt (sq2 r) ≤ Real.sqrt (sq2 x) + Real.sqrt (sq2 y) + Real.sqrt (sq2 z) := by
  have hX := Real.sqrt_nonneg (sq2 x)
  have hY := Real.sqrt_nonneg (sq2 y)
  have hZ := Real.sqrt_nonneg (sq2 z)
  rw [Real.sqrt_le_left (by positivity)]
  have hx2 : Real.sqrt (sq2 x) ^ 2 = sq2 x := Real.sq_sqrt (sq2_nonneg x)
  have hy2 : Real.sqrt (sq2 y) ^ 2 = sq2 y := Real.sq_sqrt (sq2_nonneg y)
  have hz2 : Real.sqrt (sq2 z) ^ 2 = sq2 z := Real.sq_sqrt (sq2_nonneg z)
  have cs (f g : Fin n → ℝ) : ∑ i, f i * g i ≤ Real.sqrt (sq2 f) * Real.sqrt (sq2 g) := by
    rw [← Real.sqrt_mul (sq2_nonneg f)]
    exact Real.le_sqrt_of_sq_le (inner_le_sq2 f g)
  have hpt (i : Fin n) : r i ^ 2 ≤ (x i + y i + z i) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  have hsum : sq2 r ≤ sq2 x + sq2 y + sq2 z + 2 * ∑ i, x i * y i + 2 * ∑ i, y i * z i +
      2 * ∑ i, x i * z i := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    unfold sq2
    calc ∑ i, r i ^ 2 ≤ ∑ i, (x i + y i + z i) ^ 2 := this
      _ = _ := by
        simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
        ring_nf
        simp only [Finset.sum_add_distrib]
        ring_nf
  nlinarith [cs x y, cs y z, cs x z]

lemma drho_sum (u : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℝ) (k : Fin n) :
    drho u v k = ∑ j, v j * drho u (ind j) k := by
  have hv : v = ∑ j, v j • ind j := by
    funext m; simp [ind, Finset.sum_apply, smul_eq_mul]
  conv_lhs => rw [hv]
  induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction_on with
  | empty =>
    have : drho u (0 : Fin (n + 1) → ℝ) k = 0 := by
      have := drho_smul u 0 0 k; simpa using this
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, drho_add, drho_smul, ih]

lemma sq2_hvec_le (u : Fin (n + 1) → ℝ) (a : Fin n → ℝ) :
    ∑ j, hvec u a j ^ 2 ≤ 9 * sq2 (fun k => a k - rho u k) := by
  have hlin : ∑ j, hvec u a j ^ 2 = ∑ k, (a k - rho u k) * drho u (fun j => hvec u a j) k := by
    simp only [drho_sum u (fun j => hvec u a j), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hvec, sq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hv1 : sq1 (fun j => hvec u a j) = ∑ j, hvec u a j ^ 2 := rfl
  have hA0 : 0 ≤ ∑ j, hvec u a j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ j, hvec u a j ^ 2) ^ 2 ≤
      sq2 (fun k => a k - rho u k) * sq2 (drho u (fun j => hvec u a j)) := by
    rw [hlin]; exact inner_le_sq2 _ _
  have hd9 := sq2_drho_le_nine u (fun j => hvec u a j)
  rw [hv1] at hd9
  have hw := sq2_nonneg (fun k => a k - rho u k)
  have : (∑ j, hvec u a j ^ 2) ^ 2 ≤ sq2 (fun k => a k - rho u k) * (9 * ∑ j, hvec u a j ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hd9 hw)
  rcases eq_or_lt_of_le hA0 with h | h
  · rw [← h]; positivity
  · nlinarith

lemma sum_ind_succ (f : Fin n → ℝ) (i : Fin n) :
    ∑ k : Fin n, f k * ind i.succ k.succ = f i := by
  simp only [ind, Fin.succ_inj, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]; simp

lemma sum_ind_zero (f : Fin n → ℝ) : ∑ k : Fin n, f k * ind (0 : Fin (n + 1)) k.succ = 0 := by
  simp [ind, (Fin.succ_ne_zero _).symm]

lemma sum_ind (f : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ∑ k, f k * ind j k = f j := by
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]; simp

lemma gu_eq_ind (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (j : Fin (n + 1)) :
    gu u a b j = dpsiU u a b (ind j) := rfl

lemma gu_succ (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (i : Fin n) :
    gu u a b i.succ = -cη * dnu (u i.succ) + (cη + 1) * (rr (u i.succ) * drr (u i.succ)) -
      b i * drr (u i.succ) - hvec u a i.succ := by
  rw [gu_eq_ind]
  simp only [dpsiU, dhpart]
  have h0 : ind i.succ (0 : Fin (n + 1)) = 0 := by simp [ind, Fin.succ_ne_zero]
  have h1 := sum_ind_succ (fun k => dnu (u k.succ)) i
  have h2 := sum_ind (fun j => rr (u j) * drr (u j)) i.succ
  have h3 := sum_ind_succ (fun k => (b k - rb u k) * drr (u k.succ)) i
  rw [h0, show (∑ j : Fin n, dnu (u j.succ) * ind i.succ j.succ) = dnu (u i.succ) from h1,
    show (∑ j, rr (u j) * drr (u j) * ind i.succ j) = rr (u i.succ) * drr (u i.succ) from h2]
  rw [show (∑ k, (b k - rb u k) * (drr (u k.succ) * ind i.succ k.succ)) =
      (b i - rb u i) * drr (u i.succ) by
    rw [← h3]; exact Finset.sum_congr rfl fun k _ => by ring]
  simp only [hvec, rb]
  ring

lemma gu_zero (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) :
    gu u a b 0 = -cη + cη * (rr (u 0) * drr (u 0)) - hvec u a 0 := by
  rw [gu_eq_ind]
  simp only [dpsiU, dhpart]
  have h0 : ind (0 : Fin (n + 1)) (0 : Fin (n + 1)) = 1 := by simp [ind]
  have h1 := sum_ind_zero (fun k => dnu (u k.succ))
  have h2 := sum_ind (fun j => rr (u j) * drr (u j)) 0
  have h3 := sum_ind_zero (fun k => (b k - rb u k) * drr (u k.succ))
  rw [h0, show (∑ j : Fin n, dnu (u j.succ) * ind 0 j.succ) = 0 from h1,
    show (∑ j, rr (u j) * drr (u j) * ind 0 j) = rr (u 0) * drr (u 0) from h2]
  rw [show (∑ k, (b k - rb u k) * (drr (u k.succ) * ind 0 k.succ)) = 0 by
    rw [← h3]; exact Finset.sum_congr rfl fun k _ => by ring]
  simp only [hvec]
  ring

lemma rb_coord_bound (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (i : Fin n) :
    (cη + 1) * |rb u i| ≤ |gu u a b i.succ| + |b i| + |hvec u a i.succ| := by
  rw [gu_succ]
  have hc : (10000 : ℝ) = cη := by norm_num [cη]
  set t := u i.succ
  set G := gu u a b i.succ
  set h := hvec u a i.succ
  simp only [rb]
  rw [rr_cases t, drr_cases t, dnu_cases t]
  split_ifs with h1 h2
  · rw [abs_of_nonpos h1]
    cases abs_cases (-cη * 0 + (cη + 1) * (t * 1) - b i * 1 - h) <;>
      cases abs_cases (b i) <;> cases abs_cases h <;> nlinarith
  · have hr : 0 ≤ t * (1 - t) := by nlinarith
    rw [abs_of_nonneg hr]
    have hγ : cη + 1 ≤ 6 * cη - (cη + 1) * (1 - 2 * t) := by rw [← hc]; nlinarith
    have e : -cη * (6 * (t * (1 - t))) + (cη + 1) * (t * (1 - t) * (1 - 2 * t)) -
        b i * (1 - 2 * t) - h = -(t * (1 - t)) * (6 * cη - (cη + 1) * (1 - 2 * t)) -
        b i * (1 - 2 * t) - h := by ring
    rw [e]
    have hb : |b i * (1 - 2 * t)| ≤ |b i| := by
      rw [abs_mul]
      have : |1 - 2 * t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (b i)]
    have hmain : t * (1 - t) * (6 * cη - (cη + 1) * (1 - 2 * t)) ≤
        |-(t * (1 - t)) * (6 * cη - (cη + 1) * (1 - 2 * t)) - b i * (1 - 2 * t) - h| +
          |b i| + |h| := by
      have := abs_le.mp (le_refl |-(t * (1 - t)) * (6 * cη - (cη + 1) * (1 - 2 * t)) -
        b i * (1 - 2 * t) - h|)
      cases abs_cases (-(t * (1 - t)) * (6 * cη - (cη + 1) * (1 - 2 * t)) - b i * (1 - 2 * t) - h)
        <;> cases abs_cases (b i * (1 - 2 * t)) <;> cases abs_cases h <;> nlinarith
    nlinarith
  · push Not at h1 h2
    rw [abs_of_nonpos (by linarith : 1 - t ≤ 0)]
    cases abs_cases (-cη * 0 + (cη + 1) * ((1 - t) * -1) - b i * -1 - h) <;>
      cases abs_cases (b i) <;> cases abs_cases h <;> nlinarith

lemma rr_drr_le {t : ℝ} (ht : t < 1) : rr t * drr t ≤ 1 / 4 := by
  rw [rr_cases, drr_cases]
  split_ifs with h1 h2
  · nlinarith
  · have h3 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * t - 1)]
    have h4 : 0 ≤ t * (1 - t) := by nlinarith
    have h5 : 1 - 2 * t ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h5 h4]
  · linarith

lemma sq2_sub_le (x y : Fin n → ℝ) : sq2 (fun i => x i - y i) ≤ 2 * sq2 x + 2 * sq2 y := by
  unfold sq2
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (by nlinarith [sq_nonneg (x i + y i)] : (x i - y i) ^ 2 ≤ 2 * x i ^ 2 + 2 * y i ^ 2))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  exact this

lemma sq2_a_sub_rho_le (u : Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : sq2 a ≤ Rab ^ 2) :
    sq2 (fun k => a k - rho u k) ≤ 10 := by
  have h := sq2_sub_le a (rho u)
  have h1 := sq2_rho_le_one u
  have : Rab ^ 2 = 4 := by norm_num [Rab]
  linarith

lemma hvec_sq_le (u : Fin (n + 1) → ℝ) (a : Fin n → ℝ) (ha : sq2 a ≤ Rab ^ 2) (j : Fin (n + 1)) :
    hvec u a j ^ 2 ≤ 90 := by
  have h := sq2_hvec_le u a
  have h1 : hvec u a j ^ 2 ≤ ∑ k, hvec u a k ^ 2 :=
    Finset.single_le_sum (f := fun k => hvec u a k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  linarith [sq2_a_sub_rho_le u a ha]

lemma sqrt_ten_le : Real.sqrt 10 ≤ 10 / 3 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma rb_small (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (hg : sq1 (gu u a b) < cδ ^ 2)
    (ha : sq2 a ≤ Rab ^ 2) (hb : sq2 b ≤ Rab ^ 2) : Real.sqrt (sq2 (rb u)) ≤ κ := by
  have htri := l2_triangle3 (fun i => (cη + 1) * rb u i) (fun i => |gu u a b i.succ|)
    (fun i => |b i|) (fun i => |hvec u a i.succ|) (fun i => by
      rw [abs_mul, abs_of_pos (by norm_num [cη] : (0 : ℝ) < cη + 1)]
      exact rb_coord_bound u a b i)
  have hcη : (0 : ℝ) < cη + 1 := by norm_num [cη]
  have e1 : sq2 (fun i => (cη + 1) * rb u i) = (cη + 1) ^ 2 * sq2 (rb u) := by
    simp only [sq2, mul_pow, Finset.mul_sum]
  rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_sq hcη.le] at htri
  have hx : Real.sqrt (sq2 fun i => |gu u a b i.succ|) ≤ cδ := by
    rw [Real.sqrt_le_left (by norm_num [cδ])]
    have : sq2 (fun i => |gu u a b i.succ|) ≤ sq1 (gu u a b) := by
      simp only [sq2, sq_abs]; exact sum_succ_le _
    linarith
  have hy : Real.sqrt (sq2 fun i => |b i|) ≤ Rab := by
    rw [Real.sqrt_le_left (by norm_num [Rab])]
    simpa [sq2, sq_abs] using hb
  have hz : Real.sqrt (sq2 fun i => |hvec u a i.succ|) ≤ 10 := by
    have h1 := sq2_hvec_le u a
    rw [Fin.sum_univ_succ] at h1
    have h2 : sq2 (fun i => |hvec u a i.succ|) ≤ 9 * 10 := by
      simp only [sq2, sq_abs]
      have := sq2_a_sub_rho_le u a ha
      nlinarith [sq_nonneg (hvec u a 0)]
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  rw [κ, le_div_iff₀ hcη]
  nlinarith

lemma nu_ge_of_high {t : ℝ} (ht : 1 - 2 * κ ≤ t) : 1 - 2 * κ ≤ nu t := by
  have hk := κ_small; have hk0 := κ_pos
  simp only [nu]
  split_ifs with h1 h2
  · nlinarith
  · nlinarith [mul_nonneg (sq_nonneg (1 - t)) (by linarith : (0 : ℝ) ≤ 1 + 2 * t)]
  · linarith

lemma nu_le_of_low {t : ℝ} (ht : |t| ≤ 2 * κ) : nu t ≤ 2 * κ := by
  have hk := κ_small; have hk0 := κ_pos
  have h1 := abs_le.mp ht
  simp only [nu]
  split_ifs with h2 h3
  · linarith
  · nlinarith [sq_nonneg t]
  · linarith

lemma low_or_high {t : ℝ} (h : |rr t| ≤ κ) : |t| ≤ 2 * κ ∨ 1 - 2 * κ ≤ t := by
  have hk0 := κ_pos
  rw [rr_cases] at h
  split_ifs at h with h1 h2
  · left; linarith
  · rw [abs_of_nonneg (by nlinarith)] at h
    by_cases h3 : t ≤ 1 / 2
    · left; rw [abs_of_pos (lt_of_not_ge h1)]; nlinarith
    · right; push Not at h3; nlinarith
  · right; linarith

lemma rb_le_of_sqrt (u : Fin (n + 1) → ℝ) (h : Real.sqrt (sq2 (rb u)) ≤ κ) (i : Fin n) :
    |rb u i| ≤ κ := by
  have h1 : rb u i ^ 2 ≤ sq2 (rb u) :=
    Finset.single_le_sum (f := fun j => rb u j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [← Real.sqrt_sq_eq_abs]
  exact (Real.sqrt_le_sqrt h1).trans h

lemma first_high (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (hg : sq1 (gu u a b) < cδ ^ 2)
    (ha : sq2 a ≤ Rab ^ 2) : 1 - 2 * κ ≤ u 0 := by
  by_contra hcon
  push Not at hcon
  have hk := κ_small; have hk0 := κ_pos
  have h1 : rr (u 0) * drr (u 0) ≤ 1 / 4 := rr_drr_le (by linarith)
  have h2 := hvec_sq_le u a ha 0
  have h3 : hvec u a 0 ≥ -10 := by nlinarith [sq_nonneg (hvec u a 0 + 10)]
  have hg0 : gu u a b 0 < -cδ := by
    rw [gu_zero]; norm_num [cη, cδ] at h1 ⊢; nlinarith
  have hsq : gu u a b 0 ^ 2 ≤ sq1 (gu u a b) :=
    Finset.single_le_sum (f := fun j => gu u a b j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ 0)
  have : cδ ^ 2 < gu u a b 0 ^ 2 := by
    have hc : (0 : ℝ) < cδ := by norm_num [cδ]
    nlinarith
  linarith

lemma rr_drr_le_dnu {t : ℝ} (ht : |t| ≤ 2 * κ) : rr t * drr t ≤ dnu t := by
  have hk := κ_small; have hk0 := κ_pos
  have h1 := abs_le.mp ht
  rw [rr_cases, drr_cases, dnu_cases]
  split_ifs with h2 h3
  · nlinarith
  · have h4 : 0 ≤ t * (1 - t) := by nlinarith
    have h5 : 1 - 2 * t ≤ 6 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h5 h4]
  · linarith

lemma dnu_low_le {t : ℝ} (ht : |t| ≤ 2 * κ) (hr : |rr t| ≤ κ) : dnu t ≤ 6 * κ := by
  have hk := κ_small; have hk0 := κ_pos
  have h1 := abs_le.mp ht
  by_cases h0 : t ≤ 0
  · rw [dnu_of_nonpos h0]; linarith
  · push Not at h0
    rw [dnu_eq_six_rr h0 (by linarith)]
    have := le_abs_self (rr t)
    linarith

lemma cs_bound (f g : Fin n → ℝ) : |∑ i, f i * g i| ≤ Real.sqrt (sq2 f) * Real.sqrt (sq2 g) := by
  rw [← Real.sqrt_mul (sq2_nonneg f), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (inner_le_sq2 f g)

lemma cs_bound1 (f g : Fin (n + 1) → ℝ) :
    |∑ i, f i * g i| ≤ Real.sqrt (sq1 f) * Real.sqrt (sq1 g) := by
  rw [← Real.sqrt_mul (sq1_nonneg f), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

open Classical in
noncomputable def tset (u : Fin (n + 1) → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 1 - 2 * κ ≤ u i.castSucc ∧ |u i.succ| ≤ 2 * κ)

lemma mem_tset {u : Fin (n + 1) → ℝ} {i : Fin n} :
    i ∈ tset u ↔ 1 - 2 * κ ≤ u i.castSucc ∧ |u i.succ| ≤ 2 * κ := by
  classical
  simp [tset]

lemma tset_nonempty (u : Fin (n + 1) → ℝ) (h0 : 1 - 2 * κ ≤ u 0)
    (hlast : ¬ (1 - 2 * κ ≤ u (Fin.last n)))
    (hcls : ∀ i : Fin n, |u i.succ| ≤ 2 * κ ∨ 1 - 2 * κ ≤ u i.succ) : (tset u).Nonempty := by
  classical
  have hne : (Finset.univ.filter (fun j : Fin (n + 1) => ¬ (1 - 2 * κ ≤ u j))).Nonempty :=
    ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlast⟩⟩
  obtain ⟨j0, hj0, hmin⟩ : ∃ j0, j0 ∈ Finset.univ.filter (fun j : Fin (n + 1) => ¬ (1 - 2 * κ ≤ u j)) ∧
      ∀ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => ¬ (1 - 2 * κ ≤ u j)), j0 ≤ j :=
    ⟨_, Finset.min'_mem _ hne, fun j hj => Finset.min'_le _ j hj⟩
  have hj0' : ¬ (1 - 2 * κ ≤ u j0) := (Finset.mem_filter.mp hj0).2
  have hj00 : j0 ≠ 0 := by intro h; rw [h] at hj0'; exact hj0' h0
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hj00
  refine ⟨i, mem_tset.mpr ⟨?_, ?_⟩⟩
  · by_contra hc
    have hmem : i.castSucc ∈ Finset.univ.filter (fun j : Fin (n + 1) => ¬ (1 - 2 * κ ≤ u j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    have hle := hmin _ hmem
    rw [← hi] at hle
    have : i.succ.val ≤ i.castSucc.val := hle
    simp at this
  · rw [hi]
    rcases hcls i with h | h
    · rw [hi] at h; exact h
    · rw [hi] at h; exact absurd h hj0'

lemma q_tset {u : Fin (n + 1) → ℝ} {i : Fin n} (hi : i ∈ tset u) : 1 - 4 * κ ≤ q u i := by
  have hk := κ_small; have hk0 := κ_pos
  have h1 := nu_ge_of_high (mem_tset.mp hi).1
  have h2 := nu_le_of_low (mem_tset.mp hi).2
  unfold q; nlinarith

noncomputable def fcs (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ := if j = 0 then 0 else rr (u j) ^ 2

lemma fcs_nonneg (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : 0 ≤ fcs u j := by
  unfold fcs; split_ifs <;> positivity

lemma q_not_tset {u : Fin (n + 1) → ℝ} (h0 : 1 - 2 * κ ≤ u 0)
    (hcls : ∀ i : Fin n, |u i.succ| ≤ 2 * κ ∨ 1 - 2 * κ ≤ u i.succ) {i : Fin n} (hi : i ∉ tset u) :
    q u i ^ 2 ≤ 4 * rb u i ^ 2 + 4 * fcs u i.castSucc := by
  have hk := κ_small; have hk0 := κ_pos
  have hq0 := q_nonneg u i
  have hfnn := fcs_nonneg u i.castSucc
  by_cases hhigh : 1 - 2 * κ ≤ u i.succ
  · have h1 := one_sub_nu_le hk0.le (by linarith) hhigh
    have h2 := nu_le_one (u i.castSucc)
    have h3 := nu_nonneg (u i.castSucc)
    have h4 := abs_nonneg (rr (u i.succ))
    have h5 := nu_le_one (u i.succ)
    have hq : q u i ≤ 2 * |rb u i| := by
      have hm := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ 1 - nu (u i.succ))
      calc q u i = nu (u i.castSucc) * (1 - nu (u i.succ)) := rfl
        _ ≤ 1 * (1 - nu (u i.succ)) := hm
        _ = 1 - nu (u i.succ) := one_mul _
        _ ≤ 2 * |rr (u i.succ)| := h1
        _ = 2 * |rb u i| := rfl
    have := pow_le_pow_left₀ hq0 hq 2
    rw [mul_pow, sq_abs] at this
    linarith
  · have hlow := (hcls i).resolve_right hhigh
    have hnot : ¬ (1 - 2 * κ ≤ u i.castSucc) := fun h => hi (mem_tset.mpr ⟨h, hlow⟩)
    have hne : i.castSucc ≠ 0 := by intro h; rw [h] at hnot; exact hnot h0
    obtain ⟨k, hk'⟩ := Fin.exists_succ_eq.mpr hne
    have hlowcs : |u i.castSucc| ≤ 2 * κ := by
      rw [← hk']; exact (hcls k).resolve_right (by rw [hk']; exact hnot)
    have h1 := nu_le_two_abs_rr hk0.le (by linarith) (abs_le.mp hlowcs).2
    have h5 := nu_nonneg (u i.succ)
    have h6 := nu_nonneg (u i.castSucc)
    have hq : q u i ≤ 2 * |rr (u i.castSucc)| := by
      unfold q
      have := mul_le_mul_of_nonneg_left (by linarith : 1 - nu (u i.succ) ≤ 1) h6
      nlinarith
    have := pow_le_pow_left₀ hq0 hq 2
    rw [mul_pow, sq_abs] at this
    have hfe : fcs u i.castSucc = rr (u i.castSucc) ^ 2 := by simp [fcs, hne]
    nlinarith [sq_nonneg (rb u i)]

lemma sum_fcs_le (u : Fin (n + 1) → ℝ) : ∑ i : Fin n, fcs u i.castSucc ≤ sq2 (rb u) := by
  have e1 : ∑ j, fcs u j = ∑ i : Fin n, fcs u i.castSucc + fcs u (Fin.last n) :=
    Fin.sum_univ_castSucc (fcs u)
  have e2 : ∑ j, fcs u j = fcs u 0 + ∑ i : Fin n, fcs u i.succ := Fin.sum_univ_succ (fcs u)
  have hl := fcs_nonneg u (Fin.last n)
  have hf0 : fcs u 0 = 0 := by simp [fcs]
  have hs : ∑ i : Fin n, fcs u i.succ = sq2 (rb u) := by
    unfold sq2 rb; exact Finset.sum_congr rfl fun i _ => by simp [fcs, Fin.succ_ne_zero]
  linarith

noncomputable def bconst : ℝ := (1 - 4 * κ) ^ 2 / (1 + (1 - 4 * κ) ^ 2 + 8 * κ ^ 2)

lemma ptset_lower (u : Fin (n + 1) → ℝ) (hrb : sq2 (rb u) ≤ κ ^ 2) (h0 : 1 - 2 * κ ≤ u 0)
    (hcls : ∀ i : Fin n, |u i.succ| ≤ 2 * κ ∨ 1 - 2 * κ ≤ u i.succ) (hne : (tset u).Nonempty) :
    bconst ≤ ∑ i ∈ tset u, rho u i ^ 2 := by
  classical
  have hk := κ_small; have hk0 := κ_pos
  obtain ⟨i0, hi0⟩ := hne
  have hXY : sq2 (q u) = ∑ i ∈ tset u, q u i ^ 2 + ∑ i ∈ Finset.univ.filter (fun i => i ∉ tset u), q u i ^ 2 := by
    unfold sq2
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ tset u)]
    simp
  have hY : ∑ i ∈ Finset.univ.filter (fun i => i ∉ tset u), q u i ^ 2 ≤ 8 * κ ^ 2 := by
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ tset u), q u i ^ 2 ≤
        ∑ i ∈ Finset.univ.filter (fun i => i ∉ tset u), (4 * rb u i ^ 2 + 4 * fcs u i.castSucc) :=
      Finset.sum_le_sum fun i hi => q_not_tset h0 hcls (Finset.mem_filter.mp hi).2
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ tset u), (4 * rb u i ^ 2 + 4 * fcs u i.castSucc) ≤
        ∑ i, (4 * rb u i ^ 2 + 4 * fcs u i.castSucc) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => by
        have := fcs_nonneg u i.castSucc; positivity
    have h3 : ∑ i, (4 * rb u i ^ 2 + 4 * fcs u i.castSucc) =
        4 * sq2 (rb u) + 4 * ∑ i : Fin n, fcs u i.castSucc := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
    linarith [sum_fcs_le u]
  have hX : (1 - 4 * κ) ^ 2 ≤ ∑ i ∈ tset u, q u i ^ 2 := by
    have h1 := Finset.single_le_sum (f := fun i => q u i ^ 2) (fun _ _ => sq_nonneg _) hi0
    have h3 : (1 - 4 * κ) ^ 2 ≤ q u i0 ^ 2 := pow_le_pow_left₀ (by linarith) (q_tset hi0) 2
    exact h3.trans h1
  have hP : ∑ i ∈ tset u, rho u i ^ 2 = (∑ i ∈ tset u, q u i ^ 2) / (1 + sq2 (q u)) := by
    simp only [rho, div_pow, nrm_sq, ← Finset.sum_div]
  rw [hP, hXY, bconst]
  have hY0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => i ∉ tset u), q u i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ (1 - 4 * κ) ^ 2)]

noncomputable def tdir (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 0 (fun i => if i ∈ tset u then rho u i else 0)

lemma tdir_zero (u : Fin (n + 1) → ℝ) : tdir u 0 = 0 := rfl

lemma tdir_succ (u : Fin (n + 1) → ℝ) (i : Fin n) :
    tdir u i.succ = if i ∈ tset u then rho u i else 0 := rfl

lemma sq1_tdir (u : Fin (n + 1) → ℝ) : sq1 (tdir u) = ∑ i ∈ tset u, rho u i ^ 2 := by
  classical
  unfold sq1; rw [Fin.sum_univ_succ, tdir_zero]
  simp only [tdir_succ, ite_pow]
  rw [Finset.sum_ite]; simp

lemma dhpart_tdir (u : Fin (n + 1) → ℝ) : dhpart u (tdir u) ≤ 0 := by
  unfold dhpart
  rw [Fin.sum_univ_succ (fun j => rr (u j) * drr (u j) * tdir u j), tdir_zero]
  have hterm (k : Fin n) : -dnu (u k.succ) * tdir u k.succ +
      rr (u k.succ) * drr (u k.succ) * tdir u k.succ ≤ 0 := by
    rw [tdir_succ]
    split_ifs with hkJ
    · have := rr_drr_le_dnu (mem_tset.mp hkJ).2
      have hr := rho_nonneg u k
      nlinarith [mul_le_mul_of_nonneg_right this hr]
    · simp
  have hs := Finset.sum_nonpos (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [Finset.sum_add_distrib] at hs
  have hc : (0 : ℝ) ≤ cη := by norm_num [cη]
  have e : -cη * 0 - cη * ∑ j : Fin n, dnu (u j.succ) * tdir u j.succ +
      cη * (rr (u 0) * drr (u 0) * 0 + ∑ i : Fin n, rr (u i.succ) * drr (u i.succ) * tdir u i.succ) =
      cη * (∑ k : Fin n, -dnu (u k.succ) * tdir u k.succ +
        ∑ k : Fin n, rr (u k.succ) * drr (u k.succ) * tdir u k.succ) := by
    simp only [neg_mul, Finset.sum_neg_distrib]; ring
  rw [e]
  exact mul_nonpos_of_nonneg_of_nonpos hc hs

lemma dq_tdir (u : Fin (n + 1) → ℝ) (hrbi : ∀ i, |rb u i| ≤ κ) :
    sq2 (dq u (tdir u)) ≤ 144 * κ ^ 2 * sq1 (tdir u) := by
  have hj (j : Fin (n + 1)) : |dnu (u j) * tdir u j| ≤ 6 * κ * |tdir u j| := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [tdir_zero]
    · rw [tdir_succ]
      split_ifs with hiJ
      · rw [abs_mul, abs_of_nonneg (dnu_nonneg _)]
        exact mul_le_mul_of_nonneg_right (dnu_low_le (mem_tset.mp hiJ).2 (hrbi i)) (abs_nonneg _)
      · simp
  have hpt (k : Fin n) : dq u (tdir u) k ^ 2 ≤
      72 * κ ^ 2 * (tdir u k.castSucc ^ 2 + tdir u k.succ ^ 2) := by
    have h1 := hj k.castSucc
    have h2 := hj k.succ
    have hn1 := nu_nonneg (u k.succ); have hn2 := nu_le_one (u k.succ)
    have hn3 := nu_nonneg (u k.castSucc); have hn4 := nu_le_one (u k.castSucc)
    have hb : |dq u (tdir u) k| ≤ 6 * κ * |tdir u k.castSucc| + 6 * κ * |tdir u k.succ| := by
      unfold dq
      have e1 : |dnu (u k.castSucc) * tdir u k.castSucc * (1 - nu (u k.succ))| ≤
          |dnu (u k.castSucc) * tdir u k.castSucc| := by
        rw [abs_mul (dnu (u k.castSucc) * tdir u k.castSucc),
          abs_of_nonneg (by linarith : 0 ≤ 1 - nu (u k.succ))]
        have := abs_nonneg (dnu (u k.castSucc) * tdir u k.castSucc)
        nlinarith
      have e2 : |nu (u k.castSucc) * (dnu (u k.succ) * tdir u k.succ)| ≤
          |dnu (u k.succ) * tdir u k.succ| := by
        rw [abs_mul, abs_of_nonneg hn3]
        have := abs_nonneg (dnu (u k.succ) * tdir u k.succ)
        nlinarith
      linarith [abs_sub (dnu (u k.castSucc) * tdir u k.castSucc * (1 - nu (u k.succ)))
        (nu (u k.castSucc) * (dnu (u k.succ) * tdir u k.succ))]
    have hsq : dq u (tdir u) k ^ 2 ≤ (6 * κ * |tdir u k.castSucc| + 6 * κ * |tdir u k.succ|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    nlinarith [sq_abs (tdir u k.castSucc), sq_abs (tdir u k.succ),
      sq_nonneg (|tdir u k.castSucc| - |tdir u k.succ|)]
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  unfold sq2
  nlinarith [sum_castSucc_le (tdir u), sum_succ_le (tdir u), sq_nonneg κ]

lemma bterm_tdir (u : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (hrb : Real.sqrt (sq2 (rb u)) ≤ κ)
    (heb : Real.sqrt (sq2 (fun i => b i - bstar u i)) ≤ cδ / 2) :
    -∑ i, (b i - rb u i) * (drr (u i.succ) * tdir u i.succ) ≤
      -(1 - 4 * κ) / 13 * (∑ i ∈ tset u, rho u i ^ 2) + 7 / 13 * κ + cδ / 2 := by
  classical
  have hk0 := κ_pos
  have hc0 : (0 : ℝ) < cδ := by norm_num [cδ]
  set w : Fin n → ℝ := fun i => if i ∈ tset u then rho u i else 0 with hw
  have hw2 : sq2 w = ∑ i ∈ tset u, rho u i ^ 2 := by
    simp only [sq2, hw, ite_pow]; rw [Finset.sum_ite]; simp
  have hpt (i : Fin n) : -((b i - rb u i) * (drr (u i.succ) * tdir u i.succ)) ≤
      -(1 - 4 * κ) / 13 * w i ^ 2 + 7 / 13 * (|rb u i| * w i) + |b i - bstar u i| * w i := by
    rw [tdir_succ]
    simp only [hw]
    split_ifs with hiJ
    · have hdr1 := drr_ge hk0.le (abs_le.mp (mem_tset.mp hiJ).2).2
      have hdr2 := (abs_le.mp (drr_abs (u i.succ))).2
      have hdr0 : 0 ≤ drr (u i.succ) := by linarith [κ_small]
      have hr0 := rho_nonneg u i
      have e : b i - rb u i = 1 / 13 * rho u i - 7 / 13 * rb u i + (b i - bstar u i) := by
        simp only [bstar]; ring
      rw [e]
      have hp : 0 ≤ drr (u i.succ) * rho u i := mul_nonneg hdr0 hr0
      have hp1 : drr (u i.succ) * rho u i ≤ rho u i := by nlinarith
      have t1 : -(1 / 13 * rho u i * (drr (u i.succ) * rho u i)) ≤ -(1 - 4 * κ) / 13 * rho u i ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hdr1 (mul_nonneg hr0 hr0)]
      have t2 : 7 / 13 * rb u i * (drr (u i.succ) * rho u i) ≤ 7 / 13 * (|rb u i| * rho u i) := by
        have h1 := mul_le_mul_of_nonneg_right (le_abs_self (rb u i)) hp
        have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg (rb u i))
        nlinarith
      have t3 : -((b i - bstar u i) * (drr (u i.succ) * rho u i)) ≤ |b i - bstar u i| * rho u i := by
        have h1 := mul_le_mul_of_nonneg_right (neg_abs_le (b i - bstar u i)) hp
        have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg (b i - bstar u i))
        nlinarith
      nlinarith
    · simp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hs
  have hs1 : ∑ i, w i ^ 2 = ∑ i ∈ tset u, rho u i ^ 2 := hw2
  have hc1 := cs_bound (fun i => |rb u i|) w
  have hc2 := cs_bound (fun i => |b i - bstar u i|) w
  have e1 : sq2 (fun i => |rb u i|) = sq2 (rb u) := by simp [sq2, sq_abs]
  have e2 : sq2 (fun i => |b i - bstar u i|) = sq2 (fun i => b i - bstar u i) := by simp [sq2, sq_abs]
  rw [e1] at hc1; rw [e2] at hc2
  have hP1 : ∑ i ∈ tset u, rho u i ^ 2 ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _).trans
      (sq2_rho_le_one u)
  have hwP : Real.sqrt (sq2 w) ≤ 1 := by rw [hw2, Real.sqrt_le_left (by norm_num)]; linarith
  have i1 : ∑ i, |rb u i| * w i ≤ κ := by
    have := (le_abs_self _).trans hc1
    nlinarith [Real.sqrt_nonneg (sq2 (rb u)), Real.sqrt_nonneg (sq2 w),
      mul_le_mul hrb hwP (Real.sqrt_nonneg _) hk0.le]
  have i2 : ∑ i, |b i - bstar u i| * w i ≤ cδ / 2 := by
    have := (le_abs_self _).trans hc2
    nlinarith [Real.sqrt_nonneg (sq2 fun i => b i - bstar u i), Real.sqrt_nonneg (sq2 w),
      mul_le_mul heb hwP (Real.sqrt_nonneg _) (by positivity)]
  rw [hs1] at hs
  linarith

lemma a_sub_rho_bound (u : Fin (n + 1) → ℝ) (a : Fin n → ℝ) (hrb : Real.sqrt (sq2 (rb u)) ≤ κ)
    (hea : Real.sqrt (sq2 (fun i => a i - astar u i)) ≤ cδ / 2) :
    Real.sqrt (sq2 fun i => a i - rho u i) ≤ 17 / 26 + κ / 13 + cδ / 2 := by
  have h := l2_triangle3 (fun i => a i - rho u i) (fun i => 17 / 26 * |rho u i|)
    (fun i => 1 / 13 * |rb u i|) (fun i => |a i - astar u i|) (fun i => by
      have e : a i - rho u i = -(17 / 26) * rho u i + 1 / 13 * rb u i + (a i - astar u i) := by
        simp only [astar]; ring
      rw [e]
      calc _ ≤ |-(17 / 26) * rho u i| + |1 / 13 * rb u i| + |a i - astar u i| := abs_add_three _ _ _
        _ = _ := by rw [abs_mul, abs_mul]; norm_num)
  have e1 : sq2 (fun i => 17 / 26 * |rho u i|) = (17 / 26) ^ 2 * sq2 (rho u) := by
    simp only [sq2, mul_pow, sq_abs, Finset.mul_sum]
  have e2 : sq2 (fun i => 1 / 13 * |rb u i|) = (1 / 13) ^ 2 * sq2 (rb u) := by
    simp only [sq2, mul_pow, sq_abs, Finset.mul_sum]
  have e3 : sq2 (fun i => |a i - astar u i|) = sq2 (fun i => a i - astar u i) := by
    simp only [sq2, sq_abs]
  rw [e1, e2, e3, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)] at h
  have hr1 : Real.sqrt (sq2 (rho u)) ≤ 1 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [sq2_rho_le_one u]
  nlinarith [Real.sqrt_nonneg (sq2 (rho u)), Real.sqrt_nonneg (sq2 (rb u))]

lemma final_numeric (P : ℝ) (hP : bconst ≤ P) :
    (17 / 26 + κ / 13 + cδ / 2) * (12 * κ) - (1 - 4 * κ) / 13 * P + 7 / 13 * κ + cδ / 2 < -cδ := by
  rw [bconst, κ_eq] at hP
  rw [κ_eq]
  norm_num [cδ] at hP ⊢
  nlinarith

theorem part_two (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (hg : sq1 (gu u a b) < cδ ^ 2)
    (ha : sq2 a ≤ Rab ^ 2) (hb : sq2 b ≤ Rab ^ 2)
    (hd : sq2 (fun i => a i - astar u i) + sq2 (fun i => b i - bstar u i) ≤ (cδ / 2) ^ 2)
    (hT : u (Fin.last n) ≤ 1 / 4) : False := by
  have hk := κ_small
  have hk0 := κ_pos
  have hc0 : (0 : ℝ) < cδ := by norm_num [cδ]
  have hrb := rb_small u a b hg ha hb
  have hrbi := rb_le_of_sqrt u hrb
  have hrb2 : sq2 (rb u) ≤ κ ^ 2 := by
    have := Real.sq_sqrt (sq2_nonneg (rb u))
    nlinarith [Real.sqrt_nonneg (sq2 (rb u))]
  have h0 := first_high u a b hg ha
  have hcls (i : Fin n) : |u i.succ| ≤ 2 * κ ∨ 1 - 2 * κ ≤ u i.succ := low_or_high (hrbi i)
  have hlast : ¬ (1 - 2 * κ ≤ u (Fin.last n)) := by intro h; linarith
  have hne := tset_nonempty u h0 hlast hcls
  have hPB := ptset_lower u hrb2 h0 hcls hne
  have hea : Real.sqrt (sq2 (fun i => a i - astar u i)) ≤ cδ / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; linarith [sq2_nonneg (fun i => b i - bstar u i)]
  have heb : Real.sqrt (sq2 (fun i => b i - bstar u i)) ≤ cδ / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; linarith [sq2_nonneg (fun i => a i - astar u i)]
  have hA := a_sub_rho_bound u a hrb hea
  have hP1 : ∑ i ∈ tset u, rho u i ^ 2 ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _).trans
      (sq2_rho_le_one u)
  have hv1 := sq1_tdir u
  have hlow : -cδ < dpsiU u a b (tdir u) := by
    rw [dpsiU_eq_sum]
    have h := cs_bound1 (tdir u) (gu u a b)
    have hs1 : Real.sqrt (sq1 (tdir u)) ≤ 1 := by
      rw [hv1, Real.sqrt_le_left (by norm_num)]; linarith
    have hs2 : Real.sqrt (sq1 (gu u a b)) < cδ := by
      rw [Real.sqrt_lt' hc0]; exact hg
    have h3 : Real.sqrt (sq1 (tdir u)) * Real.sqrt (sq1 (gu u a b)) < cδ := by
      calc _ ≤ 1 * Real.sqrt (sq1 (gu u a b)) :=
            mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg _)
        _ < cδ := by linarith
    have := neg_abs_le (∑ j, tdir u j * gu u a b j)
    linarith
  have hH := dhpart_tdir u
  have hdq := dq_tdir u hrbi
  have hrho : -∑ i, (a i - rho u i) * drho u (tdir u) i ≤ (17 / 26 + κ / 13 + cδ / 2) * (12 * κ) := by
    have h1 := cs_bound (fun i => a i - rho u i) (drho u (tdir u))
    have h2 : Real.sqrt (sq2 (drho u (tdir u))) ≤ 12 * κ := by
      rw [Real.sqrt_le_left (by positivity)]
      have := (sq2_drho_le u (tdir u)).trans hdq
      nlinarith
    have h3 := neg_le_abs (∑ i, (a i - rho u i) * drho u (tdir u) i)
    have h4 := mul_le_mul hA h2 (Real.sqrt_nonneg _) (by positivity)
    linarith
  have hbt := bterm_tdir u b hrb heb
  have hup : dpsiU u a b (tdir u) ≤ (17 / 26 + κ / 13 + cδ / 2) * (12 * κ) -
      (1 - 4 * κ) / 13 * (∑ i ∈ tset u, rho u i ^ 2) + 7 / 13 * κ + cδ / 2 := by
    have : dpsiU u a b (tdir u) = dhpart u (tdir u) - ∑ i, (a i - rho u i) * drho u (tdir u) i -
        ∑ i, (b i - rb u i) * (drr (u i.succ) * tdir u i.succ) := rfl
    linarith
  have hfin := final_numeric _ hPB
  linarith

end LongTails.Proofs.NcConcavePartTwo
