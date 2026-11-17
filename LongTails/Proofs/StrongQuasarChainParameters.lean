import LongTails.Proofs.StrongQuasarChainAveraging
import LongTails.Setups.HighDimensionalStrongQuasar
import Mathlib.Algebra.Order.Floor.Semifield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset

namespace LongTails.Proofs.StrongQuasarChainParameters

open LongTails.Proofs.StrongQuasarChainObjective LongTails.Proofs.StrongQuasarChainHard
open LongTails.Proofs.StrongQuasarChainAveraging LongTails.Setups.HighDimensionalStrongQuasar

noncomputable def rootKappa (p : Params) : ℝ := Real.sqrt (p.L / p.μ)

noncomputable def muN (p : Params) : ℝ := 8704 * p.μ / p.L

noncomputable def mOf (p : Params) : ℕ := ⌊rootKappa p / (4000 * p.γ)⌋₊

noncomputable def hOf (p : Params) : ℕ := ⌊rootKappa p / (8000 * p.γ)⌋₊

noncomputable def ratio (p : Params) : ℝ := p.Δ / (1000 * p.γ * rootKappa p * p.ε)

noncomputable def jOf (p : Params) : ℕ := Nat.log 2 ⌊ratio p⌋₊

noncomputable def lowerBudget (p : Params) : ℕ := hOf p * jOf p / 2

noncomputable def qOf (p : Params) : ℝ := 1 - 1 / (mOf p : ℝ)

noncomputable def shape (p : Params) (b : ℕ) : Shape :=
  { k := b + mOf p, m := mOf p, μ := muN p,
    θ := qOf p ^ (b + mOf p) / (4 * mOf p),
    ρ := qOf p ^ (b + mOf p) / (4 * mOf p) / (1 + muN p * mOf p) }

noncomputable def radius (p : Params) : ℝ := 2 * Real.sqrt (mOf p)

section

variable {p : Params} (hp : spec.valid p)
include hp

lemma kappa_ge : 870400 ≤ p.L / p.μ := by
  obtain ⟨-, hμ, -, -, -, h1, -⟩ := id hp
  rw [le_div_iff₀ hμ]; linarith

lemma rootKappa_ge : 932 ≤ rootKappa p := by
  have h := kappa_ge hp
  unfold rootKappa
  rw [show (932 : ℝ) = Real.sqrt (932 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma rootKappa_sq : rootKappa p ^ 2 = p.L / p.μ := by
  obtain ⟨hL, hμ, -⟩ := id hp
  unfold rootKappa
  exact Real.sq_sqrt (by positivity)

lemma gamma_root : 2 ≤ p.γ * rootKappa p := by
  have hs := rootKappa_sq hp
  obtain ⟨-, hμ, hγ, -, -, -, h4, -⟩ := id hp
  have h0 : 0 ≤ rootKappa p := Real.sqrt_nonneg _
  have : 4 ≤ (p.γ * rootKappa p) ^ 2 := by
    rw [mul_pow, hs, ← mul_div_assoc, le_div_iff₀ hμ]; linarith
  nlinarith [mul_nonneg hγ.le h0]

lemma root_over_gamma : 238592 ≤ rootKappa p / p.γ := by
  obtain ⟨-, -, hγ, hγ1, -⟩ := id hp
  have h := rootKappa_ge hp
  rw [le_div_iff₀ hγ]
  nlinarith

lemma mOf_ge : rootKappa p / (4250 * p.γ) ≤ mOf p := by
  obtain ⟨-, -, hγ, -⟩ := id hp
  have h := root_over_gamma hp
  have hf := Nat.lt_floor_add_one (rootKappa p / (4000 * p.γ))
  unfold mOf
  have e1 : rootKappa p / (4000 * p.γ) = (rootKappa p / p.γ) / 4000 := by field_simp
  have e2 : rootKappa p / (4250 * p.γ) = (rootKappa p / p.γ) / 4250 := by field_simp
  rw [e1] at hf
  rw [e1, e2]
  linarith

lemma mOf_le : (mOf p : ℝ) ≤ rootKappa p / (4000 * p.γ) := by
  obtain ⟨-, -, hγ, -⟩ := id hp
  have h0 : 0 ≤ rootKappa p := Real.sqrt_nonneg _
  exact Nat.floor_le (by positivity)

lemma mOf_ge16 : 16 ≤ mOf p := by
  have h := mOf_ge hp
  have h2 := root_over_gamma hp
  obtain ⟨-, -, hγ, -⟩ := id hp
  have : (16 : ℝ) ≤ mOf p := by
    have e : rootKappa p / (4250 * p.γ) = (rootKappa p / p.γ) / 4250 := by field_simp
    rw [e] at h; linarith
  exact_mod_cast this

lemma muN_pos : 0 < muN p := by
  obtain ⟨hL, hμ, -⟩ := id hp
  unfold muN; positivity

lemma muN_le : muN p ≤ 1 / 100 := by
  obtain ⟨hL, -, -, -, -, h1, -⟩ := id hp
  unfold muN
  rw [div_le_iff₀ hL]; linarith

lemma muN_eq : muN p = 8704 / rootKappa p ^ 2 := by
  obtain ⟨hL, hμ, -⟩ := id hp
  rw [rootKappa_sq hp, muN]
  field_simp

lemma sq_constant : (42 * p.γ * (mOf p : ℝ)) ^ 2 * muN p ≤ 1 := by
  have hm := mOf_le hp
  have hr := rootKappa_ge hp
  have hmu := muN_eq hp
  obtain ⟨-, -, hγ, -⟩ := id hp
  have h1 : 42 * p.γ * (mOf p : ℝ) ≤ 42 * rootKappa p / 4000 := by
    have h := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 42 * p.γ)
    have e : 42 * p.γ * (rootKappa p / (4000 * p.γ)) = 42 * rootKappa p / 4000 := by
      field_simp
    linarith
  have h0 : 0 ≤ 42 * p.γ * (mOf p : ℝ) := by positivity
  have h2 : (42 * p.γ * (mOf p : ℝ)) ^ 2 ≤ (42 * rootKappa p / 4000) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have hr2 : 0 < rootKappa p ^ 2 := by positivity
  have e2 : (42 * rootKappa p / 4000) ^ 2 * (8704 / rootKappa p ^ 2) = 42 ^ 2 * 8704 / 4000 ^ 2 := by
    field_simp
  rw [hmu]
  calc (42 * p.γ * (mOf p : ℝ)) ^ 2 * (8704 / rootKappa p ^ 2)
      ≤ (42 * rootKappa p / 4000) ^ 2 * (8704 / rootKappa p ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 42 ^ 2 * 8704 / 4000 ^ 2 := e2
    _ ≤ 1 := by norm_num

lemma muN_m_le : muN p * mOf p ≤ 2 := by
  have hm := mOf_le hp
  have hg := gamma_root hp
  have hr := rootKappa_ge hp
  have hmu := muN_eq hp
  have hγ := hp.2.2.1
  rw [hmu]
  have hr2 : 0 < rootKappa p ^ 2 := by positivity
  have h1 : 8704 / rootKappa p ^ 2 * (mOf p : ℝ) ≤ 8704 / rootKappa p ^ 2 * (rootKappa p / (4000 * p.γ)) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have e : 8704 / rootKappa p ^ 2 * (rootKappa p / (4000 * p.γ)) = 8704 / (4000 * (p.γ * rootKappa p)) := by
    field_simp
  have h2 : 8704 / (4000 * (p.γ * rootKappa p)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma muN_m_ge : 2 / (p.γ * rootKappa p) ≤ muN p * mOf p := by
  have hm := mOf_ge hp
  have hr := rootKappa_ge hp
  have hmu := muN_eq hp
  have hγ := hp.2.2.1
  rw [hmu]
  have hr2 : 0 < rootKappa p ^ 2 := by positivity
  have h1 : 8704 / rootKappa p ^ 2 * (rootKappa p / (4250 * p.γ)) ≤ 8704 / rootKappa p ^ 2 * (mOf p : ℝ) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have e : 8704 / rootKappa p ^ 2 * (rootKappa p / (4250 * p.γ)) = (8704 / 4250) / (p.γ * rootKappa p) := by
    field_simp
  have h2 : 2 / (p.γ * rootKappa p) ≤ (8704 / 4250) / (p.γ * rootKappa p) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

lemma qOf_props : 15 / 16 ≤ qOf p ∧ qOf p < 1 := by
  have hm : (16 : ℝ) ≤ mOf p := by exact_mod_cast mOf_ge16 hp
  unfold qOf
  constructor
  · have : 1 / (mOf p : ℝ) ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hm
    linarith
  · have : 0 < 1 / (mOf p : ℝ) := by positivity
    linarith

lemma hOf_eq : hOf p = mOf p / 2 := by
  have h0 : 0 ≤ rootKappa p / (4000 * p.γ) := by
    have := hp.2.2.1; have := Real.sqrt_nonneg (p.L / p.μ); unfold rootKappa; positivity
  unfold hOf mOf
  rw [← Nat.floor_div_natCast (rootKappa p / (4000 * p.γ)) 2]
  congr 1
  ring

lemma q_pow_h : 1 / 2 ≤ qOf p ^ hOf p := by
  have hm : (16 : ℝ) ≤ mOf p := by exact_mod_cast mOf_ge16 hp
  have hb := one_add_mul_le_pow (a := -(1 / (mOf p : ℝ))) (by
    have : 1 / (mOf p : ℝ) ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hm
    linarith) (hOf p)
  have hh : (2 * hOf p : ℝ) ≤ mOf p := by
    have : 2 * hOf p ≤ mOf p := by rw [hOf_eq hp]; omega
    exact_mod_cast this
  have e : (1 : ℝ) + -(1 / (mOf p : ℝ)) = qOf p := by unfold qOf; ring
  rw [e] at hb
  have h1 : (hOf p : ℝ) * (1 / (mOf p : ℝ)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have e2 : (hOf p : ℝ) * -(1 / (mOf p : ℝ)) = -((hOf p : ℝ) * (1 / (mOf p : ℝ))) := by ring
  linarith

lemma ratio_ge : 1 ≤ ratio p := by
  obtain ⟨hL, hμ, hγ, -, hε, -, -, h8, -⟩ := id hp
  have hr : 0 < rootKappa p := by unfold rootKappa; positivity
  unfold ratio
  rw [le_div_iff₀ (by positivity)]
  unfold rootKappa at hr ⊢
  linarith

lemma two_pow_j : (2 : ℝ) ^ jOf p ≤ ratio p := by
  have h1 := ratio_ge hp
  have hf : 1 ≤ ⌊ratio p⌋₊ := (Nat.one_le_floor_iff _).mpr h1
  have h2 : 2 ^ jOf p ≤ ⌊ratio p⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h3 : ((⌊ratio p⌋₊ : ℕ) : ℝ) ≤ ratio p := Nat.floor_le (by linarith)
  have h4 : ((2 ^ jOf p : ℕ) : ℝ) ≤ ((⌊ratio p⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h4
  linarith

lemma shape_valid (b : ℕ) : (shape p b).Valid := by
  have hm : (16 : ℝ) ≤ mOf p := by exact_mod_cast mOf_ge16 hp
  have hq := qOf_props hp
  have hmu0 := muN_pos hp
  have hmu := muN_le hp
  have hqk : 0 < qOf p ^ (b + mOf p) := pow_pos (by linarith) _
  have hm0 : (0 : ℝ) < mOf p := by linarith
  have h1 : 0 < 1 + muN p * mOf p := by positivity
  refine ⟨mOf_ge16 hp, hmu0, hmu, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < qOf p ^ (b + mOf p) / (4 * mOf p); positivity
  · show 4 * (mOf p : ℝ) * (qOf p ^ (b + mOf p) / (4 * mOf p)) ≤ qOf p ^ (b + mOf p)
    rw [mul_div_cancel₀ _ (by positivity)]
  · show 0 < qOf p ^ (b + mOf p) / (4 * mOf p) / (1 + muN p * mOf p); positivity
  · show qOf p ^ (b + mOf p) / (4 * mOf p) / (1 + muN p * mOf p) ≤ qOf p ^ (b + mOf p) / (4 * mOf p)
    apply div_le_self (by positivity)
    nlinarith
  · show muN p * (mOf p : ℝ) ^ 2 * (qOf p ^ (b + mOf p) / (4 * mOf p) / (1 + muN p * mOf p)) ≤
      qOf p ^ (b + mOf p)
    have e : muN p * (mOf p : ℝ) ^ 2 * (qOf p ^ (b + mOf p) / (4 * mOf p) / (1 + muN p * mOf p)) =
        qOf p ^ (b + mOf p) * (muN p * mOf p / (4 * (1 + muN p * mOf p))) := by
      field_simp
    rw [e]
    have : muN p * mOf p / (4 * (1 + muN p * mOf p)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    nlinarith

lemma scale_sq_sum_le (b : ℕ) :
    ∑ p' : Fin ((shape p b).k + 1), (shape p b).scale p' ^ 2 ≤ mOf p := by
  have hq := qOf_props hp
  have hm : (16 : ℝ) ≤ mOf p := by exact_mod_cast mOf_ge16 hp
  have hq0 : 0 ≤ qOf p ^ 2 := by positivity
  have hq1 : qOf p ^ 2 < 1 := by nlinarith
  have e : ∑ p' : Fin ((shape p b).k + 1), (shape p b).scale p' ^ 2 =
      ∑ i ∈ range ((shape p b).k + 1), (qOf p ^ 2) ^ (i + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (qOf p ^ 2) ^ (i + 1))]
    apply sum_congr rfl
    intro i _
    show (qOf p ^ (i.val + 1)) ^ 2 = (qOf p ^ 2) ^ (i.val + 1)
    rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : ∑ i ∈ range ((shape p b).k + 1), (qOf p ^ 2) ^ (i + 1) =
      ∑ i ∈ Ico 1 ((shape p b).k + 2), (qOf p ^ 2) ^ i := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply sum_congr (by simp)
    intro i _
    rw [add_comm]
  rw [e, e2]
  refine (geom_sum_Ico_le_of_lt_one hq0 hq1).trans ?_
  have h3 : 1 / (mOf p : ℝ) ≤ 1 - qOf p ^ 2 := by
    have : 1 - qOf p = 1 / (mOf p : ℝ) := by unfold qOf; ring
    nlinarith
  have h4 : (1 : ℝ) ≤ (1 - qOf p ^ 2) * mOf p := by
    rw [div_le_iff₀ (by linarith)] at h3; exact h3
  rw [pow_one, div_le_iff₀ (by linarith)]
  nlinarith

lemma radius_pos : 0 < radius p := by
  have : (0 : ℝ) < mOf p := by have := mOf_ge16 hp; exact_mod_cast (by omega : 0 < mOf p)
  unfold radius; positivity

omit hp in
lemma radius_sq : radius p ^ 2 = 4 * mOf p := by
  unfold radius
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

lemma xstar_le (b : ℕ) {d : ℕ} (π : Fin ((shape p b).k + 1) ↪ Fin d) :
    ‖xstar (shape p b) π‖ ≤ radius p / 2 := by
  have h1 := xstar_norm_sq (shape p b) π
  have h2 := scale_sq_sum_le hp b
  have hr := radius_sq (p := p)
  have hR := radius_pos hp
  have h3 : ‖xstar (shape p b) π‖ ^ 2 ≤ (radius p / 2) ^ 2 := by
    rw [h1, div_pow, hr]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h3

lemma tail_upper (b : ℕ) : tailGap (shape p b) b ≤ 14 * radius p ^ 2 := by
  have h2 := scale_sq_sum_le hp b
  have hmu := muN_le hp
  have hmu0 := muN_pos hp
  have hb := StrongQuasarChainScalar.bump_bounds 0
  have hr := radius_sq (p := p)
  have hsub : ∑ q ∈ (univ : Finset (Fin ((shape p b).k + 1))).filter (fun q => b ≤ q.val),
      (shape p b).scale q ^ 2 ≤ ∑ q : Fin ((shape p b).k + 1), (shape p b).scale q ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hs0 : 0 ≤ ∑ q ∈ (univ : Finset (Fin ((shape p b).k + 1))).filter (fun q => b ≤ q.val),
      (shape p b).scale q ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  unfold tailGap
  rw [hr]
  have hbz : StrongQuasarChainScalar.bump 0 ≤ 1 / 2 := by have := hb.2; norm_num at this; linarith
  have hm0 : (0 : ℝ) ≤ mOf p := Nat.cast_nonneg _
  change muN p * StrongQuasarChainScalar.bump 0 / 17 * _ ≤ _
  have : muN p * StrongQuasarChainScalar.bump 0 / 17 ≤ 1 := by
    have := hb.1; nlinarith
  calc muN p * StrongQuasarChainScalar.bump 0 / 17 * _
      ≤ 1 * ∑ q ∈ (univ : Finset (Fin ((shape p b).k + 1))).filter (fun q => b ≤ q.val),
        (shape p b).scale q ^ 2 := mul_le_mul_of_nonneg_right this hs0
    _ ≤ 14 * (4 * mOf p) := by linarith

lemma q_pow_lower (b : ℕ) (hb : b ≤ lowerBudget p) :
    1 / ratio p ≤ qOf p ^ (2 * b) := by
  have hq := qOf_props hp
  have hh := q_pow_h hp
  have hj := two_pow_j hp
  have h2b : 2 * b ≤ hOf p * jOf p := by
    have := Nat.mul_div_le (hOf p * jOf p) 2
    unfold lowerBudget at hb
    omega
  have h1 : qOf p ^ (hOf p * jOf p) ≤ qOf p ^ (2 * b) :=
    pow_le_pow_of_le_one (by linarith) hq.2.le h2b
  have h2 : (1 / 2 : ℝ) ^ jOf p ≤ qOf p ^ (hOf p * jOf p) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) hh _
  have h3 : 1 / ratio p ≤ (1 / 2 : ℝ) ^ jOf p := by
    have hr := ratio_ge hp
    rw [one_div_pow, one_div_le_one_div (by linarith) (by positivity)]
    exact hj
  linarith

lemma q_pow_m : 1 / 21 ≤ qOf p ^ (2 * mOf p + 2) := by
  have hq := qOf_props hp
  have hh := q_pow_h hp
  have hm : 2 * mOf p + 2 ≤ 4 * hOf p + 4 := by rw [hOf_eq hp]; omega
  have h1 : qOf p ^ (4 * hOf p + 4) ≤ qOf p ^ (2 * mOf p + 2) :=
    pow_le_pow_of_le_one (by linarith) hq.2.le hm
  have h2 : qOf p ^ (4 * hOf p + 4) = (qOf p ^ hOf p) ^ 4 * qOf p ^ 4 := by ring
  have h3 : (1 / 2 : ℝ) ^ 4 ≤ (qOf p ^ hOf p) ^ 4 := pow_le_pow_left₀ (by norm_num) hh 4
  have h4 : (15 / 16 : ℝ) ^ 4 ≤ qOf p ^ 4 := pow_le_pow_left₀ (by norm_num) hq.1 4
  have h5 : (1 / 2 : ℝ) ^ 4 * (15 / 16) ^ 4 ≤ (qOf p ^ hOf p) ^ 4 * qOf p ^ 4 :=
    mul_le_mul h3 h4 (by norm_num) (by positivity)
  norm_num at h5
  linarith

lemma filter_sum_ge (b : ℕ) :
    ((mOf p : ℝ) + 1) * qOf p ^ (2 * (b + mOf p + 1)) ≤
      ∑ q ∈ (univ : Finset (Fin ((shape p b).k + 1))).filter (fun q => b ≤ q.val),
        (shape p b).scale q ^ 2 := by
  have hq := qOf_props hp
  let e : Fin (mOf p + 1) ↪ Fin ((shape p b).k + 1) :=
    ⟨fun i => ⟨b + i.val, by have := i.isLt; simp only [shape]; omega⟩,
      fun i j h => by
        simp only [Fin.mk.injEq] at h
        exact Fin.ext (by omega)⟩
  have hsub : (univ.map e) ⊆ (univ : Finset (Fin ((shape p b).k + 1))).filter
      (fun q => b ≤ q.val) := by
    intro q hq'
    simp only [mem_map, mem_univ, true_and] at hq'
    obtain ⟨i, rfl⟩ := hq'
    simp [e]
  have h1 := sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => sq_nonneg ((shape p b).scale q))
  rw [sum_map] at h1
  have h2 : ∀ i : Fin (mOf p + 1), qOf p ^ (2 * (b + mOf p + 1)) ≤ (shape p b).scale (e i) ^ 2 := by
    intro i
    have hi := i.isLt
    change qOf p ^ (2 * (b + mOf p + 1)) ≤ (qOf p ^ (b + i.val + 1)) ^ 2
    rw [← pow_mul]
    apply pow_le_pow_of_le_one (by linarith) hq.2.le
    omega
  have h3 := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (mOf p + 1)))) => h2 i)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  push_cast at h3
  linarith

lemma tail_lower (b : ℕ) (hb : b ≤ lowerBudget p) :
    2 / (933 * (p.γ * rootKappa p) * ratio p) ≤ tailGap (shape p b) b := by
  have hq := qOf_props hp
  have hf := filter_sum_ge hp b
  have hqb := q_pow_lower hp b hb
  have hqm := q_pow_m hp
  have hmm := muN_m_ge hp
  have hmu0 := muN_pos hp
  have hbz := StrongQuasarChainScalar.bump_zero_lower
  have hr := ratio_ge hp
  have hg := gamma_root hp
  have hγ := hp.2.2.1
  have hrk : 0 < rootKappa p := by linarith [rootKappa_ge hp]
  have hm0 : (0 : ℝ) ≤ mOf p := Nat.cast_nonneg _
  have hsplit : qOf p ^ (2 * (b + mOf p + 1)) = qOf p ^ (2 * b) * qOf p ^ (2 * mOf p + 2) := by
    rw [← pow_add]; ring_nf
  have hpow : 1 / (21 * ratio p) ≤ qOf p ^ (2 * (b + mOf p + 1)) := by
    rw [hsplit]
    have : 1 / (21 * ratio p) = (1 / ratio p) * (1 / 21) := by field_simp
    rw [this]
    exact mul_le_mul hqb hqm (by norm_num) (pow_nonneg (by linarith [hq.1]) _)
  have hsum : (mOf p : ℝ) / (21 * ratio p) ≤
      ∑ q ∈ (univ : Finset (Fin ((shape p b).k + 1))).filter (fun q => b ≤ q.val),
        (shape p b).scale q ^ 2 := by
    have : (mOf p : ℝ) / (21 * ratio p) ≤ ((mOf p : ℝ) + 1) * qOf p ^ (2 * (b + mOf p + 1)) := by
      have h1 : (mOf p : ℝ) / (21 * ratio p) = (mOf p : ℝ) * (1 / (21 * ratio p)) := by ring
      rw [h1]
      exact mul_le_mul (by linarith) hpow (by positivity) (by positivity)
    linarith
  unfold tailGap
  change 2 / (933 * (p.γ * rootKappa p) * ratio p) ≤
    muN p * StrongQuasarChainScalar.bump 0 / 17 * _
  have h1 : muN p * (49 / 128) / 17 * ((mOf p : ℝ) / (21 * ratio p)) ≤
      muN p * StrongQuasarChainScalar.bump 0 / 17 *
        ∑ q ∈ (univ : Finset (Fin ((shape p b).k + 1))).filter (fun q => b ≤ q.val),
          (shape p b).scale q ^ 2 := by
    apply mul_le_mul _ hsum (by positivity) (by positivity)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hbz hmu0.le
  have h2 : 2 / (933 * (p.γ * rootKappa p) * ratio p) ≤
      muN p * (49 / 128) / 17 * ((mOf p : ℝ) / (21 * ratio p)) := by
    have e : muN p * (49 / 128) / 17 * ((mOf p : ℝ) / (21 * ratio p)) =
        (muN p * mOf p) * (49 / 45696) / ratio p := by field_simp; ring
    rw [e]
    have e2 : 2 / (933 * (p.γ * rootKappa p) * ratio p) =
        (2 / (p.γ * rootKappa p)) * (1 / 933) / ratio p := by field_simp
    rw [e2]
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply mul_le_mul hmm (by norm_num) (by norm_num) (by positivity)
  linarith

lemma gamma_root_ratio : p.γ * rootKappa p * ratio p = p.Δ / (1000 * p.ε) := by
  obtain ⟨hL, hμ, hγ, -, hε, -⟩ := id hp
  have hr : 0 < rootKappa p := by unfold rootKappa; positivity
  unfold ratio
  field_simp

lemma starValue_nonneg (b : ℕ) : 0 ≤ starValue (shape p b) := by
  have V := shape_valid hp b
  unfold starValue
  have h1 : 0 ≤ ∑ c ∈ range ((shape p b).k + 1),
      StrongQuasarChainBlock.deadEnergy (shape p b).θ
        ((shape p b).q ^ c - (shape p b).q ^ (c + 1)) :=
    sum_nonneg (fun c _ => by unfold StrongQuasarChainBlock.deadEnergy; positivity)
  have h2 : ∀ q : Fin ((shape p b).k + 1),
      -((shape p b).μ / 2 * (shape p b).scale q ^ 2) ≤ coordProfile (shape p b) q ((shape p b).scale q) := by
    intro q
    unfold coordProfile
    rw [div_self (V.scale_pos q).ne', StrongQuasarChainScalar.bump, intervalIntegral.integral_same]
    have hm := (StrongQuasarChainScalar.dead_model (shape p b).ρ 0 ((shape p b).scale q) V.hρ0.le)
    have hz := StrongQuasarChainScalar.dead_inactive (t := 0) V.hρ0.le (by simpa using V.hρ0.le)
    rw [hz.1, hz.2] at hm
    have hβ := V.beta_ge q
    have hE0 : 0 ≤ StrongQuasarChainBlock.deadEnergy (shape p b).ρ ((shape p b).scale q) := by
      unfold StrongQuasarChainBlock.deadEnergy; positivity
    have hE1 : StrongQuasarChainBlock.deadEnergy (shape p b).ρ ((shape p b).scale q) ≤
        (shape p b).scale q ^ 2 / 2 := by linarith [hm.2]
    nlinarith [mul_le_mul_of_nonneg_right hβ hE0, mul_le_mul_of_nonneg_left hE1 V.hμ0.le]
  have h3 := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Fin ((shape p b).k + 1)))) => h2 q)
  rw [sum_neg_distrib, ← mul_sum] at h3
  linarith

lemma gapZero_le (b : ℕ) : gapZero (shape p b) ≤ 1 / 10 := by
  have V := shape_valid hp b
  have hsv := starValue_nonneg hp b
  have hs := scale_sq_sum_le hp b
  have hmm := muN_m_le hp
  have hmu0 := muN_pos hp
  have hθ := V.hθ0
  unfold gapZero objZero
  have h1 : ∑ c : Fin ((shape p b).k + 1),
      (if c.val = 0 then StrongQuasarChainBlock.deadEnergy (shape p b).θ 1 else 0) ≤ 1 / 2 := by
    rw [Finset.sum_eq_single (0 : Fin ((shape p b).k + 1))]
    · simp only [Fin.val_zero, ↓reduceIte]
      unfold StrongQuasarChainBlock.deadEnergy
      have hθ1 : (shape p b).θ ≤ 1 := by
        have := V.theta_small
        have : (shape p b).q ^ (shape p b).k ≤ 1 := pow_le_one₀ V.q_pos.le V.q_lt_one.le
        linarith
      rw [abs_one, max_eq_left (by linarith)]
      nlinarith
    · intro c _ hc
      have : c.val ≠ 0 := fun h => hc (Fin.ext h)
      simp [this]
    · simp
  have h2 : ∀ q : Fin ((shape p b).k + 1), coordProfile (shape p b) q 0 ≤
      (shape p b).μ / 2 * (shape p b).scale q ^ 2 := by
    intro q
    unfold coordProfile
    have hz := StrongQuasarChainScalar.dead_inactive (t := 0) V.hρ0.le (by simpa using V.hρ0.le)
    rw [hz.1, zero_div]
    have hb := (StrongQuasarChainScalar.bump_bounds 0).2
    norm_num at hb
    have : 0 ≤ (shape p b).μ * (shape p b).scale q ^ 2 := by have := V.hμ0; positivity
    nlinarith
  have h3 := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Fin ((shape p b).k + 1)))) => h2 q)
  rw [← mul_sum] at h3
  have hμm : (shape p b).μ / 2 * ∑ q : Fin ((shape p b).k + 1), (shape p b).scale q ^ 2 ≤ 1 := by
    have : (shape p b).μ = muN p := rfl
    rw [this]
    nlinarith
  rw [div_le_iff₀ (by norm_num)]
  linarith

lemma accuracy (b : ℕ) (hb : b ≤ lowerBudget p) :
    2 * (p.ε / (p.Δ / gapZero (shape p b))) < tailGap (shape p b) b := by
  have ht := tail_lower hp b hb
  have hg := gapZero_le hp b
  have he := gamma_root_ratio hp
  obtain ⟨hL, hμ, hγ, -, hε, -, -, h8, -⟩ := id hp
  have hΔ : 0 < p.Δ := by
    have : 0 < 1000 * p.γ * rootKappa p * p.ε := by
      have : 0 < rootKappa p := by unfold rootKappa; positivity
      positivity
    unfold rootKappa at this; linarith
  have he' : 933 * (p.γ * rootKappa p) * ratio p = 933 * (p.Δ / (1000 * p.ε)) := by
    rw [mul_assoc, he]
  rw [he'] at ht
  have e : 2 / (933 * (p.Δ / (1000 * p.ε))) = 2000 * p.ε / (933 * p.Δ) := by
    field_simp; norm_num
  rw [e] at ht
  by_cases hz : gapZero (shape p b) ≤ 0
  · have : p.ε / (p.Δ / gapZero (shape p b)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hε.le (div_nonpos_of_nonneg_of_nonpos hΔ.le hz)
    have : 0 < 2000 * p.ε / (933 * p.Δ) := by positivity
    linarith
  · push Not at hz
    have e2 : p.ε / (p.Δ / gapZero (shape p b)) = p.ε * gapZero (shape p b) / p.Δ := by
      field_simp
    rw [e2]
    have : 2 * (p.ε * gapZero (shape p b) / p.Δ) ≤ 2 * (p.ε * (1 / 10) / p.Δ) := by
      gcongr
    have : 2 * (p.ε * (1 / 10) / p.Δ) < 2000 * p.ε / (933 * p.Δ) := by
      rw [show 2 * (p.ε * (1 / 10) / p.Δ) = p.ε / p.Δ * (1 / 5) by ring,
        show 2000 * p.ε / (933 * p.Δ) = p.ε / p.Δ * (2000 / 933) by ring]
      exact mul_lt_mul_of_pos_left (by norm_num) (by positivity)
    linarith

lemma budget_le_ratio (b : ℕ) (hb : b ≤ lowerBudget p) :
    (b : ℝ) + 1 ≤ rootKappa p / p.γ * ratio p / 1000 := by
  have hY := root_over_gamma hp
  have hr := ratio_ge hp
  have hγ := hp.2.2.1
  have hj : (jOf p : ℝ) ≤ ratio p := by
    have h1 : jOf p < 2 ^ jOf p := Nat.lt_two_pow_self
    have h2 := two_pow_j hp
    have h3 : ((jOf p : ℕ) : ℝ) < ((2 ^ jOf p : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hh : (hOf p : ℝ) ≤ rootKappa p / p.γ / 8000 := by
    have h0 : 0 ≤ rootKappa p / (8000 * p.γ) := by
      have := Real.sqrt_nonneg (p.L / p.μ); unfold rootKappa; positivity
    have := Nat.floor_le h0
    unfold hOf
    have e : rootKappa p / (8000 * p.γ) = rootKappa p / p.γ / 8000 := by field_simp
    rw [← e]; exact this
  have hbn : (b : ℝ) ≤ (hOf p : ℝ) * jOf p / 2 := by
    have h1 : 2 * b ≤ hOf p * jOf p := by
      have := Nat.mul_div_le (hOf p * jOf p) 2
      unfold lowerBudget at hb
      omega
    have : (2 * b : ℝ) ≤ hOf p * jOf p := by exact_mod_cast h1
    linarith
  have h0j : (0 : ℝ) ≤ jOf p := Nat.cast_nonneg _
  have h0h : (0 : ℝ) ≤ hOf p := Nat.cast_nonneg _
  have h2 : (hOf p : ℝ) * jOf p ≤ rootKappa p / p.γ / 8000 * ratio p :=
    mul_le_mul hh hj h0j (by positivity)
  nlinarith

set_option maxHeartbeats 400000 in
lemma dimension (b : ℕ) (hb : b ≤ lowerBudget p) :
    0 < (rootKappa p / p.γ) ^ 5 * ratio p ^ 3 / 2 ∧
    (rootKappa p / p.γ) ^ 5 * ratio p ^ 3 / 2 + ((shape p b).k + 1 : ℕ) ≤ p.d ∧
    2 * ((b + 1 : ℕ) * ((shape p b).k + 1 : ℕ) *
      ((3 * radius p) ^ 2 / ((shape p b).ρ / 2) ^ 2)) ≤
      (rootKappa p / p.γ) ^ 5 * ratio p ^ 3 / 2 := by
  have hY := root_over_gamma hp
  have hr := ratio_ge hp
  have hbr := budget_le_ratio hp b hb
  have hm := mOf_le hp
  have hm16 : (16 : ℝ) ≤ mOf p := by exact_mod_cast mOf_ge16 hp
  have hq := qOf_props hp
  have hqb := q_pow_lower hp b hb
  have hqm := q_pow_m hp
  have hmm := muN_m_le hp
  have hmu0 := muN_pos hp
  have hγ := hp.2.2.1
  have hd : (rootKappa p / p.γ) ^ 5 * ratio p ^ 3 ≤ p.d := hp.2.2.2.2.2.2.2.2
  have hR := radius_sq (p := p)
  set Y := rootKappa p / p.γ with hYdef
  set r := ratio p with hrdef
  set m : ℝ := (mOf p : ℝ) with hmdef
  have hmY : m ≤ Y / 4000 := by
    rw [hYdef]
    have : rootKappa p / (4000 * p.γ) = rootKappa p / p.γ / 4000 := by field_simp
    linarith
  have hk : (((shape p b).k + 1 : ℕ) : ℝ) ≤ Y * r / 500 := by
    have : (((shape p b).k + 1 : ℕ) : ℝ) = (b : ℝ) + 1 + m := by
      rw [hmdef]; simp only [shape]; push_cast; ring
    rw [this]
    nlinarith
  have hb1 : (((b + 1 : ℕ)) : ℝ) ≤ Y * r / 1000 := by push_cast; exact hbr
  set qk := qOf p ^ (b + mOf p) with hqk
  have hqk_pos : 0 < qk := pow_pos (by linarith) _
  have hqk2 : 1 / (21 * r) ≤ qk ^ 2 := by
    have h1 : qOf p ^ (2 * b + (2 * mOf p + 2)) ≤ qk ^ 2 := by
      rw [hqk, ← pow_mul]
      exact pow_le_pow_of_le_one (by linarith) hq.2.le (by omega)
    have h2 : qOf p ^ (2 * b + (2 * mOf p + 2)) = qOf p ^ (2 * b) * qOf p ^ (2 * mOf p + 2) :=
      pow_add _ _ _
    have h3 : 1 / r * (1 / 21) ≤ qOf p ^ (2 * b) * qOf p ^ (2 * mOf p + 2) :=
      mul_le_mul hqb hqm (by norm_num) (pow_nonneg (by linarith [hq.1]) _)
    have : 1 / (21 * r) = 1 / r * (1 / 21) := by field_simp
    linarith
  have hρ : (shape p b).ρ = qk / (4 * m) / (1 + muN p * m) := rfl
  have hratio : (3 * radius p) ^ 2 / ((shape p b).ρ / 2) ^ 2 ≤ 435456 * m ^ 3 * r := by
    rw [hρ, mul_pow, hR]
    have hm0 : 0 < m := by linarith
    have hden : 0 < (qk / (4 * m) / (1 + muN p * m) / 2) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have e : (qk / (4 * m) / (1 + muN p * m) / 2) ^ 2 = qk ^ 2 / (64 * m ^ 2 * (1 + muN p * m) ^ 2) := by
      field_simp; ring
    rw [e]
    have hmn : 0 ≤ muN p * m := mul_nonneg hmu0.le hm0.le
    have h1 : (1 + muN p * m) ^ 2 ≤ 9 := by nlinarith
    have hq2 : 1 ≤ 21 * r * qk ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hqk2; linarith
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ 36 * m * (64 * m ^ 2) * 9),
      mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 36 * m * (64 * m ^ 2))]
  have hY0 : 0 < Y := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · have h1 : Y * r / 500 ≤ Y ^ 5 * r ^ 3 / 2 := by
      have h2 : Y ≤ Y ^ 5 := by
        have : 1 ≤ Y ^ 4 := one_le_pow₀ (by linarith)
        nlinarith
      have h3 : r ≤ r ^ 3 := by
        have : 1 ≤ r ^ 2 := one_le_pow₀ hr
        nlinarith
      have : Y * r ≤ Y ^ 5 * r ^ 3 := mul_le_mul h2 h3 (by linarith) (by positivity)
      linarith
    linarith
  · have hm3 : m ^ 3 ≤ (Y / 4000) ^ 3 := pow_le_pow_left₀ (by linarith) hmY 3
    have hprod : ((b + 1 : ℕ) : ℝ) * (((shape p b).k + 1 : ℕ) : ℝ) *
        ((3 * radius p) ^ 2 / ((shape p b).ρ / 2) ^ 2) ≤
        (Y * r / 1000) * (Y * r / 500) * (435456 * (Y / 4000) ^ 3 * r) := by
      have hpos1 : (0 : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpos2 : (0 : ℝ) ≤ (((shape p b).k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpos3 : 0 ≤ (3 * radius p) ^ 2 / ((shape p b).ρ / 2) ^ 2 := by positivity
      have h3 : (3 * radius p) ^ 2 / ((shape p b).ρ / 2) ^ 2 ≤ 435456 * (Y / 4000) ^ 3 * r := by
        have : 435456 * m ^ 3 * r ≤ 435456 * (Y / 4000) ^ 3 * r := by gcongr
        linarith
      gcongr
    have e : (Y * r / 1000) * (Y * r / 500) * (435456 * (Y / 4000) ^ 3 * r) =
        (435456 / (1000 * 500 * 4000 ^ 3)) * (Y ^ 5 * r ^ 3) := by ring
    rw [e] at hprod
    have : 0 ≤ Y ^ 5 * r ^ 3 := by positivity
    have hc : (435456 / (1000 * 500 * 4000 ^ 3) : ℝ) ≤ 1 / 4 := by norm_num
    have := mul_le_mul_of_nonneg_right hc this
    linarith

lemma delta_pos : 0 < p.Δ := by
  obtain ⟨hL, hμ, hγ, -, hε, -, -, h8, -⟩ := id hp
  have : 0 < 1000 * p.γ * Real.sqrt (p.L / p.μ) * p.ε := by positivity
  linarith

end

end LongTails.Proofs.StrongQuasarChainParameters
