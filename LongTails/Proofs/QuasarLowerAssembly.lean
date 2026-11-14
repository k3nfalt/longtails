import LongTails.Proofs.QuasarHardFailure
import LongTails.Proofs.QuasarNoiseFailure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.QuasarLowerAssembly

open LongTails.Setups HighDimensionalConstrainedQuasar OracleTemplate
open QuasarHardInstance QuasarHardChain QuasarHardProfiles QuasarHardFailure QuasarNoiseFailure
open FiniteSumNondualLowerComponents

lemma gap_lower {d k K t : ℕ} (L a η μ : ℝ) (hL : 0 ≤ L) (ha : 0 < a) (hη : 0 ≤ η)
    (hηk : ((k : ℝ) + 1) * η ≤ 1 / 100) (hμ : 0 ≤ μ) (htK : t ≤ K) (hKk : 2 * K + 4 ≤ k + 1)
    (π : Fin (k + 1) ↪ Fin d) (y : EuclideanSpace ℝ (Fin d))
    (hs : ∀ i : Fin (k + 1), t ≤ i.val → |y (π i)| ≤ a * η / 4) :
    L * a ^ 2 / 2 * (39 / 40 / (4 * ((K : ℝ) + 1))) ≤ hardObjective L a η μ π y ∧
      μ * (((k : ℝ) + 1) / 2 * (35 / 4)) ≤ hardObjective L a η μ π y := by
  rw [hardObjective_eq L a η μ ha π y]
  set z := chainSeq a π y
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hη1 : η ≤ 1 / 100 := by nlinarith
  have hsmall : ∀ i : ℕ, t ≤ i → i ≤ k → |z i| ≤ η / 4 := by
    intro i hti hik
    have h := hs ⟨i, by omega⟩ hti
    have he : z i = y (π ⟨i, by omega⟩) / a := by
      simpa using chainSeq_apply a π y ⟨i, by omega⟩
    rw [he, abs_div, abs_of_pos ha, div_le_iff₀ ha]
    linarith
  have hcv := chainValue_nonneg η z k
  have hbs : 0 ≤ bumpSum z k := Finset.sum_nonneg (fun i _ => bump_nonneg _)
  have hc0 : 0 ≤ L * a ^ 2 / 2 := by positivity
  have htk : t ≤ k := by omega
  constructor
  · have hz := hsmall t le_rfl htk
    have htη : (t : ℝ) * η ≤ 1 / 100 := by
      have : (t : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (show t ≤ k + 1 by omega)
      nlinarith
    have hpos : 0 ≤ 1 - |z t| - (t : ℝ) * η := by nlinarith
    have hg := chainValue_gap η z k t htk hpos
    have hsq : (39 / 40 : ℝ) ≤ (1 - |z t| - (t : ℝ) * η) ^ 2 := by nlinarith
    have htK' : (t : ℝ) + 1 ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ htK
    have hcv' : 39 / 40 / (4 * ((K : ℝ) + 1)) ≤ chainValue η z k := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcv' hc0, mul_nonneg hμ hbs]
  · have hb := bumpSum_gap z k t (fun i hti hik => (hsmall i hti hik).trans (by linarith))
    have hkt : ((k : ℝ) + 1) / 2 ≤ (k : ℝ) + 1 - t := by
      have : (2 * t + 4 : ℝ) ≤ (k : ℝ) + 1 := by
        have h := (Nat.cast_le (α := ℝ)).mpr (show 2 * t + 4 ≤ k + 1 by omega)
        push_cast at h; linarith
      linarith
    have hb' : ((k : ℝ) + 1) / 2 * (35 / 4) ≤ bumpSum z k := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb' hμ, mul_nonneg hc0 hcv]

lemma sqrt_ratio_ge (p : Params) (hε : 0 < p.ε) (hX : 100000000 * p.ε ≤ p.L * p.D ^ 2) :
    10000 ≤ Real.sqrt (p.L * p.D ^ 2 / p.ε) := by
  have h : (10000 : ℝ) ^ 2 ≤ p.L * p.D ^ 2 / p.ε := by
    rw [le_div_iff₀ hε]; nlinarith
  calc (10000 : ℝ) = Real.sqrt (10000 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h

lemma sqrt_ratio_sq (p : Params) (hL : 0 < p.L) (hD : 0 < p.D) (hε : 0 < p.ε) :
    Real.sqrt (p.L * p.D ^ 2 / p.ε) ^ 2 = p.L * p.D ^ 2 / p.ε :=
  Real.sq_sqrt (by positivity)

lemma ceil_inv_bounds {γ : ℝ} (hγ : 0 < γ) :
    1 / γ ≤ (⌈1 / γ⌉₊ : ℝ) ∧ (⌈1 / γ⌉₊ : ℝ) ≤ 1 / γ + 1 :=
  ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le⟩

lemma floor_bounds (x : ℝ) (hx : 0 ≤ x) : x < (⌊x⌋₊ : ℝ) + 1 ∧ (⌊x⌋₊ : ℝ) ≤ x :=
  ⟨Nat.lt_floor_add_one x, Nat.floor_le hx⟩

lemma T_gamma_ge {γ c T : ℝ} {K : ℕ} (hγ : 0 < γ) (hc : 1 / γ ≤ c)
    (hT : T = 2 * K + 4 + c) : 1 ≤ T * γ := by
  have h1 : 1 / γ * γ = 1 := by field_simp
  have hK := Nat.cast_nonneg (α := ℝ) K
  rw [hT]
  nlinarith [mul_le_mul_of_nonneg_right hc hγ.le]

lemma T_gamma_le {γ c T r : ℝ} {K : ℕ} (hγ : 0 < γ) (hγs : γ ≤ 1 / 100) (hc : c ≤ 1 / γ + 1)
    (hT : T = 2 * K + 4 + c) (hr : 10000 ≤ r) (hK : (K : ℝ) ≤ 4 * (r / (10000 * γ))) :
    T * γ ≤ r / 1000 := by
  have h1 : c * γ ≤ 1 + γ := by
    have : (1 / γ + 1) * γ = 1 + γ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hc hγ.le]
  have h2 : (K : ℝ) * γ ≤ 4 * r / 10000 := by
    have : 4 * (r / (10000 * γ)) * γ = 4 * r / 10000 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hK hγ.le]
  rw [hT]
  have : (2 * K + 4 + c) * γ = 2 * ((K : ℝ) * γ) + 4 * γ + c * γ := by ring
  rw [this]
  linarith

lemma T_le_big {γ c T r : ℝ} {K : ℕ} (hγ : 0 < γ) (hγb : 1 / 100 < γ) (hc : c ≤ 1 / γ + 1)
    (hT : T = 2 * K + 4 + c) (hr : 10000 ≤ r) (hK : (K : ℝ) ≤ 4 * (r / (10000 * γ))) :
    T ≤ r / 10 := by
  have hinv : 1 / γ < 100 := by rw [div_lt_iff₀ hγ]; linarith
  have h2 : (K : ℝ) ≤ 4 * r / 100 := by
    have h3 : r / (10000 * γ) ≤ r / 100 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
      linarith
    linarith
  rw [hT]
  linarith

lemma dimension_bound {T Kr B dd : ℝ} (hT : 0 ≤ T) (hT6 : T ≤ 6 * (B + 1))
    (hK2 : Kr + 1 ≤ 2 * (B + 1)) (hB : 0 ≤ B) (hd : 2 ^ 34 * (B + 1) ^ 5 ≤ dd) :
    8 * (Kr + 1) * T * (160000 * T ^ 3) + T ≤ dd := by
  have hb1 : 1 ≤ B + 1 := by linarith
  have hT4 : T ^ 4 ≤ (6 * (B + 1)) ^ 4 := pow_le_pow_left₀ hT hT6 4
  have hm : (Kr + 1) * T ^ 4 ≤ (2 * (B + 1)) * (6 * (B + 1)) ^ 4 :=
    mul_le_mul hK2 hT4 (by positivity) (by positivity)
  have hpow : B + 1 ≤ (B + 1) ^ 5 := by
    calc B + 1 = (B + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hb1 (by norm_num)
  have e1 : (2 * (B + 1)) * (6 * (B + 1)) ^ 4 = 2592 * (B + 1) ^ 5 := by ring
  have e2 : 8 * (Kr + 1) * T * (160000 * T ^ 3) = 1280000 * ((Kr + 1) * T ^ 4) := by ring
  rw [e2]
  rw [e1] at hm
  have e3 : (2 : ℝ) ^ 34 = 17179869184 := by norm_num
  rw [e3] at hd
  nlinarith

lemma quasar_gap_arith {L D ε T γ : ℝ} (hL : 0 < L) (hD : 0 < D) (hT : 0 < T)
    (hγ : 0 < γ) (h : ε * (T * γ) ^ 2 ≤ L * D ^ 2 / 1000000) :
    ε < (1 / (100 * (T * γ))) ^ 2 * (L / 2 * (D ^ 2 / (4 * T)) / 2) * (T / 2 * (35 / 4)) := by
  have e : (1 / (100 * (T * γ))) ^ 2 * (L / 2 * (D ^ 2 / (4 * T)) / 2) * (T / 2 * (35 / 4)) =
      35 * L * D ^ 2 / (1280000 * (T * γ) ^ 2) := by field_simp; ring
  rw [e, lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos hL (pow_pos hD 2)]

lemma convex_gap_arith {L D ε T Kr : ℝ} (hL : 0 < L) (hD : 0 < D) (hT : 0 < T)
    (hK : 0 < Kr + 1) (hKT : Kr + 1 ≤ T / 2) (h : ε * T ^ 2 ≤ L * D ^ 2 / 100) :
    ε < L / 2 * (D ^ 2 / (4 * T)) / 2 * (39 / 40 / (4 * (Kr + 1))) := by
  have hlow : L / 2 * (D ^ 2 / (4 * T)) / 2 * (39 / 40 / (2 * T)) ≤
      L / 2 * (D ^ 2 / (4 * T)) / 2 * (39 / 40 / (4 * (Kr + 1))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  refine lt_of_lt_of_le ?_ hlow
  have e : L / 2 * (D ^ 2 / (4 * T)) / 2 * (39 / 40 / (2 * T)) = 39 * L * D ^ 2 / (1280 * T ^ 2) := by
    field_simp; ring
  rw [e, lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos hL (pow_pos hD 2)]

lemma mu_bound {s L a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 100) (hL : 0 < L) (ha : 0 < a) :
    600 * (s ^ 2 * (L / 2 * a ^ 2 / 2)) / a ^ 2 ≤ L / 2 := by
  have hs2 : s ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hs.le hs1 2
  have e : 600 * (s ^ 2 * (L / 2 * a ^ 2 / 2)) / a ^ 2 = 150 * s ^ 2 * L := by
    field_simp; ring
  rw [e]
  nlinarith

lemma eps_scale {L D ε x c : ℝ} (hε : 0 < ε) (hc : 0 < c) (hx : x ≤ (L * D ^ 2 / ε) / c) :
    ε * x ≤ L * D ^ 2 / c := by
  have := mul_le_mul_of_nonneg_left hx hε.le
  calc ε * x ≤ ε * (L * D ^ 2 / ε / c) := this
    _ = L * D ^ 2 / c := by field_simp

set_option maxHeartbeats 400000 in
lemma partA_case (p : Params) (hv : spec.valid p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ) {K : ℕ} (hK : b 0 + b 1 = K)
    (hKdet : (K : ℝ) ≤ 4 * (Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ)))
    (hKB : K ≤ 2 * ⌊Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) + p.σ ^ 2 * p.D ^ 2 *
      Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)⌋₊) :
    ∃ (I : spec.Instance (spec.publicInput p))
      (O : Oracle (spec.Query (spec.publicInput p)) (spec.Reply (spec.publicInput p)) spec.numOracles),
      spec.admissible p I O ∧
        ¬ spec.successful p I (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A b seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hD, hγ, hγ1, _, hε, hδ, hδ4, hX, _, hdim⟩ := hv
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (p.L * p.D ^ 2 / p.ε) := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) /
    (8192 * p.γ ^ 2 * p.ε ^ 2) := ⟨_, rfl⟩
  rw [← hr] at hKdet hKB
  rw [← hB2] at hKB hdim
  rw [← hr] at hdim
  obtain ⟨Bt, hBt⟩ : ∃ Bt, Bt = ⌊r / (10000 * p.γ) + B2⌋₊ := ⟨_, rfl⟩
  rw [← hBt] at hKB hdim
  have hr4 : 10000 ≤ r := hr ▸ sqrt_ratio_ge p hε hX
  have hr2 : r ^ 2 = p.L * p.D ^ 2 / p.ε := hr ▸ sqrt_ratio_sq p hL hD hε
  have hlog : 0 ≤ Real.log (1 / p.δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hB2n : 0 ≤ B2 := by rw [hB2]; positivity
  have hB1g : 1 / p.γ ≤ r / (10000 * p.γ) := by
    rw [div_le_div_iff₀ hγ (by positivity)]; nlinarith
  have hfl : r / (10000 * p.γ) + B2 < (Bt : ℝ) + 1 := hBt ▸ Nat.lt_floor_add_one _
  obtain ⟨hc1, hc2⟩ := ceil_inv_bounds hγ
  obtain ⟨k, hk⟩ : ∃ k, k = 2 * K + 3 + ⌈1 / p.γ⌉₊ := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = (k : ℝ) + 1 := ⟨_, rfl⟩
  have hT : T = 2 * K + 4 + (⌈1 / p.γ⌉₊ : ℝ) := by rw [hTdef, hk]; push_cast; ring
  have hT1 : 4 ≤ T := by
    rw [hT]
    have h1 := Nat.cast_nonneg (α := ℝ) ⌈1 / p.γ⌉₊
    have h2 := Nat.cast_nonneg (α := ℝ) K
    linarith
  have hTpos : 0 < T := by linarith
  have hKk : 2 * K + 4 ≤ k + 1 := by omega
  have hKk' : K ≤ k + 1 := by omega
  have hKR : (K : ℝ) ≤ 2 * Bt := by exact_mod_cast hKB
  have hT6 : T ≤ 6 * ((Bt : ℝ) + 1) := by rw [hT]; linarith
  have hK2 : (K : ℝ) + 1 ≤ 2 * ((Bt : ℝ) + 1) := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = p.D / (2 * Real.sqrt T) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = 1 / (100 * T) := ⟨_, rfl⟩
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsT2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
  have hapos : 0 < a := by rw [ha]; positivity
  have ha2 : a ^ 2 = p.D ^ 2 / (4 * T) := by rw [ha, div_pow, mul_pow, hsT2]; ring
  have hηpos : 0 < η := by rw [hη]; positivity
  have hη5 : η ≤ 1 / 5 := by rw [hη, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hηk : ((k : ℝ) + 1) * η = 1 / 100 := by rw [← hTdef, hη]; field_simp
  have hrad : Real.sqrt ((k : ℝ) + 1) * a ≤ p.D / 2 := by
    rw [← hTdef, ha]; field_simp; rfl
  have hratio : (p.D / 2) ^ 2 / (a * η / 4) ^ 2 = 160000 * T ^ 3 := by
    have : (a * η / 4) ^ 2 = a ^ 2 * η ^ 2 / 16 := by ring
    rw [this, ha2, hη]
    field_simp
    ring
  obtain ⟨Dc, hDc⟩ : ∃ Dc, Dc = 8 * ((K : ℝ) + 1) * ((k + 1 : ℕ) : ℝ) *
    ((p.D / 2) ^ 2 / (a * η / 4) ^ 2) := ⟨_, rfl⟩
  have hkcast : ((k + 1 : ℕ) : ℝ) = T := by rw [hTdef]; push_cast; ring
  have hDcpos : 0 < Dc := by rw [hDc, hkcast]; positivity
  have hDsz : Dc + ((k + 1 : ℕ) : ℝ) ≤ p.d := by
    rw [hDc, hratio, hkcast]
    have hdim' : (2 : ℝ) ^ 34 * ((Bt : ℝ) + 1) ^ 5 ≤ p.d := by exact_mod_cast hdim
    exact dimension_bound hTpos.le hT6 hK2 (Nat.cast_nonneg _) hdim'
  rcases le_or_gt p.γ (1 / 100) with hsmall | hbig
  · obtain ⟨s, hs⟩ : ∃ s, s = 1 / (100 * (T * p.γ)) := ⟨_, rfl⟩
    have hTγ : 1 ≤ T * p.γ := T_gamma_ge hγ hc1 hT
    have hspos : 0 < s := by rw [hs]; positivity
    have hs1 : s ≤ 1 / 100 := by
      rw [hs, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hTs : T * s = 1 / (100 * p.γ) := by rw [hs]; field_simp
    have hTs1 : 1 ≤ ((k : ℝ) + 1) * s := by
      rw [← hTdef, hTs, le_div_iff₀ (by positivity)]; linarith
    have hγs : p.γ = 1 / (100 * (((k : ℝ) + 1) * s)) := by rw [← hTdef, hTs]; field_simp
    obtain ⟨μ, hμ⟩ : ∃ μ, μ = s ^ 2 * (p.L / 2 * a ^ 2 / 2) := ⟨_, rfl⟩
    have hμpos : 0 ≤ μ := by rw [hμ]; positivity
    have hμL : 600 * μ / a ^ 2 ≤ p.L / 2 := by rw [hμ]; exact mu_bound hspos hs1 hL hapos
    have hTγr := T_gamma_le hγ hsmall hc2 hT hr4 hKdet
    have hTγ2 : (T * p.γ) ^ 2 ≤ (p.L * p.D ^ 2 / p.ε) / 1000000 := by
      rw [← hr2]
      have := pow_le_pow_left₀ (by positivity) hTγr 2
      rw [div_pow] at this
      norm_num at this ⊢
      linarith
    have hε2 := eps_scale hε (by norm_num) hTγ2
    refine exists_failure p hD hL hδ.le (by linarith) hKk' a η μ Dc hapos hηpos hη5 hμpos hμL
      hrad hDcpos hDsz hDc.symm.le ?_ ?_ A b hK
    · intro π z
      rw [hμ]
      exact hardObjective_quasar (p.L / 2) a η s p.γ (by linarith) hapos hηpos.le hηk.le
        hspos hs1 hTs1 hγs π z
    · intro π y t htK hsm
      have hg := (gap_lower (p.L / 2) a η μ (by linarith) hapos hηpos.le hηk.le
        hμpos htK hKk π y hsm).2
      refine lt_of_lt_of_le ?_ hg
      rw [hμ, ha2, hs, ← hTdef]
      exact quasar_gap_arith hL hD hTpos hγ hε2
  · have hTr := T_le_big hγ hbig hc2 hT hr4 hKdet
    have hT2 : T ^ 2 ≤ (p.L * p.D ^ 2 / p.ε) / 100 := by
      rw [← hr2]
      have := pow_le_pow_left₀ hTpos.le hTr 2
      rw [div_pow] at this
      norm_num at this ⊢
      linarith
    have hε2 := eps_scale hε (by norm_num) hT2
    refine exists_failure p hD hL hδ.le (by linarith) hKk' a η 0 Dc hapos hηpos hη5 le_rfl
      (by simp; linarith) hrad hDcpos hDsz hDc.symm.le ?_ ?_ A b hK
    · intro π z
      exact hardObjective_convex_quasar (p.L / 2) a η p.γ (by linarith) hapos hηpos.le hγ1 π z
    · intro π y t htK hsm
      have hg := (gap_lower (p.L / 2) a η 0 (by linarith) hapos hηpos.le hηk.le
        le_rfl htK hKk π y hsm).1
      refine lt_of_lt_of_le ?_ hg
      have hKT : (K : ℝ) + 1 ≤ T / 2 := by
        have h := (Nat.cast_le (α := ℝ)).mpr hKk
        push_cast at h
        rw [hTdef]; linarith
      rw [ha2]
      exact convex_gap_arith hL hD hTpos (by positivity) hKT hε2

lemma silent_bound {ν δ : ℝ} {K : ℕ} (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 9) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (hK : (K : ℝ) * ν ≤ 2 / 9 * Real.log (1 / δ)) :
    2 * δ < (1 - ν) ^ K := by
  have h1ν : 0 < 1 - ν := by linarith
  have hpow : 0 < (1 - ν) ^ K := pow_pos h1ν K
  rw [← Real.log_lt_log_iff (by positivity) hpow, Real.log_pow, Real.log_mul (by norm_num) hδ0.ne']
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - ν) by positivity)
  rw [one_div, Real.log_inv] at hl
  have hlow : -(ν / (1 - ν)) ≤ Real.log (1 - ν) := by
    have : (1 - ν)⁻¹ - 1 = ν / (1 - ν) := by field_simp; ring
    linarith
  have hfrac : ν / (1 - ν) ≤ 9 / 8 * ν := by
    rw [div_le_iff₀ h1ν]; nlinarith
  have hlogδ : Real.log δ ≤ Real.log (1 / 4) := Real.log_le_log hδ0 hδ
  have h4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  have hKn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKl : (K : ℝ) * Real.log (1 - ν) ≥ -(K : ℝ) * (9 / 8 * ν) := by
    have := mul_le_mul_of_nonneg_left (hlow.trans' (neg_le_neg hfrac)) hKn
    linarith
  rw [hinv] at hK
  nlinarith

lemma noise_product (p : Params) (hD : 0 < p.D) (hε : 0 < p.ε) (hγ : 0 < p.γ) (hσ : 0 < p.σ) :
    4 * (p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)) * noiseLevel p =
      2 / 9 * Real.log (1 / p.δ) := by
  unfold noiseLevel
  field_simp
  ring

lemma partB_case (p : Params) (hv : spec.valid p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ) {K : ℕ} (hK : b 0 + b 1 = K)
    (hnoise : Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) <
      p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2))
    (hKn : (K : ℝ) ≤ 4 * (p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)))
    (hKB : K ≤ 2 * ⌊Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) + p.σ ^ 2 * p.D ^ 2 *
      Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)⌋₊) :
    ∃ (I : spec.Instance (spec.publicInput p))
      (O : Oracle (spec.Query (spec.publicInput p)) (spec.Reply (spec.publicInput p)) spec.numOracles),
      spec.admissible p I O ∧
        ¬ spec.successful p I (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A b seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hD, hγ, hγ1, hσ0, hε, hδ, hδ4, hX, hband, hdim⟩ := hv
  have hr4 : 10000 ≤ Real.sqrt (p.L * p.D ^ 2 / p.ε) := sqrt_ratio_ge p hε hX
  have hB1pos : 0 ≤ Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) := by positivity
  have hσ : 0 < p.σ := by
    rcases hσ0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hnoise
      simp at hnoise
      linarith
  have hb : 64 * p.γ * p.ε ≤ p.σ * p.D := by
    rcases hband with h | h
    · exact absurd h hσ.ne'
    · exact h
  have hν0 := (noiseLevel_pos p hD hε hγ hσ).le
  have hν9 := noiseLevel_le p hD hε hγ hσ hb
  have hKν : (K : ℝ) * noiseLevel p ≤ 2 / 9 * Real.log (1 / p.δ) := by
    rw [← noise_product p hD hε hγ hσ]
    exact mul_le_mul_of_nonneg_right hKn hν0
  have hsil := silent_bound hν0 hν9 hδ hδ4 hKν
  have hLD : 2048 * p.ε ≤ p.L * p.D ^ 2 := by linarith
  set Bt := ⌊Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) + p.σ ^ 2 * p.D ^ 2 *
    Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)⌋₊ with hBt
  have hMd : 64 * K + 64 ≤ p.d := by
    have hdim' : 2 ^ 34 * (Bt + 1) ^ 5 ≤ p.d := hdim
    have h1 : Bt + 1 ≤ (Bt + 1) ^ 5 := by
      calc Bt + 1 = (Bt + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  exact noise_exists_failure p hD hε hγ hγ1 hσ hb hLD hδ.le (by linarith) le_rfl hMd hsil A b hK

lemma lower_failure (p : Params) (hv : spec.valid p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) 2) (b : Fin 2 → ℕ)
    (hb : ∀ i, b i ≤ ⌊Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) + p.σ ^ 2 * p.D ^ 2 *
      Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)⌋₊) :
    ∃ (I : spec.Instance (spec.publicInput p))
      (O : Oracle (spec.Query (spec.publicInput p)) (spec.Reply (spec.publicInput p)) spec.numOracles),
      spec.admissible p I O ∧
        ¬ spec.successful p I (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A b seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hv' := hv
  obtain ⟨hL, hD, hγ, _, hσ0, hε, hδ, hδ4, _, _, _⟩ := hv'
  have hKB : b 0 + b 1 ≤ 2 * ⌊Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) + p.σ ^ 2 *
      p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)⌋₊ := by
    have := hb 0; have := hb 1; omega
  have hlog : 0 ≤ Real.log (1 / p.δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hB1 : 0 ≤ Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) := by positivity
  have hB2 : 0 ≤ p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2) := by positivity
  have hfl := Nat.floor_le (add_nonneg hB1 hB2)
  have hKR : ((b 0 + b 1 : ℕ) : ℝ) ≤ 2 * (Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ) +
      p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2)) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hKB
    push_cast at h ⊢
    linarith
  rcases le_or_gt (p.σ ^ 2 * p.D ^ 2 * Real.log (1 / p.δ) / (8192 * p.γ ^ 2 * p.ε ^ 2))
      (Real.sqrt (p.L * p.D ^ 2 / p.ε) / (10000 * p.γ)) with hdet | hnoise
  · exact partA_case p hv A b rfl (by linarith) hKB
  · exact partB_case p hv A b rfl hnoise (by linarith) hKB

end LongTails.Proofs.QuasarLowerAssembly
