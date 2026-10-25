import LongTails.Proofs.WeaklyConvexSilverJoin

open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeaklyConvexSilverInduction

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace
open LongTails.Proofs.WeaklyConvexSilverBasic
open LongTails.Proofs.WeaklyConvexSilverCertificate
open LongTails.Proofs.WeaklyConvexSilverJoin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_young (u v : E) : 2 * ⟪u, v⟫ ≤ ‖u‖ ^ 2 / 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [real_inner_le_norm u v, sq_nonneg (‖u‖ - 2 * ‖v‖)]

lemma primitive_nil (f : E → ℝ) (g : E → E) (x : E) : primitive f g [] x = 0 := by
  simp [primitive, history, values, energy, run]

lemma defectSum_nil (f : E → ℝ) (g : E → E) (z x : E) : defectSum f g z [] x = 0 := by
  simp [defectSum]

lemma level_zero {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1 / 200)
    (hD : ∀ u v, -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v)) :
    BlockBound f g ρ 0 1 (21 / 5) 0 := by
  intro x e R2 η hη hx hIC
  have hs : (steps 0).sum = 0 := by simp [steps]
  have hr : run g (steps 0) x = x := by simp [steps, run]
  rw [hs, hr] at hIC
  rw [hs]
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [steps, nodes, List.mem_singleton] at hw
    rw [hw]
    have hR20 : 0 ≤ R2 := le_trans (sq_nonneg _) hx
    have h1 := hD e x
    rw [anchor_defect] at h1
    have h2 : ‖(e - g e) - (x - g x)‖ ^ 2 ≤ 2 * ‖x - (e - g e)‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
      have e1 : (e - g e) - (x - g x) = -(x - (e - g e)) + g x := by abel
      rw [e1]
      have := sq_add_le_two (-(x - (e - g e))) (g x)
      rwa [norm_neg] at this
    have h3 := inner_young (g x) (x - (e - g e))
    have h4 : ρ * ‖(e - g e) - (x - g x)‖ ^ 2 ≤ ρ * (2 * R2 + 2 * ‖g x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      linarith
    have h5 : ρ * ‖g x‖ ^ 2 ≤ 1 / 200 * ‖g x‖ ^ 2 := mul_le_mul_of_nonneg_right hρ' (sq_nonneg _)
    have h6 : ρ * R2 ≤ 1 / 200 * R2 := mul_le_mul_of_nonneg_right hρ' hR20
    constructor
    · linarith
    · linarith
  · simp only [steps, primitive_nil, mul_zero, zero_mul, neg_zero, le_refl]

noncomputable def nodeBound (k : ℕ) : ℝ := 50 * (101 / 100) ^ k

noncomputable def gradBound (k : ℕ) : ℝ := 36 * (101 / 100) ^ k

noncomputable def primBound : ℕ → ℝ
  | 0 => 0
  | 1 => 250
  | k + 2 => primBound (k + 1) * (1 + 13 / 2000) +
      (1 + 2 * ratio) * primBound (k + 1) * (θk (k + 1) + 3 / 200) +
      ratio * (steps (k + 1)).sum *
        (106 / 100 + (3 + 8 * (nodeBound (k + 1) + gradBound (k + 1))) * (θk (k + 1) + 3 / 200)) +
      ratio * ((ratio - 2) * ((steps (k + 1)).sum + 1) + 1) * (2 * (θk (k + 1) + 3 / 200) + 71 / 100)

lemma steps_one : steps 1 = [ratio - 1] := by
  show steps 0 ++ [1 + ratio ^ 0 / ratio] ++ steps 0 = [ratio - 1]
  simp only [steps, pow_zero, List.nil_append, List.append_nil, List.cons.injEq, and_true]
  rw [ratio_inverse]
  ring

lemma level_one {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ 1 / 200) (hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖)
    (hD : ∀ u v, -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v)) :
    BlockBound f g ρ 1 (nodeBound 1) (gradBound 1) 250 := by
  intro x e R2 η hη hx hIC
  have hb := ratio_bounds
  have hR20 : 0 ≤ R2 := le_trans (sq_nonneg _) hx
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ratio - 1 := ⟨_, rfl⟩
  have hμ1 : (1414213 / 1000000 : ℝ) < μ ∧ μ < 1414214 / 1000000 := by
    constructor <;> linarith [hb.1, hb.2]
  have hμ0 : 0 ≤ μ := by linarith [hμ1.1]
  have hμm : 0 ≤ μ - 1 := by linarith [hμ1.1]
  have hμsq1 : (μ - 1) ^ 2 ≤ 1716 / 10000 := by
    have := pow_le_pow_left₀ hμm (by linarith [hμ1.2] : μ - 1 ≤ 414214 / 1000000) 2
    have h2 : ((414214 : ℝ) / 1000000) ^ 2 ≤ 1716 / 10000 := by norm_num
    linarith
  have hμsq2 : μ ^ 2 ≤ 2000002 / 1000000 := by
    have := pow_le_pow_left₀ hμ0 hμ1.2.le 2
    have h2 : ((1414214 : ℝ) / 1000000) ^ 2 ≤ 2000002 / 1000000 := by norm_num
    linarith
  have hμsq3 : (1 + μ) ^ 2 ≤ 586 / 100 := by
    have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1 + μ) (by linarith [hμ1.2] : 1 + μ ≤ 2414214 / 1000000) 2
    have h2 : ((2414214 : ℝ) / 1000000) ^ 2 ≤ 586 / 100 := by norm_num
    linarith
  obtain ⟨p, hp⟩ : ∃ p, p = x - μ • g x := ⟨_, rfl⟩
  have hs1 : (steps 1).sum = μ := by rw [steps_one, hμ]; simp
  have hr1 : run g (steps 1) x = p := by rw [steps_one, hp, hμ]; simp [run]
  have hn1 : nodes g (steps 1) x = [x, p] := by rw [steps_one, hp, hμ]; simp [nodes]
  rw [hs1, hr1] at hIC
  rw [hs1, hn1]
  obtain ⟨c, hc⟩ : ∃ c, c = e - g e := ⟨_, rfl⟩
  obtain ⟨fc, hfc⟩ : ∃ fc, fc = f e - ‖g e‖ ^ 2 / 2 := ⟨_, rfl⟩
  rw [← hc] at hx ⊢
  rw [← hfc] at hIC
  have hGx0 : 0 ≤ ‖g x‖ ^ 2 := sq_nonneg _
  have hGp0 : 0 ≤ ‖g p‖ ^ 2 := sq_nonneg _
  have hxp : x - p = μ • g x := by rw [hp]; abel
  have hyy : (x - g x) - (p - g p) = (μ - 1) • g x + g p := by rw [hp]; module
  have hyyb : ‖(x - g x) - (p - g p)‖ ^ 2 ≤ 2 * (μ - 1) ^ 2 * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2 := by
    rw [hyy]
    have := sq_add_le_two ((μ - 1) • g x) (g p)
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at this
    linarith
  have hip : -(‖g x‖ ^ 2 + ‖g p‖ ^ 2) ≤ 2 * ⟪g x, g p⟫ := by
    have := sq_nonneg ‖g x + g p‖
    rw [norm_add_sq_real] at this
    linarith
  have hfxp : (2 - μ) * (‖g x‖ ^ 2 + ‖g p‖ ^ 2) -
      ρ * (2 * (μ - 1) ^ 2 * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) ≤ 2 * (f x - f p) := by
    have h1 := hD x p
    simp only [defect] at h1
    rw [hxp, inner_smul_right] at h1
    have hgg : ‖g x - g p‖ ^ 2 = ‖g x‖ ^ 2 - 2 * ⟪g x, g p⟫ + ‖g p‖ ^ 2 := norm_sub_sq_real _ _
    have h2 : (μ - 1) * (-(‖g x‖ ^ 2 + ‖g p‖ ^ 2)) ≤ (μ - 1) * (2 * ⟪g x, g p⟫) :=
      mul_le_mul_of_nonneg_left hip hμm
    have h3 : ρ * ‖(x - g x) - (p - g p)‖ ^ 2 ≤ ρ * (2 * (μ - 1) ^ 2 * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hyyb hρ
    have hc' : ⟪g p, g x⟫ = ⟪g x, g p⟫ := real_inner_comm _ _
    rw [hc'] at h1
    linarith
  have hICx : -(1 / 10) * 0 * ‖g x‖ ^ 2 - η ≤ f x - fc := by
    have h1 : ρ * (2 * (μ - 1) ^ 2 * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) ≤
        1 / 200 * (2 * (1 / 5) * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) := by
      have h2 : 2 * (μ - 1) ^ 2 * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2 ≤
          2 * (1 / 5) * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right (hμsq1.trans (by norm_num : (1716 : ℝ) / 10000 ≤ 1 / 5)) hGx0
        linarith
      calc ρ * (2 * (μ - 1) ^ 2 * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) ≤
            ρ * (2 * (1 / 5) * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hρ
        _ ≤ 1 / 200 * (2 * (1 / 5) * ‖g x‖ ^ 2 + 2 * ‖g p‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hρ' (by positivity)
    have h2 : μ * ‖g p‖ ^ 2 ≤ 1414214 / 1000000 * ‖g p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hμ1.2.le hGp0
    have h3 : (2 - 1414214 / 1000000) * (‖g x‖ ^ 2 + ‖g p‖ ^ 2) ≤
        (2 - μ) * (‖g x‖ ^ 2 + ‖g p‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hL := (level_zero hρ hρ' hD) x e R2 η hη (by rw [← hc]; exact hx)
    (by
      have hs0 : (steps 0).sum = 0 := by simp [steps]
      have hr0 : run g (steps 0) x = x := by simp [steps, run]
      rw [hs0, hr0, ← hfc]
      simpa using hICx)
  have hs0 : (steps 0).sum = 0 := by simp [steps]
  rw [hs0] at hL
  obtain ⟨hLn, -⟩ := hL
  have hxmem : x ∈ nodes g (steps 0) x := start_mem_nodes g _ x
  obtain ⟨-, hGxb⟩ := hLn x hxmem
  simp only [zero_add, mul_one] at hGxb
  set Z := R2 + 2 * (μ + 1) * η with hZ
  have hZ1 : R2 + 2 * η ≤ Z := by
    rw [hZ]; linarith [mul_nonneg hμ0 hη]
  have hZ0 : 0 ≤ Z := by linarith
  have hGxZ : ‖g x‖ ^ 2 ≤ 21 / 5 * Z := by linarith
  have hGpb : ‖g p‖ ^ 2 ≤ (1 + μ) ^ 2 * ‖g x‖ ^ 2 := by
    have h1 : ‖g p‖ ≤ ‖g x‖ + ‖g p - g x‖ := by
      have := norm_add_le (g x) (g p - g x)
      simpa using this
    have h2 : ‖g p - g x‖ ≤ μ * ‖g x‖ := by
      calc ‖g p - g x‖ ≤ ‖p - x‖ := hlip p x
        _ = μ * ‖g x‖ := by
          rw [← neg_sub, norm_neg, hxp, norm_smul, Real.norm_of_nonneg hμ0]
    have h3 : ‖g p‖ ≤ (1 + μ) * ‖g x‖ := by linarith
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [mul_pow] at h4
    exact h4
  have hGpZ : ‖g p‖ ^ 2 ≤ 25 * Z := by
    have := mul_le_mul_of_nonneg_right hμsq3 hGx0
    linarith
  have hcx := hD e x
  rw [anchor_defect, ← hc, ← hfc] at hcx
  have hcxb : ‖(e - g e) - (x - g x)‖ ^ 2 ≤ 2 * R2 + 2 * ‖g x‖ ^ 2 := by
    have e1 : (e - g e) - (x - g x) = -(x - c) + g x := by rw [hc]; abel
    rw [e1]
    have := sq_add_le_two (-(x - c)) (g x)
    rw [norm_neg] at this
    linarith
  rw [← hc] at hcxb
  have hpc : ‖p - c‖ ^ 2 ≤ 4 * Z := by
    have e1 : p - c = (x - c) - μ • g x := by rw [hp]; abel
    rw [e1, norm_sub_sq_real, norm_smul, Real.norm_of_nonneg hμ0, inner_smul_right,
      mul_pow, real_inner_comm]
    have h1 : ρ * ‖c - (x - g x)‖ ^ 2 ≤ 1 / 200 * (2 * R2 + 2 * ‖g x‖ ^ 2) := by
      calc ρ * ‖c - (x - g x)‖ ^ 2 ≤ ρ * (2 * R2 + 2 * ‖g x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcxb hρ
        _ ≤ 1 / 200 * (2 * R2 + 2 * ‖g x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hρ' (by positivity)
    have h2 : 2 * ⟪g x, x - c⟫ ≥
        ‖g x‖ ^ 2 + 2 * (f x - fc) - 1 / 200 * (2 * R2 + 2 * ‖g x‖ ^ 2) := by
      linarith
    have h3 : μ * (2 * ⟪g x, x - c⟫) ≥
        μ * (‖g x‖ ^ 2 + 2 * (f x - fc) - 1 / 200 * (2 * R2 + 2 * ‖g x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 hμ0
    have h4 : (μ ^ 2 - μ) * ‖g x‖ ^ 2 ≤ 59 / 100 * ‖g x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hμ1.1]) hGx0
    have h5 : μ * η ≤ 1414214 / 1000000 * η := mul_le_mul_of_nonneg_right hμ1.2.le hη
    have h6 : μ * (-η) ≤ μ * (f x - fc) := mul_le_mul_of_nonneg_left (by linarith) hμ0
    have h7 : μ * (1 / 200 * (2 * R2 + 2 * ‖g x‖ ^ 2)) ≤ 2 * (1 / 200 * (2 * R2 + 2 * ‖g x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith [hμ1.2]) (by positivity)
    have h8 : 0 ≤ μ * η := mul_nonneg hμ0 hη
    linarith
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hnb : (50 : ℝ) ≤ nodeBound 1 := by unfold nodeBound; norm_num
    have hqb : (36 : ℝ) ≤ gradBound 1 := by unfold gradBound; norm_num
    have hz1 := mul_le_mul_of_nonneg_right hnb hZ0
    have hz2 := mul_le_mul_of_nonneg_right hqb hZ0
    rcases hw with rfl | rfl
    · constructor
      · linarith
      · linarith
    · constructor
      · linarith
      · linarith
  · have hj := primitive_join f g [] x
    simp only [List.sum_nil, zero_add, mul_one, run, List.nil_append, List.append_nil,
      primitive_nil, defectSum_nil, mul_zero, add_zero] at hj
    have hμ' : ratio - 2 + 1 = μ := by rw [hμ]; ring
    rw [hμ', ← hp] at hj
    rw [steps_one, ← hμ, hj]
    have h1 := hD x p
    have h2 := hD p x
    have hsym : ‖(p - g p) - (x - g x)‖ ^ 2 = ‖(x - g x) - (p - g p)‖ ^ 2 := by
      rw [← norm_neg, neg_sub]
    rw [hsym] at h2
    have hyZ : ‖(x - g x) - (p - g p)‖ ^ 2 ≤ 52 * Z := by
      have := mul_le_mul_of_nonneg_right hμsq1 hGx0
      linarith
    have hr0 : 0 ≤ ratio := by linarith
    have hm1 : ratio * (-ρ * ‖(x - g x) - (p - g p)‖ ^ 2) ≤
        ratio * defect (f x) (f p) x p (g x) (g p) :=
      mul_le_mul_of_nonneg_left h1 hr0
    have hm2 : ratio * (μ - 1) * (-ρ * ‖(x - g x) - (p - g p)‖ ^ 2) ≤
        ratio * (μ - 1) * defect (f p) (f x) p x (g p) (g x) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0 hμm)
    have hm3 : ρ * ‖(x - g x) - (p - g p)‖ ^ 2 ≤ ρ * (52 * Z) := mul_le_mul_of_nonneg_left hyZ hρ
    have hm4 : ratio * μ ≤ 342 / 100 := by
      have := mul_le_mul hb.2.le hμ1.2.le hμ0 (by norm_num)
      have h2 : (2414214 : ℝ) / 1000000 * (1414214 / 1000000) ≤ 342 / 100 := by norm_num
      linarith
    have hm5 : 0 ≤ ρ * ‖(x - g x) - (p - g p)‖ ^ 2 := mul_nonneg hρ (sq_nonneg _)
    have hm6 : ratio * μ * (ρ * ‖(x - g x) - (p - g p)‖ ^ 2) ≤ 342 / 100 * (ρ * (52 * Z)) := by
      calc ratio * μ * (ρ * ‖(x - g x) - (p - g p)‖ ^ 2) ≤
            342 / 100 * (ρ * ‖(x - g x) - (p - g p)‖ ^ 2) := mul_le_mul_of_nonneg_right hm4 hm5
        _ ≤ 342 / 100 * (ρ * (52 * Z)) := mul_le_mul_of_nonneg_left hm3 (by norm_num)
    have hρZ : 0 ≤ ρ * Z := mul_nonneg hρ hZ0
    linarith

lemma nodeBound_ge (k : ℕ) : 50 ≤ nodeBound k := by
  unfold nodeBound
  have : (1 : ℝ) ≤ (101 / 100) ^ k := one_le_pow₀ (by norm_num)
  linarith

lemma gradBound_nonneg (k : ℕ) : 0 ≤ gradBound k := by
  unfold gradBound
  positivity

lemma steps_sum_nonneg (k : ℕ) : 0 ≤ (steps k).sum :=
  List.sum_nonneg (fun h hh => (steps_positive k h hh).le)

lemma θk_nonneg (k : ℕ) : 0 ≤ θk k := by
  unfold θk
  split_ifs <;> norm_num

lemma primBound_nonneg : ∀ k, 0 ≤ primBound k
  | 0 => le_refl _
  | 1 => by norm_num [primBound]
  | k + 2 => by
    have ih := primBound_nonneg (k + 1)
    have hb := ratio_bounds
    have hS := steps_sum_nonneg (k + 1)
    have hθ := θk_nonneg (k + 1)
    have hn := nodeBound_ge (k + 1)
    have hq := gradBound_nonneg (k + 1)
    have hμ : 0 ≤ (ratio - 2) * ((steps (k + 1)).sum + 1) + 1 := by nlinarith
    have t1 : 0 ≤ primBound (k + 1) * (1 + 13 / 2000) := by positivity
    have t2 : 0 ≤ (1 + 2 * ratio) * primBound (k + 1) * (θk (k + 1) + 3 / 200) := by
      have : 0 ≤ 1 + 2 * ratio := by linarith
      positivity
    have t3 : 0 ≤ ratio * (steps (k + 1)).sum *
        (106 / 100 + (3 + 8 * (nodeBound (k + 1) + gradBound (k + 1))) * (θk (k + 1) + 3 / 200)) := by
      have : 0 ≤ ratio := by linarith
      have : 0 ≤ 3 + 8 * (nodeBound (k + 1) + gradBound (k + 1)) := by linarith
      positivity
    have t4 : 0 ≤ ratio * ((ratio - 2) * ((steps (k + 1)).sum + 1) + 1) *
        (2 * (θk (k + 1) + 3 / 200) + 71 / 100) := by
      have : 0 ≤ ratio := by linarith
      positivity
    rw [primBound]
    linarith

def SmallAt (ρ : ℝ) (k : ℕ) : Prop :=
  ρ * (primBound k + 3 * (steps k).sum * (1 + 2 * (nodeBound k + gradBound k))) ≤ 1 / 200

theorem block_bounds {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ 1 / 200) (hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖)
    (hD : ∀ u v, -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v)) :
    ∀ k, 1 ≤ k → (∀ j, 1 ≤ j → j < k → SmallAt ρ j) →
      BlockBound f g ρ k (nodeBound k) (gradBound k) (primBound k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
    intro hk hsmall
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 := level_one hρ hρ' hlip hD
      simpa [primBound] using h1
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hB := ih (by omega) (fun j hj1 hj2 => hsmall j hj1 (by omega))
      refine join_bound hρ hlip hD (k := m' + 1) (by omega) (nodeBound_ge _) (gradBound_nonneg _)
        (primBound_nonneg _) (hsmall (m' + 1) (by omega) (by omega)) hB ?_ ?_ ?_
      · apply le_of_eq
        unfold nodeBound
        rw [pow_succ]
        ring
      · apply le_of_eq
        unfold gradBound
        rw [pow_succ]
        ring
      · apply le_of_eq
        rw [show m' + 1 + 1 = m' + 2 from rfl, primBound]

lemma pow_steps_sum (k : ℕ) : (steps k).sum + 1 = ratio ^ k := by
  rw [steps_sum, sub_add_cancel]

lemma growth_le (k : ℕ) (hk : 3 ≤ k) :
    (1 + 13 / 2000) + (1 + 2 * ratio) * (θk k + 3 / 200) ≤ 343 / 100 := by
  have hb := ratio_bounds
  have : θk k = 2 / 5 := by unfold θk; simp [show ¬ k < 3 by omega]
  rw [this]
  nlinarith

lemma cross_le (k : ℕ) (hk : 3 ≤ k) :
    ratio * (steps k).sum *
        (106 / 100 + (3 + 8 * (nodeBound k + gradBound k)) * (θk k + 3 / 200)) +
      ratio * ((ratio - 2) * ((steps k).sum + 1) + 1) * (2 * (θk k + 3 / 200) + 71 / 100) ≤
      697 * ((101 / 100) * ratio) ^ k + 4 := by
  have hb := ratio_bounds
  have hθ : θk k = 2 / 5 := by unfold θk; simp [show ¬ k < 3 by omega]
  rw [hθ]
  have hS := pow_steps_sum k
  have hS0 := steps_sum_nonneg k
  set r := ratio ^ k with hr
  set w := (101 / 100 : ℝ) ^ k with hw
  have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
  have hr1 : 1 ≤ r := one_le_pow₀ (by linarith)
  have hmul : ((101 / 100) * ratio) ^ k = w * r := by rw [mul_pow]
  rw [hmul]
  have hsum : (steps k).sum = r - 1 := by linarith
  rw [hsum]
  unfold nodeBound gradBound
  rw [← hw]
  have hrel : ratio * ((ratio - 2) * (r - 1 + 1) + 1) = r + ratio := by
    have := ratio_square
    nlinarith
  have e1 : ratio * ((ratio - 2) * (r - 1 + 1) + 1) * (2 * (2 / 5 + 3 / 200) + 71 / 100) =
      (r + ratio) * (2 * (2 / 5 + 3 / 200) + 71 / 100) := by rw [hrel]
  rw [e1]
  have hwr : r ≤ w * r := by nlinarith
  have h1 : ratio * (w * r) ≤ 2414214 / 1000000 * (w * r) :=
    mul_le_mul_of_nonneg_right hb.2.le (mul_nonneg (by linarith) (by linarith))
  have h2 : ratio * r ≤ 2414214 / 1000000 * r := mul_le_mul_of_nonneg_right hb.2.le (by linarith)
  have h3 : 0 ≤ ratio * w := mul_nonneg (by linarith [hb.1]) (by linarith)
  have h4 : 0 ≤ ratio := by linarith
  nlinarith

lemma primBound_two : primBound 2 ≤ 2630 := by
  have hb := ratio_bounds
  have h1 : primBound 2 = primBound 1 * (1 + 13 / 2000) +
      (1 + 2 * ratio) * primBound 1 * (θk 1 + 3 / 200) +
      ratio * (steps 1).sum *
        (106 / 100 + (3 + 8 * (nodeBound 1 + gradBound 1)) * (θk 1 + 3 / 200)) +
      ratio * ((ratio - 2) * ((steps 1).sum + 1) + 1) * (2 * (θk 1 + 3 / 200) + 71 / 100) := by
    rfl
  rw [h1]
  have hp1 : primBound 1 = 250 := rfl
  have hθ : θk 1 = 3 / 5 := by unfold θk; norm_num
  have hs : (steps 1).sum = ratio - 1 := by rw [steps_one]; simp
  rw [hp1, hθ, hs]
  unfold nodeBound gradBound
  have hsq := ratio_square
  have hc1 : 0 ≤ ratio * (ratio - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hb.2.le hc1]

lemma primBound_three : primBound 3 ≤ 17200 := by
  have hb := ratio_bounds
  have h1 : primBound 3 = primBound 2 * (1 + 13 / 2000) +
      (1 + 2 * ratio) * primBound 2 * (θk 2 + 3 / 200) +
      ratio * (steps 2).sum *
        (106 / 100 + (3 + 8 * (nodeBound 2 + gradBound 2)) * (θk 2 + 3 / 200)) +
      ratio * ((ratio - 2) * ((steps 2).sum + 1) + 1) * (2 * (θk 2 + 3 / 200) + 71 / 100) := by
    rfl
  rw [h1]
  have hθ : θk 2 = 3 / 5 := by unfold θk; norm_num
  have hs : (steps 2).sum = ratio ^ 2 - 1 := steps_sum 2
  rw [hθ, hs]
  have h2 := primBound_two
  have h20 := primBound_nonneg 2
  unfold nodeBound gradBound
  have hsq := ratio_square
  have hg : (1 + 13 / 2000) + (1 + 2 * ratio) * (3 / 5 + 3 / 200) ≤ 4592 / 1000 := by nlinarith
  have hA : primBound 2 * (1 + 13 / 2000) + (1 + 2 * ratio) * primBound 2 * (3 / 5 + 3 / 200) ≤
      2630 * (4592 / 1000) := by nlinarith
  have hc2 : 0 ≤ ratio * (ratio ^ 2 - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hb.2.le hc2]

lemma primBound_le_aux (k : ℕ) (hk : 3 ≤ k) :
    primBound k ≤ 700 * (7 / 2) ^ k - 703 * ((101 / 100) * ratio) ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h3 := primBound_three
    have hb := ratio_bounds
    have : ((101 / 100) * ratio) ^ 3 ≤ 145 / 10 := by
      have h0 := pow_le_pow_left₀ (by linarith [hb.1] : (0:ℝ) ≤ 101 / 100 * ratio)
        (by linarith [hb.2] : 101 / 100 * ratio ≤ 101 / 100 * (2414214 / 1000000)) 3
      have h1 : ((101 : ℝ) / 100 * (2414214 / 1000000)) ^ 3 ≤ 145 / 10 := by norm_num
      linarith
    nlinarith
  | succ k hk ih =>
    have hb := ratio_bounds
    have hA0 := primBound_nonneg k
    have hg := growth_le k hk
    have hc := cross_le k hk
    have h1 : primBound (k + 1) = primBound k * (1 + 13 / 2000) +
        (1 + 2 * ratio) * primBound k * (θk k + 3 / 200) +
        ratio * (steps k).sum *
          (106 / 100 + (3 + 8 * (nodeBound k + gradBound k)) * (θk k + 3 / 200)) +
        ratio * ((ratio - 2) * ((steps k).sum + 1) + 1) * (2 * (θk k + 3 / 200) + 71 / 100) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rfl
    rw [h1]
    have hgA : primBound k * (1 + 13 / 2000) + (1 + 2 * ratio) * primBound k * (θk k + 3 / 200) ≤
        343 / 100 * primBound k := by nlinarith [mul_le_mul_of_nonneg_left hg hA0]
    set w := ((101 / 100) * ratio) ^ k with hw
    set t := (7 / 2 : ℝ) ^ k with ht
    have hw0 : 0 ≤ w := pow_nonneg (by linarith [hb.1]) k
    have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
    have hw' : ((101 / 100) * ratio) ^ (k + 1) = (101 / 100) * ratio * w := by rw [pow_succ]; ring
    have ht' : (7 / 2 : ℝ) ^ (k + 1) = 7 / 2 * t := by rw [pow_succ]; ring
    rw [hw', ht']
    have hrw : ratio * w ≤ 2414214 / 1000000 * w := mul_le_mul_of_nonneg_right hb.2.le hw0
    nlinarith

lemma primBound_le (k : ℕ) (hk : 1 ≤ k) : primBound k ≤ 700 * (7 / 2) ^ k := by
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | h3
  · norm_num [primBound]
  · have := primBound_two; norm_num; linarith
  · have h := primBound_le_aux k h3
    have : 0 ≤ ((101 / 100) * ratio) ^ k := by
      have hb := ratio_bounds
      exact pow_nonneg (by linarith [hb.1]) k
    linarith

lemma small_of_power {ρ : ℝ} (hρ : 0 ≤ ρ) {k : ℕ} (hk : 1 ≤ k)
    (h : ρ * (7 / 2) ^ k ≤ 1 / 250000) : SmallAt ρ k := by
  unfold SmallAt
  have hb := ratio_bounds
  have hA := primBound_le k hk
  have hS := pow_steps_sum k
  have hS0 := steps_sum_nonneg k
  have hwr : ((101 / 100) * ratio) ^ k ≤ (7 / 2) ^ k :=
    pow_le_pow_left₀ (by linarith [hb.1]) (by linarith) k
  have hsplit : 3 * (steps k).sum * (1 + 2 * (nodeBound k + gradBound k)) ≤
      519 * ((101 / 100) * ratio) ^ k := by
    unfold nodeBound gradBound
    rw [mul_pow]
    set r := ratio ^ k
    set w := (101 / 100 : ℝ) ^ k
    have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
    have hr1 : 1 ≤ r := one_le_pow₀ (by linarith)
    have hsum : (steps k).sum = r - 1 := by linarith
    rw [hsum]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ w - 1) (by linarith : (0:ℝ) ≤ r)]
  have htot : primBound k + 3 * (steps k).sum * (1 + 2 * (nodeBound k + gradBound k)) ≤
      1219 * (7 / 2) ^ k := by linarith
  have := mul_le_mul_of_nonneg_left htot hρ
  nlinarith

theorem block_descent {f : E → ℝ} {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖)
    (hD : ∀ u v, -ρ * ‖(u - g u) - (v - g v)‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v))
    {K : ℕ} (hK : 2 ≤ K) (hsmall : ρ * (7 / 2) ^ K ≤ 1 / 250000) (x0 : E) :
    ((steps K).sum + 1) * ‖g (run g (steps K) x0)‖ ^ 2 ≤
      4 * (f x0 - f (run g (steps K) x0)) := by
  have hb := ratio_bounds
  have hpowK : (1 : ℝ) ≤ (7 / 2) ^ K := one_le_pow₀ (by norm_num)
  have hρ' : ρ ≤ 1 / 200 := by
    have := mul_le_mul_of_nonneg_left hpowK hρ
    linarith
  have hsm : ∀ j, 1 ≤ j → j < K → SmallAt ρ j := by
    intro j hj1 hj2
    apply small_of_power hρ hj1
    have : (7 / 2 : ℝ) ^ j ≤ (7 / 2) ^ K := pow_le_pow_right₀ (by norm_num) hj2.le
    linarith [mul_le_mul_of_nonneg_left this hρ]
  have hB := block_bounds hρ hρ' hlip hD K (by omega) hsm
  obtain ⟨N, hN⟩ : ∃ N, N = run g (steps K) x0 := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨S, hS⟩ : ∃ S, S = (steps K).sum := ⟨_, rfl⟩
  rw [← hS]
  set σ2 := ‖x0 - (N - g N)‖ ^ 2 with hσ2
  have hIC : -(1 / 10) * (steps K).sum * ‖g (run g (steps K) x0)‖ ^ 2 - 0 ≤
      f (run g (steps K) x0) - (f N - ‖g N‖ ^ 2 / 2) := by
    rw [← hN, ← hS]
    have : 0 ≤ S := by rw [hS]; exact steps_sum_nonneg K
    linarith [mul_nonneg this (sq_nonneg ‖g N‖), sq_nonneg ‖g N‖]
  obtain ⟨hn, hP⟩ := hB x0 N σ2 0 le_rfl le_rfl hIC
  simp only [mul_zero, add_zero] at hn hP
  have hS2 : 2 ≤ S := by
    rw [hS, steps_sum]
    have : ratio ^ 2 ≤ ratio ^ K := pow_le_pow_right₀ (by linarith) hK
    have hsq := ratio_square
    linarith [hb.1]
  have hw : ∀ h ∈ steps K, 0 ≤ h := fun h hh => (steps_positive K h hh).le
  set n := nodeBound K
  set q := gradBound K
  have hn0 : 0 ≤ n := by have := nodeBound_ge K; linarith
  have hq0 : 0 ≤ q := gradBound_nonneg K
  have hM : ∀ w ∈ nodes g (steps K) x0,
      ‖(x0 - g x0) - (w - g w)‖ ^ 2 ≤ 8 * (n + q) * σ2 := by
    intro w hm
    have hx0 := hn x0 (start_mem_nodes g _ x0)
    have hw0 := hn w hm
    have e1 : (x0 - g x0) - (w - g w) =
        ((x0 - (N - g N)) + -g x0) + -((w - (N - g N)) + -g w) := by abel
    rw [e1]
    have h1 := sq_add_le_two ((x0 - (N - g N)) + -g x0) (-((w - (N - g N)) + -g w))
    have h2 := sq_add_le_two (x0 - (N - g N)) (-g x0)
    have h3 := sq_add_le_two (w - (N - g N)) (-g w)
    rw [norm_neg] at h1 h2 h3
    linarith [hx0.1, hx0.2, hw0.1, hw0.2]
  have hI := ref_identity_at f g (steps K) x0 N x0 hN
  have hDS := defectSum_weak hρ hD x0 (steps K) x0 hw _ hM
  rw [← hS] at hI hDS
  have hxx : ‖x0 - (x0 - g x0)‖ ^ 2 = ‖g x0‖ ^ 2 := by rw [sub_sub_cancel]
  rw [hxx] at hI
  have hσ : σ2 ≤ 3 * (‖N - (x0 - g x0)‖ ^ 2 + ‖g x0‖ ^ 2 + ‖g N‖ ^ 2) := by
    have e1 : x0 - (N - g N) = -(N - (x0 - g x0)) + g x0 + g N := by abel
    rw [hσ2, e1]
    have := sq_add_le_three (-(N - (x0 - g x0))) (g x0) (g N)
    rwa [norm_neg] at this
  have hA := primBound_le K (by omega)
  have hnq : S * (n + q) ≤ 86 * (7 / 2) ^ K := by
    have hS' : S + 1 = ratio ^ K := by rw [hS]; exact pow_steps_sum K
    have hwr : ((101 / 100) * ratio) ^ K ≤ (7 / 2) ^ K :=
      pow_le_pow_left₀ (by linarith [hb.1]) (by linarith) K
    rw [mul_pow] at hwr
    have hw1 : (1 : ℝ) ≤ (101 / 100) ^ K := one_le_pow₀ (by norm_num)
    have hr1 : (1 : ℝ) ≤ ratio ^ K := one_le_pow₀ (by linarith)
    have e2 : n + q = 86 * (101 / 100) ^ K := by
      simp only [n, q, nodeBound, gradBound]; ring
    rw [e2]
    have hS' : S ≤ ratio ^ K := by linarith
    have := mul_le_mul_of_nonneg_right hS' (by positivity : (0:ℝ) ≤ (101 / 100) ^ K)
    linarith
  have herr : ρ * (primBound K + 8 * S * (n + q)) ≤ 1 / 6 := by
    have h1 : primBound K + 8 * S * (n + q) ≤ 1388 * (7 / 2) ^ K := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hρ
    linarith
  have hσ0 : 0 ≤ σ2 := sq_nonneg _
  have herrσ : ρ * (primBound K + 8 * S * (n + q)) * σ2 ≤ 1 / 6 * σ2 :=
    mul_le_mul_of_nonneg_right herr hσ0
  have hg0 : 0 ≤ ‖g x0‖ ^ 2 := sq_nonneg _
  have hgN : 0 ≤ ‖g N‖ ^ 2 := sq_nonneg _
  have hSS : 1 ≤ S * (S + 1) := by
    have := mul_le_mul_of_nonneg_left hS2 (by linarith : (0:ℝ) ≤ S)
    linarith
  have key : S * (S + 1) * ‖g N‖ ^ 2 ≤ 4 * S * (f x0 - f N) := by
    have h1 : S * (S + 1) * ‖g N‖ ^ 2 ≥ ‖g N‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hSS hgN
      linarith
    have h2 : (S - 1) * ‖g x0‖ ^ 2 ≥ ‖g x0‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ S - 1) hg0
      linarith
    have h3 := sq_nonneg ‖N - (x0 - g x0)‖
    linarith
  have hSpos : 0 < S := by linarith
  have : S * ((S + 1) * ‖g N‖ ^ 2) ≤ S * (4 * (f x0 - f N)) := by linarith
  exact le_of_mul_le_mul_left this hSpos

end LongTails.Proofs.WeaklyConvexSilverInduction
