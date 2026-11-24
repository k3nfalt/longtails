import LongTails.Proofs.NcConcaveParams
import LongTails.Proofs.NcConcaveCounting
import LongTails.Proofs.NcConcaveMeasurable
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveAssembly

open Classical
open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcavePsi LongTails.Proofs.NcConcavePartTwo
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveReply LongTails.Proofs.NcConcaveValue
open LongTails.Proofs.NcConcaveOracle LongTails.Proofs.NcConcaveSecret
open LongTails.Proofs.NcConcaveExecution LongTails.Proofs.NcConcaveCounting
open LongTails.Proofs.NcConcaveMeasurable LongTails.Proofs.NcConcaveFailure
open LongTails.Proofs.NcConcaveParams
open LongTails.Proofs.AbcHardOracle (coin unif coin_integrable coin_integral coin_sq_integral setOf_le_measurable coin_measurable)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure (stream stream_iid coinCount_tail coinCount_measurable)
open LongTails.Proofs.SmoothConvexFiniteHiding (largeSet not_largeSet_small bounded_prefix_bad_count)
open LongTails.Proofs.FiniteSumNondualLowerHiding (hits distinctWords)
open LongTails.Proofs.FiniteSumNondualLowerAveraging (CoordinateWords coordinateEmbedding coordinateEmbedding_labels subtype_indicator_sum)
open LongTails.Proofs.FiniteSumNondualLowerBound (coordinateWords_card_pos)
open LongTails.Proofs.NcConcaveGadgets LongTails.Proofs.NcConcaveTransitionBounds
open LongTails.Setups.StochasticNonconvexConcaveMinimax

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace

noncomputable def hardF (q : Params) (W : Word q.d (nOf q) (mOf q)) : Prim q.d → Dual q.d → ℝ :=
  fhat (θOf q) (alpha (mOf q)) W (sOf q) (ℓOf q)

noncomputable def hardG (q : Params) (W : Word q.d (nOf q) (mOf q)) :
    Prim q.d → Dual q.d → ℝ → Prim q.d × Dual q.d :=
  oracleG (θOf q) (alpha (mOf q)) (pOf q) W (sOf q) (ℓOf q)

noncomputable def hardOracle (q : Params) (W : Word q.d (nOf q) (mOf q)) :
    Oracle (spec.Query q) (spec.Reply q) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, z) ω => hardG q W z.1.1 z.1.2 ω

section valid

variable {q : Params} (hv : spec.valid q)
include hv

omit hv in
lemma primal_block {x : Prim q.d} (hx : x ∈ primalSet q) : blockSq x 1 ≤ (2 * sOf q) ^ 2 := by
  have := hx.2; rwa [radiusAB_eq] at this

omit hv in
lemma psi_zero : psi (0 : Fin (nOf q + 1) → ℝ) 0 0 = 0 := by
  have hq : LongTails.Proofs.NcConcaveTransitions.q (0 : Fin (nOf q + 1) → ℝ) = 0 := by
    funext i; simp [LongTails.Proofs.NcConcaveTransitions.q, nu_of_nonpos]
  have hrho : rho (0 : Fin (nOf q + 1) → ℝ) = 0 := by
    funext i; simp [rho, hq]
  simp [psi, hpart, rb, hrho, rr_zero, nu_of_nonpos]

omit hv in
lemma robB_y0 (θ τ : ℝ) (hθ : 0 < θ) (a b : ℝ) :
    robB (m := mOf q) θ τ a b (fun _ => 0) = -(alpha (mOf q) ^ 2 * (mOf q : ℝ) * zeta θ b ^ 2 / 8) := by
  have hz : zeta θ 0 = 0 := LongTails.Proofs.NcConcaveGadgets.zeta_small hθ (by simp [hθ.le])
  have hz2 : zeta (2 * θ) 0 = 0 :=
    LongTails.Proofs.NcConcaveGadgets.zeta_small (by linarith) (by simp; linarith)
  have hω : LongTails.Proofs.NcConcaveGadgets.omega θ 0 = 0 :=
    LongTails.Proofs.NcConcaveGadgets.omega_small hθ (by simp [hθ.le])
  have hH : LongTails.Proofs.NcConcaveHuber.huber τ 0 = 0 := by
    simp [LongTails.Proofs.NcConcaveHuber.huber, LongTails.Proofs.SmoothConvexFiniteGeometry.ramp]
  simp only [robB, beta, sub_self, hz, hz2, hω, hH, mul_zero, Finset.sum_const_zero,
    zero_pow (two_ne_zero), sub_zero, add_zero]
  ring

omit hv in
lemma robF_y0_lower {θ τ : ℝ} (hθ : 0 < θ)
    (u : Fin (nOf q + 1) → ℝ) (a b : Fin (nOf q) → ℝ) (U : ℝ) (hU0 : 0 ≤ U)
    (hu : ∀ j, |u j| ≤ U) (hsq : sq1 u ≤ U ^ 2) (ha : sq2 a ≤ 2 ^ 2) (hb : sq2 b ≤ 2 ^ 2) :
    -cη * (U + nOf q) - 2 - 2 * U - 2 * θ * nOf q * U - 1 / 2 ≤
      robF (m := mOf q) θ τ u a b (fun _ _ => 0) := by
  have hc : (0 : ℝ) < cη := by norm_num [cη]
  have hn0 : (0 : ℝ) ≤ nOf q := Nat.cast_nonneg _
  unfold robF
  simp only [robB_y0 θ τ hθ]
  have hblk : -(1 / 2 : ℝ) ≤ ∑ i, -(alpha (mOf q) ^ 2 * (mOf q : ℝ) * zeta θ (b i) ^ 2 / 8) := by
    have hα2 : alpha (mOf q) ^ 2 * (mOf q : ℝ) ≤ 1 := by
      rw [alpha_sq, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    have hpt : ∀ i, -(b i ^ 2 / 8) ≤ -(alpha (mOf q) ^ 2 * (mOf q : ℝ) * zeta θ (b i) ^ 2 / 8) := by
      intro i
      have hz : zeta θ (b i) ^ 2 ≤ b i ^ 2 := by
        have := LongTails.Proofs.NcConcaveC11.zeta_lip hθ (b i) 0
        rw [LongTails.Proofs.NcConcaveGadgets.zeta_small (t := 0) hθ (by rw [abs_zero]; exact hθ.le), sub_zero, sub_zero] at this
        rw [← sq_abs, ← sq_abs (b i)]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have h0 : 0 ≤ alpha (mOf q) ^ 2 * (mOf q : ℝ) := by positivity
      nlinarith [sq_nonneg (zeta θ (b i))]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    simp only [Finset.sum_neg_distrib, ← Finset.sum_div] at hs ⊢
    have : (∑ i, b i ^ 2) ≤ 4 := by unfold sq2 at hb; linarith
    linarith
  have h1 : ∑ j : Fin (nOf q), nu (zeta θ (u j.succ)) ≤ nOf q := by
    calc _ ≤ ∑ _j : Fin (nOf q), (1 : ℝ) := Finset.sum_le_sum fun j _ => nu_le_one _
      _ = nOf q := by simp
  have h2 : 0 ≤ ∑ j, rr (zeta θ (u j)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ i, zeta θ (a i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : 0 ≤ ∑ i, rho (zu θ u) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h5 : 0 ≤ ∑ i, zeta θ (b i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h6 : 0 ≤ ∑ i : Fin (nOf q), rr (zeta θ (u i.succ)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h7 : ∑ i, a i * rho (zu θ u) i ≤ 2 := by
    have hcs := cs_bound a (rho (zu θ u))
    have hsa : Real.sqrt (sq2 a) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; exact ha
    have hsr : Real.sqrt (sq2 (rho (zu θ u))) ≤ 1 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith [sq2_rho_le_one (zu θ u)]
    have := le_abs_self (∑ i, a i * rho (zu θ u) i)
    nlinarith [Real.sqrt_nonneg (sq2 a), Real.sqrt_nonneg (sq2 (rho (zu θ u))),
      mul_le_mul hsa hsr (Real.sqrt_nonneg _) (by norm_num)]
  have h8 : ∑ i, betaR θ (b i) (u i.succ) ≤ 2 * U + 2 * θ * nOf q * U := by
    have hpt : ∀ i, betaR θ (b i) (u i.succ) ≤ |b i| * |u i.succ| + 2 * θ * U := by
      intro i
      have hz := LongTails.Proofs.NcConcaveGadgets.zeta_sub_le (θ := θ) (t := b i) hθ
      rw [abs_sub_comm] at hz
      have hzb : |zeta θ (b i)| ≤ |b i| := by
        have := LongTails.Proofs.NcConcaveC11.zeta_lip hθ (b i) 0
        rwa [LongTails.Proofs.NcConcaveGadgets.zeta_small (t := 0) hθ (by rw [abs_zero]; exact hθ.le), sub_zero, sub_zero] at this
      have hr1 := abs_rr_le (u i.succ)
      have hr2 : |rr (zeta θ (u i.succ))| ≤ U := by
        have := LongTails.Proofs.NcConcaveC11.zeta_lip hθ (u i.succ) 0
        rw [LongTails.Proofs.NcConcaveGadgets.zeta_small (t := 0) hθ (by rw [abs_zero]; exact hθ.le), sub_zero, sub_zero] at this
        exact (abs_rr_le _).trans (this.trans (hu i.succ))
      have e : betaR θ (b i) (u i.succ) ≤ |zeta θ (b i) * rr (u i.succ)| +
          |(b i - zeta θ (b i)) * rr (zeta θ (u i.succ))| := by
        unfold betaR
        exact (le_abs_self _).trans (abs_add_le _ _)
      rw [abs_mul, abs_mul] at e
      have := mul_le_mul hzb hr1 (abs_nonneg _) (abs_nonneg _)
      have := mul_le_mul hz hr2 (abs_nonneg _) (by positivity)
      linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (nOf q)))) => hpt i)
    rw [Finset.sum_add_distrib] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hcs : ∑ i, |b i| * |u i.succ| ≤ 2 * U := by
      have h := cs_bound (fun i => |b i|) (fun i => |u i.succ|)
      have e1 : sq2 (fun i => |b i|) = sq2 b := by simp [sq2, sq_abs]
      have e2 : sq2 (fun i : Fin (nOf q) => |u i.succ|) ≤ U ^ 2 := by
        have := sum_succ_le u
        simp only [sq2, sq_abs]; exact this.trans hsq
      rw [e1] at h
      have hsb : Real.sqrt (sq2 b) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; exact hb
      have hsu : Real.sqrt (sq2 fun i : Fin (nOf q) => |u i.succ|) ≤ U := by
        rw [Real.sqrt_le_left hU0]; exact e2
      have := le_abs_self (∑ i, |b i| * |u i.succ|)
      nlinarith [Real.sqrt_nonneg (sq2 b), Real.sqrt_nonneg (sq2 fun i : Fin (nOf q) => |u i.succ|),
        mul_le_mul hsb hsu (Real.sqrt_nonneg _) (by norm_num)]
    nlinarith
  have hu0' := hu 0
  have hA : cη * u 0 ≤ cη * U := mul_le_mul_of_nonneg_left (by linarith [le_abs_self (u 0)]) hc.le
  have hB : cη * ∑ j : Fin (nOf q), nu (zeta θ (u j.succ)) ≤ cη * nOf q :=
    mul_le_mul_of_nonneg_left h1 hc.le
  have hC : 0 ≤ cη / 2 * ∑ j, rr (zeta θ (u j)) ^ 2 := mul_nonneg (by linarith) h2
  unfold robP
  linarith

theorem hard_gap (W : Word q.d (nOf q) (mOf q)) :
    value (hardF q W) 0 - sInf ((fun x => hardF q W x 0) '' primalSet q) ≤ q.Δ := by
  set s := sOf q
  set ℓ := ℓOf q
  have hs := s_pos hv
  have hl := ℓ_pos hv
  have hθ := θ_pos hv
  have hθ1 := θ_le_one hv
  have hτ := alpha_pos (mOf q)
  have hη0 := η_nonneg hv
  have hXe : primalSet q = primBall (radiusU q) (2 * s) := by
    simp only [primalSet, primBall, radiusAB_eq]; rfl
  have h0 : (0 : Prim q.d) ∈ primalSet q := by rw [hXe]; exact zero_mem_primBall _ _
  have hphi0 : phiW W.coords s ℓ 0 = 0 := by
    have e1 : selU W.coords s (0 : Prim q.d) = fun _ => 0 := by funext j; simp [selU]
    have e2 : selA W.coords s (0 : Prim q.d) = fun _ => 0 := by funext j; simp [selA]
    have e3 : selB W.coords s (0 : Prim q.d) = fun _ => 0 := by funext j; simp [selB]
    have : psi (fun _ : Fin (nOf q + 1) => (0 : ℝ)) (fun _ => 0) (fun _ => 0) = 0 := psi_zero
    unfold phiW
    rw [e1, e2, e3, this, mul_zero]
  have hv0 : value (hardF q W) 0 ≤ ηOf q := by
    have := (abs_le.mp (Vf_close W hs hl.le hθ hθ1 le_rfl (by
      have := alpha_le_one (mOf q); linarith) (radiusU_pos hv).le le_rfl (hD8 hv) (hD hv).le 0
        (by rw [← hXe]; exact h0))).2
    simp only [Vf] at this
    rw [hphi0, sub_zero] at this
    exact this
  set U := radiusU q / s
  have hU0 : 0 ≤ U := div_nonneg (radiusU_pos hv).le hs.le
  set lowR := -cη * (U + nOf q) - 2 - 2 * U - 2 * θOf q * nOf q * U - 1 / 2
  have hlow : ∀ z ∈ primalSet q, ℓ * s ^ 2 * lowR ≤ hardF q W z 0 := by
    intro z hz
    have hzX : z ∈ primBall (radiusU q) (2 * s) := by rw [← hXe]; exact hz
    obtain ⟨ha, hb⟩ := selC_bounds_feasible W hs z 0 hzX.2
    have hsq : sq1 (selC W s z 0).1 ≤ U ^ 2 := by
      have : sq1 (selC W s z 0).1 ≤ blockSq z 0 / s ^ 2 := by
        simp only [selC, sq1, div_pow, ← Finset.sum_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact LongTails.Proofs.NcConcaveAnalysis.sum_comp_le W.πU W.coords.hU (fun i => z (0, i) ^ 2)
          (fun _ => sq_nonneg _)
      refine this.trans ?_
      simp only [U, div_pow]
      exact div_le_div_of_nonneg_right hzX.1 (by positivity)
    have hu : ∀ j, |(selC W s z 0).1 j| ≤ U := by
      intro j
      have h1 : (selC W s z 0).1 j ^ 2 ≤ sq1 (selC W s z 0).1 :=
        Finset.single_le_sum (f := fun j => (selC W s z 0).1 j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      exact abs_le.mpr (abs_le_of_sq_le_sq' (h1.trans hsq) hU0)
    have hb2 : sq2 (selC W s z 0).2.2.1 ≤ 2 ^ 2 := by
      have h2 : sq2 (selC W s z 0).2.1 + sq2 (selC W s z 0).2.2.1 ≤ blockSq z 1 / s ^ 2 := by
        simp only [selC, sq2, div_pow, ← Finset.sum_div, ← add_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [blockSq_eq, split_sum2 W.πA W.πB W.coords.hA W.coords.hB W.coords.hAB (fun i => z (1, i) ^ 2)]
        have : 0 ≤ ∑ i ∈ (Finset.univ.map ⟨W.πA, W.coords.hA⟩ ∪ Finset.univ.map ⟨W.πB, W.coords.hB⟩)ᶜ,
            z (1, i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      have h4 : blockSq z 1 / s ^ 2 ≤ 2 ^ 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith [hzX.2]
      linarith [sq2_nonneg (selC W s z 0).2.1]
    have hy0 : (selC W s z 0).2.2.2 = fun _ _ => 0 := by
      funext i k; simp [selC]
    have hr := robF_y0_lower (τ := alpha (mOf q)) hθ (selC W s z 0).1 (selC W s z 0).2.1 (selC W s z 0).2.2.1
      U hU0 hu hsq ha hb2
    simp only [hardF, fhat, Fc]
    rw [hy0]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hne : ((fun x => hardF q W x 0) '' primalSet q).Nonempty := ⟨_, Set.mem_image_of_mem _ h0⟩
  have hinf : ℓ * s ^ 2 * lowR ≤ sInf ((fun x => hardF q W x 0) '' primalSet q) :=
    le_csInf hne (by rintro _ ⟨z, hz, rfl⟩; exact hlow z hz)
  have hε := hε hv; have hL := hL hv; have hΔ := hΔ hv
  have hc : cη = 10000 := rfl
  have hℓs : ℓ * s = 2 ^ 32 * q.ε / 2401500 := ℓs_eq hv
  have hl' : ℓ = q.L / (6 * 400250) := by simp only [ℓ, ℓOf, cF2_eq]
  have hsq : q.ε * Real.sqrt (q.Δ / q.L) ≤ q.Δ / 2 ^ 33 := by
    have h1 : (q.ε * Real.sqrt (q.Δ / q.L)) ^ 2 = q.ε ^ 2 * (q.Δ / q.L) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h2 : q.ε ^ 2 * (q.Δ / q.L) ≤ (q.Δ / 2 ^ 33) ^ 2 := by
      have := hΛ1 hv
      rw [div_pow, mul_div_assoc', div_le_div_iff₀ hL (by norm_num)]
      nlinarith
    have h0 : 0 ≤ q.Δ / 2 ^ 33 := by positivity
    have h3 : (q.ε * Real.sqrt (q.Δ / q.L)) ^ 2 ≤ (q.Δ / 2 ^ 33) ^ 2 := by rw [h1]; exact h2
    exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).mp h3
  have hsU : ℓ * s ^ 2 * U ≤ q.Δ / 30000 := by
    have e : ℓ * s ^ 2 * U = ℓ * s * radiusU q := by simp only [U]; field_simp
    rw [e, hℓs]
    have hR : radiusU q = 2 ^ 7 * Real.sqrt (q.Δ / q.L) := rfl
    rw [hR]
    have : 2 ^ 32 * q.ε / 2401500 * (2 ^ 7 * Real.sqrt (q.Δ / q.L)) =
        2 ^ 39 / 2401500 * (q.ε * Real.sqrt (q.Δ / q.L)) := by ring
    rw [this]
    have hk : (2 ^ 39 / 2401500 / 2 ^ 33 : ℝ) ≤ 1 / 30000 := by norm_num
    calc _ ≤ 2 ^ 39 / 2401500 * (q.Δ / 2 ^ 33) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (2 ^ 39 / 2401500 / 2 ^ 33) * q.Δ := by ring
      _ ≤ q.Δ / 30000 := by nlinarith
  have hls : ℓ * s ^ 2 ≤ q.Δ / 2 ^ 24 := by
    have e : ℓ * s ^ 2 = (ℓ * s) ^ 2 / ℓ := by field_simp
    rw [e, hℓs, hl']
    have := hΛ1 hv
    rw [div_div_eq_mul_div, div_le_div_iff₀ hL (by norm_num)]
    nlinarith
  have hsn : ℓ * s ^ 2 * (nOf q : ℝ) ≤ q.Δ / 30000 := by
    have hn := n_succ_le hv
    have hn' : (nOf q : ℝ) ≤ Λ1 q / 2 ^ 58 := by linarith
    have e : ℓ * s ^ 2 = (ℓ * s) ^ 2 / ℓ := by field_simp
    rw [e, hℓs, hl']
    calc (2 ^ 32 * q.ε / 2401500) ^ 2 / (q.L / (6 * 400250)) * (nOf q : ℝ) ≤
        (2 ^ 32 * q.ε / 2401500) ^ 2 / (q.L / (6 * 400250)) * (Λ1 q / 2 ^ 58) :=
          mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = 2 ^ 64 * (6 * 400250) / (2401500 ^ 2 * 2 ^ 58) * q.Δ := by
          unfold Λ1; field_simp
      _ ≤ q.Δ / 30000 := by
          have hk : (2 ^ 64 * (6 * 400250) / (2401500 ^ 2 * 2 ^ 58) : ℝ) ≤ 1 / 30000 := by norm_num
          nlinarith
  have hθnU : θOf q * nOf q * U ≤ 1 := by
    have h1 := Λ1Λ2_ge hv
    have hn := n_succ_le' hv
    have hU := U_le hv
    have hn0 : (0 : ℝ) ≤ nOf q := Nat.cast_nonneg _
    have hnU : (nOf q : ℝ) * U ≤ Λ1 q ^ 3 * Λ2 q := by
      have hL1 := Λ1_ge_one hv; have hL2 := Λ2_ge_one hv
      have : (nOf q : ℝ) * U ≤ Λ1 q * Λ1 q := mul_le_mul (by linarith) hU hU0 (by linarith)
      have : Λ1 q * Λ1 q ≤ Λ1 q ^ 3 * Λ2 q := by
        have : Λ1 q * Λ1 q ≤ Λ1 q ^ 3 := by nlinarith
        nlinarith [pow_nonneg (show (0:ℝ) ≤ Λ1 q by linarith) 3]
      linarith
    have hθe : θOf q = 1 / 2 ^ 90 / (Λ1 q ^ 3 * Λ2 q) := by unfold θOf; field_simp
    rw [mul_assoc, hθe, div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  have hη : ηOf q ≤ ℓ * s ^ 2 * (1 / 2 ^ 73) := by
    unfold ηOf; exact mul_le_mul_of_nonneg_left (θCB_le hv) (by positivity)
  have e2 : -(ℓ * s ^ 2 * lowR) = 10000 * (ℓ * s ^ 2 * U) + 10000 * (ℓ * s ^ 2 * nOf q) +
      (5 / 2) * (ℓ * s ^ 2) + 2 * (ℓ * s ^ 2 * U) + 2 * (ℓ * s ^ 2) * (θOf q * nOf q * U) := by
    simp only [lowR, hc]; ring
  have hls0 : 0 ≤ ℓ * s ^ 2 := by positivity
  have h3 : 2 * (ℓ * s ^ 2) * (θOf q * nOf q * U) ≤ 2 * (ℓ * s ^ 2) := by nlinarith
  nlinarith

theorem hard_admissible (W : Word q.d (nOf q) (mOf q)) :
    spec.admissible q (hardF q W) (hardOracle q W) := by
  have hs := s_pos hv
  have hl := ℓ_pos hv
  have hθ := θ_pos hv
  have hθ1 := θ_le_one hv
  have hτ := alpha_pos (mOf q)
  have hp0 := p_pos hv
  have hp1 := p_le_one hv
  refine ⟨gxh (θOf q) (alpha (mOf q)) W (sOf q) (ℓOf q), gyh (θOf q) (alpha (mOf q)) W (sOf q) (ℓOf q),
    ⟨unif, inferInstance⟩, ⟨stream, inferInstance⟩, hardG q W, stream_iid, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact ⟨fhat_hasGradientAt_x hθ hθ1 hτ W hs hl.le x y, fhat_hasGradientAt_y hθ hθ1 hτ W hs hl.le x y⟩
  · intro x hx x' hx' y _ y' _
    have h := fhat_lipschitz hθ hθ1 hτ W hs hl.le x x' y y' (primal_block hx) (primal_block hx')
    rw [L_eq]; exact h
  · intro x _
    exact fhat_concave hθ hτ W hs hl.le x _ (convex_closedBall _ _)
  · exact hard_gap hv W
  · exact oracleG_measurable hθ hθ1 hτ (pOf q) W (sOf q) (ℓOf q)
  · intro x hx y _
    obtain ⟨hvi, hve⟩ := oracleG_variance (θOf q) (alpha (mOf q)) hp0 hp1 W (sOf q) (ℓOf q) x y
    refine ⟨oracleG_integrable _ _ _ W _ _ x y, oracleG_integral _ _ hp0 hp1 W _ _ x y, hvi, ?_⟩
    refine (le_of_eq hve).trans ?_
    apply variance_le hv
    · have h1 := secret_bound hθ hθ1 hτ W hs x y (primal_block hx)
      have h2 := θ_secret hv
      nlinarith

omit hv in
lemma trueState_iterate {St : Type*} (G : Prim q.d × Dual q.d → ℝ → Prim q.d × Dual q.d)
    (qry : St → Prim q.d × Dual q.d) (upd : St → Prim q.d × Dual q.d → St) (init : St)
    (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (upd sc.1 (G (qry sc.1) (ω sc.2)), sc.2 + 1))^[N] (init, 0)) =
      (trueState G qry upd init ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

omit hv in
lemma execute_hard (W : Word q.d (nOf q) (mOf q))
    (A : Algorithm (spec.Query q) (spec.Reply q) (spec.Output q)) (N : ℕ) (seed : A.Seed)
    (ω : ℕ → ℝ) :
    execute (hardOracle q W) A (fun _ => N) seed ω =
      A.output (trueState (fun z ξ => hardG q W z.1 z.2 ξ) (fun st => (A.query st).2.1) A.update
        (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (hardOracle q W) A N seed ω
    (fun t query => hardG q W query.2.1.1 query.2.1.2 (ω t)) (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (trueState_iterate (q := q)
    (fun z ξ => hardG q W z.1 z.2 ξ) (fun st => (A.query st).2.1) A.update (A.initial seed) ω N)

lemma stationarity_nonneg (f : Prim q.d → Dual q.d → ℝ) (x : Prim q.d) : 0 ≤ stationarity f x := by
  unfold stationarity
  have := hL hv
  exact mul_nonneg (by linarith) Metric.infDist_nonneg

lemma output_condition (W : Word q.d (nOf q) (mOf q)) (x : Prim q.d)
    (h : ‖obsVec (sOf q) (x, (0 : Dual q.d))‖ ≤ Real.sqrt (Bsq q) →
      |x (0, W.πU (Fin.last (nOf q)))| ≤ θOf q / 2 * sOf q) :
    |x (0, W.πU (Fin.last (nOf q)))| ≤ θOf q / 2 * sOf q ∨
      2 * Real.sqrt (radiusU q ^ 2 + (2 * sOf q) ^ 2) ≤ ‖x‖ := by
  by_cases hb : ‖obsVec (sOf q) (x, (0 : Dual q.d))‖ ≤ Real.sqrt (Bsq q)
  · exact Or.inl (h hb)
  · right
    push Not at hb
    by_contra hc
    push Not at hc
    have hs := s_pos hv
    have h1 := obsVec_norm hs (x, (0 : Dual q.d))
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h1
    have h2 : ‖x‖ ^ 2 < 4 * (radiusU q ^ 2 + (2 * sOf q) ^ 2) := by
      have h0 : 0 ≤ ‖x‖ := norm_nonneg _
      have hr := Real.sq_sqrt (show (0 : ℝ) ≤ radiusU q ^ 2 + (2 * sOf q) ^ 2 by positivity)
      nlinarith [Real.sqrt_nonneg (radiusU q ^ 2 + (2 * sOf q) ^ 2)]
    have h3 : 3 * ‖x‖ ^ 2 / sOf q ^ 2 ≤ Bsq q := by
      unfold Bsq
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := sq_nonneg q.D
      nlinarith
    have h4 : ‖obsVec (sOf q) (x, (0 : Dual q.d))‖ ^ 2 < Bsq q := by
      have h5 : 3 * ‖x‖ ^ 2 / sOf q ^ 2 < Bsq q := by
        unfold Bsq
        apply div_lt_div_of_pos_right _ (by positivity)
        have := sq_nonneg q.D
        nlinarith
      linarith
    have hB0 : 0 ≤ Bsq q := by unfold Bsq; have := radiusU_pos hv; positivity
    have := Real.sq_sqrt hB0
    nlinarith [norm_nonneg (obsVec (sOf q) (x, (0 : Dual q.d))), Real.sqrt_nonneg (Bsq q)]

end valid

end LongTails.Proofs.NcConcaveAssembly
