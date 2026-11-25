import LongTails.Proofs.NcConcaveReply
import LongTails.Proofs.NcConcaveValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveOracle

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcaveInstance
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveLocality
open LongTails.Proofs.NcConcaveAnalysis LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveReply LongTails.Proofs.NcConcaveValue
open LongTails.Proofs.AbcHardOracle (coin unif coin_integrable coin_integral coin_sq_integral setOf_le_measurable coin_measurable)
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {d n m : ℕ}

noncomputable def chainSq (g : CS n m) : ℝ := nsq g.1 g.2.1 g.2.2.1 g.2.2.2

lemma emb_add {k : ℕ} (π : Fin k → Fin d) (g h : Fin k → ℝ) (i : Fin d) :
    emb π (g + h) i = emb π g i + emb π h i := by
  simp only [emb, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

lemma emb_smul {k : ℕ} (π : Fin k → Fin d) (c : ℝ) (g : Fin k → ℝ) (i : Fin d) :
    emb π (c • g) i = c * emb π g i := by
  simp only [emb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

lemma embX_add (W : Word d n m) (g h : CS n m) : embX W (g + h) = embX W g + embX W h := by
  ext c
  simp only [embX, PiLp.toLp_apply, PiLp.add_apply, Prod.fst_add, Prod.snd_add, emb_add]
  split_ifs <;> ring

lemma embX_smul (W : Word d n m) (a : ℝ) (g : CS n m) : embX W (a • g) = a • embX W g := by
  ext c
  simp only [embX, PiLp.toLp_apply, PiLp.smul_apply, Prod.smul_fst, Prod.smul_snd, emb_smul,
    smul_eq_mul]
  split_ifs <;> ring

lemma embY_add (W : Word d n m) (g h : CS n m) : embY W (g + h) = embY W g + embY W h := by
  ext i
  simp only [embY, PiLp.toLp_apply, PiLp.add_apply, Prod.snd_add, Pi.add_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

lemma embY_smul (W : Word d n m) (a : ℝ) (g : CS n m) : embY W (a • g) = a • embY W g := by
  ext i
  simp only [embY, PiLp.toLp_apply, PiLp.smul_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

lemma embX_sub (W : Word d n m) (g h : CS n m) : embX W (g - h) = embX W g - embX W h := by
  rw [sub_eq_add_neg, embX_add, show -h = (-1 : ℝ) • h by simp, embX_smul]; simp [sub_eq_add_neg]

lemma embY_sub (W : Word d n m) (g h : CS n m) : embY W (g - h) = embY W g - embY W h := by
  rw [sub_eq_add_neg, embY_add, show -h = (-1 : ℝ) • h by simp, embY_smul]; simp [sub_eq_add_neg]

lemma embY_eq (W : Word d n m) (g : CS n m) :
    embY W g = WithLp.toLp 2 (emb2 (fun p : Fin n × Fin (m + 1) => W.πY p.1 p.2)
      (fun p => g.2.2.2 p.1 p.2)) := by
  ext i
  simp only [embY, emb2, PiLp.toLp_apply]
  rw [← Fintype.sum_prod_type']

lemma emb_norm (W : Word d n m) (g : CS n m) :
    ‖embX W g‖ ^ 2 + ‖embY W g‖ ^ 2 = chainSq g := by
  rw [norm_sq_prim, embY_eq, EuclideanSpace.real_norm_sq_eq]
  simp only
  rw [emb2_sq W.πY_inj]
  have h1 : blockSq (embX W g) 0 = sq1 g.1 := by
    have h := resid_split1 W.πU W.coords.hU g.1 (fun _ => (0 : ℝ)) 0
    simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    have e : blockSq (embX W g) 0 = ∑ i, emb W.πU g.1 i ^ 2 := by
      simp [blockSq, embX, PiLp.toLp_apply]
    rw [e]; exact h
  have h2 : blockSq (embX W g) 1 = sq2 g.2.1 + sq2 g.2.2.1 := by
    have h := resid_split2 W.πA W.πB W.coords.hA W.coords.hB W.coords.hAB g.2.1 g.2.2.1
      (fun _ => (0 : ℝ)) 0
    simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    have e : blockSq (embX W g) 1 = ∑ i, (emb W.πA g.2.1 i + emb W.πB g.2.2.1 i) ^ 2 := by
      simp [blockSq, embX, PiLp.toLp_apply]
    rw [e, h, Finset.sum_add_distrib]; rfl
  rw [h1, h2]
  unfold chainSq nsq sqY
  rw [Fintype.sum_prod_type]
  ring

noncomputable def oracleG (θ τ p : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) (ξ : ℝ) :
    Prim d × Dual d :=
  ((ℓ * s) • embX W (replyC θ τ p (selC W s x y) ξ), (ℓ * s) • embY W (replyC θ τ p (selC W s x y) ξ))

noncomputable def secretC (θ τ : ℝ) (c : CS n m) : CS n m :=
  if maskedPos m n (stage (θ / 2) c) then gradC θ τ c - knownC θ τ (stage (θ / 2) c) c else 0

lemma replyC_split (θ τ p : ℝ) (c : CS n m) (ξ : ℝ) :
    replyC θ τ p c ξ = gradC θ τ c + (coin p ξ - 1) • secretC θ τ c := by
  unfold replyC secretC
  split_ifs
  · rw [sub_smul, one_smul]; abel
  · simp

lemma oracleG_split (θ τ p : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) (ξ : ℝ) :
    oracleG θ τ p W s ℓ x y ξ = (gxh θ τ W s ℓ x y + (coin p ξ - 1) • ((ℓ * s) • embX W (secretC θ τ (selC W s x y))),
      gyh θ τ W s ℓ x y + (coin p ξ - 1) • ((ℓ * s) • embY W (secretC θ τ (selC W s x y)))) := by
  simp only [oracleG, replyC_split, embX_add, embY_add, embX_smul, embY_smul, smul_add, gxh, gyh]
  congr 1 <;> rw [smul_comm]

lemma oracleG_integrable (θ τ p : ℝ) (W : Word d n m) (s ℓ : ℝ) (x : Prim d) (y : Dual d) :
    Integrable (oracleG θ τ p W s ℓ x y) unif := by
  have hc : Integrable (fun ξ => coin p ξ - 1) unif := (coin_integrable p).sub (integrable_const _)
  rw [show oracleG θ τ p W s ℓ x y = fun ξ => oracleG θ τ p W s ℓ x y ξ from rfl]
  simp only [oracleG_split]
  exact ((integrable_const _).add (hc.smul_const _)).prodMk ((integrable_const _).add (hc.smul_const _))

lemma oracleG_integral (θ τ : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (W : Word d n m) (s ℓ : ℝ)
    (x : Prim d) (y : Dual d) :
    ∫ ξ, oracleG θ τ p W s ℓ x y ξ ∂unif = (gxh θ τ W s ℓ x y, gyh θ τ W s ℓ x y) := by
  have hc : Integrable (fun ξ => coin p ξ - 1) unif := (coin_integrable p).sub (integrable_const _)
  have hc0 : ∫ ξ, (coin p ξ - 1) ∂unif = 0 := by
    rw [integral_sub (coin_integrable p) (integrable_const _), coin_integral p hp0 hp1, integral_const,
      probReal_univ, one_smul, sub_self]
  simp only [oracleG_split]
  rw [integral_pair ((integrable_const _).add (hc.smul_const _)) ((integrable_const _).add (hc.smul_const _))]
  rw [integral_add (integrable_const _) (hc.smul_const _), integral_add (integrable_const _) (hc.smul_const _),
    integral_smul_const, integral_smul_const, hc0, integral_const, integral_const, probReal_univ,
    one_smul, one_smul, zero_smul, zero_smul, add_zero, add_zero]

lemma oracleG_variance (θ τ : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (W : Word d n m) (s ℓ : ℝ)
    (x : Prim d) (y : Dual d) :
    Integrable (fun ξ => ‖(oracleG θ τ p W s ℓ x y ξ).1 - gxh θ τ W s ℓ x y‖ ^ 2 +
      ‖(oracleG θ τ p W s ℓ x y ξ).2 - gyh θ τ W s ℓ x y‖ ^ 2) unif ∧
    ∫ ξ, (‖(oracleG θ τ p W s ℓ x y ξ).1 - gxh θ τ W s ℓ x y‖ ^ 2 +
      ‖(oracleG θ τ p W s ℓ x y ξ).2 - gyh θ τ W s ℓ x y‖ ^ 2) ∂unif =
      (1 / p - 1) * ((ℓ * s) ^ 2 * chainSq (secretC θ τ (selC W s x y))) := by
  set S := secretC θ τ (selC W s x y)
  have he : (fun ξ => ‖(oracleG θ τ p W s ℓ x y ξ).1 - gxh θ τ W s ℓ x y‖ ^ 2 +
      ‖(oracleG θ τ p W s ℓ x y ξ).2 - gyh θ τ W s ℓ x y‖ ^ 2) =
      fun ξ => (coin p ξ - 1) ^ 2 * ((ℓ * s) ^ 2 * chainSq S) := by
    funext ξ
    simp only [oracleG_split, add_sub_cancel_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [← emb_norm W S]; ring
  rw [he]
  refine ⟨?_, ?_⟩
  · have hi : Integrable (fun ξ => (coin p ξ - 1) ^ 2) unif := by
      have he2 : (fun ξ => (coin p ξ - 1) ^ 2) =
          fun ξ => Set.indicator {ω | ω ≤ p} (fun _ => (1 / p - 1) ^ 2 - 1) ξ + 1 := by
        funext ξ; simp only [coin, Set.indicator, Set.mem_ofPred_eq]; split_ifs <;> ring
      rw [he2]
      exact ((integrable_const _).indicator (setOf_le_measurable _)).add (integrable_const _)
    exact hi.mul_const _
  · rw [integral_mul_const, coin_sq_integral p hp0 hp1]

end LongTails.Proofs.NcConcaveOracle
