import LongTails.Proofs.InterpolatedFiniteSumBlockOracle
import LongTails.Proofs.InterpolatedFiniteSumSmoothParameters
import LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open OracleTemplate MeasureTheory Classical

namespace LongTails.Proofs.InterpolatedFiniteSumSmoothLower

open LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
open InterpolatedFiniteSumBlocks InterpolatedFiniteSumBlockOracle
open InterpolatedFiniteSumHiddenComponent

set_option maxHeartbeats 1600000 in
lemma failure_of_scales (p : Params) (hp : spec.valid p) {k : ℕ}
    (fallback : (Fin p.n × Fin (k + 1)) ↪ Fin p.d) (carrier : Fin p.d)
    (c σ r G W B θ : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hRr : p.R ≤ r)
    (hG : 0 < G) (hW : 0 < W) (hBpos : 0 ≤ B) (hθ : 0 < θ) (hθσ : θ ≤ σ / 8)
    (hgeom : (p.n : ℝ) * (k + 1 : ℕ) ^ 3 * σ ^ 2 ≤ p.R ^ 2)
    (hwidth : 64 * G ^ 2 ≤ W * p.L0) (hrad : 4 * G / r ≤ p.L0 / 3)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hcurv : 12 * c / σ ^ 2 ≤ p.L0 / 3)
    (hgap : (k + 1 : ℕ) * c / 2 ≤ p.Δ)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (hA : 0 ≤ (k + 1 : ℕ) * c / 2 - c * θ / σ)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hdim : 8 * (((p.n : ℝ) * (k + 1 : ℕ)) ^ 2 + p.n * (k + 1 : ℕ) +
      (b + 1 : ℕ) * p.n * (k + 1 : ℕ) * (B ^ 2 / θ ^ 2)) ≤ p.d)
    (hloss : p.ε < 7 * ((k + 1 : ℕ) * c / 2 - c * θ / σ) / 8 - c * b / (2 * p.n)) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let : Nonempty (Fin p.d) := ⟨carrier⟩
  have hn : 0 < p.n := by have := hp.2.2.2.2.1; omega
  have hd : (0 : ℝ) < p.d := by exact_mod_cast (show 0 < p.d from Nat.zero_lt_of_lt carrier.isLt)
  have hr : 0 < r := hp.2.2.1.trans_le hRr
  let emb := fun π : (Fin p.n × Fin (k + 1)) → Fin p.d => safeEmbedding fallback carrier π
  let f := fun π i => shielded (block (emb π) i) c σ r G W
  let g := fun π i => shieldedField (block (emb π) i) c σ r G W
  let z := fun π => minimizer (emb π) σ
  have hzR (π : (Fin p.n × Fin (k + 1)) → Fin p.d) : ‖z π‖ ≤ p.R := by
    have hh := (minimizer_norm_sq (emb π) σ hσ.le).trans hgeom
    dsimp [z]
    nlinarith [norm_nonneg (minimizer (emb π) σ), hp.2.2.1]
  have hAd (π : (Fin p.n × Fin (k + 1)) → Fin p.d) :
      spec.admissible p (f π) (exactOracle p (f π) (g π)) :=
    InterpolatedFiniteSumBlocks.admissible p hp (emb π) c σ r G W hc hσ hr hG.le hW
      hwidth hrad hgrad hcurv ((hzR π).trans hRr) (hzR π) hgap
  apply finite_prior_failure p f g z hAd
    (fun π i x => shielded_nonnegative (block (emb π) i) c σ r G W hc hW x)
    (fun π i => shielded_minimizer_value (emb π) c σ r G W hc hσ hr hG.le hW
      ((hzR π).trans hRr) i) A b
    (7 * ((k + 1 : ℕ) * c / 2 - c * θ / σ) / 8 - c * b / (2 * p.n)) hloss
  intro seed ξ
  let bad : ((Fin p.n × Fin (k + 1)) → Fin p.d) → Prop := InterpolatedFiniteSumBlockExecution.Bad A Prod.fst (reply (k := k) c σ r G W B)
    Prod.snd id (A.initial seed) b B θ carrier
  let cost := fun π : (Fin p.n × Fin (k + 1)) → Fin p.d =>
    ∑ i, ((InterpolatedFiniteSumBlockExecution.process A Prod.fst (reply (k := k) c σ r G W B)
      (A.initial seed) π b).1.2 i : ℝ)
  let loss := fun π : (Fin p.n × Fin (k + 1)) → Fin p.d =>
    objective (f π) (execute (exactOracle p (f π) (g π)) A (fun _ => b) seed ξ)
  have hnonneg (π : (Fin p.n × Fin (k + 1)) → Fin p.d) : 0 ≤ loss π := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => shielded_nonnegative (block (emb π) i) c σ r G W hc hW _)
  have hcost (π : (Fin p.n × Fin (k + 1)) → Fin p.d) : cost π ≤ b := by
    dsimp only [cost]
    exact_mod_cast InterpolatedFiniteSumBlockExecution.process_count_sum A Prod.fst
      (reply (k := k) c σ r G W B) (A.initial seed) π b
  have hgood (π : (Fin p.n × Fin (k + 1)) → Fin p.d) (hπ : ¬bad π) :
      ((k + 1 : ℕ) * c / 2 - c * θ / σ) - (c / (2 * p.n)) * cost π ≤ loss π := by
    have hinj : Function.Injective π := by
      by_contra hh
      exact hπ (Or.inl hh)
    have havoid : ∀ ij, π ij ≠ carrier := by
      intro ij hh
      exact hπ (Or.inr (Or.inl ⟨ij, hh⟩))
    have he : (emb π : (Fin p.n × Fin (k + 1)) → Fin p.d) = π :=
      safeEmbedding_good fallback carrier π hinj havoid
    have hg : ¬InterpolatedFiniteSumBlockExecution.Bad A Prod.fst (reply (k := k) c σ r G W B)
        Prod.snd id (A.initial seed) b B θ carrier (emb π) := by rwa [he]
    have hex := coupled_execution (emb π) c σ r G W B θ hc hσ hG hW hgrad hB hθσ A b seed ξ carrier hg
    have ho := ideal_output_lower (emb π) hn c σ r G W B θ hc hσ hr.le hG hW hθ.le hB A b seed carrier hg
    rw [he] at hex ho
    have hlo : loss π = (p.n : ℝ)⁻¹ * ∑ i,
        shielded (block (emb π) i) c σ r G W
          (A.output (InterpolatedFiniteSumBlockExecution.process A Prod.fst (reply (k := k) c σ r G W B)
            (A.initial seed) π b).1.1) := by
      change (p.n : ℝ)⁻¹ * (∑ i, shielded (block (emb π) i) c σ r G W
        (execute (fullOracle (emb π) c σ r G W) A (fun _ => b) seed ξ)) = _
      rw [hex]
    rw [hlo]
    exact ho
  have hb := InterpolatedFiniteSumBlockExecution.bad_bound A Prod.fst (reply (k := k) c σ r G W B)
    (reply_prefix c σ r G W B) Prod.snd id (A.initial seed) b B θ hBpos hθ carrier
  have hbad : (p.d : ℝ) * (∑ π, if bad π then (1 : ℝ) else 0) ≤
      (p.d : ℝ) * Fintype.card ((Fin p.n × Fin (k + 1)) → Fin p.d) / 8 := by
    have hm := mul_le_mul_of_nonneg_right hdim
      (Nat.cast_nonneg (Fintype.card ((Fin p.n × Fin (k + 1)) → Fin p.d)) : (0 : ℝ) ≤ _)
    change (p.d : ℝ) * (∑ π, if bad π then (1 : ℝ) else 0) ≤ _ at hb
    nlinarith only [hb, hm]
  have hh := InterpolatedFiniteSumHiding.finite_average_loss bad loss cost
    ((k + 1 : ℕ) * c / 2 - c * θ / σ) (c / (2 * p.n)) p.d b hA (by positivity) hd
    (fun π => Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)) hcost hnonneg hgood hbad
  convert hh using 1
  ring

set_option maxHeartbeats 1600000 in
lemma smooth_failure (p : Params) (hp : spec.valid p)
    (hregime : 144 * p.n ≤ p.L0 * p.R ^ 2 / p.ε)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : b ≤ p.n * ⌊Real.sqrt ((p.L0 * p.R ^ 2 / p.ε) / p.n) / 12⌋₊ / 8) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hn : 0 < p.n := by have := hp.2.2.2.2.1; omega
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
  have hL := hp.1
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  let H := p.L0 * p.R ^ 2 / p.ε
  have hlen := InterpolatedFiniteSumSmoothParameters.length_bounds p.n hn H hregime
  let k := ⌊Real.sqrt (H / p.n) / 12⌋₊ - 1
  let t := k + 1
  have ht : 0 < t := Nat.succ_pos k
  have he : t = ⌊Real.sqrt (H / p.n) / 12⌋₊ := by dsimp [t, k]; omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htune : 144 * p.n * (t : ℝ) ^ 2 ≤ H := by rw [he]; exact hlen.2.1
  have hH : 144 ≤ H := by nlinarith only [hregime, hn1]
  have hb' : b ≤ p.n * t / 8 := by simpa only [he, H] using hb
  have hb8 : 8 * b ≤ p.n * t := by omega
  have hb8R : 8 * (b : ℝ) ≤ p.n * t := by exact_mod_cast hb8
  let c := 4 * p.ε / t
  let σ := p.R / (Real.sqrt p.n * t * Real.sqrt t)
  let G := p.L0 * p.R / 12
  let W := 4 * p.L0 * p.R ^ 2 / 9
  let B := 10 * p.R
  let θ := σ / 16
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hBpos : 0 ≤ B := by dsimp [B]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθσ : θ ≤ σ / 8 := by dsimp [θ]; linarith only [hσ]
  have hgeom : (p.n : ℝ) * (t : ℝ) ^ 3 * σ ^ 2 = p.R ^ 2 :=
    InterpolatedFiniteSumSmoothParameters.scale_radius p.n t hn ht p.R
  have hwidth : 64 * G ^ 2 ≤ W * p.L0 := by dsimp [G, W]; nlinarith
  have hrad : 4 * G / p.R ≤ p.L0 / 3 := by
    dsimp [G]
    have heq : 4 * (p.L0 * p.R / 12) / p.R = p.L0 / 3 := by field_simp; norm_num
    exact heq.le
  have hgrad : (c / σ) * (1 + 2 * Real.sqrt t) ≤ G :=
    InterpolatedFiniteSumSmoothParameters.gradient_tuned p.n t hn ht p.L0 p.R p.ε hR hε hH htune
  have hcurv : 12 * c / σ ^ 2 ≤ p.L0 / 3 :=
    InterpolatedFiniteSumSmoothParameters.curvature_tuned p.n t hn ht p.L0 p.R p.ε hR hε htune
  have hinit : (t : ℝ) * c / 2 = 2 * p.ε := by dsimp [c]; field_simp; norm_num
  have hgap : (t : ℝ) * c / 2 ≤ p.Δ := by rw [hinit]; exact hp.2.2.2.2.2.1
  have hB : 4 * p.R + ((t : ℝ) * c / 2 + W) / G ≤ B :=
    InterpolatedFiniteSumSmoothParameters.threshold_tuned t ht p.L0 p.R p.ε hL hR hε hH
  have hpen : c * θ / σ ≤ p.ε / 4 := by
    have heq : c * θ / σ = p.ε / (4 * t) := by dsimp [c, θ]; field_simp; norm_num
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (t : ℝ))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ht1 hε.le]
  have hAA : 7 * p.ε / 4 ≤ (t : ℝ) * c / 2 - c * θ / σ := by rw [hinit]; linarith only [hpen]
  have hA : 0 ≤ (t : ℝ) * c / 2 - c * θ / σ := by linarith only [hAA, hε]
  have hcost : c * b / (2 * p.n) ≤ p.ε / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p.n)).mpr
    have heq : c * b = (4 * p.ε * b) / t := by dsimp [c]; ring
    rw [heq]
    apply (div_le_iff₀ htR).mpr
    have hh := mul_le_mul_of_nonneg_left hb8R hε.le
    nlinarith only [hh]
  have hloss : p.ε < 7 * ((t : ℝ) * c / 2 - c * θ / σ) / 8 - c * b / (2 * p.n) := by
    nlinarith only [hAA, hcost, hε]
  have hratio : B ^ 2 / θ ^ 2 = 25600 * p.n * (t : ℝ) ^ 3 :=
    InterpolatedFiniteSumSmoothParameters.hiding_ratio p.n t hn ht p.R (ne_of_gt hR)
  have htH : (t : ℝ) ≤ H := by
    have ht2 := mul_nonneg htR.le (sub_nonneg.mpr ht1)
    have hn2 := mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (t : ℝ))
    nlinarith only [htune, ht2, hn2, htR]
  have hbplus : b + 1 ≤ 2 * p.n * t := by
    have hnt := Nat.mul_pos hn ht
    have hh : b + 1 ≤ 2 * (p.n * t) := by omega
    simpa only [Nat.mul_assoc] using hh
  have hdim : 8 * (((p.n : ℝ) * t) ^ 2 + p.n * t + (b + 1 : ℕ) * p.n * t * (B ^ 2 / θ ^ 2)) ≤ p.d :=
    InterpolatedFiniteSumSmoothParameters.setup_dimension p hp t b htH hbplus _ (by positivity) hratio.le
  have hntR : (0 : ℝ) < p.n * t := mul_pos hnR htR
  have hrest : 0 ≤ ((b + 1 : ℕ) : ℝ) * p.n * t * (B ^ 2 / θ ^ 2) := by positivity
  have hntd : p.n * t < p.d := by
    have hh : (p.n : ℝ) * t < p.d := by nlinarith [sq_nonneg ((p.n : ℝ) * t)]
    exact_mod_cast hh
  have hd : 0 < p.d := (Nat.mul_pos hn ht).trans hntd
  let carrier : Fin p.d := ⟨0, hd⟩
  let fallback : (Fin p.n × Fin (k + 1)) ↪ Fin p.d :=
    { toFun := fun ij => ⟨(finProdFinEquiv ij).val + 1, by
        have hh := (finProdFinEquiv ij).isLt
        change (finProdFinEquiv ij).val + 1 < p.d
        change p.n * (k + 1) < p.d at hntd
        omega⟩
      inj' := by
        intro ij uv h
        apply finProdFinEquiv.injective
        apply Fin.ext
        have hh := congrArg Fin.val h
        simpa using hh }
  exact failure_of_scales p hp fallback carrier c σ p.R G W B θ hc hσ le_rfl hG hW hBpos hθ hθσ
    hgeom.le hwidth hrad hgrad hcurv hgap hB hA A b hdim hloss

end LongTails.Proofs.InterpolatedFiniteSumSmoothLower
