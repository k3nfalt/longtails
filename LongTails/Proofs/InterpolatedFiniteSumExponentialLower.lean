import LongTails.Proofs.InterpolatedFiniteSumExponentialOracle
import LongTails.Proofs.InterpolatedFiniteSumExponentialParameters
import LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open OracleTemplate MeasureTheory Classical

namespace LongTails.Proofs.InterpolatedFiniteSumExponentialLower

open LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
open InterpolatedFiniteSumBlocks InterpolatedFiniteSumExponentialFamily
open InterpolatedFiniteSumHiddenComponent InterpolatedFiniteSumExponentialOracle
open InterpolatedFiniteSumBlockOracle (safeEmbedding safeEmbedding_good safeEmbedding_avoids)
open InterpolatedFiniteSumPairs (which)

set_option maxHeartbeats 1600000 in
lemma failure_of_scales (p : Params) (hp : spec.valid p) {g k : ℕ} (hg : 0 < g) (hgn : 2 * g ≤ p.n)
    (fallback : (Fin g × Fin (k + 1)) ↪ Fin p.d) (carrier : Fin p.d)
    (hf : ∀ i, fallback i ≠ carrier) (v : Point p) (hv : ‖v‖ = 2 * p.L1 / 7)
    (hvs : ∀ x : Point p, x carrier = 0 → ⟪v, x⟫ = 0)
    (C c σ r G W B θ : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c) (hσ : 0 < σ) (hRr : p.R ≤ r)
    (hG : 0 < G) (hW : 0 < W) (hBpos : 0 ≤ B) (hθ : 0 < θ) (hθσ : θ ≤ σ / 8)
    (hgeom : (g : ℝ) * (k + 1 : ℕ) ^ 3 * σ ^ 2 ≤ p.R ^ 2)
    (hwidth : 64 * G ^ 2 ≤ W * (4 * p.L1 ^ 2 / 49))
    (hrad : 4 * G / r ≤ (4 * p.L1 ^ 2 / 49) / 3)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hcurv : 12 * c / σ ^ 2 ≤ (4 * p.L1 ^ 2 / 49) / 3)
    (hGsmall : 2 * G ≤ p.L1 / 7) (hadd : 2 * C * p.L1 ^ 2 / 7 ≤ p.L0)
    (hgap : (2 * C * g / p.n) * (Real.exp ((k + 1 : ℕ) * c / 2) - 1) ≤ p.Δ)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (hA : 0 ≤ (2 * C * g / p.n) *
      (Real.exp ((k + 1 : ℕ) * c / 2) - 1 - Real.exp ((k + 1 : ℕ) * c / 2) * (c * θ / σ)))
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hdim : 8 * (((g : ℝ) * (k + 1 : ℕ)) ^ 2 + g * (k + 1 : ℕ) +
      (b + 1 : ℕ) * g * (k + 1 : ℕ) * (B ^ 2 / θ ^ 2)) ≤ p.d)
    (hloss : p.ε < 7 * ((2 * C * g / p.n) *
      (Real.exp ((k + 1 : ℕ) * c / 2) - 1 - Real.exp ((k + 1 : ℕ) * c / 2) * (c * θ / σ))) / 8 -
      (C * Real.exp ((k + 1 : ℕ) * c / 2) * c / p.n) * b) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let : Nonempty (Fin p.d) := ⟨carrier⟩
  have hd : (0 : ℝ) < p.d := by exact_mod_cast (show 0 < p.d from Nat.zero_lt_of_lt carrier.isLt)
  have hr : 0 < r := hp.2.2.1.trans_le hRr
  let emb := fun π : (Fin g × Fin (k + 1)) → Fin p.d => safeEmbedding fallback carrier π
  let m := fun π i => shielded (block (emb π) i) c σ r G W
  let dm := fun π i => shieldedField (block (emb π) i) c σ r G W
  let f := fun π => components hgn (m π) v C
  let df := fun π => fields hgn (m π) (dm π) v C
  let z := fun π => minimizer (emb π) σ
  let η := (k + 1 : ℕ) * c / 2
  let AA := (2 * C * g / p.n) * (Real.exp η - 1 - Real.exp η * (c * θ / σ))
  let CC := C * Real.exp η * c / p.n
  have hzR (π : (Fin g × Fin (k + 1)) → Fin p.d) : ‖z π‖ ≤ p.R := by
    have hh := (minimizer_norm_sq (emb π) σ hσ.le).trans hgeom
    dsimp [z]
    nlinarith [norm_nonneg (minimizer (emb π) σ), hp.2.2.1]
  have hmz (π : (Fin g × Fin (k + 1)) → Fin p.d) (i : Fin g) : m π i (z π) = 0 :=
    shielded_minimizer_value (emb π) c σ r G W hc hσ hr hG.le hW ((hzR π).trans hRr) i
  have hvz (π : (Fin g × Fin (k + 1)) → Fin p.d) : ⟪v, z π⟫ = 0 := by
    apply hvs
    exact InterpolatedFiniteSumChains.coordinateMap_adjoint_outside (emb π) _ carrier
      (safeEmbedding_avoids fallback carrier hf π)
  have hnon (π : (Fin g × Fin (k + 1)) → Fin p.d) (i : Fin g) (x : Point p) : 0 ≤ m π i x :=
    shielded_nonnegative (block (emb π) i) c σ r G W hc hW x
  have hAd (π : (Fin g × Fin (k + 1)) → Fin p.d) : spec.admissible p (f π) (exactOracle p (f π) (df π)) := by
    apply InterpolatedFiniteSumExponentialFamily.admissible p hp hgn (m π) (dm π) v (z π) C hC
      (fun i => shielded_gradient (block (emb π) i) c σ r G W hr hW)
      (fun i => shieldedField_differentiable (block (emb π) i) c σ r G W hr)
      (fun i => shielded_convex (block (emb π) i) c σ r G W hc hr hG.le hW)
      (fun i x => (shieldedField_norm (block (emb π) i) c σ r G W hc hσ hr hG.le hgrad x).trans hGsmall)
      hv (fun i x => shieldedField_curvature (block (emb π) i) c σ r G W (4 * p.L1 ^ 2 / 49)
        hc hσ hr hG.le hW (by positivity) hwidth hrad hgrad hcurv x)
      hadd (hnon π) (hmz π) (hvz π) (hzR π)
    have he : (p.n : ℝ)⁻¹ * (2 * C * ∑ j : Fin g, (Real.exp (m π j 0) - 1)) =
        (2 * C * g / p.n) * (Real.exp ((k + 1 : ℕ) * c / 2) - 1) := by
      simp only [m, shielded_zero _ _ _ _ _ _ hc hr hG.le hW, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [he]
    exact hgap
  apply finite_prior_failure p f df z hAd
    (fun π => components_nonnegative hgn (m π) v C hC (hnon π))
    (fun π => components_minimizer_value hgn (m π) v C (z π) (hmz π) (hvz π)) A b
    (7 * AA / 8 - CC * b) hloss
  intro seed ξ
  let pick := fun q : Fin p.n × Point p => which hg q.1
  let rep := reply (k := k) hgn v C c σ r G W B
  let bad : ((Fin g × Fin (k + 1)) → Fin p.d) → Prop := InterpolatedFiniteSumBlockExecution.Bad A pick rep
    Prod.snd id (A.initial seed) b B θ carrier
  let cost := fun π : (Fin g × Fin (k + 1)) → Fin p.d =>
    ∑ i, ((InterpolatedFiniteSumBlockExecution.process A pick rep (A.initial seed) π b).1.2 i : ℝ)
  let loss := fun π : (Fin g × Fin (k + 1)) → Fin p.d =>
    objective (f π) (execute (exactOracle p (f π) (df π)) A (fun _ => b) seed ξ)
  have hnonneg (π : (Fin g × Fin (k + 1)) → Fin p.d) : 0 ≤ loss π := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => components_nonnegative hgn (m π) v C hC (hnon π) i _)
  have hcost (π : (Fin g × Fin (k + 1)) → Fin p.d) : cost π ≤ b := by
    dsimp only [cost]
    exact_mod_cast InterpolatedFiniteSumBlockExecution.process_count_sum A pick rep (A.initial seed) π b
  have hgood (π : (Fin g × Fin (k + 1)) → Fin p.d) (hπ : ¬bad π) : AA - CC * cost π ≤ loss π := by
    have hinj : Function.Injective π := by
      by_contra hh
      exact hπ (Or.inl hh)
    have havoid : ∀ ij, π ij ≠ carrier := by
      intro ij hh
      exact hπ (Or.inr (Or.inl ⟨ij, hh⟩))
    have he : (emb π : (Fin g × Fin (k + 1)) → Fin p.d) = π :=
      safeEmbedding_good fallback carrier π hinj havoid
    have hgood' : ¬InterpolatedFiniteSumBlockExecution.Bad A pick rep
        Prod.snd id (A.initial seed) b B θ carrier (emb π) := by rwa [he]
    have hex := coupled_execution hg hgn (emb π) v C c σ r G W B θ hc hσ hG hW hgrad hB hθσ
      A b seed ξ carrier hgood'
    have ho := ideal_output_lower hg hgn (emb π) v C c σ r G W B θ hC hc hσ hr.le hG hW hθ.le hB
      A b seed carrier hgood'
    rw [he] at hex ho
    have hlo : loss π = (p.n : ℝ)⁻¹ * ∑ i, f π i
        (A.output (InterpolatedFiniteSumBlockExecution.process A pick rep (A.initial seed) π b).1.1) := by
      change (p.n : ℝ)⁻¹ * (∑ i, f π i
        (execute (fullOracle hgn (emb π) v C c σ r G W) A (fun _ => b) seed ξ)) = _
      rw [hex]
    rw [hlo]
    exact ho
  have hb := InterpolatedFiniteSumBlockExecution.bad_bound A pick rep
    (reply_prefix hg hgn v C c σ r G W B) Prod.snd id (A.initial seed) b B θ hBpos hθ carrier
  have hbad : (p.d : ℝ) * (∑ π, if bad π then (1 : ℝ) else 0) ≤
      (p.d : ℝ) * Fintype.card ((Fin g × Fin (k + 1)) → Fin p.d) / 8 := by
    have hm := mul_le_mul_of_nonneg_right hdim
      (Nat.cast_nonneg (Fintype.card ((Fin g × Fin (k + 1)) → Fin p.d)) : (0 : ℝ) ≤ _)
    change (p.d : ℝ) * (∑ π, if bad π then (1 : ℝ) else 0) ≤ _ at hb
    nlinarith only [hb, hm]
  exact InterpolatedFiniteSumHiding.finite_average_loss bad loss cost AA CC p.d b hA
    (by dsimp [CC]; positivity) hd (fun π => Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
    hcost hnonneg hgood hbad

set_option maxHeartbeats 1600000 in
lemma tuned_failure (p : Params) (hp : spec.valid p) (hL : 0 < p.L1)
    (δ η : ℝ) (hδ : 0 < δ) (hδdef : δ = p.L0 / (4 * p.L1 ^ 2))
    (hδε : δ ≤ p.ε / 4) (hη : 1 / 8 ≤ η) (hexp : δ * Real.exp η = δ + 2 * p.ε)
    (hqη : 84 * η ≤ p.L1 * p.R) {k : ℕ}
    (hscale : ((p.n / 2 : ℕ) : ℝ) * (84 * η) ^ 2 * (k + 1 : ℕ) ^ 2 ≤ (p.L1 * p.R) ^ 2)
    (htq : ((k + 1 : ℕ) : ℝ) ≤ p.L1 * p.R)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : 64 * η * b ≤ (p.n / 2 : ℕ) * (k + 1 : ℕ)) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let g := p.n / 2
  let t := k + 1
  change 64 * η * b ≤ (g : ℝ) * t at hb
  have hn2 := hp.2.2.2.2.1
  have hn : 0 < p.n := by omega
  have hg : 0 < g := by dsimp [g]; omega
  have hgn : 2 * g ≤ p.n := by dsimp [g]; omega
  have hng : p.n ≤ 3 * g := by dsimp [g]; omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast hn
  have ht : 0 < t := Nat.succ_pos k
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hη0 : 0 < η := by linarith
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  let C := p.n * δ / (2 * g)
  let c := 2 * η / t
  let σ := 84 * η / (p.L1 * Real.sqrt t)
  let G := p.L1 / 14
  let B := 10 * p.R
  let θ := σ / (64 * η)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθσ : θ ≤ σ / 8 := by
    dsimp [θ]
    apply (div_le_iff₀ (by positivity : 0 < 64 * η)).mpr
    have hh := mul_le_mul_of_nonneg_left hη hσ.le
    nlinarith only [hh]
  have hgeom : (g : ℝ) * (t : ℝ) ^ 3 * σ ^ 2 ≤ p.R ^ 2 :=
    InterpolatedFiniteSumExponentialParameters.radius_tuned g t ht η p.L1 p.R hL hscale
  have hwidth : 64 * G ^ 2 ≤ 4 * (4 * p.L1 ^ 2 / 49) := by dsimp [G]; nlinarith
  have hrad : 4 * G / p.R ≤ (4 * p.L1 ^ 2 / 49) / 3 :=
    InterpolatedFiniteSumExponentialParameters.radial_tuned p.L1 p.R hR hL.le (by linarith only [hqη, hη])
  have hgrad : (c / σ) * (1 + 2 * Real.sqrt t) ≤ G :=
    InterpolatedFiniteSumExponentialParameters.gradient_tuned t ht η p.L1 hη0 hL
  have hcurv : 12 * c / σ ^ 2 ≤ (4 * p.L1 ^ 2 / 49) / 3 :=
    InterpolatedFiniteSumExponentialParameters.curvature_tuned t ht η p.L1 hη hL
  have hGsmall : 2 * G ≤ p.L1 / 7 := by dsimp [G]; ring_nf; exact le_rfl
  have hcoef : 2 * C * g / p.n = δ := by dsimp [C]; field_simp
  have hadd : 2 * C * p.L1 ^ 2 / 7 ≤ p.L0 := by
    have hngR : (p.n : ℝ) ≤ 3 * g := by exact_mod_cast hng
    have hmul := mul_le_mul_of_nonneg_right hngR hδ.le
    have hδL : 4 * δ * p.L1 ^ 2 = p.L0 := by rw [hδdef]; field_simp
    dsimp [C]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 7)).mpr
    have he : 2 * (p.n * δ / (2 * g)) * p.L1 ^ 2 = p.n * δ * p.L1 ^ 2 / g := by ring
    rw [he]
    apply (div_le_iff₀ hgR).mpr
    have hh := mul_le_mul_of_nonneg_right hmul (sq_nonneg p.L1)
    nlinarith only [hh, hδL, mul_nonneg hgR.le hp.1.le]
  have hinit : (t : ℝ) * c / 2 = η := by dsimp [c]; field_simp
  have hgap : (2 * C * g / p.n) * (Real.exp ((t : ℝ) * c / 2) - 1) ≤ p.Δ := by
    rw [hinit, hcoef]
    nlinarith only [hexp, hp.2.2.2.2.2.1]
  have hB : 4 * p.R + ((t : ℝ) * c / 2 + 4) / G ≤ B := by
    rw [hinit]
    have hh : (η + 4) / G ≤ 6 * p.R := by
      apply (div_le_iff₀ hG).mpr
      dsimp [G]
      nlinarith only [hqη, hη]
    dsimp [B]
    linarith only [hh]
  have hpen : c * θ / σ = 1 / (32 * t) := by dsimp [c, θ]; field_simp; ring
  have hexpub : δ * Real.exp η ≤ 9 * p.ε / 4 := by linarith only [hexp, hδε]
  have hpenub : δ * Real.exp η * (c * θ / σ) ≤ p.ε / 4 := by
    rw [hpen]
    have he : δ * Real.exp η * (1 / (32 * t)) = (δ * Real.exp η) / (32 * t) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (t : ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_left ht1 hε.le
    nlinarith only [hexpub, hh, hε]
  have hAA : 7 * p.ε / 4 ≤ (2 * C * g / p.n) *
      (Real.exp ((t : ℝ) * c / 2) - 1 - Real.exp ((t : ℝ) * c / 2) * (c * θ / σ)) := by
    rw [hinit, hcoef]
    nlinarith only [hexp, hpenub]
  have hcost : (C * Real.exp ((t : ℝ) * c / 2) * c / p.n) * b ≤ p.ε / 4 := by
    rw [hinit]
    have he : (C * Real.exp η * c / p.n) * b = (δ * Real.exp η) * (η * b) / (g * t) := by
      dsimp [C, c]
      field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < (g : ℝ) * t)).mpr
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ δ * Real.exp η by positivity)
    have hh := mul_le_mul_of_nonneg_right hexpub (show 0 ≤ (g : ℝ) * t by positivity)
    have hp : 0 ≤ p.ε * ((g : ℝ) * t) := by positivity
    nlinarith only [hm, hh, hp]
  have hAA0 : 0 ≤ (2 * C * g / p.n) *
      (Real.exp ((t : ℝ) * c / 2) - 1 - Real.exp ((t : ℝ) * c / 2) * (c * θ / σ)) := by
    linarith only [hAA, hε]
  have hloss : p.ε < 7 * ((2 * C * g / p.n) *
      (Real.exp ((t : ℝ) * c / 2) - 1 - Real.exp ((t : ℝ) * c / 2) * (c * θ / σ))) / 8 -
      (C * Real.exp ((t : ℝ) * c / 2) * c / p.n) * b := by
    nlinarith only [hAA, hcost, hε]
  have hbgt : b ≤ g * t := by
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have hh := mul_le_mul_of_nonneg_right hη hb0
    have hbr : (b : ℝ) ≤ g * t := by nlinarith only [hb, hh, hb0]
    exact_mod_cast hbr
  have hbplus : b + 1 ≤ 2 * g * t := by
    have hgt := Nat.mul_pos hg ht
    have hh : b + 1 ≤ 2 * (g * t) := by omega
    simpa only [Nat.mul_assoc] using hh
  have hratio : B ^ 2 / θ ^ 2 ≤ 100 * (p.L1 * p.R) ^ 2 * t :=
    InterpolatedFiniteSumExponentialParameters.hiding_ratio t ht η p.L1 p.R hη0 hL
  have hdim := InterpolatedFiniteSumExponentialParameters.setup_dimension p hp g t b
    (by omega : g ≤ p.n) htq hbplus (B ^ 2 / θ ^ 2) (by positivity) hratio
  have hgtR : (0 : ℝ) < g * t := by positivity
  have hrest : 0 ≤ ((b + 1 : ℕ) : ℝ) * g * t * (B ^ 2 / θ ^ 2) := by positivity
  have hgtd : g * t < p.d := by
    have hh : (g : ℝ) * t < p.d := by nlinarith [sq_nonneg ((g : ℝ) * t)]
    exact_mod_cast hh
  have hd : 0 < p.d := (Nat.mul_pos hg ht).trans hgtd
  let carrier : Fin p.d := ⟨0, hd⟩
  let fallback : (Fin g × Fin (k + 1)) ↪ Fin p.d :=
    { toFun := fun ij => ⟨(finProdFinEquiv ij).val + 1, by
        have hh := (finProdFinEquiv ij).isLt
        change (finProdFinEquiv ij).val + 1 < p.d
        change g * (k + 1) < p.d at hgtd
        omega⟩
      inj' := by
        intro ij uv h
        apply finProdFinEquiv.injective
        apply Fin.ext
        have hh := congrArg Fin.val h
        simpa using hh }
  have hf : ∀ i, fallback i ≠ carrier := by
    intro i hi
    have hh := congrArg Fin.val hi
    change (finProdFinEquiv i).val + 1 = 0 at hh
    omega
  let v : Point p := (2 * p.L1 / 7) • PiLp.single 2 carrier (1 : ℝ)
  have hv : ‖v‖ = 2 * p.L1 / 7 := by
    simp only [v, norm_smul, PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one]
    exact abs_of_pos (by positivity)
  have hvs : ∀ x : Point p, x carrier = 0 → ⟪v, x⟫ = 0 := by
    intro x hx
    simp only [v, real_inner_smul_left, EuclideanSpace.inner_single_left, hx, mul_zero]
  exact failure_of_scales p hp hg hgn fallback carrier hf v hv hvs C c σ p.R G 4 B θ hC hc hσ le_rfl
    hG (by norm_num) (by dsimp [B]; positivity) hθ hθσ hgeom hwidth hrad hgrad hcurv hGsmall hadd
    hgap hB hAA0 A b hdim hloss

set_option maxHeartbeats 1600000 in
lemma exponential_failure (p : Params) (hp : spec.valid p)
    (hregime : p.L0 < p.ε * p.L1 ^ 2)
    (hactive : 84 * Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0) * Real.sqrt (p.n / 2 : ℕ) ≤ p.L1 * p.R)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : 64 * Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0) * b ≤
      ((p.n / 2 : ℕ) : ℝ) * ⌊(p.L1 * p.R) /
        (84 * Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0) * Real.sqrt (p.n / 2 : ℕ))⌋₊) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let g := p.n / 2
  let δ := p.L0 / (4 * p.L1 ^ 2)
  let η := Real.log (1 + 8 * p.ε * p.L1 ^ 2 / p.L0)
  have hR := hp.2.2.1
  have hg : 0 < g := by dsimp [g]; have := hp.2.2.2.2.1; omega
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hsg1 : 1 ≤ Real.sqrt g := by simpa using Real.sqrt_le_sqrt hg1
  have hL : 0 < p.L1 := by
    have hsq : 0 < p.L1 ^ 2 := by nlinarith [hp.1, hp.2.2.2.1]
    nlinarith [hp.2.1]
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos hp.1 (by positivity)
  have hδε : δ ≤ p.ε / 4 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * p.L1 ^ 2)).mpr
    nlinarith only [hregime]
  have hηdef : η = Real.log (1 + 2 * p.ε / δ) := by
    dsimp [η, δ]
    congr 1
    field_simp
    ring
  have hη : 1 / 8 ≤ η := by
    rw [hηdef]
    exact InterpolatedFiniteSumExponentialParameters.eta_lower δ p.ε hδ hp.2.2.2.1 hδε
  have hη0 : 0 < η := by linarith
  have hexp : δ * Real.exp η = δ + 2 * p.ε := by
    rw [hηdef]
    exact InterpolatedFiniteSumExponentialParameters.exponential_scale δ p.ε hδ hp.2.2.2.1
  have hlen := InterpolatedFiniteSumExponentialParameters.length_bounds g hg (p.L1 * p.R) η hη0 hactive
  let k := ⌊(p.L1 * p.R) / (84 * η * Real.sqrt g)⌋₊ - 1
  let t := k + 1
  have ht : 0 < t := Nat.succ_pos k
  have he : t = ⌊(p.L1 * p.R) / (84 * η * Real.sqrt g)⌋₊ := by dsimp [t, k]; omega
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hden : 1 ≤ 84 * η * Real.sqrt g := by
    have hh := mul_le_mul_of_nonneg_left hsg1 (by positivity : 0 ≤ 84 * η)
    nlinarith only [hh, hη]
  have hqη : 84 * η ≤ p.L1 * p.R := by
    have hh := mul_le_mul_of_nonneg_left hsg1 (by positivity : 0 ≤ 84 * η)
    change 84 * η * Real.sqrt g ≤ p.L1 * p.R at hactive
    nlinarith only [hh, hactive]
  have htq : (t : ℝ) ≤ p.L1 * p.R := by
    have hf := Nat.floor_le (by positivity : 0 ≤ (p.L1 * p.R) / (84 * η * Real.sqrt g))
    rw [← he] at hf
    have hh := (le_div_iff₀ (by positivity : 0 < 84 * η * Real.sqrt g)).mp hf
    have hm := mul_le_mul_of_nonneg_left hden ht0
    nlinarith only [hh, hm]
  apply tuned_failure p hp hL δ η hδ rfl hδε hη hexp hqη (k := k)
  · rw [show k + 1 = t from rfl, he]
    exact hlen.2.1
  · exact htq
  · simpa only [show k + 1 = t from rfl, he, η, g] using hb

end LongTails.Proofs.InterpolatedFiniteSumExponentialLower
