import LongTails.Proofs.ComponentEnvelopePotential
import LongTails.Proofs.ComponentEnvelopeEpochWork
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

lemma epochs_accuracy_recursion (p : Params) (g : Fin p.n × p.E → p.E) (F : p.E → ℝ)
    (V : ℕ → p.E → p.E → p.E → ℝ) (e : ℕ → ℝ) (hR : 0 ≤ p.R)
    (hprogress : ∀ s snapshot y z,
      snapshot ∈ Metric.closedBall p.x0 p.R → y ∈ Metric.closedBall p.x0 p.R → z ∈ Metric.closedBall p.x0 p.R →
      (𝔼 samples : Fin p.n → Fin p.n,
        let cache := fun i => Program.eval g (componentPlan p i snapshot)
        let state := Program.eval g (epochPlan p s snapshot cache p.n samples ⟨y, z, 0⟩)
        V (s + 1) ((p.n : ℝ)⁻¹ • state.total) state.y state.z) ≤ V s snapshot y z + e s)
    (houtput : ∀ s snapshot y z,
      snapshot ∈ Metric.closedBall p.x0 p.R → y ∈ Metric.closedBall p.x0 p.R → z ∈ Metric.closedBall p.x0 p.R →
      (p.n : ℝ) * (𝔼 samples : Fin p.n → Fin p.n,
        let cache := fun i => Program.eval g (componentPlan p i snapshot)
        let state := Program.eval g (epochPlan p s snapshot cache p.n samples ⟨y, z, 0⟩)
        F ((p.n : ℝ)⁻¹ • state.total)) ≤
        2 * ((2 : ℝ) / (s + 4)) ^ 2 * (V s snapshot y z + e s))
    (k : ℕ) (hk : 0 < k) (s : ℕ) (snapshot y z : p.E)
    (hw : snapshot ∈ Metric.closedBall p.x0 p.R) (hy : y ∈ Metric.closedBall p.x0 p.R)
    (hz : z ∈ Metric.closedBall p.x0 p.R) :
    (p.n : ℝ) * (𝔼 samples : Fin k → Fin p.n → Fin p.n,
      F (Program.eval g (epochsPlan p k samples s snapshot y z))) ≤
      2 * ((2 : ℝ) / ((s : ℝ) + k + 3)) ^ 2 *
        (V s snapshot y z + ∑ j ∈ Finset.range k, e (s + j)) := by
  induction k generalizing s snapshot y z with
  | zero => omega
  | succ k ih =>
      let cache := fun i => Program.eval g (componentPlan p i snapshot)
      let next := fun samples : Fin p.n → Fin p.n =>
        Program.eval g (epochPlan p s snapshot cache p.n samples ⟨y, z, 0⟩)
      have hmem (samples : Fin p.n → Fin p.n) :=
        (epoch_eval_bounds p g hR s snapshot cache p.n samples ⟨y, z, 0⟩ hy hz).1
      have hmean (samples : Fin p.n → Fin p.n) :=
        epoch_mean_mem p g hR s snapshot cache p.n (NeZero.pos _) samples y z hy hz
      rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
      simp only [epochs_eval_succ, Fin.cons_zero, Fin.cons_succ]
      change (p.n : ℝ) * (𝔼 samples : Fin p.n → Fin p.n, 𝔼 rest : Fin k → Fin p.n → Fin p.n,
        F (Program.eval g (epochsPlan p k rest (s + 1) ((p.n : ℝ)⁻¹ • (next samples).total)
          (next samples).y (next samples).z))) ≤ _
      by_cases hk0 : k = 0
      · subst k
        simp only [epochsPlan, Program.eval, Fintype.expect_const, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
        simp only [Nat.zero_add, Finset.sum_range_one, Nat.add_zero]
        have hh := houtput s snapshot y z hw hy hz
        change (p.n : ℝ) * (𝔼 samples : Fin p.n → Fin p.n, F ((p.n : ℝ)⁻¹ • (next samples).total)) ≤ _ at hh
        convert hh using 1
        congr 2
        ring
      · have ht (samples : Fin p.n → Fin p.n) := ih (Nat.pos_of_ne_zero hk0) (s + 1)
          ((p.n : ℝ)⁻¹ • (next samples).total) (next samples).y (next samples).z
          (hmean samples) (hmem samples).1 (hmem samples).2
        have hav := Finset.expect_le_expect (s := Finset.univ) (fun samples _ => ht samples)
        have hp := hprogress s snapshot y z hw hy hz
        change (𝔼 samples : Fin p.n → Fin p.n,
          V (s + 1) ((p.n : ℝ)⁻¹ • (next samples).total) (next samples).y (next samples).z) ≤ V s snapshot y z + e s at hp
        have hden : ((s + 1 : ℕ) : ℝ) + k + 3 = (s : ℝ) + (k + 1 : ℕ) + 3 := by push_cast; ring
        rw [hden] at hav
        simp only [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const] at hav
        have hsum : (∑ j ∈ Finset.range (k + 1), e (s + j)) =
            e s + ∑ j ∈ Finset.range k, e (s + 1 + j) := by
          rw [Finset.sum_range_succ', add_comm]
          simp only [Nat.add_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          omega
        rw [hsum]
        have hscaled := mul_le_mul_of_nonneg_left hp
          (show 0 ≤ 2 * ((2 : ℝ) / ((s : ℝ) + (k + 1 : ℕ) + 3)) ^ 2 by positivity)
        nlinarith
lemma epochs_cost_affine (p : Params) (g : Fin p.n × p.E → p.E)
    (V : ℕ → p.E → p.E → p.E → ℝ) (d h e : ℕ → ℝ)
    (a b : ℕ → ℕ → ℝ) (hR : 0 ≤ p.R)
    (ha0 : ∀ s, a s 0 = 0) (hb0 : ∀ s, b s 0 = 0)
    (ha : ∀ s k, a s (k + 1) = d s + a (s + 1) k)
    (hb : ∀ s k, b s (k + 1) = h s + b (s + 1) k + a (s + 1) k * e s)
    (han : ∀ s k, 0 ≤ a s k)
    (hcost : ∀ s w y z,
      w ∈ Metric.closedBall p.x0 p.R → y ∈ Metric.closedBall p.x0 p.R → z ∈ Metric.closedBall p.x0 p.R →
      (∑ i, (Program.cost g (componentPlan p i w) : ℝ)) +
        (𝔼 samples : Fin p.n → Fin p.n,
          (Program.cost g (epochPlan p s w (fun i => Program.eval g (componentPlan p i w)) p.n samples ⟨y, z, 0⟩) : ℝ)) ≤
        d s * V s w y z + h s)
    (hprogress : ∀ s w y z,
      w ∈ Metric.closedBall p.x0 p.R → y ∈ Metric.closedBall p.x0 p.R → z ∈ Metric.closedBall p.x0 p.R →
      (𝔼 samples : Fin p.n → Fin p.n,
        let cache := fun i => Program.eval g (componentPlan p i w)
        let state := Program.eval g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩)
        V (s + 1) ((p.n : ℝ)⁻¹ • state.total) state.y state.z) ≤ V s w y z + e s)
    (k s : ℕ) (w y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R) (hy : y ∈ Metric.closedBall p.x0 p.R)
    (hz : z ∈ Metric.closedBall p.x0 p.R) :
    (𝔼 samples : Fin k → Fin p.n → Fin p.n,
      (Program.cost g (epochsPlan p k samples s w y z) : ℝ)) ≤ a s k * V s w y z + b s k := by
  induction k generalizing s w y z with
  | zero => simp [epochsPlan, Program.cost, ha0, hb0]
  | succ k ih =>
      let cache := fun i => Program.eval g (componentPlan p i w)
      let next := fun samples : Fin p.n → Fin p.n =>
        Program.eval g (epochPlan p s w cache p.n samples ⟨y, z, 0⟩)
      have hmem samples := (epoch_eval_bounds p g hR s w cache p.n samples ⟨y, z, 0⟩ hy hz).1
      have hmean samples := epoch_mean_mem p g hR s w cache p.n (NeZero.pos _) samples y z hy hz
      have ht samples := ih (s + 1) ((p.n : ℝ)⁻¹ • (next samples).total)
        (next samples).y (next samples).z (hmean samples) (hmem samples).1 (hmem samples).2
      have hav := Finset.expect_le_expect (s := Finset.univ) (fun samples _ => ht samples)
      have hp := mul_le_mul_of_nonneg_left (hprogress s w y z hw hy hz) (han (s + 1) k)
      have hc := hcost s w y z hw hy hz
      rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
      simp only [epochs_cost_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_add, Nat.cast_sum,
        Finset.expect_add_distrib, Fintype.expect_const]
      simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hav
      rw [ha, hb]
      change _ ≤ (d s + a (s + 1) k) * V s w y z + (h s + b (s + 1) k + a (s + 1) k * e s)
      dsimp [next, cache] at hav hp hc
      nlinarith

open LongTails.Proofs.RecursiveEnvelopeGeometry OracleTemplate.FiniteSum
lemma model_epochs_accuracy (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (k : ℕ) (hk : 0 < k) (s : ℕ) (w y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let F := fun x => H x - H u
    (p.n : ℝ) * (𝔼 samples : Fin k → Fin p.n → Fin p.n,
      F (Program.eval g (epochsPlan p k samples s w y z))) ≤
      2 * ((2 : ℝ) / ((s : ℝ) + k + 3)) ^ 2 *
        (startPotential p F u s w y z +
          ∑ j ∈ Finset.range k, p.n * (4 * p.R * tolerance p) / ((2 : ℝ) / (((s + j : ℕ) : ℝ) + 4)) ^ 2) := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  apply epochs_accuracy_recursion p g F (startPotential p F u)
    (fun j => p.n * (4 * p.R * tolerance p) / ((2 : ℝ) / (j + 4)) ^ 2) hR
  · intro t a b c ha hb hc
    exact (model_epoch_transition p g f G hm hR hζ u hu hgu hrad herr t a b c ha hb hc).1
  · intro t a b c ha hb hc
    exact (model_epoch_transition p g f G hm hR hζ u hu hgu hrad herr t a b c ha hb hc).2
  · exact hk
  · exact hw
  · exact hy
  · exact hz

lemma total_epoch_error (p : Params) (hμ : 0 ≤ smoothing p) (hR : 0 ≤ p.R)
    (hζ : 0 ≤ tolerance p) :
    (∑ j ∈ Finset.range (epochCount p),
      (p.n : ℝ) * (4 * p.R * tolerance p) / ((2 : ℝ) / (j + 4)) ^ 2) ≤ smoothing p * p.R ^ 2 := by
  have h := epoch_error_sum (S := epochCount p)
    (δ := (p.n : ℝ) * (4 * p.R * tolerance p)) (by positivity)
  rw [tolerance_total_error] at h
  have hn : 0 ≤ smoothing p * p.R ^ 2 := by positivity
  linarith

lemma model_expected_accuracy (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (h0 : 0 < p.L0) (he : 0 < p.ε) (hRp : 0 < p.R)
    {ι : Type*} [Fintype ι] [Nonempty ι] (w y z : ι → p.E)
    (hw : ∀ i, w i ∈ Metric.closedBall p.x0 p.R)
    (hy : ∀ i, y i ∈ Metric.closedBall p.x0 p.R) (hz : ∀ i, z i ∈ Metric.closedBall p.x0 p.R)
    (hinit : (𝔼 i, startPotential p
      (fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u)
      u 0 (w i) (y i) (z i)) ≤ 14 * smoothing p * p.R ^ 2) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    (𝔼 i, 𝔼 samples : Fin (epochCount p) → Fin p.n → Fin p.n,
      H (Program.eval g (epochsPlan p (epochCount p) samples 0 (w i) (y i) (z i)))) - H u ≤ p.ε / 60 := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  have hμ := (hm 0).pos
  have hk := epoch_count_positive p h0 he hRp
  have ht i := model_epochs_accuracy p g f G hm hR hζ u hu hgu hrad herr (epochCount p) hk 0
    (w i) (y i) (z i) (hw i) (hy i) (hz i)
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => ht i)
  simp only [Nat.cast_zero, zero_add, Finset.expect_sub_distrib, Fintype.expect_const,
    Finset.expect_add_distrib, ← Finset.mul_expect] at hav
  have herrsum := total_epoch_error p hμ.le hR hζ
  have hcoef : 0 ≤ 2 * ((2 : ℝ) / ((epochCount p : ℝ) + 3)) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hinit herrsum) hcoef
  have hrate := epoch_count_accuracy p h0 he hRp
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hd : 0 < ((epochCount p : ℝ) + 3) ^ 2 := by positivity
  have hident : 2 * ((2 : ℝ) / ((epochCount p : ℝ) + 3)) ^ 2 *
      (14 * smoothing p * p.R ^ 2 + smoothing p * p.R ^ 2) =
        120 * smoothing p * p.R ^ 2 / ((epochCount p : ℝ) + 3) ^ 2 := by field_simp; ring
  rw [hident] at hscaled
  have hrate' := (div_le_iff₀ (mul_pos hn hd)).mp hrate
  have hfinal : 120 * smoothing p * p.R ^ 2 / ((epochCount p : ℝ) + 3) ^ 2 ≤ (p.n : ℝ) * (p.ε / 60) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  dsimp only [H, F] at hav hscaled ⊢
  nlinarith [hscaled.trans hfinal]

lemma model_warmup_potential (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (u : p.E) (hgu : ∀ i, G (i, u) = 0) (hu : ‖p.x0 - u‖ ≤ p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let w := fun samples : Fin (4 * p.n) → Fin p.n =>
      (((4 * p.n : ℕ) : ℝ)⁻¹ • (Program.eval g (warmupPlan p (4 * p.n) samples p.x0 0)).2)
    (𝔼 samples, startPotential p (fun x => H x - H u) u 0 (w samples) (w samples) (w samples)) ≤
      14 * smoothing p * p.R ^ 2 := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let w := fun samples : Fin (4 * p.n) → Fin p.n =>
    (((4 * p.n : ℕ) : ℝ)⁻¹ • (Program.eval g (warmupPlan p (4 * p.n) samples p.x0 0)).2)
  have hμ := (hm 0).pos
  have hζ := tolerance_pos p h0 he hR
  have hu' : u ∈ Metric.closedBall p.x0 p.R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
  have hx : p.x0 ∈ Metric.closedBall p.x0 p.R := Metric.mem_closedBall_self hR.le
  have hrad (a : p.E) (ha : a ∈ Metric.closedBall p.x0 p.R) : ‖a - u‖ ≤ 2 * p.R := by
    have h1 : ‖a - p.x0‖ ≤ p.R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using ha
    have h2 := norm_add_le (a - p.x0) (p.x0 - u)
    rw [show a - p.x0 + (p.x0 - u) = a - u by module] at h2
    linarith
  have hn : 0 < p.n := NeZero.pos _
  have hk : 0 < 4 * p.n := Nat.mul_pos (by omega) hn
  have hwm samples : w samples ∈ Metric.closedBall p.x0 p.R :=
    warmup_mean_mem p g hR.le (4 * p.n) hk samples p.x0 hx
  have hgap := warmup_expected_accuracy p g f G hm hR.le u hu' hgu hrad herr (4 * p.n) hk p.x0 hx
  have htol := tolerance_warmup p h0 he hR
  have hdist := pow_le_pow_left₀ (norm_nonneg (p.x0 - u)) hu 2
  have hdist' := mul_le_mul_of_nonneg_left hdist hμ.le
  have htol' := mul_le_mul_of_nonneg_left htol hR.le
  have hwgap : (p.n : ℝ) * (𝔼 samples : Fin (4 * p.n) → Fin p.n, F (w samples)) ≤ smoothing p * p.R ^ 2 := by
    dsimp [F, w]
    simp only [Finset.expect_sub_distrib, Fintype.expect_const]
    push_cast at hgap ⊢
    dsimp only [H] at *
    nlinarith
  have hinit := initial_potential_expect p F u w w hμ.le hwgap (fun i => hrad (w i) (hwm i))
  exact hinit

lemma model_plan_accuracy (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (u : p.E) (hgu : ∀ i, G (i, u) = 0) (hu : ‖p.x0 - u‖ ≤ p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    (𝔼 seed : Seeds p, H (Program.eval g (plan p seed))) - H u ≤ p.ε / 60 := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let w := fun samples : Fin (4 * p.n) → Fin p.n =>
    (((4 * p.n : ℕ) : ℝ)⁻¹ • (Program.eval g (warmupPlan p (4 * p.n) samples p.x0 0)).2)
  have hμ := (hm 0).pos
  have hζ := tolerance_pos p h0 he hR
  have hu' : u ∈ Metric.closedBall p.x0 p.R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
  have hx : p.x0 ∈ Metric.closedBall p.x0 p.R := Metric.mem_closedBall_self hR.le
  have hrad (a : p.E) (ha : a ∈ Metric.closedBall p.x0 p.R) : ‖a - u‖ ≤ 2 * p.R := by
    have h1 : ‖a - p.x0‖ ≤ p.R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using ha
    have h2 := norm_add_le (a - p.x0) (p.x0 - u)
    rw [show a - p.x0 + (p.x0 - u) = a - u by module] at h2
    linarith
  have hn : 0 < p.n := NeZero.pos _
  have hk : 0 < 4 * p.n := Nat.mul_pos (by omega) hn
  have hwm samples : w samples ∈ Metric.closedBall p.x0 p.R :=
    warmup_mean_mem p g hR.le (4 * p.n) hk samples p.x0 hx
  have hinit := model_warmup_potential p g f G hm u hgu hu herr h0 he hR
  have hfull : fullGradient G u = 0 := by simp [fullGradient, hgu]
  have hmain := model_expected_accuracy p g f G hm hR.le hζ.le u hu' hfull hrad herr h0 he hR
    w w w hwm hwm hwm hinit
  change (𝔼 seed : Seeds p, H (Program.eval g (plan p seed))) - H u ≤ p.ε / 60
  change (𝔼 seed : (Fin (4 * p.n) → Fin p.n) × (Fin (epochCount p) → Fin p.n → Fin p.n),
    H (Program.eval g (plan p seed))) - H u ≤ p.ε / 60
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simpa only [plan, Program.eval_bind, w, H] using hmain

lemma model_epochs_affine_cost (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hcost : ∀ x ∈ Metric.closedBall p.x0 p.R,
      (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i x) : ℝ)) ≤ C * (1 + β *
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u)))
    (huniform : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      (Program.cost g (componentPlan p i x) : ℝ) ≤ C * (1 + 4 * p.L1 ^ 2 * p.R ^ 2))
    (k s : ℕ) (w y z : p.E)
    (hw : w ∈ Metric.closedBall p.x0 p.R)
    (hy : y ∈ Metric.closedBall p.x0 p.R) (hz : z ∈ Metric.closedBall p.x0 p.R) :
    let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let F := fun x => H x - H u
    let weight := fun j : ℕ => if j = 0 then (0 : ℝ) else ((2 : ℝ) / (j + 4)) ^ 2
    let d := fun j => (16 * C * β) * weight j
    let h := fun j => 2 * p.n * C + (4 * C * β * p.n * smoothing p * p.R ^ 2) * weight j +
      2 * C * β * p.n * (4 * p.R * tolerance p) + (if j = 0 then 8 * C * p.n * (p.L1 * p.R) ^ 2 else 0)
    let e := fun j : ℕ => p.n * (4 * p.R * tolerance p) / ((2 : ℝ) / (j + 4)) ^ 2
    (𝔼 samples : Fin k → Fin p.n → Fin p.n,
      (Program.cost g (epochsPlan p k samples s w y z) : ℝ)) ≤
      costWeight d s k * startPotential p F u s w y z + costOffset d h e s k := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let weight := fun j : ℕ => if j = 0 then (0 : ℝ) else ((2 : ℝ) / (j + 4)) ^ 2
  let d := fun j => (16 * C * β) * weight j
  let h := fun j => 2 * p.n * C + (4 * C * β * p.n * smoothing p * p.R ^ 2) * weight j +
    2 * C * β * p.n * (4 * p.R * tolerance p) + (if j = 0 then 8 * C * p.n * (p.L1 * p.R) ^ 2 else 0)
  let e := fun j : ℕ => p.n * (4 * p.R * tolerance p) / ((2 : ℝ) / (j + 4)) ^ 2
  have hd j : 0 ≤ d j := by
    dsimp [d, weight]
    split_ifs <;> positivity
  refine epochs_cost_affine p g (startPotential p F u) d h e (costWeight d) (costOffset d h e) hR
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (costWeight_nonneg hd) ?_ ?_ k s w y z hw hy hz
  · intro t a b c ha hb hc
    by_cases ht : t = 0
    · subst t
      have hh := epoch_uniform_cost p g hR (C * (1 + 4 * p.L1 ^ 2 * p.R ^ 2)) huniform 0 a
        (fun i => Program.eval g (componentPlan p i a)) b c ha hb hc
      dsimp [d, h, weight]
      simp only [mul_zero, zero_mul, zero_add, add_zero]
      have herrnonneg : 0 ≤ 2 * C * β * p.n * (4 * p.R * tolerance p) := by positivity
      nlinarith
    · have hh := model_epoch_nominal_cost p g f G hm hR hζ u hu hgu hrad herr C β hC hβ hcost
        t (Nat.one_le_iff_ne_zero.mpr ht) a b c ha hb hc
      dsimp [d, h, weight]
      simp only [ht, ↓reduceIte, add_zero]
      convert hh using 1
      ring
  · intro t a b c ha hb hc
    exact (model_epoch_transition p g f G hm hR hζ u hu hgu hrad herr t a b c ha hb hc).1

lemma model_expected_cost (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (hR : 0 ≤ p.R) (hζ : 0 ≤ tolerance p) (u : p.E)
    (hu : u ∈ Metric.closedBall p.x0 p.R) (hgu : fullGradient G u = 0)
    (hrad : ∀ a ∈ Metric.closedBall p.x0 p.R, ‖a - u‖ ≤ 2 * p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (C β : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hcost : ∀ x ∈ Metric.closedBall p.x0 p.R,
      (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i x) : ℝ)) ≤ C * (1 + β *
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u)))
    (huniform : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      (Program.cost g (componentPlan p i x) : ℝ) ≤ C * (1 + 4 * p.L1 ^ 2 * p.R ^ 2))
    {ι : Type*} [Fintype ι] [Nonempty ι] (w y z : ι → p.E)
    (hw : ∀ i, w i ∈ Metric.closedBall p.x0 p.R)
    (hy : ∀ i, y i ∈ Metric.closedBall p.x0 p.R) (hz : ∀ i, z i ∈ Metric.closedBall p.x0 p.R)
    (hinit : (𝔼 i, startPotential p
      (fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u)
      u 0 (w i) (y i) (z i)) ≤ 14 * smoothing p * p.R ^ 2) :
    (𝔼 i, 𝔼 samples : Fin (epochCount p) → Fin p.n → Fin p.n,
      (Program.cost g (epochsPlan p (epochCount p) samples 0 (w i) (y i) (z i)) : ℝ)) ≤
      C * (2 * p.n * epochCount p + 8 * p.n * (p.L1 * p.R) ^ 2) +
        244 * C * β * p.n * smoothing p * p.R ^ 2 +
          2 * C * β * p.n * (4 * p.R * tolerance p) * epochCount p := by
  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let weight := fun j : ℕ => if j = 0 then (0 : ℝ) else ((2 : ℝ) / (j + 4)) ^ 2
  let d := fun j => (16 * C * β) * weight j
  let h := fun j => 2 * p.n * C + (4 * C * β * p.n * smoothing p * p.R ^ 2) * weight j +
    2 * C * β * p.n * (4 * p.R * tolerance p) + (if j = 0 then 8 * C * p.n * (p.L1 * p.R) ^ 2 else 0)
  let e := fun j : ℕ => p.n * (4 * p.R * tolerance p) / ((2 : ℝ) / (j + 4)) ^ 2
  have hμ := (hm 0).pos
  have hD : 0 ≤ 16 * C * β := by positivity
  have hd j : 0 ≤ d j := by dsimp [d, weight]; split_ifs <;> positivity
  have hweight s k : costWeight d s k ≤ 16 * C * β := costWeight_epoch_bound _ hD s k
  have he' j : 0 ≤ e j := by dsimp [e]; positivity
  have ht i := model_epochs_affine_cost p g f G hm hR hζ u hu hgu hrad herr C β hC hβ hcost huniform
    (epochCount p) 0 (w i) (y i) (z i) (hw i) (hy i) (hz i)
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => ht i)
  change (𝔼 i, 𝔼 samples : Fin (epochCount p) → Fin p.n → Fin p.n,
      (Program.cost g (epochsPlan p (epochCount p) samples 0 (w i) (y i) (z i)) : ℝ)) ≤
    (𝔼 i, (costWeight d 0 (epochCount p) * startPotential p F u 0 (w i) (y i) (z i) + costOffset d h e 0 (epochCount p))) at hav
  simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at hav
  have hscaled := mul_le_mul_of_nonneg_left hinit (costWeight_nonneg hd 0 (epochCount p))
  have hstart := mul_le_mul_of_nonneg_right (hweight 0 (epochCount p))
    (show 0 ≤ 14 * smoothing p * p.R ^ 2 by positivity)
  have hoff := costOffset_bound d h e (16 * C * β) he' hweight 0 (epochCount p)
  simp only [zero_add] at hoff
  have hsum := epoch_overhead_sum (2 * p.n * C) (4 * C * β * p.n * smoothing p * p.R ^ 2)
    (2 * C * β * p.n * (4 * p.R * tolerance p)) (8 * C * p.n * (p.L1 * p.R) ^ 2)
    (by positivity) (by positivity) (epochCount p)
  change (∑ j ∈ Finset.range (epochCount p), h j) ≤ _ at hsum
  have herrsum := total_epoch_error p hμ.le hR hζ
  change (∑ j ∈ Finset.range (epochCount p), e j) ≤ smoothing p * p.R ^ 2 at herrsum
  have herrscaled := mul_le_mul_of_nonneg_left herrsum hD
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast (NeZero.pos p.n)
  have hmore : 16 * C * β * (15 * smoothing p * p.R ^ 2) ≤
      240 * C * β * p.n * smoothing p * p.R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 240 * C * β * smoothing p * p.R ^ 2 by positivity)
    nlinarith
  dsimp only [F, H] at hav hscaled
  nlinarith

lemma model_plan_cost (p : Params) (g : Fin p.n × p.E → p.E)
    (f : Fin p.n → p.E → ℝ) (G : Fin p.n × p.E → p.E)
    (hm : ∀ i, Model (smoothing p) (f i) (fun x => G (i, x)))
    (u : p.E) (hgu : ∀ i, G (i, u) = 0) (hu : ‖p.x0 - u‖ ≤ p.R)
    (herr : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      ‖Program.eval g (componentPlan p i x) - G (i, x)‖ ≤ tolerance p)
    (h0 : 0 < p.L0) (he : 0 < p.ε) (hR : 0 < p.R)
    (C : ℝ) (hC : 0 ≤ C)
    (hcost : ∀ x ∈ Metric.closedBall p.x0 p.R,
      (𝔼 i : Fin p.n, (Program.cost g (componentPlan p i x) : ℝ)) ≤ C * (1 + (2 * p.L1 ^ 2 / smoothing p) *
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u)))
    (huniform : ∀ i x, x ∈ Metric.closedBall p.x0 p.R →
      (Program.cost g (componentPlan p i x) : ℝ) ≤ C * (1 + 4 * p.L1 ^ 2 * p.R ^ 2)) :
    (𝔼 seed : Seeds p, (Program.cost g (plan p seed) : ℝ)) ≤
      C * ((p.n : ℝ) * (4 + 2 * epochCount p) + 752 * p.n * (p.L1 * p.R) ^ 2) := by

  let H := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let F := fun x => H x - H u
  let w := fun samples : Fin (4 * p.n) → Fin p.n =>
    (((4 * p.n : ℕ) : ℝ)⁻¹ • (Program.eval g (warmupPlan p (4 * p.n) samples p.x0 0)).2)
  have hμ := (hm 0).pos
  have hζ := tolerance_pos p h0 he hR
  have hu' : u ∈ Metric.closedBall p.x0 p.R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
  have hx : p.x0 ∈ Metric.closedBall p.x0 p.R := Metric.mem_closedBall_self hR.le
  have hrad (a : p.E) (ha : a ∈ Metric.closedBall p.x0 p.R) : ‖a - u‖ ≤ 2 * p.R := by
    have h1 : ‖a - p.x0‖ ≤ p.R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using ha
    have h2 := norm_add_le (a - p.x0) (p.x0 - u)
    rw [show a - p.x0 + (p.x0 - u) = a - u by module] at h2
    linarith
  have hn : 0 < p.n := NeZero.pos _
  have hk : 0 < 4 * p.n := Nat.mul_pos (by omega) hn
  have hwm samples : w samples ∈ Metric.closedBall p.x0 p.R :=
    warmup_mean_mem p g hR.le (4 * p.n) hk samples p.x0 hx
  have hinit := model_warmup_potential p g f G hm u hgu hu herr h0 he hR
  have hfull : fullGradient G u = 0 := by simp [fullGradient, hgu]
  let β := 2 * p.L1 ^ 2 / smoothing p
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hmain := model_expected_cost p g f G hm hR.le hζ.le u hu' hfull hrad herr C β hC hβ hcost huniform
    w w w hwm hwm hwm hinit
  have hwarm := Finset.expect_le_expect (s := Finset.univ) (fun samples _ =>
    warmup_cost_bound p g hR.le (C * (1 + 4 * p.L1 ^ 2 * p.R ^ 2)) huniform (4 * p.n) samples p.x0 0 hx)
  simp only [Fintype.expect_const, Nat.cast_mul, Nat.cast_ofNat] at hwarm
  have htol := tolerance_cost_error p hμ
  have htol' := mul_le_mul_of_nonneg_left htol (show 0 ≤ 2 * C * p.n by positivity)
  have hid : 244 * C * β * p.n * smoothing p * p.R ^ 2 = 488 * C * p.n * (p.L1 * p.R) ^ 2 := by
    dsimp [β]
    field_simp
    ring
  rw [hid] at hmain
  change (𝔼 seed : (Fin (4 * p.n) → Fin p.n) × (Fin (epochCount p) → Fin p.n → Fin p.n),
    (Program.cost g (plan p seed) : ℝ)) ≤ _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp only [plan, Program.cost_bind, Nat.cast_add, Finset.expect_add_distrib, Fintype.expect_const]
  change (𝔼 samples : Fin (4 * p.n) → Fin p.n, (Program.cost g (warmupPlan p (4 * p.n) samples p.x0 0) : ℝ)) +
    (𝔼 i, 𝔼 samples : Fin (epochCount p) → Fin p.n → Fin p.n,
      (Program.cost g (epochsPlan p (epochCount p) samples 0 (w i) (w i) (w i)) : ℝ)) ≤ _
  have hpos : 0 ≤ C * p.n * (p.L1 * p.R) ^ 2 := by positivity
  change _ ≤ 2 * C * p.n * (p.L1 * p.R) ^ 2 at htol'
  change 2 * C * p.n * (β * (4 * p.R * tolerance p) * epochCount p) ≤ _ at htol'
  nlinarith

end OracleTemplate.ComponentEnvelope
