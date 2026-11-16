import LongTails.Proofs.GapCalibratedConjugate
import LongTails.Proofs.GapBoundedSmoothChain
import LongTails.Proofs.CompactMollification
import LongTails.Proofs.GeneralizedSmoothChainPrefix

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapChainPrefix

local instance pointMeasurableSpace (m : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin m)) :=
  WithLp.measurableSpace 2 (Fin m → ℝ)

open CompactConjugate GeneralizedSmoothHardChain

lemma conjugate_prefix {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (H : EuclideanSpace ℝ (Fin m) → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hH : ContinuousOn H K) (j : Fin m) (x y : EuclideanSpace ℝ (Fin m))
    (hxy : ∀ i, i ≤ j → x i = y i)
    (hx : ∀ i, j < i → maximizer K H x i = 0)
    (hy : ∀ i, j < i → maximizer K H y i = 0)
    (M : ℝ) (hM : 0 < M)
    (hgrowth : ⟪x, maximizer K H y⟫ - H (maximizer K H y) +
      ‖maximizer K H x - maximizer K H y‖ ^ 2 / (2 * M) ≤ value K H x) :
    maximizer K H x = maximizer K H y ∧ value K H x = value K H y := by
  let u := maximizer K H x
  let v := maximizer K H y
  have hu := maximizer_spec hK hne hH x
  have hv := maximizer_spec hK hne hH y
  have heu := inner_prefix_eq j x y u hxy hx
  have hev := inner_prefix_eq j x y v hxy hy
  have ho : ⟪y, u⟫ - H u ≤ ⟪y, v⟫ - H v := hv.2 hu.1
  change ⟪x, v⟫ - H v + ‖u - v‖ ^ 2 / (2 * M) ≤ ⟪x, u⟫ - H u at hgrowth
  rw [heu, hev] at hgrowth
  have hn : ‖u - v‖ ^ 2 / (2 * M) ≤ 0 := by linarith
  have hs := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp hn
  have he : u = v := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (u - v)]
  refine ⟨he, ?_⟩
  change ⟪x, u⟫ - H u = ⟪y, v⟫ - H v
  rw [heu, he]

lemma smooth_prefix {m : ℕ} (L G b τ : ℝ) (hL : 0 < L) (hG : 0 < G)
    (hb : 0 ≤ b) (hsep : G / L + 2 * τ < b) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -τ ≤ x j) (hxt : ∀ i, j < i → x i ≤ τ) (hyt : ∀ i, j < i → y i ≤ τ) :
    GapBoundedSmoothChain.field L G b x = GapBoundedSmoothChain.field L G b y ∧
    GapBoundedSmoothChain.objective L G b x = GapBoundedSmoothChain.objective L G b y := by
  let K := GeneralizedSmoothHardDual.feasible (fun _ : Fin m => G)
  let H := GapBoundedSmoothDual.quadratic (m := m) L
  let σ := GapBoundedSmoothChain.shift m b
  have hK := GeneralizedSmoothHardDual.feasible_compact (fun _ : Fin m => G) G
    (fun _ => hG) hG.le (fun _ => le_rfl)
  have hne : K.Nonempty := ⟨0, GeneralizedSmoothHardDual.feasible_zero _⟩
  have hH : ContinuousOn H K := (GapBoundedSmoothDual.quadratic_continuous L).continuousOn
  have hu := maximizer_spec hK hne hH (x + σ)
  have hv := maximizer_spec hK hne hH (y + σ)
  have hyj : -τ ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  apply conjugate_prefix K H hK hne hH j (x + σ) (y + σ)
  · intro i hi
    change x i + σ i = y i + σ i
    rw [hxy i hi]
  · intro i hi
    exact GapBoundedSmoothChain.field_tail_zero L G b τ hL hG hb hsep x j i hi hxj (hxt i hi)
  · intro i hi
    exact GapBoundedSmoothChain.field_tail_zero L G b τ hL hG hb hsep y j i hi hyj (hyt i hi)
  · exact hL
  · exact GapBoundedSmoothDual.optimizer_growth L G (x + σ) _ _ hu.1 hv.1 hu.2

lemma generalized_prefix {m : ℕ} (hm : 0 < m) (L₀ L₁ B A τ : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
    (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) (hA : 0 ≤ A) (j : Fin m)
    (horder : ∀ i, j < i → G i ≤ G j)
    (hsep : ∀ i, j < i → τ * (G j + G i) < 2 * (G j - G i) / L₁)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -τ ≤ x j) (hxt : ∀ i, j < i → x i ≤ τ) (hyt : ∀ i, j < i → y i ≤ τ) :
    GapCalibratedConjugate.field L₀ L₁ B A G x = GapCalibratedConjugate.field L₀ L₁ B A G y ∧
    GapCalibratedConjugate.objective L₀ L₁ B A G x = GapCalibratedConjugate.objective L₀ L₁ B A G y := by
  let K := GeneralizedSmoothHardDual.feasible G
  let H := GeneralizedSmoothHardDual.dual (m := m) L₀ L₁
  let σ := GapCalibratedConjugate.constantVector m A + GeneralizedSmoothHardTransfer.shift L₀ L₁ B G
  have hK := GeneralizedSmoothHardDual.feasible_compact G B hG hB hGB
  have hne : K.Nonempty := ⟨0, GeneralizedSmoothHardDual.feasible_zero G⟩
  have hH := GeneralizedSmoothHardDual.dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G
  have hu := maximizer_spec hK hne hH (x + σ)
  have hv := maximizer_spec hK hne hH (y + σ)
  have hyj : -τ ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have ht := conjugate_prefix K H hK hne hH j (x + σ) (y + σ)
    (fun i hi => by change x i + σ i = y i + σ i; rw [hxy i hi])
    (fun i hi => by
      simpa only [σ, GapCalibratedConjugate.field, ← add_assoc] using
        GapCalibratedConjugate.field_tail_zero hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB hA τ j i hi
          (horder i hi) x hxj (hxt i hi) (hsep i hi))
    (fun i hi => by
      simpa only [σ, GapCalibratedConjugate.field, ← add_assoc] using
        GapCalibratedConjugate.field_tail_zero hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB hA τ j i hi
          (horder i hi) y hyj (hyt i hi) (hsep i hi))
    (L₀ + L₁ * max ‖maximizer K H (x + σ)‖ ‖maximizer K H (y + σ)‖) (by positivity)
    (GeneralizedSmoothHardDualSegments.dual_optimizer_growth hm L₀ L₁ hL₀ hL₁ G
      (x + σ) _ _ hu.1 hv.1 hu.2)
  simpa only [GapCalibratedConjugate.field, GapCalibratedConjugate.objective, σ,
    K, H, add_assoc] using ht

lemma average_prefix {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (τ θ : ℝ) (hθ : θ + φ.rOut ≤ τ) (j : Fin m)
    (hprefix : ∀ x y : EuclideanSpace ℝ (Fin m), (∀ i, i ≤ j → x i = y i) →
      -τ ≤ x j → (∀ i, j < i → x i ≤ τ) → (∀ i, j < i → y i ≤ τ) → f x = f y)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -θ ≤ x j) (hxt : ∀ i, j < i → x i ≤ θ) (hyt : ∀ i, j < i → y i ≤ θ) :
    CompactMollification.average φ f x = CompactMollification.average φ f y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  apply hprefix
  · intro i hi
    change x i - CompactMollification.noise φ z i = y i - CompactMollification.noise φ z i
    rw [hxy i hi]
  · have hn := (abs_le.mp ((PiLp.norm_apply_le (CompactMollification.noise φ z) j).trans
      (CompactMollification.noise_norm φ z))).2
    change -τ ≤ x j - CompactMollification.noise φ z j
    linarith
  · intro i hi
    have hn := (abs_le.mp ((PiLp.norm_apply_le (CompactMollification.noise φ z) i).trans
      (CompactMollification.noise_norm φ z))).1
    have hh := hxt i hi
    change x i - CompactMollification.noise φ z i ≤ τ
    linarith
  · intro i hi
    have hn := (abs_le.mp ((PiLp.norm_apply_le (CompactMollification.noise φ z) i).trans
      (CompactMollification.noise_norm φ z))).1
    have hh := hyt i hi
    change y i - CompactMollification.noise φ z i ≤ τ
    linarith

lemma average_tail {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hc : Continuous g)
    (τ θ : ℝ) (hθ : θ + φ.rOut ≤ τ) (j l : Fin m)
    (htail : ∀ x : EuclideanSpace ℝ (Fin m), -τ ≤ x j → x l ≤ τ → g x l = 0)
    (x : EuclideanSpace ℝ (Fin m)) (hxj : -θ ≤ x j) (hxl : x l ≤ θ) :
    CompactMollification.average φ g x l = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) : g (x - CompactMollification.noise φ z) l = 0 := by
    apply htail
    · have hn := (abs_le.mp ((PiLp.norm_apply_le (CompactMollification.noise φ z) j).trans
        (CompactMollification.noise_norm φ z))).2
      change -τ ≤ x j - CompactMollification.noise φ z j
      linarith
    · have hn := (abs_le.mp ((PiLp.norm_apply_le (CompactMollification.noise φ z) l).trans
        (CompactMollification.noise_norm φ z))).1
      change x l - CompactMollification.noise φ z l ≤ τ
      linarith
  have hi := CompactMollification.average_integrable φ g hc x
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) l).integral_comp_comm hi
  change (∫ z, g (x - CompactMollification.noise φ z) l ∂(CompactMollification.probability φ : Measure _)) =
    CompactMollification.average φ g x l at hp
  rw [← hp]
  simp only [hz, integral_zero]

lemma truncated_pair {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (θ : ℝ) (hθ : 0 ≤ θ) (j : Fin m)
    (hprefix : ∀ x y : EuclideanSpace ℝ (Fin m), (∀ i, i ≤ j → x i = y i) →
      -θ ≤ x j → (∀ i, j < i → x i ≤ θ) → (∀ i, j < i → y i ≤ θ) →
      g x = g y ∧ f x = f y)
    (htail : ∀ x : EuclideanSpace ℝ (Fin m), ∀ i, j < i → -θ ≤ x j → x i ≤ θ → g x i = 0)
    (x : EuclideanSpace ℝ (Fin m)) (hx : ∀ i, j ≤ i → |x i| ≤ θ) :
    f (GeneralizedSmoothChainPrefix.truncate j.val x) = f x ∧
      GeneralizedSmoothChainPrefix.truncate j.val (g (GeneralizedSmoothChainPrefix.truncate j.val x)) = g x := by
  have hh := hprefix x (GeneralizedSmoothChainPrefix.truncate j.val x)
    (fun i hi => by simp only [GeneralizedSmoothChainPrefix.truncate, WithLp.ofLp_toLp, show i.val ≤ j.val from hi, ↓reduceIte])
    (abs_le.mp (hx j le_rfl)).1
    (fun i hi => (abs_le.mp (hx i hi.le)).2)
    (fun i hi => by simpa only [GeneralizedSmoothChainPrefix.truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ j.val by omega, ↓reduceIte] using hθ)
  refine ⟨hh.2.symm, ?_⟩
  rw [← hh.1]
  apply GeneralizedSmoothChainPrefix.truncate_eq_self
  intro i hi
  exact htail x i hi (abs_le.mp (hx j le_rfl)).1 (abs_le.mp (hx i (by omega))).2

end LongTails.Proofs.GapChainPrefix
