import LongTails.Proofs.EscapeChainCoin
import LongTails.Proofs.AbcLowerMeasure

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.EscapeChainFreeze

open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcLowerMeasure EscapeChainCoin
open OracleTemplate.StochasticGeneralized

variable {S : Type*} [MeasurableSpace S]

noncomputable def extend (t : ℕ) (pre : Fin t → ℝ) : ℕ → ℝ := (splitStream (Ω := ℝ) t).symm (pre, 0)

lemma extend_apply_lt {t : ℕ} (pre : Fin t → ℝ) {s : ℕ} (hs : s < t) : extend t pre s = pre ⟨s, hs⟩ := by
  simp [extend, splitStream, hs]

lemma split_fst (t : ℕ) (ω : ℕ → ℝ) (s : Fin t) : (splitStream (Ω := ℝ) t ω).1 s = ω s := rfl

lemma split_snd (t : ℕ) (ω : ℕ → ℝ) : (splitStream (Ω := ℝ) t ω).2 0 = ω t := by
  simp [splitStream]

lemma extend_agree (t : ℕ) (ω : ℕ → ℝ) :
    ∀ s < t, extend t (splitStream (Ω := ℝ) t ω).1 s = ω s := by
  intro s hs
  rw [extend_apply_lt _ hs, split_fst]

lemma extend_measurable (t : ℕ) : Measurable (extend t) := by
  unfold extend
  exact (splitStream (Ω := ℝ) t).symm.measurable.comp (measurable_id.prodMk measurable_const)

theorem freeze (μ : Measure S) [IsProbabilityMeasure μ] (t : ℕ)
    (φ : S × (ℕ → ℝ) → ENNReal) (a p : S × (ℕ → ℝ) → ℝ)
    (hφ : Measurable φ) (ha : Measurable a) (hp : Measurable p)
    (hφt : ∀ z ω', (∀ s < t, z.2 s = ω' s) → φ (z.1, ω') = φ z)
    (hat : ∀ z ω', (∀ s < t, z.2 s = ω' s) → a (z.1, ω') = a z)
    (hpt : ∀ z ω', (∀ s < t, z.2 s = ω' s) → p (z.1, ω') = p z)
    (h0 : ∀ z, 0 ≤ a z) (h2 : ∀ z, a z + p z ≤ 1) :
    ∫⁻ z, φ z * (if a z ≤ z.2 t ∧ z.2 t < a z + p z then 1 else 0) ∂(μ.prod stream) =
      ∫⁻ z, φ z * ENNReal.ofReal (p z) ∂(μ.prod stream) := by
  classical
  set e := splitStream (Ω := ℝ) t
  have he : MeasurePreserving e stream
      ((Measure.pi fun _ : Fin t => unif).prod (Measure.infinitePi fun _ : ℕ => unif)) :=
    splitStream_preserving unif t
  let Φ : S × (Fin t → ℝ) → ENNReal := fun w => φ (w.1, extend t w.2)
  let a' : S × (Fin t → ℝ) → ℝ := fun w => a (w.1, extend t w.2)
  let p' : S × (Fin t → ℝ) → ℝ := fun w => p (w.1, extend t w.2)
  have hΦm : Measurable Φ := hφ.comp (measurable_fst.prodMk ((extend_measurable t).comp measurable_snd))
  have ha'm : Measurable a' := ha.comp (measurable_fst.prodMk ((extend_measurable t).comp measurable_snd))
  have hp'm : Measurable p' := hp.comp (measurable_fst.prodMk ((extend_measurable t).comp measurable_snd))
  have hrep : ∀ z : S × (ℕ → ℝ), φ z = Φ (z.1, (e z.2).1) ∧ a z = a' (z.1, (e z.2).1) ∧
      p z = p' (z.1, (e z.2).1) := by
    intro z
    have hag : ∀ s < t, z.2 s = extend t (e z.2).1 s := fun s hs => (extend_agree t z.2 s hs).symm
    exact ⟨(hφt z _ hag).symm, (hat z _ hag).symm, (hpt z _ hag).symm⟩
  have hpres : MeasurePreserving (Prod.map id e) (μ.prod stream)
      (μ.prod ((Measure.pi fun _ : Fin t => unif).prod (Measure.infinitePi fun _ : ℕ => unif))) :=
    (MeasurePreserving.id μ).prod he
  set ν := (Measure.pi fun _ : Fin t => unif).prod (Measure.infinitePi fun _ : ℕ => unif)
  let G : S × ((Fin t → ℝ) × (ℕ → ℝ)) → ENNReal := fun w =>
    Φ (w.1, w.2.1) * (if a' (w.1, w.2.1) ≤ w.2.2 0 ∧ w.2.2 0 < a' (w.1, w.2.1) + p' (w.1, w.2.1)
      then 1 else 0)
  let H : S × ((Fin t → ℝ) × (ℕ → ℝ)) → ENNReal := fun w =>
    Φ (w.1, w.2.1) * ENNReal.ofReal (p' (w.1, w.2.1))
  have hG : Measurable G := by
    refine (hΦm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    have hA : Measurable fun w : S × ((Fin t → ℝ) × (ℕ → ℝ)) => a' (w.1, w.2.1) :=
      ha'm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hP : Measurable fun w : S × ((Fin t → ℝ) × (ℕ → ℝ)) => p' (w.1, w.2.1) :=
      hp'm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hT : Measurable fun w : S × ((Fin t → ℝ) × (ℕ → ℝ)) => w.2.2 0 :=
      (measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd)
    exact (measurableSet_le hA hT).inter (measurableSet_lt hT (hA.add hP))
  have hH : Measurable H :=
    (hΦm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (hp'm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))))
  have hL : ∫⁻ z, φ z * (if a z ≤ z.2 t ∧ z.2 t < a z + p z then 1 else 0) ∂(μ.prod stream) =
      ∫⁻ w, G w ∂(μ.prod ν) := by
    rw [← hpres.lintegral_comp hG]
    refine lintegral_congr fun z => ?_
    obtain ⟨r1, r2, r3⟩ := hrep z
    have hs : (e z.2).2 0 = z.2 t := split_snd t z.2
    simp only [G, Prod.map, id, r1, r2, r3, hs]
  have hR : ∫⁻ z, φ z * ENNReal.ofReal (p z) ∂(μ.prod stream) = ∫⁻ w, H w ∂(μ.prod ν) := by
    rw [← hpres.lintegral_comp hH]
    refine lintegral_congr fun z => ?_
    obtain ⟨r1, r2, r3⟩ := hrep z
    simp only [H, Prod.map, id, r1, r3]
  rw [hL, hR, lintegral_prod _ hG.aemeasurable, lintegral_prod _ hH.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hGx : Measurable fun y => G (x, y) := hG.comp (measurable_const.prodMk measurable_id)
  have hHx : Measurable fun y => H (x, y) := hH.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hGx.aemeasurable, lintegral_prod _ hHx.aemeasurable]
  refine lintegral_congr fun pre => ?_
  simp only [G, H]
  have hset : MeasurableSet {tail : ℕ → ℝ | a' (x, pre) ≤ tail 0 ∧ tail 0 < a' (x, pre) + p' (x, pre)} :=
    (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt (measurable_pi_apply 0) measurable_const)
  have hind : (fun tail : ℕ → ℝ => Φ (x, pre) * (if a' (x, pre) ≤ tail 0 ∧
      tail 0 < a' (x, pre) + p' (x, pre) then 1 else 0)) =
      Set.indicator {tail : ℕ → ℝ | a' (x, pre) ≤ tail 0 ∧ tail 0 < a' (x, pre) + p' (x, pre)}
        (fun _ => Φ (x, pre)) := by
    funext tail; simp only [Set.indicator, Set.mem_ofPred_eq]; split_ifs <;> simp
  rw [hind, lintegral_indicator hset, setLIntegral_const, lintegral_const, measure_univ, mul_one]
  have hmap : (Measure.infinitePi fun _ : ℕ => unif) {tail : ℕ → ℝ |
      a' (x, pre) ≤ tail 0 ∧ tail 0 < a' (x, pre) + p' (x, pre)} =
      unif (Set.Ico (a' (x, pre)) (a' (x, pre) + p' (x, pre))) := by
    have hsetEq : {tail : ℕ → ℝ | a' (x, pre) ≤ tail 0 ∧ tail 0 < a' (x, pre) + p' (x, pre)} =
        (fun f : ℕ → ℝ => f 0) ⁻¹' Set.Ico (a' (x, pre)) (a' (x, pre) + p' (x, pre)) := by
      ext tail; simp [Set.mem_Ico]
    rw [hsetEq, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ico,
      Measure.infinitePi_map_eval]
  rw [hmap, unif_Ico (h0 _) (h2 _)]

end LongTails.Proofs.EscapeChainFreeze
