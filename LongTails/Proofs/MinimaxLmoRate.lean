import LongTails.Algorithms.MinimaxLmoGda
import LongTails.Proofs.MinimaxLmoAssembly
import LongTails.Proofs.MinimaxLmoParameters
import LongTails.Proofs.Execution

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO constantMomentum)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax clip lmoGda)
open LongTails.Algorithms.MinimaxLmoGda (constantGda)
open OracleTemplate.NormBallLMO

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω]

lemma gda_output_integral (lmo : Space d₁ → Space d₁) (hlmo : Measurable lmo) (γ a β c : ℝ) (T : ℕ)
    (x₁ : Space d₁) (y₁ : Space d₂) {ox : Space d₁ → Space d₂ → Ω → Space d₁}
    {oy : Space d₁ → Space d₂ → Ω → Space d₂}
    (hox : Measurable (fun z : (Space d₁ × Space d₂) × Ω => ox z.1.1 z.1.2 z.2))
    (hoy : Measurable (fun z : (Space d₁ × Space d₂) × Ω => oy z.1.1 z.1.2 z.2))
    (P₀ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (P₀ : Measure Ω) (P : Measure (ℕ → Ω)))
    (K : ℕ) (hK : T ≤ K) (F : Space d₁ → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : ∀ j, j ≤ T → ∀ ξ, |F (cpath lmo γ a β c x₁ y₁ ox oy ξ j).1| ≤ B) :
    Measurable (fun seed : (constantGda lmo x₁ y₁ T γ a β c).Seed × ((k : ℕ) → Ω) =>
        execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } :
          Oracle (Space d₁ × Space d₂) (Space d₁ × Space d₂)) (constantGda lmo x₁ y₁ T γ a β c)
          (fun _ => K) seed.1 seed.2) ∧
      Integrable (fun seed : (constantGda lmo x₁ y₁ T γ a β c).Seed × ((k : ℕ) → Ω) =>
        F (execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } :
          Oracle (Space d₁ × Space d₂) (Space d₁ × Space d₂)) (constantGda lmo x₁ y₁ T γ a β c)
          (fun _ => K) seed.1 seed.2))
        (((constantGda lmo x₁ y₁ T γ a β c).law : Measure _).prod (P : Measure (ℕ → Ω))) ∧
      ∫ seed : (constantGda lmo x₁ y₁ T γ a β c).Seed × ((k : ℕ) → Ω),
          F (execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } :
            Oracle (Space d₁ × Space d₂) (Space d₁ × Space d₂)) (constantGda lmo x₁ y₁ T γ a β c)
            (fun _ => K) seed.1 seed.2)
          ∂(((constantGda lmo x₁ y₁ T γ a β c).law : Measure _).prod (P : Measure (ℕ → Ω))) =
        1 / ((T : ℝ) + 1) * ∫ ξ, ∑ j ∈ Finset.range (T + 1), F (cpath lmo γ a β c x₁ y₁ ox oy ξ j).1
          ∂(Measure.infinitePi fun _ : ℕ => (P₀ : Measure Ω)) := by
  have hP : (P : Measure (ℕ → Ω)) = Measure.infinitePi fun _ : ℕ => (P₀ : Measure Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → Ω)))).symm.trans this
  have hexec : ∀ seed : (constantGda lmo x₁ y₁ T γ a β c).Seed × ((k : ℕ) → Ω),
      execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } :
        Oracle (Space d₁ × Space d₂) (Space d₁ × Space d₂)) (constantGda lmo x₁ y₁ T γ a β c)
        (fun _ => K) seed.1 seed.2 =
      (cpath lmo γ a β c x₁ y₁ ox oy seed.2 (seed.1 : Fin (T + 1)).val).1 :=
    fun seed => execute_lmoGda lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy T
      (PMF.uniformOfFintype (Fin (T + 1))) P K hK seed.1 seed.2
  have hpath := measurable_gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy
    hlmo hox hoy
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) => (cpath lmo γ a β c x₁ y₁ ox oy ω.2 ω.1.val).1) :=
    measurable_from_prod_countable_right fun j => (hpath j.val).fst
  have hu := uniform_integral (μ := (P : Measure (ℕ → Ω)))
    (fun (j : Fin (T + 1)) ξ => F (cpath lmo γ a β c x₁ y₁ ox oy ξ j.val).1)
    (fun j => hF.comp (hpath j.val).fst) (fun j ξ => hB j.val (Nat.lt_succ_iff.mp j.isLt) ξ)
  simp only [hexec]
  refine ⟨hm, hu.1, ?_⟩
  have h2 := hu.2
  rw [Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, F (cpath lmo γ a β c x₁ y₁ ox oy ξ j).1 ∂(P : Measure _))] at h2
  rw [← hP]
  refine h2.trans ?_
  congr 1
  rw [integral_finsetSum]
  intro j hj
  exact Integrable.of_bound (hF.comp (hpath j).fst).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact hB j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) ξ)

lemma gda_pos (p : LongTails.Setups.MinimaxLmo.Params) (hp : LongTails.Setups.MinimaxLmo.spec.valid p)
    {κ d q ϑx ϑy ω ℓ Lx y θi ib ia x cc γ a β c : ℝ} {T : ℕ}
    (hκ : κ = p.L₀ / p.μ) (hd : d = 32 * p.L₀ * p.Δ / p.ε ^ 2 + 1) (hq : q = Real.sqrt ((1 + κ) * d))
    (hϑx : ϑx = p.ζ * p.σx / p.ε) (hϑy : ϑy = p.σy / p.ε) (hω : ω = p.L₀ * p.W / p.ε)
    (hℓ : ℓ = p.L₁ * p.ε / p.L₀)
    (hLx : Lx = 40 * Real.log (2 ^ 20 * (2 + κ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + ϑx + ϑy + ω + ℓ)))
    (hy : y = q + Lx) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hia : ia = 8192 * ϑx ^ 2 + 1)
    (hx : x = 4 * ω / 3 + y / (48 * (1 + ℓ * y)))
    (hcc : cc = κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2))
    (hγ : γ = d * (p.ε / p.L₀) / (((T : ℝ) + 1) * p.ρ)) (ha : a = 1 / ia) (hβ : β = 1 / (ib * p.μ))
    (hc : c = cc * p.ε) :
    0 ≤ γ ∧ 0 < a ∧ a ≤ 1 ∧ 0 ≤ β ∧ 0 < c := by
  obtain ⟨-, hρ, -, -, hζ0, -, hμ, hμL, hL₁, hσx, hσy, hΔ, hW, -, hε⟩ := hp
  have hL₀ : 0 < p.L₀ := lt_of_lt_of_le hμ hμL
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  have hd1 : 1 ≤ d := by
    have : 0 ≤ 32 * p.L₀ * p.Δ / p.ε ^ 2 := by positivity
    rw [hd]; linarith
  have hϑx0 : 0 ≤ ϑx := by rw [hϑx]; positivity
  have hϑy0 : 0 ≤ ϑy := by rw [hϑy]; positivity
  have hω0 : 0 ≤ ω := by rw [hω]; positivity
  have hLx0 : 0 ≤ Lx := by
    rw [hLx]
    have : 1 ≤ 2 ^ 20 * (2 + κ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + ϑx + ϑy + ω + ℓ) := by
      have : 0 ≤ 32 * p.L₀ * p.Δ / p.ε ^ 2 := by positivity
      nlinarith
    have := Real.log_nonneg this
    positivity
  have hy0 : 0 < y := by
    have : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr (by positivity)
    rw [hy]; linarith
  have hia1 : 1 ≤ ia := by
    have : 0 ≤ 8192 * ϑx ^ 2 := by positivity
    rw [hia]; linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  refine ⟨by rw [hγ]; positivity, by rw [ha]; positivity, by rw [ha, div_le_one (by linarith)]; exact hia1,
    by rw [hβ, hib, hθ]; positivity, by rw [hc, hcc]; positivity⟩

set_option maxHeartbeats 4000000 in
lemma minimax_core (p : LongTails.Setups.MinimaxLmo.Params) (hp : LongTails.Setups.MinimaxLmo.spec.valid p)
    (f : Space p.d₁ → Space p.d₂ → ℝ)
    (O : Oracle (Space p.d₁ × Space p.d₂) (Space p.d₁ × Space p.d₂))
    (hadm : LongTails.Setups.MinimaxLmo.spec.admissible p f O)
    {κ d q ϑx ϑy ω ℓ Lx y B θi ib ia x cc γ a β c : ℝ} {T : ℕ}
    (hκ : κ = p.L₀ / p.μ) (hd : d = 32 * p.L₀ * p.Δ / p.ε ^ 2 + 1) (hq : q = Real.sqrt ((1 + κ) * d))
    (hϑx : ϑx = p.ζ * p.σx / p.ε) (hϑy : ϑy = p.σy / p.ε) (hω : ω = p.L₀ * p.W / p.ε)
    (hℓ : ℓ = p.L₁ * p.ε / p.L₀)
    (hLx : Lx = 40 * Real.log (2 ^ 20 * (2 + κ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + ϑx + ϑy + ω + ℓ)))
    (hy : y = q + Lx)
    (hB : B = 2 ^ 39 * (1 + κ) * (1 + ℓ * (1 + y)) ^ 4 * (d + ω + q + ϑx) * (ϑx ^ 2 + κ ^ 2 * (1 + y + ϑy ^ 2)))
    (hT : T = ⌈B⌉₊) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hia : ia = 8192 * ϑx ^ 2 + 1)
    (hx : x = 4 * ω / 3 + y / (48 * (1 + ℓ * y)))
    (hcc : cc = κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2))
    (hγ : γ = d * (p.ε / p.L₀) / (((T : ℝ) + 1) * p.ρ)) (ha : a = 1 / ia) (hβ : β = 1 / (ib * p.μ))
    (hc : c = cc * p.ε) :
    LongTails.Setups.MinimaxLmo.spec.successful p f
      (fun seed : (constantGda p.lmo p.x₁ p.y₁ T γ a β c).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (constantGda p.lmo p.x₁ p.y₁ T γ a β c) (fun _ => T) seed.1 seed.2)
      ⟨((constantGda p.lmo p.x₁ p.y₁ T γ a β c).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hdef, hρ, hlmo, hR, hζ0, hζ, hμ, hμL, hL₁, hσx, hσy, hΔ, hW, hLW, hε⟩ := hp
  obtain ⟨gx, gy, ox, oy, P₀, P, hIID, rfl, H⟩ := hadm
  have hL₀ : 0 < p.L₀ := lt_of_lt_of_le hμ hμL
  obtain ⟨u, hu⟩ : ∃ u, p.ε / p.L₀ = u := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [← hu]; positivity
  have hκ1 : 1 ≤ κ := by rw [hκ, le_div_iff₀ hμ]; linarith only [hμL]
  have hκ0 : 0 < κ := by linarith only [hκ1]
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  have hd1 : 1 ≤ d := by
    have : 0 ≤ 32 * p.L₀ * p.Δ / p.ε ^ 2 := by positivity
    rw [hd]; linarith only [this]
  have hϑx0 : 0 ≤ ϑx := by rw [hϑx]; positivity
  have hϑy0 : 0 ≤ ϑy := by rw [hϑy]; positivity
  have hω0 : 0 ≤ ω := by rw [hω]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hqpos : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = (1 + κ) * d := by rw [hq, Real.sq_sqrt (by positivity)]
  rw [show 2 + κ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + ϑx + ϑy + ω + ℓ = 1 + κ + d + ϑx + ϑy + ω + ℓ by
    rw [hd]; ring] at hLx
  have hLx0 : 0 ≤ Lx := by
    rw [hLx]
    have : 1 ≤ 2 ^ 20 * (1 + κ + d + ϑx + ϑy + ω + ℓ) := by
      linarith only [hκ1, hd1, hϑx0, hϑy0, hω0, hℓ0]
    have := Real.log_nonneg this
    positivity
  have hℓω : 32 * ℓ * ω ≤ 1 := by
    have e : 32 * ℓ * ω = 32 * p.L₁ * p.W := by rw [hℓ, hω]; field_simp
    rw [e]; exact hLW
  have hL₀u : p.L₀ = p.ε / u := by rw [← hu]; field_simp
  have hμu : p.μ = p.ε / (κ * u) := by rw [hκ, ← hu]; field_simp
  have hL₁u : p.L₁ = ℓ / u := by rw [hℓ, ← hu]; field_simp
  have hσyu : p.σy = ϑy * p.ε := by rw [hϑy]; field_simp
  have hWu : p.W = ω * u := by rw [hω, ← hu]; field_simp
  have hΔu : p.Δ ≤ d * p.ε * u / 32 := by
    have e : d * p.ε * u / 32 = p.Δ + p.ε ^ 2 / (32 * p.L₀) := by rw [hd, ← hu]; field_simp
    have : 0 ≤ p.ε ^ 2 / (32 * p.L₀) := by positivity
    rw [e]; linarith only [this]
  have hζσ : p.ζ * p.σx = ϑx * p.ε := by rw [hϑx]; field_simp
  have hB0 : 0 ≤ B := by rw [hB, hy]; positivity
  have hTB : B ≤ (T : ℝ) := by rw [hT]; exact Nat.le_ceil B
  have hTB2 : (T : ℝ) < B + 1 := by rw [hT]; exact Nat.ceil_lt_add_one hB0
  have hn0 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ (T : ℝ) + 1 := by
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    linarith only [this]
  have hBn : B ≤ (T : ℝ) + 1 := by linarith only [hTB]
  have hs : γ * p.ρ = d * u / ((T : ℝ) + 1) := by rw [hγ, ← hu]; field_simp
  obtain ⟨R1, R2, R3, R4, R5, R6, R7, R8⟩ := tune_budget (g := (5 * q + ℓ * q ^ 2) / 12) hκ1 hℓ0 hd1 hϑx0
    hω0 hq0 hq2 hLx0 hy hθ hib hia rfl hB
  have hia1 : 1 ≤ ia := by
    have : 0 ≤ 8192 * ϑx ^ 2 := by positivity
    rw [hia]; linarith only [this]
  obtain ⟨hs0, ha0, ha1, hsa, hr16, hβ0, hβ2, hβμ, hc0, hrc, hr0, hWr, hlam0, hlamB, hcond, hΛ⟩ :=
    tune_phys (r := x * u) (lam := 1 / (β * c + p.L₀ / p.μ * (γ * p.ρ))) hε hu0 hκ1 hℓ0 hd1 hq0 hq2 hω0 hℓω
      hLx0 hy hθ hib hia1 hx hcc hn0 (by linarith only [R6, hBn]) (by linarith only [R7, hBn]) (by linarith only [R8, hBn]) hL₀u hμu hL₁u hσyu hWu hs rfl
      hc hβ rfl ha
  have hγ0 : 0 < γ := by
    have := hs0
    by_contra h
    push Not at h
    have : γ * p.ρ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hρ.le
    linarith only [this, hs0]
  have hlmo_m : Measurable p.lmo := hlmo.measurable
  have hR0 : 0 ≤ p.R := by have := hR 0 (by simp); simpa using this
  obtain ⟨ht0, htL, hGt⟩ := tune_G0 (t := q * u / (2 * (1 + κ) * (1 + ℓ * q))) hε hu0 hκ0 hℓ0 hqpos hq2
    hL₀u hμu hL₁u hΔu rfl
  have hG₀0 : 0 ≤ dualNorm p.N (gPhi H hμ p.x₁) := dualNorm_nonneg hR _
  have hG₀ : dualNorm p.N (gPhi H hμ p.x₁) ≤ p.ε * ((5 * q + ℓ * q ^ 2) / 12) :=
    (G_initial H hμ hR hdef hL₀.le hL₁ ht0 htL).trans hGt
  have hloc : p.L₁ * (γ * p.ρ) ≤ 1 := by
    have h1 : 16 * (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ) ≤ 1 := hsa.trans ha1
    have h2 : 0 ≤ p.L₀ / p.μ * p.L₁ * (γ * p.ρ) := by positivity
    linarith only [h1, h2]
  have hlocK : p.L₁ * ((1 + p.L₀ / p.μ) * (γ * p.ρ)) ≤ 1 := by
    have h1 : 16 * (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ) ≤ 1 := hsa.trans ha1
    have h2 : 0 ≤ (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ) := by positivity
    have e : p.L₁ * ((1 + p.L₀ / p.μ) * (γ * p.ρ)) = (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ) := by ring
    linarith only [h1, h2, e]
  have hgrad_out : ∀ j, j ≤ T → ∀ ξ : ℕ → p.Ω,
      |dualNorm p.N (gPhi H hμ (cpath p.lmo γ a β c p.x₁ p.y₁ ox oy ξ j).1)| ≤
        (dualNorm p.N (gPhi H hμ p.x₁) + (1 + p.L₀ / p.μ) * p.L₀ * (γ * p.ρ) * T) *
          (1 + (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ)) ^ T := by
    intro j hj ξ
    rw [abs_of_nonneg (dualNorm_nonneg hR _)]
    refine (G_path_le H hμ hR hL₀.le hL₁ hlmo hγ0.le hρ hlocK ξ j).trans ?_
    have hj' : (j : ℝ) ≤ T := by exact_mod_cast hj
    have hE : 1 ≤ 1 + (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ) := by
      have : 0 ≤ (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ) := by positivity
      linarith only [this]
    refine mul_le_mul ?_ (pow_le_pow_right₀ hE hj) (by positivity) (by positivity)
    have : 0 ≤ (1 + p.L₀ / p.μ) * p.L₀ * (γ * p.ρ) := by positivity
    have := mul_le_mul_of_nonneg_left hj' this
    linarith only [this]
  have hF : Measurable (fun x => dualNorm p.N (gPhi H hμ x)) :=
    ((continuous_dualNorm hR hR0).comp ((gx_continuous H hR hL₀.le hL₁).comp
      (continuous_id.prodMk (ystar_continuous H hμ hL₀.le hL₁)))).measurable
  have hout := gda_output_integral p.lmo hlmo_m γ a β c T p.x₁ p.y₁ H.measurable_x H.measurable_y P₀ P hIID T
    le_rfl (fun x => dualNorm p.N (gPhi H hμ x)) hF hgrad_out
  refine ⟨hout.1, ⟨ystar H hμ, fun x y => ystar_max H hμ x y⟩, fun ys hys => ?_⟩
  have hfun : (fun x => f x (ys x)) = Phi H hμ := funext fun x =>
    le_antisymm (ystar_max H hμ x (ys x)) (hys x (ystar H hμ x))
  have hgrad : ∀ x, gradient (fun x => f x (ys x)) x = gPhi H hμ x := by
    intro x; rw [hfun]; exact (Phi_hasGradient H hμ hR hdef hL₀.le hL₁ x).gradient
  simp only [hgrad]
  obtain ⟨hint, heq⟩ := hout.2
  refine ⟨hint, heq.le.trans ?_⟩
  have hE := expected_sum H hμ hR hdef hL₀.le hL₁ hρ hlmo hlmo_m hζ hζ0 hσx hγ0 ha0 ha1 hsa hr16 hβ0 hβ2 hβμ
    hc0 hrc (T + 1) (by omega)
  have hX := exit_total H hμ γ a β c hL₀.le hL₁ hlmo_m hρ hlmo hγ0.le hloc (lam := 1 / (β * c + p.L₀ / p.μ * (γ * p.ρ))) (r₀ := x * u) (aB := x * u / 2)
    hβ0.le hβ2 hc0 (by positivity) hlam0.le hlamB.le (by linarith only [hr16, mul_nonneg hL₁ hr0.le]) hrc hcond (T + 1 + 1)
  have hcr := tune_crude (m := (T : ℝ) + 1 + 1) hκ1 hℓ0 hd1 hϑx0 hϑy0 hω0 hq0 hq2 hLx hy rfl hB
    (by positivity) (by linarith only [hTB2])
  have hex := tune_exit (T + 1) hε hu0 hκ0 hℓ0 (by linarith only [hd1]) (by omega) hq2 hL₀u hμu hL₁u
    (by push_cast; exact hs) hG₀0 hG₀ hr0.le hWr hlam0.le hlamB hΛ (by push_cast; exact hcr)
  obtain ⟨hibl, hib1, hccl, hcc0⟩ := tune_misc hκ1 hℓ0 hω0 hqpos hLx0 hy hθ hib hx hcc
  have hsum := tune_sum (n := (T : ℝ) + 1) hε hu0 hκ1 hℓ0 hd1 hϑx0 hω0 hn1 hibl hib1 hia hccl hcc0
    (by linarith only [R1, hBn]) (by linarith only [R2, hBn]) (by linarith only [R3, hBn])
    (by linarith only [R4, hBn]) (by linarith only [R5, hBn])
    hL₀u hμu hL₁u hσyu hWu hΔu hζσ hG₀ hs hc hβ ha
  push_cast at hE hX hex
  have hπ0 : 0 ≤ ∫ ξ, (1 - gp H hμ p.lmo γ a β c (x * u) ξ (T + 1 + 1))
      ∂(Measure.infinitePi fun _ : ℕ => (P₀ : Measure p.Ω)) := integral_nonneg fun ξ => by
    show (0 : ℝ) ≤ 1 - gp H hμ p.lmo γ a β c (x * u) ξ (T + 1 + 1)
    linarith only [gp_le_one (lmo := p.lmo) H hμ γ a β c (x * u) ξ (T + 1 + 1)]
  generalize ∫ ξ, (1 - gp H hμ p.lmo γ a β c (x * u) ξ (T + 1 + 1))
      ∂(Measure.infinitePi fun _ : ℕ => (P₀ : Measure p.Ω)) = π at hE hX hπ0
  have hGm0 : 0 ≤ (dualNorm p.N (gPhi H hμ p.x₁) + (1 + p.L₀ / p.μ) * p.L₀ * (γ * p.ρ) * ((T : ℝ) + 1)) *
      (1 + (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ)) ^ (T + 1) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hX.2 hGm0
  have hlast := mul_le_mul_of_nonneg_left (hstep.trans hex) hn0.le
  rw [one_div_mul_eq_div, div_le_iff₀ hn0]
  have e : ((T : ℝ) + 1) * ((dualNorm p.N (gPhi H hμ p.x₁) + (1 + p.L₀ / p.μ) * p.L₀ * (γ * p.ρ) * ((T : ℝ) + 1)) *
      (1 + (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ)) ^ (T + 1) * π) =
      ((T : ℝ) + 1) * ((dualNorm p.N (gPhi H hμ p.x₁) + (1 + p.L₀ / p.μ) * p.L₀ * (γ * p.ρ) * ((T : ℝ) + 1)) *
      (1 + (1 + p.L₀ / p.μ) * p.L₁ * (γ * p.ρ)) ^ (T + 1)) * π := by ring
  refine hE.2.trans ?_
  linarith only [hsum, hlast, e, mul_nonneg hn0.le hε.le]

theorem minimax_lmo_convergence :
    Convergence LongTails.Setups.MinimaxLmo.spec (fun p _ => ⌈2 ^ 39 * (1 + p.L₀ / p.μ) * (1 + p.L₁ * p.ε / p.L₀ * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))))) ^ 4 * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1 + p.L₀ * p.W / p.ε + Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + p.ζ * p.σx / p.ε) * ((p.ζ * p.σx / p.ε) ^ 2 + (p.L₀ / p.μ) ^ 2 * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))) + (p.σy / p.ε) ^ 2))⌉₊) := by
  apply convergence_of_public_budget (S := LongTails.Setups.MinimaxLmo.spec) (fun p => ⌈2 ^ 39 * (1 + p.L₀ / p.μ) * (1 + p.L₁ * p.ε / p.L₀ * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))))) ^ 4 * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1 + p.L₀ * p.W / p.ε + Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + p.ζ * p.σx / p.ε) * ((p.ζ * p.σx / p.ε) ^ 2 + (p.L₀ / p.μ) ^ 2 * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))) + (p.σy / p.ε) ^ 2))⌉₊)
  refine ⟨fun p =>
    let κ := p.L₀ / p.μ
    let d := 32 * p.L₀ * p.Δ / p.ε ^ 2 + 1
    let ϑx := p.ζ * p.σx / p.ε
    let ϑy := p.σy / p.ε
    let ω := p.L₀ * p.W / p.ε
    let ℓ := p.L₁ * p.ε / p.L₀
    let y := Real.sqrt ((1 + κ) * d) + 40 * Real.log (2 ^ 20 * (2 + κ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + ϑx + ϑy + ω + ℓ))
    let ib := κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * (1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    let x := 4 * ω / 3 + y / (48 * (1 + ℓ * y))
    let T := ⌈2 ^ 39 * (1 + p.L₀ / p.μ) * (1 + p.L₁ * p.ε / p.L₀ * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))))) ^ 4 * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1 + p.L₀ * p.W / p.ε + Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + p.ζ * p.σx / p.ε) * ((p.ζ * p.σx / p.ε) ^ 2 + (p.L₀ / p.μ) ^ 2 * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))) + (p.σy / p.ε) ^ 2))⌉₊
    constantGda p.lmo p.x₁ p.y₁ T (d * (p.ε / p.L₀) / (((T : ℝ) + 1) * p.ρ)) (1 / (8192 * ϑx ^ 2 + 1))
      (1 / (ib * p.μ)) (κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2) * p.ε), ?_, ?_⟩
  · intro p hp f O hadm
    exact minimax_core p hp f O hadm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · intro p hp
    obtain ⟨hγ, ha0, ha1, hβ, hc⟩ := gda_pos p hp rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (T := ⌈2 ^ 39 * (1 + p.L₀ / p.μ) * (1 + p.L₁ * p.ε / p.L₀ * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))))) ^ 4 * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1 + p.L₀ * p.W / p.ε + Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + p.ζ * p.σx / p.ε) * ((p.ζ * p.σx / p.ε) ^ 2 + (p.L₀ / p.μ) ^ 2 * (1 + (Real.sqrt ((1 + p.L₀ / p.μ) * (32 * p.L₀ * p.Δ / p.ε ^ 2 + 1)) + 40 * Real.log (2 ^ 20 * (2 + p.L₀ / p.μ + 32 * p.L₀ * p.Δ / p.ε ^ 2 + p.ζ * p.σx / p.ε + p.σy / p.ε + p.L₀ * p.W / p.ε + p.L₁ * p.ε / p.L₀))) + (p.σy / p.ε) ^ 2))⌉₊)
    refine ⟨_, _, _, _, _, _, fun k => hγ, fun k => ?_, fun k => hβ, fun k => hc, rfl⟩
    simp only [constantMomentum]
    split_ifs <;> constructor <;> linarith

end OracleTemplate.MinimaxLmo
