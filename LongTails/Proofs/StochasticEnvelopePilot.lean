import LongTails.Algorithms.StochasticEnvelopePilot
import LongTails.Proofs.StochasticEnvelopeGeometry
import LongTails.Proofs.InexactAcceleratedConvergence
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Proofs.StochasticEnvelopeSampling
import LongTails.Proofs.StochasticEnvelopeFreshness

open scoped RealInnerProductSpace ENNReal

namespace LongTails.Proofs.StochasticEnvelopePilot

open OracleTemplate RecursiveEnvelopeGeometry
open LongTails.Algorithms.StochasticEnvelopePilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma sampledRun_zero_radius {Ω : Type*} (g : E → Ω → E)
    (L μ β : ℝ) (center : E) {b n : ℕ}
    (ξ : ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) (N : ℕ) :
    sampledRun g L μ β 0 center ξ N = (center, center) := by
  have hz (v : E) : clip 0 v = 0 :=
    norm_eq_zero.mp (le_antisymm (norm_clip_le le_rfl v) (norm_nonneg _))
  have hs (k : ℕ) (state : E × E) :
      sampledStep g L μ β 0 center state (ξ k) = (center, center) := by
    simp [sampledStep, hz]
  have ha (N call : ℕ) : StochasticGradient.advance
      (fun k state => sampledStep g L μ β 0 center state (ξ k))
      N call (center, center) = (center, center) := by
    induction N generalizing call with
    | zero => rfl
    | succ N ih =>
      rw [StochasticGradient.advance, hs]
      exact ih (call + 1)
  exact ha N 0

omit [CompleteSpace E] in
lemma boundedRun_zero_radius (L μ β : ℝ) (center : E) (answer : ℕ → E → E)
    (N call : ℕ) : boundedRun L μ β 0 center answer N call = (center, center) := by
  have hz (v : E) : clip 0 v = 0 :=
    norm_eq_zero.mp (le_antisymm (norm_clip_le le_rfl v) (norm_nonneg _))
  unfold boundedRun bounded
  simp only [hz, add_zero]
  induction N generalizing call with
  | zero => rfl
  | succ N ih =>
    rw [StochasticGradient.advance]
    exact ih (call + 1)

omit [CompleteSpace E] in
lemma run_succ (L μ β : ℝ) (center : E) (answer : ℕ → E → E) (N call : ℕ) :
    run L μ β center answer (N + 1) call =
      update L μ β center (run L μ β center answer N call)
        (answer (call + N) (InexactGradient.query
          (InexactGradient.momentum (L + μ) μ (2 * β)) (run L μ β center answer N call))) := by
  unfold run
  rw [HeavyTailedMarkovGradient.advance_add]
  rfl

omit [CompleteSpace E] in
lemma sampledRun_radius {Ω : Type*} (g : E → Ω → E) (L μ β : ℝ)
    {radius : ℝ} (hradius : 0 ≤ radius) (center : E) {b n : ℕ}
    (ξ : ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) (N : ℕ) :
    ‖(sampledRun g L μ β radius center ξ N).1 - center‖ ≤ radius ∧
      ‖(sampledRun g L μ β radius center ξ N).2 - center‖ ≤ radius := by
  cases N with
  | zero => simpa [sampledRun, StochasticGradient.advance] using And.intro hradius hradius
  | succ N =>
    unfold sampledRun
    rw [HeavyTailedMarkovGradient.advance_add]
    dsimp only [StochasticGradient.advance, sampledStep]
    simp only [add_sub_cancel_left]
    exact ⟨norm_clip_le hradius _, norm_clip_le hradius _⟩

omit [CompleteSpace E] in
lemma localizedRadius_bounds {Ω : Type*} (g : E → Ω → E) (L β : ℝ)
    {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (center : E) {b n : ℕ}
    (rough : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω)
    (ξ : ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) (N : ℕ) :
    let S := 4 * (‖robustMean (fun i j k => g center (rough i j k))‖ + s) / μ
    0 ≤ localizedRadius g L μ s β center rough ξ N ∧
      localizedRadius g L μ s β center rough ξ N ≤
        144 * Real.sqrt ((L + μ) / μ) * S + 128 * (s / μ) := by
  dsimp only
  have hr : 0 ≤ 72 * Real.sqrt ((L + μ) / μ) *
      (4 * (‖robustMean (fun i j k => g center (rough i j k))‖ + s) / μ) := by positivity
  have hb := (sampledRun_radius g L μ β hr center ξ N).1
  rw [norm_sub_rev] at hb
  unfold localizedRadius
  dsimp only
  constructor
  · positivity
  · rw [show 128 * s / μ = 128 * (s / μ) by ring]
    nlinarith only [hb]

omit [CompleteSpace E] in
lemma run_congr_path (L μ β : ℝ) (center : E) (answer other : ℕ → E → E) (N call : ℕ)
    (he : ∀ k < N, other (call + k) (InexactGradient.query
      (InexactGradient.momentum (L + μ) μ (2 * β)) (run L μ β center answer k call)) =
      answer (call + k) (InexactGradient.query
        (InexactGradient.momentum (L + μ) μ (2 * β)) (run L μ β center answer k call))) :
    run L μ β center other N call = run L μ β center answer N call := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [run_succ, run_succ, ih (fun k hk => he k (by omega)), he N (by omega)]

omit [CompleteSpace E] in
lemma bounded_run_agrees (L μ β radius : ℝ) (center : E) (answer : ℕ → E → E)
    (N call : ℕ)
    (hbound : ∀ k ≤ N,
      ‖(run L μ β center answer k call).1 - center‖ ≤ radius ∧
      ‖(run L μ β center answer k call).2 - center‖ ≤ radius) :
    let A := bounded L μ β radius center
    StochasticGradient.advance (fun k state => A.update state (answer k (A.query state).2))
      N call (center, center) = run L μ β center answer N call := by
  dsimp only [bounded]
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [HeavyTailedMarkovGradient.advance_add]
    simp only [StochasticGradient.advance]
    rw [ih (fun k hk => hbound k (by omega))]
    have hb := hbound (N + 1) (by omega)
    rw [run_succ] at hb ⊢
    rw [clip_eq_self hb.1, clip_eq_self hb.2]
    simp only [add_sub_cancel]

omit [CompleteSpace E] in
lemma boundedRun_congr_path (L μ β radius : ℝ) (center : E)
    (answer other : ℕ → E → E) (N call : ℕ)
    (he : ∀ k < N, other (call + k) (InexactGradient.query
      (InexactGradient.momentum (L + μ) μ (2 * β))
        (boundedRun L μ β radius center answer k call)) =
      answer (call + k) (InexactGradient.query
        (InexactGradient.momentum (L + μ) μ (2 * β))
          (boundedRun L μ β radius center answer k call))) :
    boundedRun L μ β radius center other N call = boundedRun L μ β radius center answer N call := by
  induction N with
  | zero => rfl
  | succ N ih =>
    dsimp only [boundedRun, bounded] at ih he ⊢
    rw [HeavyTailedMarkovGradient.advance_add, HeavyTailedMarkovGradient.advance_add]
    simp only [StochasticGradient.advance]
    rw [ih (fun k hk => he k (by omega)), he N (by omega)]

lemma rough_radius {L μ s : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hs : 0 ≤ s) (center estimate : E)
    (he : ‖estimate - g center‖ ≤ (‖g center‖ + s) / 4) :
    let r := ‖center - prox g μ center‖
    let S := 4 * (‖estimate‖ + s) / μ
    r + s / μ ≤ S ∧ S ≤ 10 * (L + μ) / μ * (r + s / μ) := by
  let r := ‖center - prox g μ center‖
  have hr : 0 ≤ r := norm_nonneg _
  have hL := h.pos
  have hlo : μ * r ≤ ‖g center‖ := by
    simpa only [sub_self, smul_zero, add_zero] using h.regularized_distance hμ center center
  have hup : ‖g center‖ ≤ μ * r + 2 * L * r := by
    exact StochasticEnvelopeGeometry.localized_field_bound h hμ center center center
      le_rfl (by simpa using hr)
  have hn := norm_le_norm_sub_add estimate (g center)
  have hn' := norm_le_norm_sub_add (g center) estimate
  rw [norm_sub_rev (g center) estimate] at hn'
  constructor
  · apply (le_div_iff₀ hμ).mpr
    have heq : (r + s / μ) * μ = μ * r + s := by field_simp
    rw [heq]
    nlinarith only [he, hn', hlo, hs, norm_nonneg (g center)]
  · have hbasic : 4 * (‖estimate‖ + s) ≤ 10 * (L + μ) * r + 5 * s := by
      have hmr : 0 ≤ μ * r := by positivity
      nlinarith only [he, hn, hup, hmr]
    have hsμ : μ * (s / μ) = s := by field_simp
    have hLs : 0 ≤ L * (s / μ) := by positivity
    have hgoal : 4 * (‖estimate‖ + s) ≤ 10 * (L + μ) * (r + s / μ) := by
      nlinarith only [hbasic, hsμ, hLs, hs]
    calc
      _ ≤ (10 * (L + μ) * (r + s / μ)) / μ := div_le_div_of_nonneg_right hgoal hμ.le
      _ = _ := by ring

lemma clamp_radius_tuning {L μ S : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ) (hS : 0 ≤ S) :
    0 ≤ 72 * Real.sqrt ((L + μ) / μ) * S ∧
      5000 * (L + μ) * S ^ 2 ≤ μ * (72 * Real.sqrt ((L + μ) / μ) * S) ^ 2 := by
  have hk : 0 ≤ (L + μ) / μ := by positivity
  have he := Real.sq_sqrt hk
  have hcancel : μ * ((L + μ) / μ) = L + μ := by field_simp
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, he]
  nlinarith [mul_nonneg (show 0 ≤ L + μ by positivity) (sq_nonneg S)]

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma refined_radius {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (center pilot target : E)
    (hp : ‖pilot - target‖ ≤ ‖center - target‖ / 8 + 32 * s / μ) :
    ‖center - target‖ + s / μ ≤ 2 * ‖center - pilot‖ + 128 * s / μ ∧
      2 * ‖center - pilot‖ + 128 * s / μ ≤ 192 * (‖center - target‖ + s / μ) := by
  have hlo := norm_sub_le_norm_sub_add_norm_sub center pilot target
  have hup := norm_sub_le_norm_sub_add_norm_sub center target pilot
  rw [norm_sub_rev target pilot] at hup
  have hsμ : 0 ≤ s / μ := by positivity
  have he32 : 32 * s / μ = 32 * (s / μ) := by ring
  have he128 : 128 * s / μ = 128 * (s / μ) := by ring
  rw [he32] at hp
  rw [he128]
  constructor <;> nlinarith only [hlo, hup, hp, hsμ, norm_nonneg (center - target)]

lemma mixed_potential {L μ β s : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32)
    (answer : ℕ → E → E) (herr : ∀ k x, ‖answer k x - g x‖ ≤ β * ‖g x‖ + s)
    (center : E) (N call : ℕ) :
    let θ := InexactGradient.momentum (L + μ) μ (2 * β)
    let r := ‖center - prox g μ center‖
    InexactGradient.potential (regularized f μ center) μ (prox g μ center)
      (run L μ β center answer N call) ≤
      (1 - θ / 2) ^ N * (L + μ) * r ^ 2 + 128 * (β * μ * r + s) ^ 2 / μ := by
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  let r := ‖center - prox g μ center‖
  let δ := β * μ * r + s
  let F := 2 / θ * (2 / (1 - 2 * β) * (3 / (4 * (L + μ)) + 2 * θ / μ) * δ ^ 2)
  have hL := h.pos
  have hLp : 0 < L + μ := by linarith
  have hβ1 : 2 * β < 1 := by linarith
  obtain ⟨hθ0, hθ1, hθL, hθα, hθlow, _⟩ :=
    InexactGradient.momentum_bounds hμ (show μ ≤ L + μ by linarith) (by positivity : 0 ≤ 2 * β) hβ1
  have he : ∀ k x, ‖(answer k x + μ • (x - center)) - (g x + μ • (x - center))‖ ≤
      (2 * β) * ‖g x + μ • (x - center)‖ + δ := by
    intro k x
    simpa only [δ, r, add_assoc] using
      StochasticEnvelopeGeometry.regularized_mixed_error h hμ hβ0 center x (answer k x) (herr k x)
  have hstep := InexactGradient.advance_potential hLp hμ (by positivity : 0 ≤ 2 * β) hβ1
    hθ0 hθ1 hθL hθα (h.regularized_upper center) (h.regularized_lower center)
    (h.prox_minimum hμ center) (fun k x => answer k x + μ • (x - center)) he N call (center, center)
  have hf0 : 0 ≤ F := by dsimp [F]; positivity
  have hdelta : 136 * δ ^ 2 ≤ μ * (1 - 2 * β) ^ 2 * (256 * δ ^ 2 / μ) := by
    have hb : 136 ≤ 256 * (1 - 2 * β) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg δ)
    have heq : μ * (1 - 2 * β) ^ 2 * (256 * δ ^ 2 / μ) =
        256 * (1 - 2 * β) ^ 2 * δ ^ 2 := by field_simp
    rw [heq]
    nlinarith only [hh]
  have hfloor : F ≤ 128 * δ ^ 2 / μ := by
    have hh := InexactGradient.floor_le hLp hμ (by positivity : 0 ≤ 2 * β) hβ1 hθ0 hθlow hdelta
    change F ≤ (256 * δ ^ 2 / μ) / 2 at hh
    convert hh using 1
    ring
  have hinit : InexactGradient.potential (regularized f μ center) μ (prox g μ center)
      (center, center) ≤ (L + μ) * r ^ 2 := by
    have hh := h.regularized_upper (μ := μ) center (prox g μ center) center
    rw [h.prox_stationary hμ, inner_zero_left, add_zero] at hh
    dsimp [InexactGradient.potential, r]
    nlinarith [sq_nonneg ‖center - prox g μ center‖]
  have hq : 0 ≤ (1 - θ / 2) ^ N := pow_nonneg (by dsimp [θ]; linarith) _
  have hp := mul_le_mul_of_nonneg_left hinit hq
  have hf := mul_nonneg hq hf0
  change InexactGradient.potential (regularized f μ center) μ (prox g μ center)
      (run L μ β center answer N call) - F ≤
      (1 - θ / 2) ^ N * (InexactGradient.potential (regularized f μ center) μ
        (prox g μ center) (center, center) - F) at hstep
  change InexactGradient.potential (regularized f μ center) μ (prox g μ center)
      (run L μ β center answer N call) ≤ (1 - θ / 2) ^ N * (L + μ) * r ^ 2 + 128 * δ ^ 2 / μ
  nlinarith only [hstep, hp, hf, hfloor]

lemma mixed_distance {L μ β s : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1024) (hs : 0 ≤ s)
    (answer : ℕ → E → E) (herr : ∀ k x, ‖answer k x - g x‖ ≤ β * ‖g x‖ + s)
    (center : E) (N call : ℕ)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N * (L + μ) ≤ μ / 1024) :
    ‖(run L μ β center answer N call).1 - prox g μ center‖ ≤
      ‖center - prox g μ center‖ / 8 + 32 * s / μ := by
  let r := ‖center - prox g μ center‖
  let v := run L μ β center answer N call
  let δ := β * μ * r + s
  have hr : 0 ≤ r := norm_nonneg _
  have hp := mixed_potential h hμ hβ0 (by linarith : β ≤ 1 / 32) answer herr center N call
  have ht := mul_le_mul_of_nonneg_right htrans (sq_nonneg r)
  have hg := h.prox_growth hμ center v.1
  have hz : 0 ≤ μ / 4 * ‖v.2 - prox g μ center‖ ^ 2 := by positivity
  have hb : μ / 2 * ‖v.1 - prox g μ center‖ ^ 2 ≤ μ * r ^ 2 / 1024 + 128 * δ ^ 2 / μ := by
    dsimp only [InexactGradient.potential] at hp
    change regularized f μ center v.1 - envelope f g μ center +
      μ / 4 * ‖v.2 - prox g μ center‖ ^ 2 ≤ _ at hp
    change envelope f g μ center + μ / 2 * ‖v.1 - prox g μ center‖ ^ 2 ≤ _ at hg
    change _ ≤ μ * r ^ 2 / 1024 + 128 * (β * μ * r + s) ^ 2 / μ
    dsimp only [r] at ht
    nlinarith only [hp, ht, hg, hz]
  have hb2 : μ ^ 2 * ‖v.1 - prox g μ center‖ ^ 2 ≤ μ ^ 2 * r ^ 2 / 512 + 256 * δ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * μ)
    have he : 2 * μ * (μ * r ^ 2 / 1024 + 128 * δ ^ 2 / μ) =
        μ ^ 2 * r ^ 2 / 512 + 256 * δ ^ 2 := by field_simp; ring
    rw [he] at hm
    nlinarith only [hm]
  have hsmall : (β * μ * r) ^ 2 ≤ (μ * r / 1024) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hβ (mul_nonneg hμ.le hr)]
  have hsum : δ ^ 2 ≤ 2 * (β * μ * r) ^ 2 + 2 * s ^ 2 := by
    dsimp [δ]
    nlinarith [sq_nonneg (β * μ * r - s)]
  have hcross : 0 ≤ μ * r * s := by positivity
  have hnorm : μ * ‖v.1 - prox g μ center‖ ≤ μ * r / 8 + 32 * s := by
    have hh : (μ * ‖v.1 - prox g μ center‖) ^ 2 ≤ (μ * r / 8 + 32 * s) ^ 2 := by
      nlinarith only [hb2, hsmall, hsum, hcross, sq_nonneg s, sq_nonneg (μ * r)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hh
  change ‖v.1 - prox g μ center‖ ≤ r / 8 + 32 * s / μ
  apply (mul_le_mul_iff_right₀ hμ).mp
  calc
    μ * ‖v.1 - prox g μ center‖ ≤ μ * r / 8 + 32 * s := hnorm
    _ = μ * (r / 8 + 32 * s / μ) := by field_simp

lemma pathwise_distance {L μ β s : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1024) (hs : 0 ≤ s)
    (answer : ℕ → E → E) (center : E) (N call : ℕ)
    (herr : ∀ k < N,
      let x := InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β))
        (run L μ β center answer k call)
      ‖answer (call + k) x - g x‖ ≤ β * ‖g x‖ + s)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N * (L + μ) ≤ μ / 1024) :
    ‖(run L μ β center answer N call).1 - prox g μ center‖ ≤
      ‖center - prox g μ center‖ / 8 + 32 * s / μ := by
  classical
  let other := fun k x => if ‖answer k x - g x‖ ≤ β * ‖g x‖ + s then answer k x else g x
  have he : ∀ k x, ‖other k x - g x‖ ≤ β * ‖g x‖ + s := by
    intro k x
    dsimp [other]
    split_ifs with hh
    · exact hh
    · simp only [sub_self, norm_zero]
      positivity
  have hrun := run_congr_path L μ β center answer other N call (fun k hk => by
    dsimp only [other]
    exact ite_eq_left (herr k hk))
  rw [← hrun]
  exact mixed_distance h hμ hβ0 hβ hs other he center N call htrans

lemma mixed_trajectory {L μ β s S : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32)
    (hs : 0 ≤ s) {center : E} (hS : ‖center - prox g μ center‖ ≤ S) (hsS : s ≤ μ * S)
    (answer : ℕ → E → E) (herr : ∀ k x, ‖answer k x - g x‖ ≤ β * ‖g x‖ + s)
    (N call : ℕ) :
    let v := run L μ β center answer N call
    μ * ‖v.1 - center‖ ^ 2 ≤ 5000 * (L + μ) * S ^ 2 ∧
      μ * ‖v.2 - center‖ ^ 2 ≤ 5000 * (L + μ) * S ^ 2 := by
  let r := ‖center - prox g μ center‖
  let v := run L μ β center answer N call
  have hr : 0 ≤ r := norm_nonneg _
  have hS0 : 0 ≤ S := le_trans hr hS
  have hL := h.pos
  have hLp : 0 < L + μ := by linarith
  obtain ⟨hθ0, hθ1, _⟩ := InexactGradient.momentum_bounds hμ
    (show μ ≤ L + μ by linarith) (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  have hq : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  have hp := mixed_potential h hμ hβ0 hβ answer herr center N call
  have hδ : β * μ * r + s ≤ 2 * μ * S := by
    have hb := mul_le_mul_of_nonneg_right (show β ≤ 1 by linarith) (mul_nonneg hμ.le hr)
    have hh := mul_le_mul_of_nonneg_left hS hμ.le
    nlinarith only [hb, hh, hsS]
  have hδ2 := pow_le_pow_left₀ (by positivity : 0 ≤ β * μ * r + s) hδ 2
  have hr2 := pow_le_pow_left₀ hr hS 2
  have hfloor : 128 * (β * μ * r + s) ^ 2 / μ ≤ 512 * μ * S ^ 2 := by
    apply (div_le_iff₀ hμ).mpr
    nlinarith only [hδ2]
  have ht := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ (L + μ) * r ^ 2)
  have ht2 := mul_le_mul_of_nonneg_left hr2 hLp.le
  have hP : InexactGradient.potential (regularized f μ center) μ (prox g μ center) v ≤
      513 * (L + μ) * S ^ 2 := by
    have hh : 0 ≤ L * S ^ 2 := by positivity
    change _ ≤ _ at hp
    nlinarith only [hp, ht, ht2, hfloor, hh]
  have hg := h.prox_growth hμ center v.1
  change envelope f g μ center + μ / 2 * ‖v.1 - prox g μ center‖ ^ 2 ≤ _ at hg
  change regularized f μ center v.1 - envelope f g μ center +
    μ / 4 * ‖v.2 - prox g μ center‖ ^ 2 ≤ _ at hP
  have ha : 0 ≤ μ * ‖v.1 - prox g μ center‖ ^ 2 := by positivity
  have hb : 0 ≤ μ * ‖v.2 - prox g μ center‖ ^ 2 := by positivity
  have bound (x : E) (hx : μ * ‖x - prox g μ center‖ ^ 2 ≤ 2052 * (L + μ) * S ^ 2) :
      μ * ‖x - center‖ ^ 2 ≤ 5000 * (L + μ) * S ^ 2 := by
    have hn := norm_sub_le_norm_sub_add_norm_sub x (prox g μ center) center
    rw [norm_sub_rev (prox g μ center) center] at hn
    have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hm := mul_le_mul_of_nonneg_left hn2 hμ.le
    have hc := mul_nonneg hμ.le (sq_nonneg (‖x - prox g μ center‖ - r))
    have hrm := mul_le_mul_of_nonneg_left hr2 hμ.le
    have hLS : 0 ≤ L * S ^ 2 := by positivity
    have hμS : 0 ≤ μ * S ^ 2 := by positivity
    change _ ≤ (‖x - prox g μ center‖ + r) ^ 2 at hn2
    nlinarith only [hm, hc, hx, hrm, hLS, hμS]
  exact ⟨bound v.1 (by nlinarith only [hP, hg, hb, ha]),
    bound v.2 (by nlinarith only [hP, hg, ha])⟩

lemma bounded_pathwise_distance {L μ β s S radius : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1024) (hs : 0 ≤ s)
    (hradius : 0 ≤ radius) (center : E)
    (hS : ‖center - prox g μ center‖ ≤ S) (hsS : s ≤ μ * S)
    (hR : 5000 * (L + μ) * S ^ 2 ≤ μ * radius ^ 2)
    (answer : ℕ → E → E) (N call : ℕ)
    (herr : ∀ k < N,
      let x := InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β))
        (boundedRun L μ β radius center answer k call)
      ‖answer (call + k) x - g x‖ ≤ β * ‖g x‖ + s)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N * (L + μ) ≤ μ / 1024) :
    ‖(boundedRun L μ β radius center answer N call).1 - prox g μ center‖ ≤
      ‖center - prox g μ center‖ / 8 + 32 * s / μ := by
  classical
  let other := fun k x => if ‖answer k x - g x‖ ≤ β * ‖g x‖ + s then answer k x else g x
  have he : ∀ k x, ‖other k x - g x‖ ≤ β * ‖g x‖ + s := by
    intro k x
    dsimp [other]
    split_ifs with hh
    · exact hh
    · simp only [sub_self, norm_zero]
      positivity
  have hcongr := boundedRun_congr_path L μ β radius center answer other N call (fun k hk => by
    dsimp only [other]
    exact ite_eq_left (herr k hk))
  have hbound (k : ℕ) (_ : k ≤ N) :
      ‖(run L μ β center other k call).1 - center‖ ≤ radius ∧
      ‖(run L μ β center other k call).2 - center‖ ≤ radius := by
    have hh := mixed_trajectory h hμ hβ0 (by linarith : β ≤ 1 / 32) hs hS hsS other he k call
    have bound (x : E) (hx : μ * ‖x - center‖ ^ 2 ≤ 5000 * (L + μ) * S ^ 2) :
        ‖x - center‖ ≤ radius := by
      apply (sq_le_sq₀ (norm_nonneg _) hradius).mp
      exact (mul_le_mul_iff_right₀ hμ).mp (hx.trans hR)
    exact ⟨bound _ hh.1, bound _ hh.2⟩
  rw [← hcongr]
  have hagree : boundedRun L μ β radius center other N call = run L μ β center other N call :=
    bounded_run_agrees L μ β radius center other N call hbound
  rw [hagree]
  exact mixed_distance h hμ hβ0 hβ hs other he center N call htrans

lemma pilot_relative_tuning {κ a : ℝ} (hκ : 2 ≤ κ) (ha : a ≤ κ⁻¹ ^ 2) :
    let β := 1 / (1024 * κ)
    0 ≤ β ∧ β ≤ 1 / 1024 ∧ a ≤ 512 * β ∧
      β ^ 2 * κ ≤ Real.sqrt κ / 256 := by
  have hk : 0 < κ := by linarith
  have hs : 1 ≤ Real.sqrt κ := (Real.le_sqrt (by norm_num) hk.le).mpr (by nlinarith)
  dsimp only
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  · apply ha.trans
    rw [inv_pow, inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < κ ^ 2)).mpr
    have he : 512 * (1 / (1024 * κ)) * κ ^ 2 = κ / 2 := by field_simp; ring
    rw [he]
    linarith
  · have he : (1 / (1024 * κ)) ^ 2 * κ = 1 / (1048576 * κ) := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    have hp := mul_le_mul_of_nonneg_right hs hk.le
    nlinarith

lemma momentum_cost {A μ β κ : ℝ} (hμ : 0 < μ) (hA : μ ≤ A)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32) (hκ : A = μ * κ)
    (hnoise : β ^ 2 * κ ≤ Real.sqrt κ / 256) :
    2 / InexactGradient.momentum A μ (2 * β) ≤ 17 * Real.sqrt κ := by
  have hκ1 : 1 ≤ κ := by nlinarith only [hA, hκ, hμ]
  have hκ0 : 0 ≤ κ := by linarith
  have hs2 := Real.sq_sqrt hκ0
  have hs0 := Real.sqrt_nonneg κ
  obtain ⟨_, _, _, _, _, heq⟩ := InexactGradient.momentum_bounds hμ hA
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  rw [heq]
  have hden : 0 < μ * (1 - 2 * β) := mul_pos hμ (by linarith)
  have hhalf : 1 / 2 ≤ 1 - 2 * β := by linarith
  have hratio : A / (μ * (1 - 2 * β)) ≤ 4 * κ := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 4 * μ * κ)
    nlinarith only [hh, hκ, mul_nonneg hμ.le hκ0]
  have hs : Real.sqrt (A / (μ * (1 - 2 * β))) ≤ 2 * Real.sqrt κ := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hratio, hs2]
  have ht : 32 * (2 * β) ^ 2 * A / (μ * (1 - 2 * β)) ≤ Real.sqrt κ := by
    apply (div_le_iff₀ hden).mpr
    have hn := mul_le_mul_of_nonneg_left hnoise hμ.le
    have hh := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hμ.le hs0)
    rw [hκ]
    nlinarith only [hn, hh]
  linarith only [hs, ht]

lemma pilot_transient {A μ β : ℝ} (hμ : 0 < μ) (hA : μ ≤ A)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 32) (N : ℕ)
    (hN : ⌈(2 / InexactGradient.momentum A μ (2 * β)) *
      Real.log (1 + A / (μ / 1024))⌉₊ ≤ N) :
    (1 - InexactGradient.momentum A μ (2 * β) / 2) ^ N * A ≤ μ / 1024 := by
  obtain ⟨hθ0, hθ1, _⟩ := InexactGradient.momentum_bounds hμ hA
    (by positivity : 0 ≤ 2 * β) (by linarith : 2 * β < 1)
  exact PLGradient.geometric_budget 2 _ A (μ / 1024) hθ0 (by linarith)
    (hμ.le.trans hA) (by positivity) N hN

section Sampling

open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampledRun_eq_boundedRun (g : E → Ω → E) (L μ β radius : ℝ) (center : E) {b n : ℕ}
    (ξ : ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) (N : ℕ) :
    sampledRun g L μ β radius center ξ N = boundedRun L μ β radius center
      (fun k x => robustMean (fun i j l => g x (ξ k i j l))) N 0 := rfl

omit [CompleteSpace E] in
lemma measurable_sampledReply {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (θ : ℝ) (b n : ℕ) :
    Measurable (Function.uncurry (sampledReply (b := b) (n := n) g θ)) := by
  have hq : Measurable (InexactGradient.query (E := E) θ) := by
    unfold InexactGradient.query
    fun_prop
  apply (StochasticEnvelopeSampling.measurable_robustMean b n).comp
  refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => Measurable.of_eval (fun k => ?_)))
  exact hg.comp ((hq.comp measurable_fst).prodMk (by fun_prop))

omit [CompleteSpace E] in
lemma measurable_variable_clip {A : Type*} [MeasurableSpace A]
    {R : A → ℝ} {X : A → E} (hR : Measurable R) (hX : Measurable X) :
    Measurable (fun ω => clip (R ω) (X ω)) := by
  unfold clip
  exact Measurable.ite (measurableSet_le hX.norm hR) hX ((hR.div hX.norm).smul hX)

omit [CompleteSpace E] in
lemma measurable_sampledStep {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ β radius : ℝ) (center : E) (b n : ℕ) :
    Measurable (Function.uncurry (sampledStep (b := b) (n := n) g L μ β radius center)) := by
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  have hq : Measurable (InexactGradient.query (E := E) θ) := by
    unfold InexactGradient.query
    fun_prop
  let reply := fun w : (E × E) × (Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) =>
    robustMean (fun i j k => g (InexactGradient.query θ w.1) (w.2 i j k))
  have hr : Measurable reply := by
    apply (StochasticEnvelopeSampling.measurable_robustMean b n).comp
    refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => Measurable.of_eval (fun k => ?_)))
    exact hg.comp ((hq.comp measurable_fst).prodMk (by fun_prop))
  have hu : Measurable (fun w : (E × E) × E => update L μ β center w.1 w.2) := by
    unfold update InexactGradient.step InexactGradient.query
    fun_prop
  have hn := hu.comp (measurable_fst.prodMk hr)
  change Measurable (fun w => (center + clip radius ((update L μ β center w.1 (reply w)).1 - center),
    center + clip radius ((update L μ β center w.1 (reply w)).2 - center)))
  exact (measurable_const.add ((measurable_clip radius).comp (hn.fst.sub measurable_const))).prodMk
    (measurable_const.add ((measurable_clip radius).comp (hn.snd.sub measurable_const)))

omit [CompleteSpace E] in
lemma measurable_sampledRun {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ β : ℝ) (center : E) {b n : ℕ} {R : A → ℝ}
    {ξ : A → ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω}
    (hR : Measurable R) (hξ : Measurable ξ) (N : ℕ) :
    Measurable (fun ω => sampledRun g L μ β (R ω) center (ξ ω) N) := by
  induction N with
  | zero => simp [sampledRun, StochasticGradient.advance]
  | succ N ih =>
    have hsample : Measurable (fun ω => ξ ω N) := (measurable_pi_apply N).comp hξ
    have hr := (measurable_sampledReply hg
      (InexactGradient.momentum (L + μ) μ (2 * β)) b n).comp (ih.prodMk hsample)
    have hu : Measurable (fun w : (E × E) × E => update L μ β center w.1 w.2) := by
      unfold update InexactGradient.step InexactGradient.query
      fun_prop
    have hn := hu.comp (ih.prodMk hr)
    have hc : Measurable (fun _ : A => center) := measurable_const
    have hh := (hc.add (measurable_variable_clip hR
      (hn.fst.sub hc))).prodMk
      (hc.add (measurable_variable_clip hR (hn.snd.sub hc)))
    convert hh using 1
    funext ω
    unfold sampledRun
    rw [HeavyTailedMarkovGradient.advance_add, Nat.zero_add]
    rfl

omit [CompleteSpace E] in
lemma measurable_localizedRadius {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ s β : ℝ) (center : E) (b n N : ℕ) :
    Measurable (fun w : (Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) ×
      (ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) =>
      localizedRadius g L μ s β center w.1 w.2 N) := by
  let estimate := fun w : (Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) ×
      (ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) =>
    robustMean (fun i j k => g center (w.1 i j k))
  have he : Measurable estimate := by
    apply (StochasticEnvelopeSampling.measurable_robustMean b n).comp
    refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => Measurable.of_eval (fun k => ?_)))
    exact hg.comp (measurable_const.prodMk (by fun_prop))
  have hR : Measurable (fun w => 72 * Real.sqrt ((L + μ) / μ) *
      (4 * (‖estimate w‖ + s) / μ)) := by fun_prop
  have hY := measurable_sampledRun hg L μ β center hR measurable_snd N
  change Measurable (fun w => 2 * ‖center -
    (sampledRun g L μ β (72 * Real.sqrt ((L + μ) / μ) *
      (4 * (‖estimate w‖ + s) / μ)) center w.2 N).1‖ + 128 * s / μ)
  fun_prop

lemma sampledRun_failure_probability {Ω₀ : Type} [MeasurableSpace Ω₀]
    (P : Measure Ω₀) [IsProbabilityMeasure P] {g : E → Ω₀ → E} {field : E → E}
    (hg : Measurable (Function.uncurry g)) (hfield : Measurable field)
    {p s a β : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hβ : 0 ≤ β) (haβ : a ≤ 512 * β)
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (L μ radius : ℝ) (center : E) (n N : ℕ) (hn : 8 ≤ n + 1) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let θ := InexactGradient.momentum (L + μ) μ (2 * β)
    (Measure.infinitePi fun _ : ℕ => Q) {ξ | ∃ j < N,
      let state := sampledRun g L μ β radius center ξ j
      β * ‖field (InexactGradient.query θ state)‖ + s <
        ‖sampledReply g θ state (ξ j) - field (InexactGradient.query θ state)‖} ≤
      ENNReal.ofReal (N * (1 / 2 : ℝ) ^ (n + 1)) := by
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  let Q := Measure.pi fun _ : Fin (n + 1) =>
    Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  let bad : Set ((E × E) × (Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀)) :=
    {w | β * ‖field (InexactGradient.query θ w.1)‖ + s <
      ‖sampledReply g θ w.1 w.2 - field (InexactGradient.query θ w.1)‖}
  have hq : Measurable (fun w : (E × E) × (Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀) =>
      field (InexactGradient.query θ w.1)) := by
    apply hfield.comp
    unfold InexactGradient.query
    fun_prop
  have hbad : MeasurableSet bad := measurableSet_lt
    ((measurable_const.mul hq.norm).add measurable_const)
    (((measurable_sampledReply hg θ b n).sub hq).norm)
  have hprob (state : E × E) : Q.real {ω | (state, ω) ∈ bad} ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    let x := InexactGradient.query θ state
    have hh := (StochasticEnvelopeSampling.robustMean_affine
      (hg.comp measurable_prodMk_left) (field x) hp hp2 hs ha hβ haβ
      (hi x) (hmean x) (hpi x) (hm x) n hn).2.2
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa [measureReal_def, Q, bad, sampledReply, x, Function.comp_def, InexactGradient.query,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1))] using ht
  have hh := StochasticEnvelopeFreshness.fixed_step_failure_probability Q
    (sampledStep g L μ β radius center) (measurable_sampledStep hg L μ β radius center b n)
    bad hbad hprob N (center, center)
  exact hh.2

lemma sampledRun_distance_failure {Ω₀ : Type} [MeasurableSpace Ω₀]
    (P : Measure Ω₀) [IsProbabilityMeasure P] {g : E → Ω₀ → E} {field : E → E} {f : E → ℝ}
    (hg : Measurable (Function.uncurry g)) (hfield : Measurable field)
    {L μ p s a β S radius : ℝ} (hmodel : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1024) (haβ : a ≤ 512 * β)
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (hradius : 0 ≤ radius) (center : E)
    (hS : ‖center - prox field μ center‖ ≤ S) (hsS : s ≤ μ * S)
    (hR : 5000 * (L + μ) * S ^ 2 ≤ μ * radius ^ 2)
    (n N : ℕ) (hn : 8 ≤ n + 1)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N * (L + μ) ≤ μ / 1024) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    (Measure.infinitePi fun _ : ℕ => Q) {ξ |
      ‖center - prox field μ center‖ / 8 + 32 * s / μ <
        ‖(sampledRun g L μ β radius center ξ N).1 - prox field μ center‖} ≤
      ENNReal.ofReal (N * (1 / 2 : ℝ) ^ (n + 1)) := by
  apply (measure_mono ?_).trans
    (sampledRun_failure_probability P hg hfield hp hp2 hs ha hβ0 haβ hi hmean hpi hm
      L μ radius center n N hn)
  intro ξ hfail
  by_contra hnone
  have herr : ∀ k < N,
      let x := InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β))
        (boundedRun L μ β radius center
          (fun j x => robustMean (fun i l m => g x (ξ j i l m))) k 0)
      ‖robustMean (fun i l m => g x (ξ k i l m)) - field x‖ ≤ β * ‖field x‖ + s := by
    intro k hk
    apply le_of_not_gt
    intro hbad
    apply hnone
    exact ⟨k, hk, hbad⟩
  have hd := bounded_pathwise_distance hmodel hμ hβ0 hβ hs hradius center hS hsS hR
    (fun j x => robustMean (fun i l m => g x (ξ j i l m))) N 0 (by simpa only [Nat.zero_add] using herr) htrans
  exact (not_lt_of_ge hd) hfail

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma refined_radius_failure {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P : Measure Ω₀) {Y : Ω₀ → E} {μ s η : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s)
    (center target : E)
    (hfail : P {ω | ‖center - target‖ / 8 + 32 * s / μ < ‖Y ω - target‖} ≤
      ENNReal.ofReal η) :
    P {ω | 2 * ‖center - Y ω‖ + 128 * s / μ < ‖center - target‖ + s / μ ∨
      192 * (‖center - target‖ + s / μ) < 2 * ‖center - Y ω‖ + 128 * s / μ} ≤
      ENNReal.ofReal η := by
  apply (measure_mono ?_).trans hfail
  intro ω hbad
  by_contra hn
  obtain ⟨hlo, hup⟩ := refined_radius hμ hs center (Y ω) target (le_of_not_gt hn)
  rcases hbad with hbad | hbad
  · exact (not_lt_of_ge hlo) hbad
  · exact (not_lt_of_ge hup) hbad

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma joint_refined_radius_failure {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure U) (Q : Measure V) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : U → E} {Y : U × V → E} (hX : Measurable X) (hY : Measurable Y)
    (center target value : E) {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s)
    {ε₀ ε₁ : ℝ≥0∞}
    (hrough : P {u | (‖value‖ + s) / 4 < ‖X u - value‖} ≤ ε₀)
    (hpilot : ∀ u, ‖X u - value‖ ≤ (‖value‖ + s) / 4 →
      Q {v | ‖center - target‖ / 8 + 32 * s / μ < ‖Y (u, v) - target‖} ≤ ε₁) :
    (P.prod Q) {ω | 2 * ‖center - Y ω‖ + 128 * s / μ < ‖center - target‖ + s / μ ∨
      192 * (‖center - target‖ + s / μ) < 2 * ‖center - Y ω‖ + 128 * s / μ} ≤
      ε₀ + ε₁ := by
  have hU : Measurable (fun ω => 2 * ‖center - Y ω‖ + 128 * s / μ) := by fun_prop
  apply StochasticEnvelopeFreshness.product_failure_probability P Q
    ((measurableSet_lt hU measurable_const).union (measurableSet_lt measurable_const hU))
    (measurableSet_lt measurable_const ((hX.sub measurable_const).norm)) hrough
  intro u hu
  apply (measure_mono ?_).trans (hpilot u (le_of_not_gt hu))
  intro v hv
  by_contra hn
  obtain ⟨hlo, hup⟩ := refined_radius hμ hs center (Y (u, v)) target (le_of_not_gt hn)
  rcases hv with hv | hv
  · exact (not_lt_of_ge hlo) hv
  · exact (not_lt_of_ge hup) hv

lemma localizedRadius_failure {Ω₀ : Type} [MeasurableSpace Ω₀]
    (P : Measure Ω₀) [IsProbabilityMeasure P] {g : E → Ω₀ → E} {field : E → E} {f : E → ℝ}
    (hg : Measurable (Function.uncurry g)) (hfield : Measurable field)
    {L μ p s a β : ℝ} (hmodel : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1024) (haβ : a ≤ 512 * β)
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) (n N : ℕ) (hn : 8 ≤ n + 1)
    (htrans : (1 - InexactGradient.momentum (L + μ) μ (2 * β) / 2) ^ N * (L + μ) ≤ μ / 1024) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let r := ‖center - prox field μ center‖
    (Q.prod (Measure.infinitePi fun _ : ℕ => Q)) {w |
      localizedRadius g L μ s β center w.1 w.2 N < r + s / μ ∨
      192 * (r + s / μ) < localizedRadius g L μ s β center w.1 w.2 N} ≤
      ENNReal.ofReal ((N + 1 : ℝ) * (1 / 2 : ℝ) ^ (n + 1)) := by
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  let Q := Measure.pi fun _ : Fin (n + 1) =>
    Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
  let X := fun ξ : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀ =>
    robustMean (fun i j k => g center (ξ i j k))
  let S := fun ξ => 4 * (‖X ξ‖ + s) / μ
  let R := fun ξ => 72 * Real.sqrt ((L + μ) / μ) * S ξ
  let Y := fun w : (Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀) ×
      (ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀) =>
    (sampledRun g L μ β (R w.1) center w.2 N).1
  have hX : Measurable X := by
    apply (StochasticEnvelopeSampling.measurable_robustMean b n).comp
    refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => Measurable.of_eval (fun k => ?_)))
    exact hg.comp (measurable_const.prodMk (by fun_prop))
  have hR : Measurable R := by dsimp [R, S]; fun_prop
  have hY : Measurable Y := (measurable_sampledRun hg L μ β center
    (hR.comp measurable_fst) measurable_snd N).fst
  have hrough := (StochasticEnvelopeSampling.robustMean_rough
    (hg.comp measurable_prodMk_left) (field center) hp hp2 hs ha ha1
    (hi center) (hmean center) (hpi center) (hm center) n hn).2.2
  have hj := joint_refined_radius_failure Q (Measure.infinitePi fun _ : ℕ => Q)
    hX hY center (prox field μ center) (field center) hμ hs hrough
    (ε₁ := ENNReal.ofReal (N * (1 / 2 : ℝ) ^ (n + 1))) ?_
  · apply hj.trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  · intro ξ hξ
    have hS0 : 0 ≤ S ξ := by dsimp [S]; positivity
    have hS := (rough_radius hmodel hμ hs center (X ξ) hξ).1
    have hsμ : 0 ≤ s / μ := by positivity
    have hrS : ‖center - prox field μ center‖ ≤ S ξ := by linarith
    have hsS : s ≤ μ * S ξ := by
      have hh : s / μ ≤ S ξ := by linarith [norm_nonneg (center - prox field μ center)]
      exact (div_le_iff₀ hμ).mp hh |>.trans_eq (mul_comm _ _)
    obtain ⟨hR0, hRbound⟩ := clamp_radius_tuning hmodel.pos.le hμ hS0
    exact sampledRun_distance_failure P hg hfield hmodel hμ hp hp2 hs ha hβ0 hβ haβ
      hi hmean hpi hm hR0 center hrS hsS hRbound n N hn htrans

open LongTails.Proofs.StochasticEnvelopeSampling in
lemma localizedRadius_fourth_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a : ℝ} (h : Model L f field)
    (hg : Measurable (Function.uncurry g)) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (β : ℝ) (center : E) (n N : ℕ) (hn : 8 ≤ n + 1) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let R := Q.prod (Measure.infinitePi fun _ : ℕ => Q)
    Integrable (fun w => localizedRadius g L μ s β center w.1 w.2 N ^ 4) R ∧
      (∫ w, localizedRadius g L μ s β center w.1 w.2 N ^ 4 ∂R) ≤
        2 ^ 48 * ((L + μ) / μ) ^ 6 * (‖center - prox field μ center‖ + s / μ) ^ 4 := by
  have hκ : 1 ≤ (L + μ) / μ := (le_div_iff₀ hμ).mpr (by linarith [h.pos])
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  let Q := Measure.pi fun _ : Fin (n + 1) =>
    Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
  let R := Q.prod (Measure.infinitePi fun _ : ℕ => Q)
  let Z := fun rough : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω =>
    robustMean (fun i j k => g center (rough i j k))
  let S := fun rough => 4 * (‖Z rough‖ + s) / μ
  have hg0 : Measurable (g center) := hg.comp measurable_prodMk_left
  have hZ : Measurable Z := by
    apply (measurable_robustMean b n).comp
    exact Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
      Measurable.of_eval (fun k => hg0.comp (by fun_prop))))
  obtain ⟨hZi, hZm, _⟩ := robustMean_rough hg0 (field center) hp hp2 hs ha ha1
    (hi center) (hmean center) (hpi center) (hm center) n hn
  have hfield : ‖field center‖ ≤ μ * ((L + μ) / μ) * ‖center - prox field μ center‖ := by
    convert StochasticEnvelopeGeometry.center_field_bound h hμ center using 1
    field_simp
  obtain ⟨hSi, hSm⟩ := rough_radius_scaled_moment hZ (field center) hμ hs hκ hfield hZi hZm
  have hf : MeasurePreserving Prod.fst R Q := measurePreserving_fst
  have hlift : Integrable (fun w => S w.1 ^ 4) R := hf.integrable_comp_of_integrable hSi
  have he : (∫ w, S w.1 ^ 4 ∂R) = ∫ rough, S rough ^ 4 ∂Q := by
    calc
      _ = ∫ rough, S rough ^ 4 ∂Measure.map Prod.fst R :=
        (integral_map hf.measurable.aemeasurable (by
          simpa only [hf.map_eq] using hSi.aestronglyMeasurable)).symm
      _ = _ := by rw [hf.map_eq]
  have hliftm : (∫ w, S w.1 ^ 4 ∂R) ≤
      4096 * ((L + μ) / μ) ^ 4 * (‖center - prox field μ center‖ + s / μ) ^ 4 := by
    rw [he]
    exact hSm
  exact refined_radius_fourth_moment (measurable_localizedRadius hg L μ s β center b n N)
    (fun _ => by dsimp [S]; positivity)
    (fun w => (localizedRadius_bounds g L β hμ hs center w.1 w.2 N).1)
    hκ (norm_nonneg _) (by positivity) hlift hliftm
    (fun w => (localizedRadius_bounds g L β hμ hs center w.1 w.2 N).2)

lemma localizedRadius_tuned_failure {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E} {f : E → ℝ}
    {L μ p s a η : ℝ} (hmodel : Model L f field) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a) (hη : 0 < η)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let κ := (L + μ) / μ
    let β := 1 / (1024 * κ)
    let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
    let n := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η)⌉₊
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let r := ‖center - prox field μ center‖
    (Q.prod (Measure.infinitePi fun _ : ℕ => Q)) {w |
      localizedRadius g L μ s β center w.1 w.2 N < r + s / μ ∨
      192 * (r + s / μ) < localizedRadius g L μ s β center w.1 w.2 N} ≤
        ENNReal.ofReal η := by
  let κ := (L + μ) / μ
  let β := 1 / (1024 * κ)
  let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
  let n := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η)⌉₊
  have hκ0 : 0 < κ := by change 2 ≤ κ at hκ; linarith
  have hak : a ≤ κ⁻¹ ^ 2 := by
    have he : κ ^ (-2 : ℝ) = κ⁻¹ ^ 2 := by
      rw [Real.rpow_neg hκ0.le, Real.rpow_two, inv_pow]
    rw [he] at haκ
    exact haκ
  have ht := pilot_relative_tuning hκ hak
  change 0 ≤ β ∧ β ≤ 1 / 1024 ∧ a ≤ 512 * β ∧
    β ^ 2 * κ ≤ Real.sqrt κ / 256 at ht
  have ha1 : a ≤ 1 := by linarith [ht.2.1, ht.2.2.1]
  have hA : μ ≤ L + μ := by linarith [hmodel.pos]
  have hβ32 : β ≤ 1 / 32 := by linarith [ht.2.1]
  have hcost := momentum_cost hμ hA ht.1 hβ32
    (show L + μ = μ * κ by dsimp [κ]; field_simp) ht.2.2.2
  have hlog : 0 ≤ Real.log (1 + 1024 * κ) :=
    Real.log_nonneg (by linarith)
  have hN : ⌈(2 / InexactGradient.momentum (L + μ) μ (2 * β)) *
      Real.log (1 + (L + μ) / (μ / 1024))⌉₊ ≤ N := by
    apply Nat.ceil_mono
    have he : (L + μ) / (μ / 1024) = 1024 * κ := by dsimp [κ]; field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hcost hlog
  have htrans := pilot_transient hμ hA ht.1 hβ32 N hN
  have hc := StochasticEnvelopeSampling.confidence_allocation N hη
  have hfield : Measurable field := by
    have hl : LipschitzWith ⟨L, hmodel.pos.le⟩ field :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        simp only [dist_eq_norm]
        change ‖field x - field y‖ ≤ L * ‖x - y‖
        exact hmodel.lipschitz x y)
    exact hl.continuous.measurable
  have hh := localizedRadius_failure P hg hfield hmodel hμ hp hp2 hs ha ha1
    ht.1 ht.2.1 ht.2.2.1 hi hmean hpi hm center n N hc.1 htrans
  exact hh.trans (ENNReal.ofReal_le_ofReal hc.2)

end Sampling

end LongTails.Proofs.StochasticEnvelopePilot
