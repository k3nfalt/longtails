import LongTails.Algorithms.CoupledMinimaxInner
import LongTails.Proofs.CompositeGapGeometry
import LongTails.Proofs.FeasibleGapExecution

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxAcceleration

open LongTails.Algorithms.CoupledMinimaxInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma accumulated_nonneg {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 ≤ accumulated L k := by
  unfold accumulated
  positivity

lemma weight_pos {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 < weight L k := by
  unfold weight
  positivity

lemma accumulated_add {L : ℝ} (hL : 0 < L) (k : ℕ) :
    accumulated L k + weight L k = accumulated L (k + 1) := by
  unfold accumulated weight
  push_cast
  field_simp
  ring

lemma accumulated_succ_pos {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < accumulated L (k + 1) := by
  rw [← accumulated_add hL]
  exact add_pos_of_nonneg_of_pos (accumulated_nonneg hL k) (weight_pos hL k)

lemma weight_bound {L : ℝ} (hL : 0 < L) (k : ℕ) :
    L * weight L k ^ 2 ≤ accumulated L (k + 1) := by
  unfold accumulated weight
  push_cast
  field_simp
  nlinarith [(show (0 : ℝ) ≤ k by positivity)]

lemma coefficients {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 ≤ accumulated L k / accumulated L (k + 1) ∧
    0 ≤ weight L k / accumulated L (k + 1) ∧
    accumulated L k / accumulated L (k + 1) +
      weight L k / accumulated L (k + 1) = 1 := by
  have hp := accumulated_succ_pos hL k
  refine ⟨div_nonneg (accumulated_nonneg hL k) hp.le,
    div_nonneg (weight_pos hL k).le hp.le, ?_⟩
  rw [← add_div, accumulated_add hL, div_self hp.ne']

lemma queryPoint_mem {Y : Set E} (hY : Convex ℝ Y) {L : ℝ} (hL : 0 < L)
    (k : ℕ) {s : State E} (hx : s.x ∈ Y) (hz : s.z ∈ Y) :
    queryPoint L k s ∈ Y := by
  obtain ⟨ha, hb, hab⟩ := coefficients hL k
  exact hY hx hz ha hb hab

lemma update_mem {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y) {L : ℝ} (hL : 0 < L)
    (center : E) (k : ℕ) {s : State E} (hx : s.x ∈ Y) (g : E) :
    (update P L center k s g).x ∈ Y ∧ (update P L center k s g).z ∈ Y := by
  obtain ⟨ha, hb, hab⟩ := coefficients hL k
  exact ⟨hY hx (hP _) ha hb hab, hP _⟩

lemma scaled_query {L : ℝ} (hL : 0 < L) (k : ℕ) (s : State E) :
    accumulated L (k + 1) • queryPoint L k s =
      accumulated L k • s.x + weight L k • s.z := by
  have hp := (accumulated_succ_pos hL k).ne'
  simp only [queryPoint, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma scaled_update {P : E → E} {L : ℝ} (hL : 0 < L) (center : E)
    (k : ℕ) (s : State E) (g : E) :
    accumulated L (k + 1) • (update P L center k s g).x =
      accumulated L k • s.x + weight L k • (update P L center k s g).z := by
  have hp := (accumulated_succ_pos hL k).ne'
  simp only [update, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

lemma projected_model_min {Y : Set E} {P : E → E}
    (hP : ∀ x, ∀ u ∈ Y, ⟪x - P x, u - P x⟫ ≤ 0)
    (center v : E) (A c : ℝ) :
    IsMinOn (CompositeGapGeometry.model (fun _ : E => 0) center A v c)
      Y (P (center - v)) := by
  intro u hu
  let z := P (center - v)
  have hp := hP (center - v) u hu
  change ⟪center - v - z, u - z⟫ ≤ 0 at hp
  have he : u - center = (u - z) + (z - center) := by abel
  have hn : ‖u - center‖ ^ 2 = ‖u - z‖ ^ 2 +
      2 * ⟪u - z, z - center⟫ + ‖z - center‖ ^ 2 := by
    rw [he, norm_add_sq_real]
  have hi : ⟪v, u - center⟫ = ⟪v, u - z⟫ + ⟪v, z - center⟫ := by
    rw [he, inner_add_right]
  have hvec : center - v - z = -(z - center) - v := by abel
  rw [hvec, inner_sub_left, inner_neg_left, real_inner_comm (u - z) (z - center)] at hp
  change CompositeGapGeometry.model (fun _ : E => 0) center A v c z ≤ _
  simp only [CompositeGapGeometry.model, mul_zero, add_zero]
  nlinarith [sq_nonneg ‖u - z‖]

lemma step_potential {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y) {L : ℝ} (hL : 0 < L) {f : E → ℝ}
    (center : E) (k : ℕ) (s : State E) (g : E) (c : ℝ)
    (hz : s.z ∈ Y)
    (hmin : IsMinOn (CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L k) s.v c) Y s.z)
    (hold : accumulated L k * f s.x ≤ CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L k) s.v c s.z)
    (hconv : f (queryPoint L k s) + ⟪g, s.x - queryPoint L k s⟫ ≤ f s.x)
    (hsmooth : f (update P L center k s g).x ≤
      f (queryPoint L k s) + ⟪g, (update P L center k s g).x - queryPoint L k s⟫ +
        L / 2 * ‖(update P L center k s g).x - queryPoint L k s‖ ^ 2) :
    accumulated L (k + 1) * f (update P L center k s g).x ≤
      CompositeGapGeometry.model (fun _ : E => 0) center (accumulated L (k + 1))
        (update P L center k s g).v
        (c + weight L k * (f (queryPoint L k s) - ⟪g, queryPoint L k s - center⟫))
        (update P L center k s g).z := by
  have hq := scaled_query hL k s
  have hu := scaled_update (P := P) hL center k s g
  rw [← accumulated_add hL k] at hq hu
  have hgrowth := CompositeGapGeometry.model_growth hY (convexOn_const (0 : ℝ) hY)
    (accumulated_nonneg hL k) hz (hP (center - (s.v + weight L k • g))) hmin
  have hnew := CompositeGapGeometry.model_append (fun _ : E => 0) center s.v g
    (queryPoint L k s) (update P L center k s g).z (accumulated L k)
    (weight L k) c (f (queryPoint L k s))
  have hw : 2 * (L / 2) * weight L k ^ 2 ≤ accumulated L k + weight L k := by
    rw [accumulated_add hL k]
    nlinarith [weight_bound hL k]
  have hh := CompositeGapGeometry.cumulative_step (ψ := fun _ : E => 0)
    (accumulated_nonneg hL k)
    (add_pos_of_nonneg_of_pos (accumulated_nonneg hL k) (weight_pos hL k))
    hq hu hconv (by simp) hsmooth (by simpa using hold) hgrowth hnew hw
  simpa only [add_zero, accumulated_add hL k, update] using hh

lemma phase_bound {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y)
    (hPv : ∀ x, ∀ u ∈ Y, ⟪x - P x, u - P x⟫ ≤ 0)
    {L : ℝ} (hL : 0 < L) {f : E → ℝ} {grad : E → E}
    (hconv : ∀ x ∈ Y, ∀ u ∈ Y, f x + ⟪grad x, u - x⟫ ≤ f u)
    (hsmooth : ∀ x ∈ Y, ∀ u ∈ Y,
      f u ≤ f x + ⟪grad x, u - x⟫ + L / 2 * ‖u - x‖ ^ 2)
    (center : E) {u : E} (hu : u ∈ Y) (N k : ℕ) (s : State E) (c : ℝ)
    (hx : s.x ∈ Y) (hz : s.z ∈ Y)
    (hmin : IsMinOn (CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L k) s.v c) Y s.z)
    (hold : accumulated L k * f s.x ≤ CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L k) s.v c s.z)
    (hmodel : CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L k) s.v c u ≤ ‖u - center‖ ^ 2 / 2 + accumulated L k * f u) :
    accumulated L (k + N) *
      (f (OracleTemplate.QueryPlan.eval grad (phase id id P L center N k s)) - f u) ≤
        ‖u - center‖ ^ 2 / 2 := by
  induction N generalizing k s c with
  | zero =>
      simp only [Nat.add_zero, phase, OracleTemplate.QueryPlan.eval]
      have hh : CompositeGapGeometry.model (fun _ : E => 0)
          center (accumulated L k) s.v c s.z ≤
        CompositeGapGeometry.model (fun _ : E => 0) center (accumulated L k) s.v c u := hmin hu
      nlinarith
  | succ N ih =>
      let y := queryPoint L k s
      let g := grad y
      let t := update P L center k s g
      let c' := c + weight L k * (f y - ⟪g, y - center⟫)
      have hy : y ∈ Y := queryPoint_mem hY hL k hx hz
      have ht := update_mem hY hP hL center k hx g
      have hpot := step_potential hY hP hL center k s g c hz hmin hold
        (hconv y hy s.x hx) (hsmooth y hy t.x ht.1)
      have hmin' : IsMinOn (CompositeGapGeometry.model (fun _ : E => 0)
          center (accumulated L (k + 1)) t.v c') Y t.z :=
        projected_model_min hPv center t.v (accumulated L (k + 1)) c'
      have hmodel' : CompositeGapGeometry.model (fun _ : E => 0)
          center (accumulated L (k + 1)) t.v c' u ≤
            ‖u - center‖ ^ 2 / 2 + accumulated L (k + 1) * f u := by
        have ha := (weight_pos hL k).le
        have hc := mul_le_mul_of_nonneg_left (hconv y hy u hu) ha
        have happ := CompositeGapGeometry.model_append (fun _ : E => 0)
          center s.v g y u (accumulated L k) (weight L k) c (f y)
        change CompositeGapGeometry.model (fun _ : E => 0)
          center (accumulated L (k + 1)) (s.v + weight L k • g) c' u ≤ _
        rw [← accumulated_add hL k]
        dsimp only [c']
        rw [happ]
        simp only [add_zero]
        dsimp only [g] at *
        nlinarith
      have hh := ih (k + 1) t c' ht.1 ht.2 hmin' hpot hmodel'
      have hidx : k + (N + 1) = (k + 1) + N := by omega
      rw [hidx]
      exact hh

lemma phase_mem {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y) {L : ℝ} (hL : 0 < L) (grad : E → E)
    (center : E) (N k : ℕ) (s : State E) (hx : s.x ∈ Y) (hz : s.z ∈ Y) :
    OracleTemplate.QueryPlan.eval grad (phase id id P L center N k s) ∈ Y := by
  induction N generalizing k s with
  | zero => exact hx
  | succ N ih =>
      have ht := update_mem hY hP hL center k hx (grad (queryPoint L k s))
      exact ih (k + 1) _ ht.1 ht.2

lemma phase_initial_bound {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y)
    (hPv : ∀ x, ∀ u ∈ Y, ⟪x - P x, u - P x⟫ ≤ 0)
    {L : ℝ} (hL : 0 < L) {f : E → ℝ} {grad : E → E}
    (hconv : ∀ x ∈ Y, ∀ u ∈ Y, f x + ⟪grad x, u - x⟫ ≤ f u)
    (hsmooth : ∀ x ∈ Y, ∀ u ∈ Y,
      f u ≤ f x + ⟪grad x, u - x⟫ + L / 2 * ‖u - x‖ ^ 2)
    {center u : E} (hc : center ∈ Y) (hu : u ∈ Y) (N : ℕ) :
    accumulated L N *
      (f (OracleTemplate.QueryPlan.eval grad (phase id id P L center N 0 (initial center))) - f u) ≤
        ‖u - center‖ ^ 2 / 2 := by
  have hm : IsMinOn (CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L 0) (0 : E) 0) Y center := by
    intro v _
    change CompositeGapGeometry.model (fun _ : E => 0)
      center (accumulated L 0) (0 : E) 0 center ≤
      CompositeGapGeometry.model (fun _ : E => 0) center (accumulated L 0) (0 : E) 0 v
    simp only [CompositeGapGeometry.model, inner_zero_left, mul_zero, add_zero,
      sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
    positivity

  have hh := phase_bound hY hP hPv hL hconv hsmooth center hu N 0 (initial center) 0 hc hc hm
    (by simp [accumulated, initial, CompositeGapGeometry.model])
    (by simp [accumulated, initial, CompositeGapGeometry.model])
  simpa only [Nat.zero_add] using hh

lemma phase_halves {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y)
    (hPv : ∀ x, ∀ u ∈ Y, ⟪x - P x, u - P x⟫ ≤ 0)
    {L μ : ℝ} (hL : 0 < L) {f : E → ℝ} {grad : E → E}
    (hconv : ∀ x ∈ Y, ∀ v ∈ Y, f x + ⟪grad x, v - x⟫ ≤ f v)
    (hsmooth : ∀ x ∈ Y, ∀ v ∈ Y,
      f v ≤ f x + ⟪grad x, v - x⟫ + L / 2 * ‖v - x‖ ^ 2)
    {center u : E} (hc : center ∈ Y) (hu : u ∈ Y)
    (hgrowth : ∀ v ∈ Y, μ / 2 * ‖v - u‖ ^ 2 ≤ f v - f u)
    (N : ℕ) (hweight : 4 ≤ μ * accumulated L N) :
    ‖OracleTemplate.QueryPlan.eval grad (phase id id P L center N 0 (initial center)) - u‖ ≤
      ‖center - u‖ / 2 := by
  have hm := phase_mem hY hP hL grad center N 0 (initial center) hc hc
  have hb := phase_initial_bound hY hP hPv hL hconv hsmooth hc hu N
  have hg := mul_le_mul_of_nonneg_left (hgrowth _ hm) (accumulated_nonneg hL N)
  have hw := mul_le_mul_of_nonneg_right hweight
    (sq_nonneg ‖OracleTemplate.QueryPlan.eval grad
      (phase id id P L center N 0 (initial center)) - u‖)
  rw [norm_sub_rev u center] at hb
  nlinarith [norm_nonneg (center - u), norm_nonneg
    (OracleTemplate.QueryPlan.eval grad (phase id id P L center N 0 (initial center)) - u)]

lemma restart_bound {Y : Set E} (hY : Convex ℝ Y) {P : E → E}
    (hP : ∀ x, P x ∈ Y)
    (hPv : ∀ x, ∀ u ∈ Y, ⟪x - P x, u - P x⟫ ≤ 0)
    {L μ : ℝ} (hL : 0 < L) {f : E → ℝ} {grad : E → E}
    (hconv : ∀ x ∈ Y, ∀ v ∈ Y, f x + ⟪grad x, v - x⟫ ≤ f v)
    (hsmooth : ∀ x ∈ Y, ∀ v ∈ Y,
      f v ≤ f x + ⟪grad x, v - x⟫ + L / 2 * ‖v - x‖ ^ 2)
    {center u : E} (hc : center ∈ Y) (hu : u ∈ Y)
    (hgrowth : ∀ v ∈ Y, μ / 2 * ‖v - u‖ ^ 2 ≤ f v - f u)
    (N : ℕ) (hweight : 4 ≤ μ * accumulated L N) (S : ℕ) :
    OracleTemplate.QueryPlan.eval grad (restart id id P L N S center) ∈ Y ∧
    ‖OracleTemplate.QueryPlan.eval grad (restart id id P L N S center) - u‖ ≤
      (1 / 2 : ℝ) ^ S * ‖center - u‖ := by
  induction S generalizing center with
  | zero => simpa only [restart, OracleTemplate.QueryPlan.eval, pow_zero, one_mul] using
      (show center ∈ Y ∧ ‖center - u‖ ≤ ‖center - u‖ from ⟨hc, le_rfl⟩)
  | succ S ih =>
      have hm := phase_mem hY hP hL grad center N 0 (initial center) hc hc
      have hh := phase_halves hY hP hPv hL hconv hsmooth hc hu hgrowth N hweight
      have hb := ih hm
      simp only [restart, OracleTemplate.QueryPlan.eval_bind]
      refine ⟨hb.1, hb.2.trans ?_⟩
      calc
        (1 / 2 : ℝ) ^ S * ‖OracleTemplate.QueryPlan.eval grad
            (phase id id P L center N 0 (initial center)) - u‖ ≤
            (1 / 2 : ℝ) ^ S * (‖center - u‖ / 2) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = (1 / 2 : ℝ) ^ (S + 1) * ‖center - u‖ := by rw [pow_succ]; ring

lemma phase_eval_map {Q R : Type*} (query : E → Q) (read : R → E) (oracle : Q → R)
    (P : E → E) (L : ℝ) (center : E) (N k : ℕ) (s : State E) :
    OracleTemplate.QueryPlan.eval oracle (phase query read P L center N k s) =
      OracleTemplate.QueryPlan.eval (fun y => read (oracle (query y)))
        (phase id id P L center N k s) := by
  induction N generalizing k s with
  | zero => rfl
  | succ N ih => exact ih (k + 1) _

lemma restart_eval_map {Q R : Type*} (query : E → Q) (read : R → E) (oracle : Q → R)
    (P : E → E) (L : ℝ) (N S : ℕ) (center : E) :
    OracleTemplate.QueryPlan.eval oracle (restart query read P L N S center) =
      OracleTemplate.QueryPlan.eval (fun y => read (oracle (query y)))
        (restart id id P L N S center) := by
  induction S generalizing center with
  | zero => rfl
  | succ S ih =>
      simp only [restart, OracleTemplate.QueryPlan.eval_bind]
      rw [phase_eval_map query read oracle]
      exact ih _

lemma phase_supported {Q R : Type*} {Y : Set E} (hY : Convex ℝ Y)
    {P : E → E} (hP : ∀ x, P x ∈ Y) {L : ℝ} (hL : 0 < L)
    (query : E → Q) (read : R → E) (oracle : Q → R) (allowed : Q → Prop)
    (hquery : ∀ y ∈ Y, allowed (query y))
    (center : E) (N k : ℕ) (s : State E) (hx : s.x ∈ Y) (hz : s.z ∈ Y) :
    FeasibleGapExecution.Supported oracle allowed (phase query read P L center N k s) := by
  induction N generalizing k s with
  | zero => trivial
  | succ N ih =>
      refine ⟨hquery _ (queryPoint_mem hY hL k hx hz), ?_⟩
      have ht := update_mem hY hP hL center k hx (read (oracle (query (queryPoint L k s))))
      exact ih (k + 1) _ ht.1 ht.2

lemma restart_supported {Q R : Type*} {Y : Set E} (hY : Convex ℝ Y)
    {P : E → E} (hP : ∀ x, P x ∈ Y) {L : ℝ} (hL : 0 < L)
    (query : E → Q) (read : R → E) (oracle : Q → R) (allowed : Q → Prop)
    (hquery : ∀ y ∈ Y, allowed (query y))
    (N S : ℕ) {center : E} (hc : center ∈ Y) :
    FeasibleGapExecution.Supported oracle allowed (restart query read P L N S center) := by
  induction S generalizing center with
  | zero => trivial
  | succ S ih =>
      apply FeasibleGapExecution.supported_bind
      · exact phase_supported hY hP hL query read oracle allowed hquery center N 0
          (initial center) hc hc
      · apply ih
        rw [phase_eval_map]
        exact phase_mem hY hP hL _ center N 0 (initial center) hc hc

end LongTails.Proofs.CoupledMinimaxAcceleration
