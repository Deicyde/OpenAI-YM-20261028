import YM.Push.SECTOR_MEASURE.Bounds
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Haar



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Per-link bills: intact Haar with chord damping or chart at t scale

Keep probability Haar for every still-slice coordinate (not yet a determinant
estimate; the $C_L$ this leaves per integrated position compared to fluctuation
scale **isn't** a bound uniformly in volume at Gaussian normalization).
Later use floored products to retain the probability AND earn separately, even
with inactive sets varying in the inventory. No spin-plane replacements.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ENNReal

variable (G : Gauge)

/-- Gaussian scale *bound on real compact group integration*. Not substitution by a
Gaussian measure or normalization by a free Z. -/
def candle (γ a u : ℝ) := Real.exp (-γ*(u/a)^2)
lemma candle_nn (γ a u : ℝ) : 0≤candle γ a u := (Real.exp_pos _).le

lemma candle_integrable (γ a : ℝ) : Integrable (fun u : G.El => candle γ a (G.chord u)) G.probHaar :=
  (Env.compact (by unfold candle; fun_prop)).integrable _

/-- Annuli avoid any global chart computation. -/
lemma candle_billed (γ : ℝ) (hγ : 0<γ) : ∃ H : ℝ, 0<H ∧ ∀ s : ℝ, 0<s →
    ∫ u : G.El, candle γ s (G.chord u) ∂G.probHaar ≤ H*s^dim G := by
  obtain ⟨D,hD,h⟩ := shell_billed G
  let cap (n : ℕ) := Real.exp (-γ*(n:ℝ)^2)
  let f (n : ℕ) := ((n:ℝ)+1)^dim G * cap n
  have hf : Summable f := by
    have he := ((Real.summable_pow_mul_exp_neg_nat_mul (dim G) hγ).comp_injective (i:=fun i : ℕ => i+1)
      (by intro i j he; simpa using he)).mul_right (Real.exp (2*γ))
    apply he.of_nonneg_of_le (g:=f) (fun _ => by dsimp only [f,cap]; positivity)
    intro n
    change f n ≤ (((n+1:ℕ):ℝ)^dim G*Real.exp (-γ*((n+1:ℕ):ℝ)))*Real.exp (2*γ)
    unfold f cap; rw [mul_assoc,← Real.exp_add]; push_cast
    apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity)
    have hh : (n:ℝ) - 1 ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-(1/2:ℝ))]
    nlinarith only [mul_le_mul_of_nonneg_left hh hγ.le]
  let H := ∑' i, f i
  have hm (n) : 0 ≤ f n := by dsimp only [f,cap]; positivity
  have hH : 0≤H := tsum_nonneg hm
  refine ⟨D*H+1,by positivity,fun s hs => ?_⟩
  let N := ⌊2/s⌋₊+1
  let w (n : ℕ) := G.shell (((n:ℝ)+1)*s)
  let F (n : ℕ) := (w n).indicator (fun _ => cap n)
  have he (n : ℕ) : Integrable (F n) G.probHaar := (integrable_const _).indicator (G.shell_meas _)
  calc
    _ ≤ ∫ u, ∑ i∈Finset.range N, F i u ∂G.probHaar := integral_mono (candle_integrable G γ s)
      (integrable_finsetSum _ fun i _ => he i) fun u => by
        let x := G.chord u
        have hu : 0 ≤ x := G.chord_nonneg _
        let m : ℕ := ⌊x/s⌋₊
        have hm : m < N := Nat.lt_succ_of_le (Nat.floor_le_floor (by gcongr; exact G.chord_le_two u))
        have hv (i) (_ : i∈ Finset.range N) : 0 ≤ F i u := Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u
        have hp : u ∈ w m := ((div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (x/s))).le
        refine le_trans ?_ (Finset.single_le_sum hv (Finset.mem_range.mpr hm))
        unfold F; rw [Set.indicator_of_mem hp]; unfold cap
        exact Real.exp_monotone (mul_le_mul_of_nonpos_left
          (pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity : 0≤x/s)) 2) (by linarith))
    _ = ∑ i ∈ Finset.range N, G.probHaar.real (w i) * cap i := by
      rw [integral_finsetSum _ fun i _ => he i]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (∫ u, F i u ∂G.probHaar) = _ from integral_indicator_const _ (G.shell_meas ..), smul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range N, f i * (D*s^dim G) := by
      refine Finset.sum_le_sum fun i _ => ?_
      apply (mul_le_mul_of_nonneg_right (h (((i:ℝ)+1)*s) (by positivity)) (Real.exp_pos _).le).trans_eq
      unfold f; rw [mul_pow]; ring
    _ ≤ H*(D*s^dim G) := by rw [← Finset.sum_mul]; gcongr; exact hf.sum_le_tsum _ (fun i _ => hm _)
    _ ≤ _ := by nlinarith [pow_nonneg hs.le (dim G)]

section modes

/-- clipped: carrying *only the grant* (and chart small, not penalized),
shielded: use also cut coarse V factor for squares. -/
inductive Mode where
  | clipped | shielded
namespace Mode

def size (m : Mode) (G : Gauge) (L : Side) (x : ℝ) : ℝ := match m with
  | clipped => fiery G x L
  | shielded => g G L x

variable {G} in
def light (m : Mode) (C γ s : ℝ) (u : G.El) : ℝ := match m with
  | clipped => (G.shell (C*s)).indicator (fun _ => (1:ℝ)) u
  | shielded => candle γ s (G.chord u)

variable {G} in
def share (m : Mode) (C γ s : ℝ) (u : G.El) := m.light C γ s u + s ^ dim G

variable (m : Mode)
lemma light_env (C γ s : ℝ) : Envelope (m.light (G:=G) C γ s) := by
  cases m
  · unfold light; simp only [Set.indicator]
    exact Envelope.piece (G.shell_meas _) (Envelope.const _) (Envelope.const _)
  exact Env.compact (show Continuous (fun u : G.El => candle γ s (G.chord u)) by unfold candle; fun_prop)
lemma light_nonneg (C γ s : ℝ) (u : G.El) : 0 ≤ m.light C γ s u := by
  cases m
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  exact candle_nn ..

lemma share_env (C γ s : ℝ) : Envelope (m.share (G:=G) C γ s) := (light_env G m C γ s).add (Envelope.const _)
lemma share_nonneg (C γ s : ℝ) (h : 0≤s) (u : G.El) : 0≤m.share C γ s u := add_nonneg (light_nonneg ..) (by positivity)

lemma light_price (C γ : ℝ) (hC : 0<C) (hγ : 0<γ) : ∃ D : ℝ, 1 ≤ D ∧ ∀ s : ℝ, 0 < s →
    ∫ u : G.El, m.light C γ s u ∂G.probHaar ≤ D*s^dim G := by
  cases m
  · obtain ⟨D,hd,h⟩ := shell_billed G
    refine ⟨max 1 (D*C^dim G),le_max_left ..,fun s hs => ?_⟩
    rw [show (∫ u : G.El, clipped.light C γ s u ∂G.probHaar) = G.probHaar.real (G.shell (C*s))*1 from
      integral_indicator_const _ (G.shell_meas _), mul_one]
    refine (h (C*s) (by positivity)).trans ?_
    rw [mul_pow, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
  obtain ⟨D,hd,h⟩ := candle_billed G γ hγ
  exact ⟨max 1 D,le_max_left ..,fun s hs => (h _ hs).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))⟩

variable {G} {ι : Type*} [Fintype ι] (t : ι → G.El)

def lamp (C γ s : ℝ) (a : ι → G.El) := ∏ i, m.share C γ s (a i*(t i)⁻¹)

lemma lamp_env (C γ s : ℝ) : Envelope (m.lamp t C γ s) := by
  have hf i : Measurable (fun a : ι → G.El => a i*(t i)⁻¹) := by fun_prop
  let v i (a : ι → G.El) := m.share C γ s (a i*(t i)⁻¹)
  have hv i : Envelope (v i) := Env.along (m.share_env G ..) (hf i)
  choose b hb using fun i => (hv i).cost
  refine ⟨Finset.measurable_fun_prod _ fun i _ => (hv i).meas,∏ i, b i,fun i => ?_⟩
  unfold lamp; rw [norm_prod]; exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hb j i)

lemma lamp_nonneg (C γ s : ℝ) (h : 0≤s) (a : ι → G.El) : 0≤m.lamp t C γ s a :=
  Finset.prod_nonneg (fun i _ => share_nonneg G m C γ s h _)

/-- Restore each floored weight even at the inactive positions (later this
cost is billed entirely through the seed exponential). -/
lemma floor_cost (C γ s : ℝ) (hs : 0<s) (a : ι → G.El) (E : Finset ι) :
    (∏ i ∈ E, m.light C γ s (a i*(t i)⁻¹)) ≤ (s⁻¹ ^ dim G)^(Fintype.card ι-E.card)*m.lamp t C γ s a := by
  classical
  let A (i : ι) := m.share C γ s (a i*(t i)⁻¹)
  have hA (i) : s^dim G ≤ A i := le_add_of_nonneg_left (light_nonneg ..)
  have hp : 0<s^dim G := pow_pos hs _
  unfold lamp; change _ ≤ _ * ∏ i, A i
  rw [← Finset.prod_mul_prod_compl E, mul_left_comm, inv_pow,← Finset.card_compl E]
  have he : 1 ≤ ((s ^ dim G)⁻¹) ^ Eᶜ.card * ∏ i∈Eᶜ, A i := by
    have h := Finset.prod_le_prod (s:=Eᶜ) (fun _ _ => hp.le) (fun i _ => hA i)
    rw [Finset.prod_const] at h
    have hx : (0:ℝ) < (s^dim G) ^ Eᶜ.card := by positivity
    rwa [inv_pow,← div_eq_inv_mul,le_div_iff₀ hx,one_mul]
  refine le_trans ?_ (le_mul_of_one_le_right (Finset.prod_nonneg (fun i _ => hp.le.trans (hA i))) he)
  exact Finset.prod_le_prod (fun _ _ => light_nonneg ..) (fun _ _ => le_add_of_nonneg_right hp.le)

/-- Per-link universal integral price, centers arbitrary; constants uniform
in number of links but the resulting products explicitly aren't at scale s^d.
Doesn't return `$s_g$` or a vacuum energy. -/
lemma lamp_price (C γ : ℝ) (hC : 0<C) (hγ : 0<γ) : ∃ D : ℝ, 1 ≤ D ∧
    ∀ (ι : Type) [Fintype ι] (t : ι → G.El) (s : ℝ), 0<s →
    (∫ a, m.lamp t C γ s a ∂(Measure.pi fun _ => G.probHaar)) ≤ (D*s^dim G)^Fintype.card ι := by
  obtain ⟨D,hD,h⟩ := light_price G m C γ hC hγ
  refine ⟨D+1,by linarith,fun ι _ t s hs => ?_⟩
  let X (i : ι) (u : G.El) := m.share C γ s (u*(t i)⁻¹)
  unfold lamp; rw [show (∫ a, ∏ i, m.share C γ s (a i*(t i)⁻¹) ∂(Measure.pi fun (_i : ι) => G.probHaar)) = _ from integral_fintype_prod_eq_prod (E:=fun _ : ι => G.El) X, ← Finset.card_univ, ← Finset.prod_const]; unfold X
  have he (i : ι) : (∫ u : G.El, m.share C γ s (u*(t i)⁻¹) ∂G.probHaar) =
      (∫ u : G.El, m.share C γ s u ∂G.probHaar) := integral_mul_right_eq_self ..
  apply Finset.prod_le_prod (fun i _ => by apply integral_nonneg; intro; exact share_nonneg G m C γ s hs.le _) (fun i _ => ?_)
  rw [he]
  unfold share; rw [integral_add ((light_env G m C γ s).integrable _) (integrable_const _),integral_const]; simp only [probReal_univ,one_smul]
  linarith [h s hs]
end Mode
end modes
end YM.SectorNext.Remainder
