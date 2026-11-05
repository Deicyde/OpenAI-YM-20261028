import YM.Extra.ITERATION_NO_LOSS.Rebuild

/-!
# Further application: the within-schedule mixed-radius rebuild

Neither a choice of singleton envelopes nor a construction of
Bands. Only a radius/exponent ledger, conditioned on full-support funded
input estimates on actual coefficients. The extra `r` in output cover units
must also be bought from prior reserves (e.g. Rebuild/V); prove localization
before using Shapes resets. Not applied to stand-alone near-coincident keys
for which `far` fails.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.MarkerRoom
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Rebuild Scales
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {C : Family G}




/-- k,j are fine/coarse stage in that order. `r` a per-transition reserve
(can be chosen pre-L), `n` maximum admitted exponent in Mix.width, `d`
maximum engineering power on this physical step. Can make these grow along
the stages. `F.output` one post-L bill; applied only **once for this step**,
not iterating a post-L factor in the same native radius. -/
structure Priced (r : ℕ → ℕ → ℝ) (n d : ℕ → ℕ) (F : Rebuild.Fuel D) (W : Supply.Delays Θ) : Prop where
  room (k j : ℕ) : j ≤ k → k ≤ j+1 → ∀ x, W.betaEntry k ≤ x →
    Vac.Numbers.Hat x ≤ 2 * Vac.Numbers.Hat (betaF G x (D.L k)) ∧
    F.output k j x (Θ.theta k) * ((D.L k).val:ℝ)^(d k) * (2^(n k) * (S.profile k).columns^(2:ℕ)) ≤ Real.exp (r k j * radiusB x/64)

lemma eventual (k j : ℕ) {r : ℝ} (hr : 0 < r) (n d : ℕ) (F : Rebuild.Fuel D) (Θ : Protection D) :
    ∀ᶠ x : ℝ in atTop, Vac.Numbers.Hat x ≤ 2*Vac.Numbers.Hat (betaF G x (D.L k)) ∧
      F.output k j x (Θ.theta k) * ((D.L k).val:ℝ)^d * (2^n * (S.profile k).columns^(2:ℕ)) ≤ Real.exp (r*radiusB x/64) := by
  let s := G.slopeConstant*Real.log (D.L k).val
  let A := 2^(n:ℕ)*(S.profile k).columns^(2:ℕ)
  have hA : 0 ≤ A := by unfold A; positivity
  have ht := ((tiny_poly s (F.cost k j) (Θ.theta k) (F.nonnegative ..) (F.power k j)).mul (Tiny.const tendsto_id (((D.L k).val:ℝ)^d)
    (by positivity)) tendsto_id).mul (Tiny.const tendsto_id A hA) tendsto_id
  filter_upwards [first (r/64) 1 (by positivity),ht 1 zero_lt_one,eventually_gt_atTop (2:ℝ), eventually_ge_atTop s,eventually_gt_atTop (-s)]
    with x he hx hl hy hz
  have h1 : 0 < x := by linarith
  have h2 : 0 < x+s := by linarith
  constructor
  · unfold Vac.Numbers.Hat betaF
    change (Real.sqrt x)⁻¹ ≤ 2*(Real.sqrt (x+s))⁻¹
    rw [← one_div,le_mul_inv_iff₀ (Real.sqrt_pos.mpr h2),one_div_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr h1)]
    nlinarith [Real.sq_sqrt h1.le,Real.sq_sqrt h2.le,Real.sqrt_pos.mpr h1,Real.sqrt_pos.mpr h2]
  change F.output k j x (Θ.theta k) * _ * A ≤ _
  apply hx.2.trans; rw [id_eq,Real.rpow_one]
  rw [show -(r/64)*radiusB x=-(r*radiusB x/64) by ring,Real.exp_neg,Real.rpow_neg_one] at he
  exact (inv_le_inv₀ (Real.exp_pos _) h1).mp he

lemma prices (r : ℕ → ℕ → ℝ) (hr : ∀ i j, 0 < r i j) (n d : ℕ → ℕ) (F : Rebuild.Fuel D) (W : Supply.Delays Θ) :
    ∃ W' : Supply.Delays Θ, W'.shells=W.shells ∧ W'.growth=W.growth ∧ W'.scaleEntry=W.scaleEntry ∧ W.betaEntry ≤ W'.betaEntry ∧ Priced r n d F W' := by
  choose w hw using fun i j => eventually_atTop.mp (eventual i j (hr i j) (n i) (d i) F Θ)
  refine ⟨{W with betaEntry := fun i => max (W.betaEntry i) (max (w i i) (w i (i-1)))},rfl,rfl,rfl,fun _ => le_max_left ..,⟨fun i j hj hi x hx => hw i j x (le_trans (le_max_of_le_right ?_) hx)⟩⟩
  rcases (show j=i ∨ j=i-1 by omega) with rfl|rfl; exact le_max_left ..; exact le_max_right ..


open Overlay Marker
variable {r : ℕ → ℕ → ℝ} {n d : ℕ → ℕ} {F : Rebuild.Fuel D}
variable (h : Priced r n d F W) (hC : Paid I C.path.levels) (m : ℕ)
local notation "a" => C.path.levels
local notation "k" => Calendar.J (Levels.clock a) (m+1)
local notation "j" => Calendar.J (Levels.clock a) m

include h hC



end YM.Extra.Iteration.MarkerRoom
