import YM.Push.BETA_TRANSPORT.Controlled
import YM.Push.PRICE_COMPILER.Canonical
import YM.Push.PRICE_COMPILER.Powers
import YM.UVNext.COUPLING_RESET.Probe


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Purchase the scalar price comparisons (not the RG estimates)

All-position nonempty trial-data *prices*, not making a Directed. First fix
stages and sensor constants for all paths satisfying those stage budgets;
these constants can be used repeatedly and in transitions. At or before
delays (AFTER rolls and other fixed costs if necessary), quote residual &
dial-motion multipliers for actual estimates scaled here by the regular-output
allowance, and ask ANY positive recovery radii through the unit interval.
Raising the entrance gate pays the comparison with the inverse price with no
shrinkage of this allowance or any path/label width at subsequent steps. Not
a claim that a cost of a different order (e.g., fixed coefficient error in
units threshold^2, with no decrease by L or by delay) can be made small in
these currencies by weak-coupling delay. Loop/full-return logs aren't bounded
by the schedule. Need real interacting estimates at all the required curves,
after *permitted* quotes.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.PriceCompiler Filter Set Lattice RG RG.Supply Wilson Precision
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

structure ResetPrices where
  cost : ℕ → ℕ → ℝ -- `j i`, finer stage j can equal coarser stage i
  radius : ℕ → ℕ → ℝ
  cost_pos j i : 0 < cost j i
  rad_pos j i : 0 < radius j i
  unit j i : radius j i ≤ 1

def Sensors (p : Sheet G) (η : ℕ → ℝ) := ∀ i, Sensor G (p.profile i).clip (p.profile i).paths (η i)
lemma sensors (hG : G.Simple) (p : Sheet G) : ∃ η, Sensors p η := by
  letI := hG.nontrivial_color
  choose η hη using (fun i => sensor G (p.profile i).clip (p.profile i).paths (p.profile i).paths_pos.le)
  exact ⟨η,hη⟩

variable {p : Sheet G} {q : ResetPrices} {η : ℕ → ℝ}

def Gate (η : ℕ → ℝ) (q : ResetPrices) (j i : ℕ) (x : ℝ) :=
    2*(q.cost j i+1) ≤ η i * q.radius j i * (mon x)^2

theorem can_delay_reset (q : ResetPrices) (η : ℕ → ℝ) (hη : ∀ i, 0 < η i) (e : ℕ → ℝ) :
    ∃ f, Monotone f ∧ e ≤ f ∧ ∀ j x, f j ≤ x → ∀ i, StepStages j i → Gate η q j i x := by
  apply collect_upper e; intro j; apply eventually_transitions
  intro i _
  have he : Tendsto (fun x => η i * q.radius j i * (mon x)^2) atTop atTop :=
    ((tendsto_pow_atTop (n:=2) (by decide)).comp mon_deep).const_mul_atTop (mul_pos (hη i) (q.rad_pos j i))
  exact he.eventually_ge_atTop _

variable {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}

def PricedReset (a : Levels G) (η : ℕ → ℝ) (q : ResetPrices) := ∀ m,
    let i := a.clock.J m; let j := a.clock.J (m+1)
    Sensor G (a.params m).clip (a.params m).paths (η i) ∧
      2*(q.cost j i+1) * a.clock.allowance m ≤ η i * (a.budget m).threshold^2 * q.radius j i

lemma buys_reset (a : Levels G) (h : Paid I a) (hη : Sensors p η)
    (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → Gate η q j i x) : PricedReset a η q := by
  intro m i j
  have hG := hg _ _ (h.pays m) _ (step_paid a m)
  have hd := a.fits.delayed m
  let g := a.clock.hatCoupling m
  let M := a.clock.monitor m
  have hp : 0 < g := inv_pos.mpr <| Real.sqrt_pos.mpr (zero_lt_one.trans hd)
  have h1 : g ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hd.le)
  have hq := q.cost_pos j i
  constructor
  · rw [params_eq h]; exact hη i
  calc
    _ ≤ 2*(q.cost j i + 1) * g^(2:ℝ) := by
      unfold Calendar.allowance; gcongr _ * ?_
      exact Real.rpow_le_rpow_of_exponent_ge hp h1 (by norm_num)
    _ ≤ (η i * q.radius j i * M^2)*g^2 := by
      rw [Real.rpow_two]; exact mul_le_mul_of_nonneg_right hG (sq_nonneg _)
    _ = _ := by change _ = _ * (g*M)^2 * _; ring


end YM.UVNext.CouplingReset
