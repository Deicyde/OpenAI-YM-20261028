import YM.RemainderComparison.Access.Geometry
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hallmark

/-!
 # First-rate stencil bound

 Do not absorb a loss in the power of the norm of opaque, inherited
 activities; e.g., this invoice survives b^{-R} testing where b is the
 *actual* coupling. Matching collar powers is not equivalent to changing
 the exponent on e. Strengthen the earned rates at bill time; no
 assumption that `Rate 0` is polynomial in monitors. For calls
 post L and finite Staple orders only, need to purchase at procured
 stamp.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison
open Function Filter Lattice RG Pressure Pressure.Stores Push.AbsoluteSums
open ConnectedActivityE6 Coat Mask PhysicalNext.Repeat Lantern
open scoped Topology BigOperators Classical
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ} {a b t : ℝ}
local notation "M" => Delay.fineMonitor G L
local notation "Z" => (fun x=>betaF G x L)

def Gear (G : Gauge) (L : Side) (a : ℝ) (p : ℝ→ℝ) : Prop := Reserve G L fun s=> (betaF G s L)^(-a) * p s

namespace Gear

lemma compare (hp : Gear G L a p) (h : ∀ᶠ x in atTop, |q x| ≤ |p x|) : Gear G L a q :=by
  apply (show Reserve G L _ from hp).compare
  filter_upwards [h] with x hx; rw [abs_mul,abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
lemma congr (hp : Gear G L a p) (h : q=ᶠ[atTop] p) : Gear G L a q := hp.compare (by filter_upwards [h] with x hx; rw [hx])
lemma rate (hp : Gear G L a p) : Rate G L a p :=by
  have hv:= (show Reserve G L _ from hp).rate.mul (Rate.power (a:=a)); rw [zero_add] at hv
  apply hv.congr; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]; change _= (Z x ^ a)⁻¹*p x* _; field_simp
lemma ascend (hp : Rate G L a p) (h : a<b) : Gear G L b p :=by
  have hv := (Rate.power (a:=-b)).mul hp; have ht := hv.below (by linarith) 1 zero_lt_one
  exact (Reserve.const (1:ℝ)).compare (ht.mono fun x hx=>hx.trans (le_abs_self _))
lemma weaken (hp : Gear G L a p) (h : a≤b) : Gear G L b p :=by
  rcases h.eq_or_lt with hx|hx; · exact hx ▸ hp
  exact ascend hp.rate hx
lemma absG (hp : Gear G L a p) : Gear G L a (fun x=>|p x|) := hp.compare (Eventually.of_forall fun x=> (abs_abs (p x)).le)
lemma zero : Gear G L 0 p ↔ Reserve G L p := by simp only [Gear,neg_zero,Real.rpow_zero,one_mul]
lemma mul (hp : Gear G L a p) (hq : Gear G L b q) : Gear G L (a+b) fun x=> p x*q x:= by
  apply ((show Reserve G L _ from hp).mul hq).compare
  filter_upwards [Delay.shift_pos G L] with x hx; apply le_of_eq; rw [neg_add,Real.rpow_add hx]; apply congrArg; ring
lemma pow (hp : Gear G L a p) (n : ℕ) : Gear G L (a*n) fun x=> p x ^ n:=by
  induction n with
  | zero => simp only [Nat.cast_zero,mul_zero,pow_zero,Gear.zero]; exact Reserve.const _
  | succ n ih => simpa only [Nat.cast_succ,mul_add,mul_one,pow_succ] using! (ih.mul hp)
lemma mul_left (hp : Gear G L a p) (c : ℝ) : Gear G L a (fun x=> c*p x) :=by
  simpa only [zero_add] using! ((Gear.zero.mpr (Reserve.const c)).mul hp)
lemma mul_right (hp : Gear G L a p) (c : ℝ) : Gear G L a (fun x=> p x*c) :=by
  simpa only [add_zero] using! (hp.mul (Gear.zero.mpr (Reserve.const c)))
lemma power : Gear G L a (fun x=> Z x ^ a) :=by
  apply (Reserve.const (1:ℝ)).compare
  filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le,inv_mul_cancel₀ (Real.rpow_pos_of_pos hx _).ne']
lemma flame : Gear G L (-(1/2)) (fun x=> Pressure.fiery G x L):=by
  have he:= (power (a:=-(1/2))).mul (Gear.zero.mpr (Reserve.monitoring (G:=G) (L:=L))); rw [add_zero] at he
  apply he.congr; filter_upwards [Delay.shift_pos G L] with x hx
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]; rfl
lemma inverse : Gear G L (1/2) (fun x=>(Pressure.fiery G x L)⁻¹) :=by
  refine Gear.power.compare ?_
  filter_upwards [Delay.shift_pos G L] with s hs
  let A:= Real.sqrt (betaF G s L); have hh:0<A:=Real.sqrt_pos.mpr hs
  have h: A⁻¹ ≤ Pressure.fiery G s L:=le_mul_of_one_le_right (inv_pos.mpr hh).le (Real.one_le_exp (sq_nonneg _))
  rw [← Real.sqrt_eq_rpow,abs_of_pos (inv_pos.mpr ((inv_pos.mpr hh).trans_le h)),abs_of_pos hh]; exact (inv_anti₀ (inv_pos.mpr hh) h).trans_eq (inv_inv _)
lemma add (hp : Gear G L a p) (hq : Gear G L a q) : Gear G L a fun x=> p x+q x:=by
  apply ((show Reserve G L _ from hp).add (show Reserve G L _ from hq)).compare
  filter_upwards with x; rw [mul_add]
end Gear
namespace Reserve
lemma field : Reserve G L (fun x=> (radiusB x:ℝ)):= covers Bolt.size
open Animals
lemma ball (f:ℝ→ℕ) (h : Reserve G L (fun x=> (f x:ℝ))) : Reserve G L (fun s=> (ballCost (f s):ℝ)):=by
  unfold ballCost; push_cast
  exact ((h.add h).add (Reserve.const _)).pow _
lemma tillP : Reserve G L (fun s=> (till s:ℝ)):= field.compare (by filter_upwards with x; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast Nat.div_le_self _ _)
lemma lag (i j:ℕ) : Reserve G L (fun s=>(↑(i*radiusB s+j):ℝ)) := by push_cast; exact ((Reserve.const _).mul Reserve.field).add (Reserve.const _)
end Reserve
end YM.RemainderComparison
