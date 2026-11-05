import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Cells.Tiling
import YM.Complex.Gaps
import YM.Shoot.Criteria
import YM.Source.Construction
/-!
# Carry the *whole* marked polynomial in the physical kernels

It uses the very same StepData (same linking, gauge image,
physical choices) and acts on the *actual* unnormalized densities.

One
new sequence of inverse couplings (finite here), not different between
components or different markers.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open MeasureTheory Lattice Wilson RG 
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)

/-- Restarted at level k (image from steps ABOVE k unchanged).
All choice probabilities etc still exactly from C. The positivity field
on the active range is included for applications rather than to obtain the
mere kernel mass identity. It is indexed by the level m, not weak stride
k-m. Even on step k→k-1 the old inverse coupling is used (for this
choice of restart). -/
structure Wire (r k N p : ℕ) where
  cost : ℕ → ℝ
  chosen (m : ℕ) (hm : k ≤ m) (ht : m ≤ N) : cost m=C.path.β N p m
  pays (m : ℕ) : r ≤ m → m ≤ N → 0 < cost m

namespace Wire
variable {r k p N : ℕ}
variable {C} (B : Wire C r k N p)

section Any
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact transport from cutoff N to m ≤ N. -/
def push (F : Config G (C.side N p) → V) (m : ℕ) (h : m ≤ N) : Config G (C.side m p) → V :=
    if e : m=N then fun U => F (cast (by rw [e]) U) else
    (C.path.levels.clock.op m p).push (B.cost (m+1)) (push F (m+1) (by omega))
termination_by N-m
decreasing_by omega

lemma own (F : Config G (C.side N p) → V) : B.push F N le_rfl=F := by rw [push,dif_pos (rfl : N=N)]; simp
lemma pushes (F : Config G (C.side N p) → V) (m : ℕ) (h : m < N) :
    B.push F m h.le=(C.path.levels.clock.op m p).push (B.cost (m+1)) (B.push F (m+1) h) := by
  rw [push,dif_neg h.ne]

lemma integrable (F : Config G (C.side N p) → V) (h : Integrable F (prior G _))
    (m : ℕ) (hm : m ≤ N) : Integrable (B.push F m hm) (prior G _) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [B.own]; exact h
  | of_succ i hi ih => rw [B.pushes _ _ hi]; exact StepData.push_integrable (C.path.levels.transition_mass ..) _ ih

lemma mass [CompleteSpace V] (F : Config G (C.side N p) → V) (h : Integrable F (prior G _))
    (m : ℕ) (hm : m ≤ N) : (∫ U,B.push F m hm U ∂prior G _) = ∫ U,F U ∂prior G _ := by
  induction hm using Nat.decreasingInduction with
  | self => rw [B.own]
  | of_succ i hi ih => rw [B.pushes _ _ hi,StepData.push_integral (C.path.levels.transition_mass ..) _ (B.integrable F h _ hi),ih]

lemma linear_image [CompleteSpace V] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (L : V →L[ℝ] W) (F : Config G (C.side N p) → V) (h : Integrable F (prior G _)) (m : ℕ) (hm : m ≤ N) (U) :
    B.push (fun Y => L (F Y)) m hm U=L (B.push F m hm U) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [B.own,B.own]
  | of_succ i hi ih =>
    rw [B.pushes _ _ hi,B.pushes _ _ hi]
    unfold StepData.push
    rw [← ContinuousLinearMap.integral_comp_comm _ (StepData.push_slice (C.path.levels.transition_mass ..) _ _ (B.integrable F h _ hi))]
    simp_rw [ih,map_smul]
end Any

/-- Same volume of unnormalized densities through this lens. -/
def vacuum (m : ℕ) (h : m ≤ N) : Config G (C.side m p) → ℝ := B.push (bare (C.beta N p)) m h

lemma vacuum_mass (m : ℕ) (h : m ≤ N) : (∫ U,B.vacuum m h U∂prior G _) = partition G (C.side N p) (C.beta N p) := B.mass _ (bare_integrable _) _ _
lemma vacuum_io (m : ℕ) (h : m ≤ N) : Integrable (B.vacuum m h) (prior G _) := B.integrable _ (bare_integrable _) _ _
lemma vacuum_pos (m : ℕ) (h : m ≤ N) (U : Config G (C.side m p)) : 0 ≤ B.vacuum m h U := by
  unfold vacuum
  induction h using Nat.decreasingInduction with
  | self => rw [B.own]; exact (bare_pos ..).le
  | of_succ i hi ih =>
    rw [B.pushes _ _ hi]; exact integral_nonneg fun _ => mul_nonneg (StepData.density_positive ..) (ih _)

lemma vacuum_agrees (h : C.Makes) {m} (hk : k ≤ m) (ht : m ≤ N) : B.vacuum m ht = (C.path.rep N p m).eval := by
  unfold vacuum
  induction ht using Nat.decreasingInduction with
  | self => rw [B.own,(h.wilson.starts ..).2]
  | of_succ i hi ih => rw [pushes B _ _ hi,B.chosen _ (by omega) hi,ih (by omega),(h.wilson.steps N p _ hi).1]

-- Conditional on one x (Fubini integrable), Haar change at fine level.
private lemma crossed (i : ℕ) (F : Config G (C.side (i+1) p) → ℝ) (h : GaugeInvariant F) (hi : Integrable F (prior G _)) :
    GaugeInvariant ((C.path.levels.clock.op i p).push (B.cost (i+1)) F) := by
  let A := C.path.levels.clock.op i p
  let c := B.cost (i+1)
  intro t U
  let T := t ∘ Function.invFun A.ratio.embed
  have hx : T ∘ A.ratio.embed=t := funext fun b => by simp only [Function.comp_apply,T,Function.leftInverse_invFun A.ratio.embed_injective b]
  have ht (V : Config G (C.side (i+1) p)) : A.density c (Lattice.gauge T V) (Lattice.gauge t U) = A.density c V U :=
    hx ▸ (C.path.levels.blocks i p).gauge c V U T
  let M := prior G (C.side (i+1) p)
  let Φ := fun V : Config G (C.side (i+1) p) => A.density c V (Lattice.gauge t U) • F V
  have hh : Integrable Φ M := StepData.push_slice (C.path.levels.transition_mass ..) _ _ hi
  have hp := prior_gauge T
  have hm : (∫ V, Φ (Lattice.gauge T V)∂M)=∫ V,Φ V ∂M := by
    have he := integral_map (μ:=M) (φ:=Lattice.gauge T) (f:=Φ) hp.aemeasurable
      (by change AEStronglyMeasurable Φ ((prior G _).map _); rw [hp.map_eq]; exact hh.aestronglyMeasurable)
    exact he.symm.trans (by dsimp only [M] at *; rw [hp.map_eq])
  apply hm.symm.trans
  apply integral_congr_ae
  filter_upwards with v
  unfold Φ; rw [ht v,h T v]
lemma vacuum_invariant (m : ℕ) (h : m ≤ N) : GaugeInvariant (B.vacuum m h) := by
  unfold vacuum; induction h using Nat.decreasingInduction with
  | self => rw [B.own]; exact fun t U => bare_gauge ..
  | of_succ i hi ih => rw [B.pushes _ _ hi]; exact crossed B _ _ ih (vacuum_io ..)
end Wire
end YM.Push.Corrected
