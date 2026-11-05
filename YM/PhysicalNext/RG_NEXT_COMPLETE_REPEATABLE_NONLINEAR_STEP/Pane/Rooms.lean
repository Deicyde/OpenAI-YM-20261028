import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Handover
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Purl

/-!
# Cash on **auxiliary torus**. For comparisons only, at W. Identity
 reconstruction always on physical period, using its actual forest.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler
open ConnectedActivityE6 Testing SectorMeasure RG.Shoot
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} (A : Alloy X D) {N m : ℕ} {c f : Side}
section P
variable {c f : Side} {S : StepData c f}
def virgin (T : Tube G S) (B : BudgetPoint) (β : ℝ) : RG.Rep G f := ⟨T.up,T.high,pale f G,B,β,0⟩
lemma sparkling (T : Tube G S) (B : BudgetPoint) (β : ℝ) (V : Config G f) : (virgin T B β).eval V= if flags B.threshold V=∅ then Real.exp (-(β*mainTerm T.high T.up V+Precision.loop T.up V)) else 0 := by
  obtain ⟨h,h'⟩:= pale_value B V; unfold Rep.eval Rep.exponent virgin; dsimp only; rw [h,h',zero_mul,zero_sub, sub_zero]; split
  · rw [crystalline _ _ _ _ _ (by assumption),mul_one]
  rw [mul_zero]
end P
section income
local notation "sc" => A.B.a.S
abbrev panel (m : ℕ) (h : f.val=c.val*(A.B.a.S.block m).val) := again A.B.a m c f h
variable (N) (H : f.val=c.val*(A.B.a.S.block m).val)

def orchestra : Tube G (panel A m H) := ⟨A.B.M.towers N m,A.B.kin.path N (m+1), (A.B.a.params (m+1)).clip,A.B.kin.path N m,(A.B.a.params m).clip⟩ -- named h lowercase
abbrev asks (m : ℕ) := Testing.query X.p X.K (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)

lemma accepts (hm : m<N) (hx : 100*(1+radiusB (A.B.a.clock.hatBeta m))≤ c.val) : Works (asks A m) (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) (panel A m H) (orchestra A N H) := by
  have hh:=proceeds A.B N m 0 hm
  have hz:= panes A.B.plan hm c f H
  exact ⟨⟨hh.knobs,hh.atStep,hh.kernel,hh.crosses,hh.low,hh.high,hh.feeds,_,_,A.B.support.links N (m+1) hm,A.B.support.links N m hm.le, complete_roll A.B.plan hm c f H hz⟩,PriceCompiler.block_eq A.B.valid m,hx⟩

lemma ovation (hm : m<N) (h : ∀ N m n,m≤N → Sworn (A.B.M.H N m) n G) : SliceRows.Stamp (orchestra A N H) := by
  have hz:= panes A.B.plan hm c f H
  exact ⟨_,_,hz,complete_roll A.B.plan hm c f H hz,h N _ _ hm,h N _ _ hm.le,A.B.support.links N (m+1) hm,A.B.support.links N m hm.le,_,_,A.B.plan.all N _ hm _,_,_,A.B.plan.all _ _ hm.le _⟩

variable (hm : m<N) (hx : 100*(1+radiusB (A.B.a.clock.hatBeta m))≤ c.val) {β : ℝ}
include hm hx
lemma ingots (hb : β∈band A.B.a (m+1)) :
    Intake (asks A m) (orchestra A N H) (A.B.a.clock.hatBeta m) (virgin (orchestra A N H) (A.B.a.budget (m+1)) β) := by
  let B:=A.B.a; let t:=B.clock; let T:= orchestra A N H; let S := panel A m H; let x:=t.hatBeta m; let s:=B.params (m+1); let b:= B.budget (m+1)
  have he : betaF G x S.patch.L=t.hatBeta (m+1):= (Application.clock_next B m 0).symm
  have hS:=PriceCompiler.params_eq A.B.valid (m+1)
  have hg : t.loopCap (m+1) ≤ loopBill G S.patch.L x := by
    unfold Calendar.loopCap loopBill Delay.fineMonitor; rw [he]
    have he' := t.adm (m+1); have ht := B.fits.thetaRange (m+1)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [show Vac.Numbers.P (t.hatBeta (m+1)) = (t.monitor (m+1)) ^ (1:ℝ) by rw [Real.rpow_one]; rfl]
    exact Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) (ht.2.trans (inv_le_one_of_one_le₀ (by exact_mod_cast show 1 ≤ t.J (m+1) by omega)))
  have hL : T.up.Bounds T.high s.width s.paths (B.clock.loopCap (m+1)):= A.B.support.cap N (m+1) hm
  have hs : (asks A m).top=s:= hS.symm
  have ht:= whey f G b
  exact ⟨(accepts A N H hm hx).funds,⟨rfl,rfl,(show b.threshold=Pressure.temp (betaF G x S.patch.L) by rw [he]; rfl)⟩,
    ⟨(show T.up.Bounds T.high (asks A m).top.width (asks A m).top.paths _ from hs ▸ {hL with two:=budget_loosen hL.two hg}), {ht with boundE:= VerifiedReset.Time.E_rises ht.boundE (by unfold incomingE; positivity),boundK:= VerifiedReset.Time.K_rises ht.boundK (Real.exp_pos _).le}⟩,congr_arg RG.Stage.supportExponent hs, he ▸ B.fits.delayed (m+1), (show b.B=radiusB (betaF G x S.patch.L) by rw [he]; rfl), (show _ from he ▸ hb)⟩
variable {P : Targets X.p X.K} {Z : Expenses P} {v : Return.Wages} {u : ℕ→ℝ} (R : Register D Z v u) (T' : u ≤ A.delay.betaEntry)

include T'
lemma affords (h : ∀ N m n,m≤N → Sworn (A.B.M.H N m) n G) (hb : β∈band A.B.a (m+1)) : let x:=A.B.a.clock.hatBeta m; let T:= orchestra A N H
    let p := virgin T (A.B.a.budget (m+1)) β; let i:= A.B.a.clock.J m; let j:=A.B.a.clock.J (m+1); let k:=Z j i
    ∃ Y: Cash (v j i) x (R.μ j i) (D.L j) (P j i) (R.o j i) (R.c j i) T p,Cash.Renewed k.degrees k.earn k.one k.two Y := by
  intro x T p i j k
  exact ((R.consumes j i (PriceCompiler.step_paid A.B.a m)).2.2.2 x ((T' j).trans (A.B.valid.pays m))).2 _ _ _ T (accepts A N H hm hx)|>.2 (ovation A N H hm h) p (ingots A N H hm hx hb)
end income
end YM.PhysicalNext.Repeat.Pane
