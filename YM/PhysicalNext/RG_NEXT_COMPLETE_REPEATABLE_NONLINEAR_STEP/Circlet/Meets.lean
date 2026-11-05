import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Levels

/-!
# Scratch legibility for linear V9 ONLY

Harness Pt2 as FORECAST tester even where Directed path's Tower prices too small for this bought matrix.No change to T.path hence record evaluation constant.

Preserve.ACTUAL flags, actual M.W.Health clocks.

Require certificate for BOTH threads.

No inference about E6 actual marginal from scratch.E6.

Not changing what's installed. 'Plays' Bulletin separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG RG.Supply Wilson Pressure Pressure.Tube Tree Next Next.Foundations Precision
open Push Push.PriceCompiler AnalyticBridge LocalGaussianLaws JointLoad JointLoad.Heir JointLoad.Heir.Suite
open Input Org Extra.Histories Planned.PrimaryIntegral295 WaterLevels Bloch Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{M: Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}(hQ:Capital M.p M.K Q) (B:Bolt A){i N p:ℕ}(h:i<N)
local notation "K"=> A.B.a
local notation "S"=> A.B.a.clock.op i p
local notation "f"=> A.B.a.clock.J (i+1)
local notation "t"=> A.B.a.clock.J i
local notation "U"=> Testing.ships A.B N i p
local notation "U'"=> WaterLevels.forecast B i N p
variable (hp : ∀ n s m : ℕ, m ≤ n → Bid.Sworn (A.B.M.H n m) (A.B.a.S.side m s) G)
include hQ h hp
set_option maxHeartbeats 500000 in
lemma boats : Lift.Booth (Q f t) S U ∧ Lift.Booth (Q f t) S U' := by
   let c:= A.B.kin.path; let J:=K; let F:= A.B.M.H; let g:= M.K
   let i':=t; let j':=f; let L:= J.S.block i
   let s:=M.p; have hh : Teller.Funds (Pressure.Testing.query s g j' i') S U:=Pressure.Testing.proceeds A.B N i p h
   have hj:= J.clock.adm (i+1); have hi:= J.clock.adm i
   obtain ⟨hk,hu,H⟩:= hQ.costs j' i' hj hi; obtain ⟨hT,hB,hJ,hK⟩:= hQ.setup.braids j' i'; let u:= Q j' i'; let v:=U; let w:=U'
   have hx := piper (p:=p) B hQ h
   have hF : Towers.Roll S (F N (i+1)) (F N i) w.R v.high v.low ∧ Towers.Diagonal S (F N (i+1)) (F N i) w.R ∧ Bid.Sworn (F N i) (A.B.a.S.side i p) G := Edens.laureates K A.B.M A.B.plan N i p h
   let U0:=(F N (i+1)); let V0:=F N i
   have hz (N n i:ℕ)(h:i≤N) : Attached (F N i) (c N i):= A.B.support.links N i h
   -- use funds pieces
   have he : v.R.Deep u.η u.C (u.j-2):=by
     change v.R.Deep u.η u.C ((Q _ _).j- _); rw [hJ]
     obtain ⟨h₁,h₂,h₃,h₄⟩:= hh.crosses; refine ⟨strip_mono h₁ hk hu,strip_mono h₂ hk hu,strip_mono h₃ hk (div_le_div_of_nonneg_right hu (by positivity)),fun l hl=>?_⟩; exact ⟨strip_mono (h₄ _ hl).1 hk (div_le_div_of_nonneg_right hu (by positivity)),strip_mono (h₄ _ hl).2 hk (div_le_div_of_nonneg_right hu (by positivity))⟩
   have h1:u.top=(Testing.query s g j' i').top:=hT; have h2:u.below=(Testing.query s g j' i').below:=hB
   have hxB:Teller.Funds u S v:= ⟨hh.knobs.trans hK,hJ.symm,hK ▸ s.has _,he,hh.low.trans (congr_arg RG.Stage.clip h2.symm),hh.high.trans (congr_arg RG.Stage.clip h1.symm),(by rw [h1,h2]; exact hh.feeds),hh.tilts⟩ -- may rw hK let
   have hyB : Teller.Funds u S w:= ⟨hxB.knobs,hxB.atStep,hxB.kernel, by change w.R.Deep _ _ ((Q _ _).j-2); rw [hJ]; exact hx.money,hxB.low,hxB.high,hxB.feeds,_,_,A.B.support.links N (i+1) h,A.B.support.links N i h.le, hF.1⟩
   exact ⟨⟨hxB,_,_,_,_,_,_, A.B.plan.all N (i+1) h _,A.B.plan.all N i h.le _,hz _ p _ h,hz _ p _ h.le,hp _ _ _ h,hp _ _ _ h.le,A.B.plan.crossings N i p h,A.B.plan.stack N i p h⟩,
     ⟨hyB, U0,V0,_,_,_,_, A.B.plan.all N (i+1) h _,A.B.plan.all N i h.le _,hz _ p _ h,hz _ p _ h.le,hp _ _ _ h,hp _ _ _ h.le,hF.2.1,hF.1⟩⟩

omit hp hQ
lemma venture : Seam U (wide M.K f t) (scale M.K f t) ∧ Seam U' (wide M.K f t) (scale M.K f t):=by
   have he:= seam_of p A.B.M A.B.kin.path A.B.plan h
   let C:=A.B.M.H
   have hp : (M.K).Ω t ≤ scale M.K f t ∧ M.K.Ω f ≤ scale M.K f t:= by unfold scale; constructor <;> grind [le_abs_self]
   have hv : Towers.Diagonal S (C N (i+1)) (C N i) (U').R:=Edens.laureates K A.B.M A.B.plan N i p h|>.2.1
   exact ⟨he,he.tCross,C N (i+1),C N i,hv,mul_eq_one_comm.mp (A.B.plan.all N (i+1) h _).diagonalInv,strip_mono (A.B.plan.rows N (i+1) h).2.2.2.2 (min_le_left ..) hp.2,strip_mono (A.B.plan.rows N i h.le).1 (min_le_right ..) hp.1⟩

omit h
-- Actual equality of V9 uses EVERYWHERE due to forecast's evidence-only A0. Museum stays same mapcase.
open Next.SectorChange Rows MeasureTheory Push.SectorMeasure Exterior
open AnalyticBridge.NonflatCovarianceLocality.Placement
variable {q:Type}[Fintype q][DecidableEq q] {F:Forest (A.B.a.clock.op i p).ratio} {X : Support (A.B.a.S.side (i+1) p)} {Y : Support (A.B.a.S.side i p)} {D0 : Stores (A.B.a.clock.op i p)}{x:ℝ}
lemma muse (Z:Museum F x D0 X Y q)(L k τ j l G' V): Z.hymn U L k τ j l G' V=Z.hymn U' L k τ j l G' V:=rfl
end YM.PhysicalNext.Repeat.Circlet
