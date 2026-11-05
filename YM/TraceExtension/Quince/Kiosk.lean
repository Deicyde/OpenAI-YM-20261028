import YM.TraceExtension.Quince.Gas
import YM.TraceExtension.Quince.Surrey
import YM.TraceExtension.Quince.Soil
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source Pressure
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Legato Malachite
open Mallow Lotus Planned.PrimaryIntegral295 PPX
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
variable {M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{C:ℕ→ℝ}{K:Bid.Worth}(b:Bandage X C K)(Z:Bolt A)
section thus
variable {m n d N:ℕ}
set_option quotPrecheck false
local notation "H"=> Issue.trail Z
local notation "J"=> A.B.a.clock.J
local notation "F"=> (Labels.frames G).level d
local notation "X'"=> D.L (J (m+1))
set_option quotPrecheck false
variable (h:Nest X Z)(hp:d+3 ≤ A.B.a.clock.J m) (ht:m<N)
local notation "x"=> A.B.a.clock.hatBeta m
include ht h hp
lemma mosaic (hG:G.Simple){u v y:ℝ}(hU:0<u)(he:Bunk G (M.p.profile (J m)) (M.p.profile (J (m+1))) d X' u v y)
    (I:Medal G (J (m+1)) (J m) d (M.p.profile (J m)).order X' (M.p.profile (J m)) (M.p.profile (J (m+1))) M.p.kernel (b.prices (J (m+1)) (J m)) (b.memberB (J (m+1)) (J m)) (X.target (J (m+1)) (J m)) (X.walls (J (m+1)) (J m)) (X.shape.o (J (m+1)) (J m)) (X.shape.μ (J (m+1)) (J m)) x y v (X.span (J (m+1)) (J m)))
   (hL:20*(Malachite.radiusD x+Heir.reach x+1)<(A.B.a.S.side m n).val):
   let E:=Warehouse.flight H N m
   let B' := A.B.a.budget
   ∃ (ht:4 ≤ A.B.a.clock.J m)(hp:d ≤ A.B.a.clock.J (m+1))(hx:Blend 2 (B' (m+1)).threshold (B' m).threshold),
       Surrey.Stepper (localSection G d) H N n m (hol G) (Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos ht (Next.Foundations.valuation G d) E hp hx) (C (J (m+1))) (sprite G x X' y) (Doors.rate X'):=by
   intro E B'; let T:=A.B.a; have hJ:=step_paid A.B.a m
   have hd':d ≤ J (m+1):=((Nat.le_add_right d 3).trans hp).trans hJ.1
   obtain ⟨l,s,Q,W,i,hQ,hP,hR⟩:= (h.held N m n ht).1; let x' : Set.Icc l s:= ⟨i,hQ⟩; have h' : (H).rep N n m=W.result x':=hR; have hh : (H).rep N n (m+1)=Q x':=hP
   have hz:=I.eve.scaleP _ _ (show (A.B.a.budget m).threshold=temp x from rfl) (Circlet.shifting (A:=A) (m:=m)).1
   have hΨ:Progress.DirectedRecipe.HasSlots ((Q x').p) (Q x').activities:= hh ▸ h.samples hG N (m+1) n ht
   have hq:(Q x').p=A.B.a.budget (m+1):=(W.knows _ x'.2).1.point
   have hσ : (H).S.block m=X':= Push.PriceCompiler.block_eq A.B.valid m
   have hb:=Graces.feet (A:=A) hp b.clock
   have hi:= T.clock.adm m; let k:=Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos hi (Next.Foundations.valuation G d) E hd' hz; refine ⟨hi,hd',hz,fun i hx=>?_,fun f r z hP hpf=> ?_,fun f i c hx _ hv=>?_⟩
   · have hQ : Push.Local.Readable (hol G) (localSection G d) (Q x').p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (J (m+1)))):= hq.symm ▸ (by
         rw[show Cub.title G (M.p.profile (J (m+1)))=authors T (m+1) from ?_]; exact lively b.clock hd' (n:=n)
         unfold title authors; rw [show T=A.B.a from rfl,params_eq A.B.valid (m+1)])
     dsimp only; rw [hh,hσ]; exact primaryT ht b.songs b.PStage b.wait hb h b.r W x' hQ hΨ hG h' hh hp b.shape b.clock b.stamp i hx I hi hd' hz (b.tunes _ _ d hb _ (D.large _).need|>.1) he
   ·
     rw [hh] at hP hpf ⊢
     exact salaryT ht b.songs b.PStage hb h b.r W x' hΨ hG h' hh hp b.clock b.stamp b.tunes b.furthering I r f hP z hpf he hU hL
   rw [hh] at hx ⊢
   exact gasT ht h b.r W x' hG h' hh hp b.clock b.stamp I i f hx c hv
end thus
end YM.PhysicalNext.Repeat.Quince
#print axioms YM.PhysicalNext.Repeat.Quince.mosaic
