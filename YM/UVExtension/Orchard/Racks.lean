import YM.UVExtension.Orchard.Apple
import YM.UVExtension.Spire.Spark
/-!
 Actual points bearing book. here all Tours exactly stock. Even regulator dependent coordinates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Orchard
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Spire Dales Guild
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{R : Factor A}(S:Uses R hG)

local notation "T"=> A.B.a
set_option quotPrecheck false
abbrev Rose (S : Uses R hG):= {b:ℝ // (b:ℂ)∈Camp.Broad A.B.a} -- linter ok fix
abbrev rose0 : Rose S:= ⟨0,Uses.centerP _⟩
abbrev Keys (S : Uses R hG):= ℕ→ℕ→Rose S

def landsK (v: Keys S) (N n :ℕ):= S.realBeat (v N n).val N n

def ministry (v:Keys S) : Vintage.YM.Org.Bolt A:=by
   let V:= landsK S v -- replace
   let h (N p:ℕ):= S.ticking N p (v N p).property; let X := A.B.bake.make V
   have hT(N n i:ℕ)(hi:i≤N) : Lives A.B.bake N i n (V N n i):= ((h N n).prices i (Nat.zero_le _) hi).1
   have hx(N p m:ℕ)(hm:m≤N): X.Conv N p m:= ⟨(hT N p m hm).point,(hT N p m hm).clip,(hT _ _ _ hm).valid, ((h N p).prices _ (Nat.zero_le _) hm).2⟩
   have hp(N p i:ℕ)(hm:i<N): X.Transfer N p i:= ⟨((h N p).persists i (Nat.zero_le _) hm).link, ((h N p).persists i (Nat.zero_le _) hm).drift⟩
   exact ⟨R.worksNow hG,V,h,⟨fun N p q m hm=> (hT _ _ _ hm).path.trans (hT _ _ _ hm|>.path.symm),hx,fun N p=> ⟨(h N p).fromTop.scalars,(h N p).fromTop.raw⟩,hp,fun _ _=> trivial,traject X hx hp⟩, fun N m n hm=> (S.housing N n (v N n).property m hm).1⟩
lemma housed (v:Keys S): Vintage.YM.PhysicalNext.Repeat.Graces.Nest R (ministry S v):= ⟨fun N p=> S.slotReady N p (v N p).property, fun N m p hm=> (S.housing N p (v N p).property m hm).2.symm⟩

def Path (S : Uses R hG)(v:Keys S): History G:= Vintage.YM.Extra.Histories.Issue.trail (ministry S v)
lemma selected (v:Keys S) : Vintage.YM.RG.History.Selected (Orchard.Path S v) := (ministry S v).choice

def shrine (m:ℕ)(N p:ℕ)(h:m<N):= (S.fits N p).charts m h
section sector
variable (N n m:ℕ) (b:Rose S) (hm:m<N)
local notation "Z'"=> S.fits N n
local notation "P'"=> S.cart N n
local notation "τ"=> S.grove.coins
local notation "C₁"=> S.realBeat b.val N n (m+1)
local notation "C₀"=> S.realBeat b.val N n m
local notation "O"=> (Z').acts P' (S.token N n) τ b.2
local notation "Y!"=> (Z').charts m hm
local notation "ℓ"=> (Z').Sail P' τ b.val (m+1)
set_option quotPrecheck false
abbrev beam0 : Icc (0:ℝ) 1 := ⟨0,left_mem_Icc.mpr zero_le_one⟩
abbrev beam := Voyage R (shrine S m N n hm).atTopH (shrine S m N n hm).k (shrine S m N n hm).W 0 1 (fun _=> C₁) (fun _=> (Y!).oracle R _ ((O).1.alive _ hm) ℓ) -- parameter h.n
lemma filled : Nonempty (beam S N n m b hm):=by
    let U:=Y!; let t:=fun _:ℝ=>C₁; let z:= S.grove.pledge
    have hp:= (Z'|>.sample (O).1 (m+1) hm)
    have hv : (C₁).beta∈ band T (m+1):= ((O).1.alive _ hm).1
    have hc : Curve (A.B.a.budget (m+1)) t (Set.Icc 0 1) := by
       refine ⟨continuousOn_const,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,fun ε h x hx=>?_⟩
       filter_upwards with v
       exact ⟨fun _=>0,fun _=>0,fun j=>⟨le_refl _,fun _ _ _ _ _=> by simp [t]⟩, fun i=>⟨le_rfl,by simp [t]⟩,show SumBudget (fun i=> (T|>.budget (m+1)).mass ((C₁).activities.reg i).support 0) ε from (by simp [BudgetPoint.mass, SumBudget,h.le]),by simp [BudgetPoint.mass,SumBudget,h.le]⟩
    exact Guild.voyaging R hm hG z U.atTopH U.k U.W U.hr (l:=0) (t:=1) zero_le_one t _ hc (fun i hi=> ⟨hp,hv⟩)

def ray := (filled S N n m b hm).some
lemma ponds : C₀ = (ray S N n m b hm).body.result beam0:= ((O).1.passes m hm).trans ((ray S N n m b hm).pay beam0|>.symm)
end sector
open MergeProof
variable (v: Keys S)

def roof (N p m:ℕ)(hm:m<N) : GaugeDoor ((Orchard.Path S v).rep N p (m+1)) ((Orchard.Path S v).rep N p m) := duet _ _ _ _ (ponds S N p m (v N p) hm) rfl (sandboxK (ray S N p m (v N p) hm).body beam0)
lemma routes (N p m:ℕ)(hm:m<N) : Vintage.YM.PhysicalNext.Repeat.Legato.Bandage.Climbs R (ministry S v) N m p (roof S v N p m hm):=
    ⟨0,1,_,(ray S N p m (v N p) hm).body,beam0, ponds S N p m (v N p) hm, rfl, rfl⟩
end YM.UVExtension.Orchard
#print axioms YM.UVExtension.Orchard.roof
#print axioms YM.UVExtension.Orchard.routes
