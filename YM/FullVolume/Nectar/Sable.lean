import YM.FullVolume.Nectar.OrbitA
import YM.FullVolume.Nectar.OrbitS
import YM.FullVolume.Nectar.Keys
import YM.FullVolume.Nectar.Bower
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 360000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V] {W Z:Type} [SeminormedAddCommGroup W][NormedSpace ℝ W]
open Luna Frets Empire Imago
local notation "𝒬" => Board (A:=A) N m n T
variable {B: Marker.Census V}
namespace Orchard
open Orchard
variable (Xk:Orchard N m n T B I W) (x: Board (A:=A) N m n T) (a:W)
open MergeProof.Menu MergeProof Extra.Trajectories Lotus
/- Use Xk.hat for base, heap.Co.Dir F. index through a fixed absent altar (one Board for type if not Empty). Weights chromatic. Homogeneous powers in mark fiber even collisions.In.Card rather than label count. -/
abbrev Castor (p:Board (A:=A) N m n T):= Menu.Mound (Xk.hat p (0:W))
variable (p: Board (A:=A) N m n T)
local notation "X₀"=> Xk.hat p 0
local notation "X'" => Xk.hat x a
local notation "ma"=> Xk.mode
lemma keyP (i:I): WKey (Xk.hat x a i)=Xk.turn i:=Xk.serial x a i
lemma logAlign : Menu.logDeck X'=Menu.logDeck X₀:=by
    ext i; rw [cams,cams]; simp_rw [keyP]
lemma plotLevel (v:Wing) : atKey X' v=atKey X₀ v:=by unfold Menu.atKey; simp_rw [keyP]
lemma slotOn (v:Wing)(s:Finset I) : harvestKind X' v s ↔ harvestKind X₀ v s:= by rw [Menu.harvestKind, Menu.harvestKind,plotLevel Xk x a p]; rfl
local notation "K" t:max => (Menu.Rock (Xk.hat t 0))
-- use explicit val.Pair projections
abbrev flex (k: ℕ):= Menu.Rock X₀ (.logKey k)
def leadT : ↥(logDeck X₀)≃ ↥(logDeck X') := Equiv.subtypeEquiv (Equiv.refl _) (by intro i; rw [logAlign Xk x a p]; rfl)
def hayE (v:Wing): Hay X₀ v≃ Hay X' v:= Equiv.subtypeEquiv (Equiv.refl _) (by intro i; exact (slotOn Xk x a p ..).symm)
def rockE (i: ℕ): Menu.Rock X₀ (.logKey i)≃Menu.Rock X' (.logKey i):=Equiv.subtypeEquiv (hayE Xk x a p _) (by intro i; rfl)
def jumpX : Castor Xk p ≃ Mound (X'):=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongr (leadT Xk x a p) (fun j=> rockE Xk x a p j.val)) -- name
local notation "V₀"=> Castor Xk p
local notation "q_"=> jumpX Xk x a p
lemma jumped (i:I): q_ (Sum.inl i)=Sum.inl i:=rfl
set_option quotPrecheck false
lemma jumping (k:logDeck (Xk.hat p (0:W)))(i:flex Xk p k.val): q_ (Sum.inr ⟨k,i⟩)=Sum.inr ⟨leadT Xk x a p k,rockE Xk x a p k.val i⟩:=by rfl
-- lifted Orchard fields with uniform.Mode.Shape.Paying price.
local notation "Zt"=> fun (x:Board (A:=A) N m n T) (y:W) (i:Castor Xk p)=> heap (Xk.hat x y) (jumpX Xk x y p i)
def toast (x:Board (A:=A) N m n T)(a:W)(i:Castor Xk p): Menu.Hat B x.val.val.val:= heap (Xk.hat x a) (jumpX Xk x a p i)
lemma pre (i:I): toast Xk p x a (.inl i)=Xk.hat x a i:=rfl
lemma post (j:logDeck (Xk.hat p (0:W)))(i:flex Xk p j.val) : toast Xk p x a (.inr ⟨j,i⟩)= Menu.rise X' (.logKey j.val) (Xk.hayE x a p _ i.val) := by unfold toast; rw [jumping]; rfl
lemma bill (i:Castor Xk p): let A:= toast Xk p x a i; let U:=toast Xk p p 0 i
    A.s=U.s ∧ A.M.turn=U.M.turn ∧ A.charge=U.charge:=by
    rcases i with k|⟨j,i⟩; intro v u; exact ⟨rfl,(Xk.serial x a k).trans (Xk.serial p 0 k).symm,rfl⟩; rw [Xk.post x a p, Xk.post p 0 p];exact ⟨rfl,rfl,rfl⟩
lemma promises (x':Board (A:=A) N m n T)(i:Castor Xk p): (toast Xk p x a i).M.ingredient=(toast Xk p x' a i).M.ingredient ∧ (toast Xk p x a i).M.weight=(toast Xk p x' a i).M.weight:=by
    rcases i with i|⟨j,i⟩; exact ⟨Xk.color x x' a i,Xk.height x x' a i⟩
    rw [Xk.post x a p,Xk.post x' a p]; let J:=i.val.val
    change (fun v=>∏ j∈J,(Xk.orbit x a j).ingredient v)=(fun v=>∏ j∈J,(Xk.orbit x' a j).ingredient v) ∧ ∏ j∈J,(Xk.orbit x a j).weight=∏ j∈J,(Xk.orbit x' a j).weight
    simp_rw [Xk.color x x' a, Xk.height x x' a]; trivial
local notation "λ!"=> Xk.hat
open Push.Local Merge
-- warehouse: output `M` fields. `Sector` inherits turn-split Budget. Ensure sum combin. with deg.phy and hy.T.Ch.Fum

def colony (p: Board (A:=A) N m n T) : Orchard N m n T B (Castor Xk p) W where
   turn i:= (Xk.toast p p 0 i).M.turn
   charge i:=(Xk.toast p p 0 i).charge
   va i:= (Xk.toast p p 0 i).shiny
   mode i:= (Xk.toast p p 0 i).s
   orbit x v i:= (Xk.toast p x v i).M
   serial x v i:= (Xk.bill x v p i).2.1
   color _ _ _ i:= (promises Xk ..).1
   height _ _ _ i:=(promises Xk ..).2
lemma keeps(i: Castor Xk p): (Xk.colony p|>.hat x a i)=toast Xk p x a i:=by unfold hat; rw [show (Xk.colony p).charge i=_ from (bill Xk x a p i|>.2.2).symm]; congr! 1; exact (bill Xk x a p i).1.symm -- ext
end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil
