import YM.FullVolume.Gables.Pillar
import YM.FullVolume.Roll.Meridian
/-! Retrieve actual witnesses; layout for all mark stems. Ref t fixed pre calibration and ≥1: will allow reference motions auxiliary. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
namespace Campaign
set_option quotPrecheck false
/-- Strengthening. Brands retained under mark choices (same actual recipe heights). -/
structure Pillars (R:Run G) (T:Campaign R) where
   late (d:ℕ): 1 ≤ R.t d
   yields : ∀ N p, Branch R.kit R.T.history N p 0
   earnings : R.doors= Bandage.ease yields
   shares : ∀ N p m,∀ h:m<N,Boutique.Flavor T.L ((yields N p).steps m (Nat.zero_le _) h)
   ports : Bandage.Accounting R.b R.tuning.receipts R.t R.accepts yields R.stories
open Boutique
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. k>=1. later reserve may request hard-limit recipe. -/
lemma pillarY (h:G.Simple){q:ℕ→ℕ}(hh:Ahead b q){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T) ∧ R.family.path.levels=A.B.a :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hh,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩; exact ⟨R,T',⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl⟩
end
lemma vendee (h:G.Simple)(w:ℝ)(hw:0<w):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay∧ Nonempty (Pillars R T) ∧ R.family.path.levels.clock.kernel.penalty=w:=by
   obtain ⟨X,P,A,F,L,Q,b,hY,hC,hYs,hW,hH,ξ,v,t,a,D,Φ⟩ := factorGK h hw
   obtain ⟨R,T,hx,hp,hb,h⟩:= pillarY h hH Φ hY hC hYs; rw [← h] at hW; exact ⟨_,_,hx,hp,hb,hW⟩
variable {R:Run G} {T:Campaign R} (H:T.Winter)(h : Pillars R T)
open Matric
local notation "A"=> R.alloy
local notation "L"=> A.B.a
variable (he:Jams.Wild R.kit.shape R.alloy.delay)
local notation "D"=> R.T
set_option quotPrecheck false
local notation "W"=> Issue.trail R.T
local notation "F"=> R.family
include H he h
lemma shapes (p d m:ℕ)(hw:R.t d ≤ m)(y:(Labels.frames G|>.level d|>.Coeff)): let f(n:ℕ):=(R.stories d n p).entries m ((R.stories d n p).terminal.symm y); let Z:= attire R.T m p
     CauchySeq (fun n=> (f n).x) ∧ ∃ T:ℕ→ Matric.Coin ((Labels.frames G).level d) (hol G) Z,CauchySeq T ∧ ∀ n:ℕ,∀ hg:m≤ n,Coin.uses (T n)=capture (f n) (Guard.Keeper.sufficient ((h.yields n p).slots m (Nat.zero_le _) hg)):=by
    intro f Z
    let P n:= R.stories d n p; have hv n : ∀ (w:R.t d ≤ n), Branch.Piano R.b (h.yields n p) (fun i=> Boutique.brochure D i p R.tuning.receipts) (Nat.zero_le _) (R.accepts d) (P n) w:=fun w=> h.ports d n p w
    exact Branch.stays (Y:=R.T) (q:=fun _=> R.T.history) (f:=id) (p:=p) T.gains.SimpleR R.b R.tuning.receipts (fun i=> Boutique.brochure D i p R.tuning.receipts) (Nat.zero_le _) (R.accepts d) (fun n=> h.yields n p) (helmed T H p) he P hv (fun n hx=> R.makes.calibrated d n p hx) y m hw
end Campaign
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.vendee
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.shapes
