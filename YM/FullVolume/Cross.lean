import YM.FullVolume.Forge

/-!
# First same-witness endpoint: uniform real coverage on admitted calendars,
strict interior on every successful trial, entire campaign on a common
connected bare interval per N,p with actual representatives on one dictionary
there, and the field-independent divergence for the SAME construction
supporting the field system and continuum. Intermediate purchases retained
for later UV bounds.
-/
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

/-- One campaign. Move/Competes and startup retained through Chosen's arc.
Also stamp that all future run-throughs may retain support all the way through
Phase selection. ζ/α clocks and constants bought before L etc at daggers.
Fields are on EXACTLY this campaign. -/
structure Run (G : Gauge) where
   metals : Metals G
   rolls : Rolls metals.p
   alloy : Alloy metals rolls
   kit : Factor alloy
   y : ℕ→ℝ
   w : Bid.Worth
   b : Bandage kit y w
   Q : ℕ→ℕ
   bought : Ahead b Q
   T : Bolt alloy
   tuning : FullVolume.Chosen kit T
   t : ℕ→ℕ
   accepts d : d+3 ≤ (Issue.trail T).levels.clock.J (t d)
   doors : ∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m)
   stories : ∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail T) N p
   makes : (Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t stories).Makes
   carries : ∀ N m p (hm:m<N), Climbs kit T N m p (doors N p m hm)
   books : ∀ d N p : ℕ, t d ≤ N → Freight T tuning.receipts N p d (stories d N p) (t d) w (doors N p)
namespace Run

variable (R : Run G)

def family : Family G := Family.mk (Issue.trail R.T) (hol G) (Labels.frames G) (localSection G) R.t R.stories

theorem ramp (h : G.Simple) (b : ℝ) (hp : 0<b) : ∃ R : Run G, R.family.path.levels.clock.kernel.penalty=b:=by
   obtain ⟨M,P,A,X,Y,K,bC,hK,h⟩:= dagger h hp
   obtain ⟨T,⟨Z⟩⟩:= rod (by assumption) X
   choose t ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   obtain ⟨D,S,hm,hc,hH,hF⟩:= squad (by assumption) bC T Z.receipts t ht
   exact ⟨⟨_,_,_,_,_,_,bC,_,h,T,Z,t,ht,D,S,hm,hH,hF⟩,hK⟩

/-- A client for the UV estimate may use these rank/equation probe
inputs, all on the very same purchased trajectory; not invoking noel again.
These distinguish W vs unrelated shots. -/
structure Ties : Prop where
   control : Extraction.Wcmain R.family
   tabs : Stock.Tabs R.alloy.B.a
   scrim : Scrim R.family R.w (far R.alloy.B.a) (waybill R.alloy.B.a) (near R.alloy.B.a) (renal R.alloy.B.a) (fly R.alloy.B.a) (mutt R.alloy.B.a R.Q) R.doors
   fridge : Fridge R.family (far R.alloy.B.a) (fly R.alloy.B.a)
   receipts : ∃ (V:∀ d, SectionData (R.family.labels.level d)) (W:Push.Mark.Weave G),∃ U e,(∀ d:ℕ,Push.Mark.Portfolio R.family.params (V d) (W d)) ∧ Hearthside R.family V W U e (fly R.alloy.B.a)
   detectors : ∀ S:Table R.family.book,∀ d, ∃ (X:Cells.Columns R.family S d) (Y:X.Trials), Market.Purchases Y

theorem again (h : G.Simple) : R.Ties ∧ ∀ f:Extraction.Order,∃ (g:Extraction.Order)(S:Table R.family.book), Nonempty (Spec.Final R.family (f.refine g) S):= by
   obtain ⟨hW,h,hC,hf,hS,hQ,H⟩:= ahead h R.bought R.tuning.receipts R.accepts R.makes R.carries R.books
   exact ⟨⟨hW,h,hC,hf,hS,hQ⟩,H⟩
end Run
open FullVolume

/-- Actual same-witness extension step. No implication about uniqueness or
limits of (properly normalized) couplings is made *here*. Selection does not
enter the calibration tasks; doesn't claim these preliminary witnesses vary
continuously with target b. -/
theorem realized (h:G.Simple) (w:ℝ) (hw:0<w) : ∃ (R : Run G), R.family.path.levels.clock.kernel.penalty=w ∧ R.Ties ∧
    (∀ f:Extraction.Order,∃ (g:Extraction.Order)(S:Table R.family.book), Nonempty (Spec.Final R.family (f.refine g) S)) ∧
    (∀ b∈nearby R.alloy.B.a,∀ N p:ℕ, let U:=R.tuning.arc p N; ∃ β∈Icc U.left U.right,
      Competes (still R.kit) p N 0 (U.replay β) ∧ (U.replay β 0).beta=b ∧ (U.replay β N).beta=β) ∧
    (∀ N p:ℕ, let U:=R.tuning.arc p N; R.family.path.rep N p=U.replay (R.tuning.beta p N)) ∧
    ∀ m p:ℕ, (∃ c : ℝ, 0<c ∧ ∀ N≥m,c≤ stripped R.family.path N p m) ∧ Tendsto (fun N => (R.family.path.rep N p m).v) atTop atBot:=by
   obtain ⟨R,hW⟩:= Run.ramp h w hw
   obtain ⟨H,h⟩:= Run.again R h
   refine ⟨R,hW,H,h,fun b hb N p=> ?_,fun N p=> (R.tuning.central p N).symm, fun m p=>⟨?_,?_⟩⟩
   · intro U; obtain ⟨β,hv,ht⟩:= U.covers hb
     exact ⟨β,hv,U.trials β hv,ht,U.top β hv⟩
   · exact FullVolume.saved (A:=R.family.path) R.makes.wilson m p
   exact FullVolume.field_independent R.makes.wilson (by assumption) m p
end YM.PhysicalNext.Repeat.Legato
