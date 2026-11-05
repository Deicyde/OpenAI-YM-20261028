import YM.RemainderComparison.Placement.Input
/-! # Entry and texture of real and virtual stamped Rosette. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song
variable {G : Gauge} {f c: Side} {R:Rep G f}{P:Teller G} {q j:ℕ}
variable (R) (e:ℕ) (ι:Type) [Countable ι]
variable {α:Type*}{A:ℝ}
set_option quotPrecheck false
local notation "M"=> (Site f×ι)
abbrev numbers (f:Side): ℕ≃ℕ⊕ (Site f×ι):= Extra.Iteration.numbering _
local notation "g"=> Placement.numbers ι f -- verify order
local notation "p"=> R.p

def stub (u:M):= Tile.aperture u.1 e
def file := Dove.arcadia R (Placement.stub e ι) (Placement.numbers ι f)
local notation "R_"=> Placement.file R e ι -- warning notation
variable {ι}
def sign (u:M) := Dove.right (Placement.numbers ι f) u
lemma facts (u:M): (R_).activities.reg (Placement.sign u) = Tile.aperture u.1 e ∧ (R_).activities.E (Placement.sign u)=0:= Dove.plots R _ _ u
variable {U V D H W:ℝ}
omit [Countable ι] in
lemma position_covariance (s:Signed)(z:Site f)(j:Site f) : Tile.aperture (affine s z j) e= Song.line (Tile.aperture j e) (s,z):= (Ethereal.lineTest (b:=z) (s:=s) rfl (Turn.circle_wind s z j e)).symm -- i omit
-- Moves use same port groups; P registration row symmetry.
omit [Countable ι] in
def perm (ι:Type)(s:Signed)(z:Site f) : Equiv.Perm (Site f × ι):= Equiv.prodCongr (StepData.sendSites s z) (Equiv.refl _)
variable (ι)
lemma gains (h:R.Lawful U V D H W) : (Placement.file R e ι).Lawful U V D H W:=by
    exact Dove.binds R _ _ h (fun s z=> ⟨Placement.perm ι s z, fun u=> Placement.position_covariance e s z u.1⟩)
-- declaration in-clade Chartlet.R obtains textureAfford; does not prove issuance for ALG.AP.Post..
variable {Q:Teller G}{S:StepData c f}{T:Tube G S}
lemma attends (h:Intake Q T W R):Intake Q T W (Placement.file R e ι):=by
    refine ⟨h.ready, ?_, Placement.gains R _ _ h.cap,h.exponent,h.height,h.sizes,h.window⟩
    obtain ⟨hP,hR,hV⟩:=h.received; exact ⟨hP,hR,hV⟩
lemma evaluates : (R_).eval = R.eval:= (Dove.maths R _ _ 1).2
variable (s:Signed)(z:Site f)(π:R.activities.Moves s z)
def movement : (R_).activities.Moves s z:=
    Dove.portal R _ _ s z (Placement.perm ι s z) π (fun i=>Placement.position_covariance e s z i.1)
lemma shifted (X:M) : (Placement.movement R e ι s z π).ep (Placement.sign X)=Placement.sign ((Placement.perm ι s z) X):= Dove.epic ..
variable {ι e} (i:ι)

structure SignedIn (R:Rep G f)(D: Tile G α q e A)(w: Portrait (Placement.file R e ι) α) (x:Site f) (i:ι): Prop where
    appearance : w.wing=Wing.logKey (Placement.sign (x,i))
    inputs (a:α) : (w.angle a).ingredient= RG.masked R.p.threshold (neighbors e x) (Tile.read D x a)
    earnings : w.weight=Tile.peso G q e A R.p
variable (a:α) (X:ι→ Tile G α q e A)
variable (hp:0 < R.beta) (o:ι→Site f)
variable (M' :ι→ Portrait (Placement.file R e ι) α)
set_option quotPrecheck false
local notation "w" i:max=> Tile.script (X i) (o i) a
local notation "p'" => (R_).p
include hp a
lemma commissions : ∃ f:ι→ Portrait (R_) α, ∀ i,SignedIn R (X i) (f i) (o i) i:=by
    have h(i:ι):∃ f : Portrait (R_) α,SignedIn R (X i) f (o i) i:=by
      obtain ⟨Z,h₀,h₁,h₂⟩:= Sagas.Packet.ready (R:=R_) (w i) hp ((Placement.facts R e (o i,i)).1) ((Placement.facts R e (o i,i)).2)
      exact ⟨Z,h₀,fun x=>by rw [h₂]; change RG.masked _ _ ((w i).send R.beta x) =_; rw [Tile.delivers (hb:=hp)]; rfl,h₁.trans (Tile.enumerates _ _ _ p _ hp)⟩ -- arguments hp etc
    choose V G using h; exact ⟨V,G⟩
-- photoframe θ-independent call.Co.Mark symbols can vary geometry.Funding relies on giving one actual realization of α already.

def plants : ι→ Portrait (Placement.file R e ι) α:= Classical.choose (Placement.commissions R a X hp o)
lemma planted : ∀ i,SignedIn R (X i) ((Placement.plants R a X hp o) i) (o i) i:= Classical.choose_spec (Placement.commissions R a X hp o)
end YM.RemainderComparison.Placement
