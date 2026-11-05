import YM.RemainderComparison.Apo.Clock
import YM.RemainderComparison.Lobby.Doses
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Funk
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι δ : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Aux Mosaic Verse Muse Apo Marker Push.Uniform Lapis Sienna Fare Boulevard Herbal WickReps Lyric Typeface
open Trio Next.Rank.Glyph Next.Rank.Exponential
variable (Q:ConnectedActivityE6.Target G P) (Ω:KernelChoices)
-- one auxiliary star on a query µ.N.
structure Pier (c : Side) (G : Gauge) {P:Teller G}(W x μ:ℝ)(L:Side)(Q:ConnectedActivityE6.Target G P)(o:ConnectedActivityE6.Target.Order G W)(C:ℝ) (β:ℝ)(χ:Chi) (α:Type*) where
   τ : Type -- finite mark-index, uniform in ambient α
   [alphabet : Fintype τ]
   token : Type
   sealQ : Type
   bp : Side
   stepP : StepData c bp
   dataP : Tube G stepP
   modelF : Forest stepP.ratio
   earnest : stepP.Choices
   vital : Bid.Dir G c → AxisChart G modelF
   rep : Rep G bp
   coupling : rep.beta=β
   B : BudgetPoint
   reader : Cash W x μ L Q o C dataP rep
   pose : τ→ Portrait rep α
   starts : α
   goal : modes τ
   pay : τ→ℝ
   spill : Manor G c τ α token
   root : τ→Support c
   terrain : α→Eden bp G sealQ
   key : α→ τ → Eden bp G sealQ
   diary : α→Eden c G sealQ
   scalar : α→ℝ
   reads : Set (Sleet.Staff (brand pose starts) reader)
   owes : Set token

attribute [instance] Pier.alphabet
-- tariffs constructors.R.FIX. Keep same at ALL apertures. Dummy.Growth until later.
structure Platform where
   a : ℝ -- regular support exponent
   grade : ℕ -- maximum order internal label spaces occupancy and rocket
   view : ℕ -- angular order
   rise : ℕ -- power of coarse norm
   k : ℕ -- horizon of load
   s : ℕ -- power of high grades
   p : ℕ -- expansion order
   sharp : ℕ -- highest anchor occupation across Fine prices
   Delta : ℝ -- E long tariff inverse-width
   epsi : ℝ -- hat invocation for Muse
   Y : ℝ
   pV : ℝ
   R : ℝ
   sky : ℝ
   Ky : ℕ -- weather budget
   arm : ℕ -- Mentor lane order
   title : ℕ -- broad mark count
   hype : ℝ→ℝ -- weather V(D)
   wick : ℝ
   gap : ℝ
   sealV : ℝ→ℝ -- weather aperture tangent
   probe : ℝ→ℝ -- weather line.Canvas.D
   Z : ℝ -- input chart.C
   Auth : ℝ→ℝ -- Sect grants (AP)
   B : ℝ  
   chord : ℝ -- Model tail exponent
   cJet : ℝ -- tolerance p factor
structure Currency where
   Y : ℝ
   sky : ℝ→ℝ -- Airstrip
   hum : ℝ→ℝ
   view : ℝ→ℝ
   toll : ℝ→ℝ
   spin : ℝ
   e : ℝ -- older e companion from V crop
   t : ℝ

variable (Λ:Platform)(Ha:Currency) (P':BudgetPoint) (β:ℝ)
def crown (x:ℝ):=Apo.skyFare P'.order Λ.p Λ.title Λ.R (Ha.sky x) (Ha.view x) Λ.cJet Λ.sky
def wages' (x:ℝ):=(gStep β)^(Λ.p+1)*Funk.crown Λ Ha P' x
-- viability F.Power assembly uses same patch & x query explicitly. No Props changing tests
structure Treasury (P':BudgetPoint) (β x:ℝ):Prop where
    weather : Airstrip (G:=G) L Ω Λ.wick Λ.gap Λ.hype Λ.sealV Λ.probe Λ.Auth P'.order Λ.p Λ.arm Λ.Ky Λ.grade Λ.title Λ.Z Ha.sky Ha.hum Ha.view Ha.toll x
    high : Λ.p+1≤ Λ.s
    pose : P'.B=radiusB x
    pose2 : P'.threshold=Pressure.temp x
    pose3 : P'.order≤Λ.view
    pose4 : P'.power≤Λ.rise
    support : P'.supportExponent≤Λ.a
    mores : 1 ≤ Λ.R
    coup : gStep β ≤1
    ramp : Arc.Tracer P' G β Λ.R
    root : 0≤ Λ.chord
    port : Sleet.pigment Λ.chord x * Λ.B ≤ (gStep β)^(Λ.p+1)

namespace Pier
variable {P' β}(χ : Chi)
variable (V : Pier c G W x μ L Q o C β χ α)
abbrev staff := Sleet.Staff (brand V.pose V.starts) V.reader
def vane : Manor G c V.τ α V.staff := Creek.theater V.reader χ V.pose V.starts V.pay Set.univ 0
local notation "V₁"=> V.vane Q χ
-- edit params
variable (P':BudgetPoint)
def tiny (s:Finset (V.staff Q χ))(t:Finset V.token)(a:α) := Apo.offset V.reader χ V.pose V.starts a V.pay 0 V.spill V.goal (k':=V.earnest) V.vital V.scalar s t

-- RG03 constructs. Qualifications for aperture range.
structure Materia : Prop where
    scroll : Apo.Ascribes (Q:=Q) (T:=V.dataP) V.pose V.pay P' V.spill V.goal (k':=V.earnest) (Λ:=V.B) V.vital V.terrain V.key V.diary Λ.grade Λ.p Λ.Ky Λ.Z 
     (gStep V.rep.beta^(Λ.p+1)*Λ.cJet) Λ.R (Λ.Auth x) V.scalar
    census : Fintype.card V.τ≤ Λ.title ∧ V.goal.val.card≤Λ.k
    region : (Fintype.card (Site c):ℝ) ≤ Λ.sky
    modelPays : ∃ l: V.token→ℕ,Breeze.Sonorous P' V.spill l Set.univ V.root Λ.a Λ.chord Λ.B∧ ∀ i,i∉ V.owes→ Pressure.Stores.till x ≤ l i
    road : ∃ (r:ℝ) (n:ℕ) (F':Set ℕ) (wp:ℕ→ℝ)(Y':Set V.τ) (U:Type) (_:Fintype U) (X': U→ Site V.bp) (p: V.τ→Finset U),
          Lyric.Scale X' p (Typeface.brand V.pose V.starts) (Creek.rage Y' (Sleet.pigment Λ.Delta x) V.pay) Λ.sharp r Λ.Y V.stepP ∧ Lyric.Scale X' p (Typeface.brand V.pose V.starts) V.pay Λ.sharp r Λ.Y V.stepP ∧ radiusCost Q L r ∧
          Creek.Wand V.reader χ V.pose V.starts V.pay Set.univ 0 n Λ.k Λ.s ∅ F' Y' V.reads ∧ Halo.Presents V.rep F' wp (Sleet.pigment Λ.Delta x * Λ.pV)
-- common r for both scales as in financer. Derate later if needed.
-- include AUTH coefficient Power overhead. Stamp genuine.
structure Enrollment : Prop where
   inPan : ∀ y:Positions (Uniform.Primary c G), ‖y‖ ≤ Λ.R → Arc.route G V.rep.beta y∈ Boulevard.sunny P' →Weather V.dataP V.modelF Q.table V.earnest V.vital V.B V.rep.beta Λ.wick x Λ.gap (Λ.hype x) (Λ.sealV x) (Λ.probe x) Ω P Λ.Ky y L
   march : ∃ U:Pad V.reader Λ.view χ, Roles V.reader χ U Λ.k Λ.s Λ.rise Λ.sharp Λ.a Λ.Delta Λ.epsi Λ.Y Λ.pV Ha.Y Ha.spin Ha.e Ha.t

structure Cuts where
   A : Finset (Sleet.Staff (brand V.pose V.starts) V.reader)
   B : Finset V.token
variable {χ V P'}
def pays (V:Pier c G W x μ L Q o C β χ α) := V.reads ∩ Portal.ringSet (Typeface.brand V.pose V.starts) V.reader V.goal
structure Cuts.Above (S T: Pier.Cuts Q χ V) : Prop where
   validA : (T.A:Set (staff Q χ V))⊆ pays Q V
   sailsA : (S.A:Set (staff Q χ V))∩pays Q V ⊆ (T.A:Set (staff Q χ V))
   validB : (T.B:Set V.token)⊆V.owes
   sailsB : (S.B:Set V.token)∩ V.owes ⊆ (T.B:Set V.token)
structure Receipts (V:Pier c G W x μ L Q o C β χ α) (P':BudgetPoint) (T:Pier.Cuts Q χ V)(u b:ℝ) : Prop where
   heard (a:α) : P'.Regular univ (Pier.tiny Q χ V T.A T.B a)∧ Portal.Mare P' (Pier.tiny Q χ V T.A T.B a) β u b

lemma barns (h:Treasury (G:=G) (L:=L) Ω Λ Ha P' β x)(hf:Pier.Materia Q Λ χ V P')(hp: Enrollment Q Ω Λ Ha χ V P') :
     ∃ S: Pier.Cuts Q χ V,∀ T:Pier.Cuts Q χ V,Cuts.Above Q S T → Receipts Q V P' T Λ.R (Funk.wages' Λ Ha P' β x):=by
    obtain ⟨U,hU⟩:=hp.march
    obtain ⟨r,n,F',wp,Y',Ua,hu,X',pP,hX,hG,hh,hK,hV⟩:=hf.road
    obtain ⟨l,hq,hB⟩:= hf.modelPays
    have hh' : Motto (brand V.pose V.starts) (Creek.rage Y' (Sleet.pigment Λ.Delta x) V.pay) 0 V.reader r Λ.Y Ha.Y Λ.sharp:=⟨⟨Ua,hu,X',pP,hX⟩, hh, le_rfl,by simp,by simp⟩
    have ht : Motto (brand V.pose V.starts) V.pay 0 V.reader r Λ.Y Ha.Y Λ.sharp := ⟨⟨Ua,hu,X',pP,?_⟩, hh,le_rfl,by simp,by simp⟩
    -- derate proof trivial from crop Δ>0
    · obtain ⟨s,t,hy⟩:=Apo.gift V.reader χ U V.pose V.starts V.pay 0 hU ht P' V.spill V.root V.goal F' Y' V.owes V.reads V.vital Λ.grade Λ.p V.terrain V.key V.diary V.scalar h.weather hp.inPan hf.scroll hf.census.1 hf.census.2 h.high h.pose h.pose2 h.pose3 h.pose4 h.support (V.coupling.symm ▸ h.coup) h.mores le_rfl (V.coupling.symm ▸ h.ramp) hK wp hV hh' l Λ.chord h.root hq hB (by rw [V.coupling]; exact h.port) hf.region
      refine ⟨⟨s,t⟩,fun T hH=>⟨fun a=>?_⟩⟩
      obtain ht' := hy T.A T.B (by have hv:=hH.validA; unfold pays at hv; rwa [Set.inter_comm]) (by have hv:=hH.sailsA; nth_rw 2 [Set.inter_comm]; exact hv) hH.validB hH.sailsB
      have htP := ht'.aims a; dsimp only at htP; rw [V.coupling] at htP; exact htP
    -- proof derate? temporarily combine road.Cost
    exact hG
end Pier
end YM.RemainderComparison.Funk
