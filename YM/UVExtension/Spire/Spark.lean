import YM.UVExtension.Spire.Orbs
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
open Cart

/-! # common construction output including Bolt.Nest at zero offset.
    Later payout still on the present choice. Distinguish family lookups for
    the many cutoff/p and disk origins; still same atlas. -/
structure Grove where
    witness : ℝ
    pledge : Crest R witness
    enabled : Paperwork R.shape witness Camp.soft A.delay
    peak : Planned.Port.AtTop A.B.kin
    rise N : Start.Allows A.B.a N
    climbed (N:ℕ) : Entry A.B.a N Camp.soft
    coins : Camp.Fees A.B.a

variable (D0:Grove R)
structure Uses where
    grove : Grove R
    fits (N n:ℕ): Fitted R hG grove.pledge grove.peak grove.rise N n
    cart (N n:ℕ): Cart A.B.a N (fits N n).Hut
    token (N n:ℕ) : (fits N n).Took (cart N n)
include D0
lemma utilize :Nonempty (Uses R hG) := by
   let H (N n : ℕ) := Classical.choice (fitted R hG D0.pledge D0.peak D0.rise N n)
   choose V hv using fun N n=> (H N n).zesty D0.enabled D0.climbed
   exact ⟨⟨D0,H,V,hv⟩⟩

namespace Uses
omit D0
variable {R hG} (S:Uses R hG)

def realBeat (b:ℝ) (N n : ℕ) := (S.fits N n).race ((S.fits N n).Rest (S.cart N n) S.grove.coins b) ((S.fits N n).Third (S.cart N n) S.grove.coins b) ((S.fits N n).Sail (S.cart N n) S.grove.coins b)

def Trial (N n:ℕ)(b β :ℝ) := ∃ f v s,(S.fits N n).Shot f v s ∧ v N=β∧ v 0=A.B.a.clock.bar+b

variable {b:ℝ}(hp': (b:ℂ)∈ Camp.Broad A.B.a) {β:ℝ}
include hp'
lemma terminates : Trial S N n b ((realBeat S b N n N).beta) := by
   let hx := S.fits N n|>.acts (S.cart N n) (S.token N n) S.grove.coins hp'
   exact ⟨_,_,_,hx.1,rfl,hx.2⟩
lemma only (hB : Trial S N n b β): β=(S.realBeat b N n N).beta:= by
    obtain ⟨f,w,s,hV,hY,h⟩:=hB
    let hx := S.fits N n|>.acts (S.cart N n) (S.token N n) S.grove.coins hp'; rw [← hY]
    exact ((S.fits N n).unions S.grove.enabled S.grove.climbed (S.cart N n) (S.token N n) hV hp' h S.grove.coins hx.1 hx.2 N le_rfl).2.1
lemma ticking : RG.Shoot.Competes A.B.bake n N 0 (S.realBeat b N n) := by
    let hx:= S.fits N n|>.acts (S.cart N n) (S.token N n) S.grove.coins hp'
    exact ((S.fits N n).round hx.1).1
lemma hits : (S.realBeat b N n 0).beta=A.B.a.clock.bar+b:= (S.fits N n|>.acts (S.cart N n) (S.token N n) S.grove.coins hp').2
lemma housing (i:ℕ)(hi:i<N): let b₀:= realBeat S b N n i; let b₁:= realBeat S b N n (i+1)
    A.B.Move N i n b₀ b₁ ∧ UVNext.CouplingReset.Accurate A.B R.post N i n b₀ b₁ ∧ PhysicalNext.Repeat.Graces.Protected R N i n b₀ b₁:= by
   exact (S.fits N n|>.serves (S.fits N n|>.acts (S.cart N n) (S.token N n) S.grove.coins hp'|>.1)) i hi
lemma slotReady : HasSlots (S.realBeat b N n N).p (S.realBeat b N n N).activities:= by
    exact ((S.fits N n).round (S.fits N n|>.acts (S.cart N n) (S.token N n) S.grove.coins hp'|>.1)).2

omit hp'

lemma centerP (T : Levels G) : ((0:ℝ):ℂ)∈Camp.Broad T:= mem_ball_self (flat_pos T)
lemma exists_bolt : ∃ Q: Bolt A,Q.history=S.realBeat 0 ∧ PhysicalNext.Repeat.Graces.Nest R Q:=by
   let V:= S.realBeat 0; let hZ (N n:ℕ):= S.ticking N n (centerP _); let he:= A.B.bake
   let X := he.make V
   have hQ (N n:ℕ) : X.β N n 0=A.B.a.clock.bar:= (S.hits N n (centerP _)).trans (add_zero _)
   have hstep N n i (hi:i<N): X.Transfer N n i:= ⟨((hZ N n).persists i (Nat.zero_le _) hi).link, ((hZ N n).persists i (Nat.zero_le _) hi).drift⟩
   have ht (N p m:ℕ)(hm:m≤N): Lives he N m p (V N p m):= ((hZ N p).prices m (Nat.zero_le _) hm).1
   let Q : Org.Bolt A:= ⟨R.worksNow hG, V,hZ, ⟨fun N n p m hm=> (ht _ _ _ hm).path.trans (ht _ _ _ hm|>.path.symm),fun N p i hi=> ⟨(ht _ _ _ hi).point,(ht _ _ _ hi).clip,(ht _ _ _ hi).valid,((hZ N p).prices _ (Nat.zero_le _) hi).2⟩,fun N p=>⟨(hZ N p).fromTop.scalars,(hZ N p).fromTop.raw⟩,hstep,hQ,RG.Shoot.trajectory X hQ hstep⟩, fun N m p hm=> (S.housing N p (centerP _) m hm).1⟩
   exact ⟨Q,rfl,fun N p=> S.slotReady N p (centerP _), fun N m p hm=> (S.housing N p (centerP _) m hm).2.symm⟩
end Uses
end YM.UVExtension.Spire
