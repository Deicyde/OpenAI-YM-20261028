import YM.FullVolume.Relay.Anchors
/- Analytic step proceeds for a Particular true chord. -/
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
variable {v q d t d' t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 460000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
local notation "Ls"=> D.L (A.B.a.clock.J (m+1))
local notation "Q!"=> R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "db"=> ((A.B.a.budget m).supportExponent)
local notation "dc"=> (Q).supportExponent
local notation "B₀"=> A.B.a.budget m
local notation "S'" => A.B.a.clock.op m n
open Board MergeProof Marker JointLoad Heir Merge Mallow Luna Frets Empire Imago
variable (Θ:Tableau q 300)
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V]
variable {B: Marker.Census V}
variable (g:G.Simple)
namespace Ship
open FullVolume.Amp FullVolume.Nectar FullVolume.Paint Tower
variable (p:Booker A N m n T) (o:V→ Site (A.B.a.S.side (m+1) n))
variable (w:V→ℝ)(f:sun→Booker A N m n T)(M: Ship p f o B I)
structure Barge (H:Chord R N m n t t) (f:sun→ Booker A N m n T) : Prop where
    pathV : ∀ i:sun,Orchard.Visit H (f i).val.val
    itinerary : ∃ (y:sun→ℝ × Nilot T)(X':FullVolume.Amp.Beam (ℝ × Guild T)),
       (∀ s:sun, mild (A.B.a.clock.hatBeta (m+1)) (y s).1)∧‖(y tip).2‖≤1/8∧(∀ s:sun, ReadsF (f s).val (y s))∧ ‖X'‖≤1/8∧∀ t:sun,Guild.groupB T (y t)=Guild.groupB T (y tip)+FullVolume.Amp.Beam.read _ t X'
-- numerical stage payments. Exclude climate from receipt if inherited around.R.Pers. Ship price paid for **one** occupant.If root Cap.N needed change argument.
structure Fund (H:Chord R N m n t t)(Θ:Tableau q 300)(a u v d:ℝ): Prop where
    rooms : Rooms H Θ 1 a v d
    foldE : u+Real.exp u*u≤ a
    positive : 0<u
    issued : Palette.shipPrice (D.L (A.B.a.clock.J (m+1))) (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) 1 a
    early : Climate (A.B.a.clock.hatBeta (m+1))
    song : choir q
variable (hT:Barge H f)(hw : ∀ i,0<w i) {M':ℕ} {a a' v₀:ℝ}(hp:Fund H Θ a a' v d)
variable (hu : Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ o) 1)
open Orchard ArmadaP
local notation "μ_"=> Mallow.straw (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) Ls G β
local notation "b_" => billboardC (Fintype.card V) (q/2)
local notation "tK"=> timeK H f
-- price definitions exposed with only post-L data.
abbrev singleBillE (q:ℝ)(Φ:Tableau q 300)(k:ℕ)(L:Side)(w:ℝ):= 4*(billboardC k (q/2)*(tempo Φ L*w))
abbrev singleBillK (q:ℝ)(k:ℕ)(fAllowance:ℝ)(w:ℝ):=4*(billboardC k (q/2)*(Real.sqrt fAllowance*w))
abbrev groupBillE (G:Gauge)(q:ℝ) (k:ℕ)(L:Side)(hat:ℝ):= 4*(billboardC k (q/2)*(k*(2*pottery G L hat)))
abbrev groupBillK (G:Gauge)(q:ℝ) (k:ℕ)(L:Side)(hat α:ℝ):=4*(billboardC k (q/2)*(k*Mallow.straw α L G hat))
variable (u u': V→ℝ) (ν:sun→V→ℂ)
local notation "sE"=> fun x=>singleBillE q Θ (Fintype.card V) Ls (u x)
local notation "sK"=> fun x=>singleBillK q (Fintype.card V) (A.B.a.clock.forcedAllowance m) (u x)
local notation "tE"=> groupBillE G q (Fintype.card V) Ls β
local notation "sL"=> groupBillK G q (Fintype.card V) Ls β (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m))
variable (F:sun→ Config G (A.B.a.S.side (m+1) n)→ Poly B)
local notation "r_" => (A.B.a.clock.op m n).ratio
local notation "o'"=> (A.B.a.clock.op m n).ratio.parent ∘ o
abbrev parent : V→ Site (A.B.a.S.side m n):= o'
abbrev remit (F:sun→ Config G (A.B.a.S.side (m+1) n)→Poly B) (v:sun):=(A.B.a.clock.op m n).push ((f v).val.val.val.beta) (F v)
local notation "Fx"=> remit f F
open MergeProof.Accent
include hw hu hT hp g
lemma extraction (h:∀ s:sun,F s= Orchard.story (f s).val.val.val (ν s) (M.stamp p f o s)) (hv:FoldT p M.arm w a' u (1/8) M.fare)(hf:∀ i,0<u i):
     ∃ E K, Proceeds (timeK H f) o' w E K ν (A.B.a.budget m) (remit f F) tE sL (fun i:V=>sE i) (fun i:V=>sK i)∧∀ i s x u,(K i s u).part (B.fire x)= M.oweK H p f o i x s u:=by
    obtain ⟨y,X,hy,hx,hP,hY,hZ⟩:=hT.itinerary
    have he i:M.arm.charge i≠0:=norm_pos_iff.mp ((M.unitC i).symm ▸ zero_lt_one)
    obtain ⟨E,K,hK⟩:= ArmadaP.program H Θ g p o M.arm w f M.crew y hy hx hP X hY hZ M.shares M.earns hw hp.rooms hu hp.foldE hp.positive hf he hv hT.pathV hp.issued hp.early hp.song ν (lively B)
    have hxE:= curvatureH hw (fun i=> (hK.seen i).1) hK.rollsE (fun i j=> (hK.realE i j).toBorne) (fun i h=> (lively_ne _).1 h)
    have hxK:= curvatureH hw (fun i=> (hK.seen i).2.1) hK.rollsK (fun i j=> (hK.realK i j).toBorne) (fun i h=> (lively_ne _).1 h)
    have hg : Pact w id E (lively B) (B₀).B (db+2) (tE):=⟨hxE⟩ -- check literal shape `exists` wrapping
    have hX(i): (A.B.a.clock.op m n).push (f i).val.val.val.beta (F i)=oven ((tK) i) (ν i) (E i) (K i):=by rw [h i]; exact hK.laws i
    have hR: Refresh (tK) o' E K (FullVolume.Nectar.spectrum E ν) (p:= A.B.a.budget m):=by
       refine ⟨hK.realE,hK.realK,fun s U=>?_,hK.quiet,fun s x j hj=>?_⟩
       · unfold FullVolume.Nectar.spectrum;rw [Poly.part_plus,Poly.part_sum,mute,zero_add]; exact sum_eq_zero (fun j _=> (hK.realE s j).sil U)
       unfold FullVolume.Nectar.spectrum;rw [Poly.part_plus, hush _ j hj,zero_add]
    refine ⟨E,K,⟨hR, hX,(hg.lower hw (p:=db+2) (q:=db) (by linarith)).subtype hw multiple_lively, ⟨hxK⟩,fun i=>?_,fun i=>?_⟩,fun i s x U=> hK.owe i s U x⟩
    · exact Treasure.mk (balanceH (fun s=> ((hK.seen s).2.2 i).1) (hK.tracksE i))
    exact Treasure.mk (balanceH (fun s=> ((hK.seen s).2.2 i).2) (hK.tracksK i))
-- multiple combined call. Token budget passed as v(j): lanes singular `Sen*paySlot`. u for extra output allocation (FoldT). power rates down refresh.
variable {x:ℝ}
variable (α:sun→V→ Config G (A.B.a.S.side (m+1) n)→ℂ)(κ:sun→ V→ Res G (A.B.a.S.side (m+1) n))
variable (he : ∀ j, 0< u j)(hF:((∑ i:V,w i*u' i)+4*v₀) /a'+ (∑ i:V,(u' i)/(u i)) ≤ 1/8)
include he hF
local notation "e_"=> dc-4
lemma many {I:V→Type}[∀ i,Fintype (I i)] (L: ∀ i:V,Ship p f o B (I i)) (hO:∀ i, Token p f o (L i) (fun s=> α s i) (fun s=> κ s i) (fun s=> ν s i) i (u' i)) (hC:Attic B (fun s:sun=> (f s).val.val.val) (A.B.a.budget (m+1)) o w F α κ x v₀) (hr:(A.B.a.budget (m+1)).supportExponent-4≤ x) : ∃ E K,Proceeds (timeK H f) o' w E K ν (A.B.a.budget m) (remit f F) tE sL (sE) (sK)∧∀ i s x u,(K i s u).part (B.fire x)= (L x).oweK H p f o i x s u:=by
    obtain ⟨J,hJ,M,hM,hP,hx'⟩:= Ship.combine H p f o w hw ν u' F α κ L hO a' u hp.positive he hr hC hF
    obtain ⟨E,K,hK,hA⟩:= extraction H Θ g p o w f M hT hw hp hu u ν F hP hM he
    exact ⟨E,K,hK,fun s i x U=> (hA s i x U).trans (congr_fun (congr_fun (hx' s x) i) U)⟩
end Ship
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.many
