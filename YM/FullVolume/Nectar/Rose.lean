import YM.FullVolume.Nectar.Emits
import YM.FullVolume.Nectar.House
import YM.FullVolume.Nectar.Rites
import YM.FullVolume.Nectar.Celiac
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
set_option maxHeartbeats 400000
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
local notation "Ce"=> fire G Ls β
local notation "Δe"=> thaw G Ls β
local notation "db"=> ((A.B.a.budget m).supportExponent)
local notation "dc"=> (Q).supportExponent
local notation "B₀"=> A.B.a.budget m
local notation "S'" => A.B.a.clock.op m n
open Board MergeProof Marker JointLoad Heir Merge Mallow Luna Frets Empire Imago
variable (Θ:Tableau q 300)
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V] {W Z:Type} [SeminormedAddCommGroup W][NormedSpace ℝ W]
variable {B: Marker.Census V}
variable (g:G.Simple)
namespace Orchard
open Orchard
variable (U:Orchard N m n T B I W)(f:sun→Board (A:=A) N m n T) {Y:Mist A.B.a m (fire G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) (thaw G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))}
local notation "Fk"=> fun t:sun=> (f t).val.val
variable (hx: SectorOn (A:=A) (fun t:sun=> (f t).val.val) Y)
variable {w:V→ℝ}{u:V→ℝ}(hw:∀ i,0<w i){o:V→ Site (A.B.a.S.side (m+1) n)}{a:ℝ} (hP:U.Ensues w o a u)
variable {M:ℕ}(h:Rooms H Θ M a v d)(hX:Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ o) M) (ha:0≤ a)(r:W)(hr:‖r‖≤1)
include hx hw hP h hX ha hr
local notation "Fℓ"=>fun t:sun=> Jams.gate Fk Y t.val
local notation "V₀"=>pass_zero (F:=Fk) (Y.base.val) Y.base.property
local notation "Q₁"=> vacation H U f hx r
local notation "o'"=> (A.B.a.clock.op m n).ratio.parent ∘ o
local notation "F₀"=> fun t:sun=> (H.sight (Fℓ t))
local notation "B'"=> (U.qB w)
local notation "C'"=> U.vitality w
local notation "partE"=> fun t:sun=> Crew.facesT Q₁ t
local notation "Vh"=> Mallow.straw (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) Ls G β
local notation "w0"=> tempo Θ Ls
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "Φ" => fun s:sun=> PE H U w (f s) r
local notation "K'"=> fun s:sun=> PK H U w (f s) r
local notation "B_'"=> (A.B.a.budget m).B
open Marker Accent Switch
lemma marketE (t:sun)(y:Config G (A.B.a.S.side m n)):Summable (fun j:(H.sight (f t).val.val).fragrances=> Photo.headSheet (U.orbit (f t) r) (H.sight (f t).val.val) Chi.canonical (U.vitality w) B (U.qB w) j y):=
    (cashing H U f hx r t w).2 _ (Frets.echoE H h.hm hx h.hQ h.gears Q₁ (C') (minted H Θ U f hx hw hP h hX ha r hr) B' w hw (fun i=>Menu.paid (U.hat (f tip) r i) hw) t y)
include g
abbrev fleece (U: Orchard N m n T B I W)(t:Board (A:=A) N m n T)(s:W)(w:V→ℝ):= Photo.Fleece (Cryst.brands H t.val.val (U.orbit t s) (U.vitality w)) B (U.qB w)
lemma marketK (t:sun)(y:Config G (A.B.a.S.side m n)):Summable (fun j:ℕ=> fleece H U (f t) r w j y):=by
    have hk(i): fleece H U (f t) r w i=postK H hx Q₁ (C') B' t i:= (mining H U f hx r t w).2 i
    simp_rw [hk]; exact Frets.echoK H h.hm hx h.hQ h.gears g Q₁ (C') (minted H Θ U f hx hw hP h hX ha r hr) B' w hw (fun i=>Menu.paid (U.hat (f tip) r i) hw) t y
local notation "KX"=> Fintype.card V
variable {c b:W}
omit hr
include hX hP
local notation "a_"=>fun t:sun=> c+t.val • b
local notation "p_"=> sampleP (Fintype.card V)
local notation "T_"=>fun i t=>Nail.title (Fintype.card V) i t
variable (hv:∀ s:sun,‖c+s.val • b‖≤1) (x y:sun)
include hv
set_option maxHeartbeats 560000 in
omit g in
lemma spiceR : PE H U w (f x) (c + y.val • b)= ∑ i,(↑(Nail.title (Fintype.card V) i y):ℂ) • PE H U w (f x) (a_ (p_ i)):=by
    let Hx:= H.sight (f x|>.val.val); let fz t:= U.orbit (f x) (a_ t); let p i:= sampleP (Fintype.card V) i; funext k Vp
    let g(t:sun)(j:Hx.fragrances):= Photo.headSheet (fz t) Hx Chi.canonical (C') B (B') j Vp
    let Zt(t:sun)(j:Hx.fragrances):= Photo.tones (fz t) Hx Chi.canonical (C') j Vp
    let u(i):ℂ:=Nail.title (Fintype.card V) i y
    have hp(j):g y j=∑ i,u i • g (sampleP (Fintype.card V) i) j:=Bed.viewTag U.mode (U.dye w) (show FullVolume.Ray.Bed (fun i:I=> (U.mode i).val.card) (fun t=> Zt t j) from (Tier.markTones Hx hP.tape Vp (C') Chi.canonical j)) _
    have hs(t:sun):Summable (g t):=marketE H Θ U f hx hw hP h hX ha (a_ t) (hv t) x Vp
    let v:= fun t:sun=> PE H U w (f x) (a_ t)
    simp only [Finset.sum_apply, Pi.smul_apply]; let j:= {l:Hx.fragrances//Hx.bookFoot (.inr l)= k}; change (∑' i:j,g y i.val)=∑ i,u i • ∑' l:j,g (p i) l.val
    simp_rw [fun j=>hp j];rw [Summable.tsum_finsetSum];exact sum_congr rfl (fun i _=>( (Summable.tsum_const_smul _ ((hs (p i)).comp_injective (i:=Subtype.val (p:=fun j:Hx.fragrances=> Hx.bookFoot (.inr j)=k)) Subtype.val_injective))))
    intro i _; exact ((hs (p i)).comp_injective Subtype.val_injective).const_smul _
lemma spiceK : PK H U w (f x) (c + y.val • b)= ∑ i,(↑(Nail.title (Fintype.card V) i y):ℂ) • PK H U w (f x) (a_ (p_ i)) :=by
    let Hx:=f x|>.val.val; let p(i):= sampleP (Fintype.card V) i; let u(i):ℂ:= (Nail.title (Fintype.card V) i y); funext k Vp
    let D(t:sun)(i:ℕ):=fleece H U (f x) (a_ t) w i Vp; let Z₀:= barcode (H.moment Hx).activities
    have hp (j): D y j=∑ i,u i • D (p i) j:=Bed.viewTag U.mode (U.dye w) (FullVolume.Ray.Bed.billboard H Hx («P»:=fun y:sun=> U.orbit (f x) (a_ y)) hP.tape (C') j Vp) _ -- bad implicit
    have hs(t:sun): Summable (D t):= marketK H Θ g U f hx hw hP h hX ha _ (hv t) x Vp
    simp only [Finset.sum_apply, Pi.smul_apply]; let j:={l:ℕ// Z₀ l=k}; change (∑' i:j,D y i.val)=∑ i,u i • ∑' l:j,D (p i) l.val
    simp_rw [fun j=>hp j]; rw [Summable.tsum_finsetSum];exact sum_congr rfl (fun i _=> (Summable.tsum_const_smul _ ((hs (p i)).comp_injective (i:=Subtype.val (p:=fun j:ℕ=> Z₀ j=k)) Subtype.val_injective)))
    intro i _; exact ((hs (p i)).comp_injective Subtype.val_injective).const_smul _
end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil
