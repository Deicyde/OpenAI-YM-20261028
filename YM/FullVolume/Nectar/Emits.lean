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
-- V.full input orientation anchors.W arms including Y. camera λ orbit const
lemma authorizedE : Ankh w (q/2) Φ (B_') id (db+2) (2*pottery G Ls β):=by -- syntax
     simp_rw [fun s=> (cashing H U f hx r s w).1]
     exact tall H h.hm hx h.hQ h.gears Q₁ (C') (minted H Θ U f hx hw hP h hX ha r hr) B' w hw (fun i=> Menu.paid (U.hat (f tip) r i) hw)
include g
lemma authorizedK : Ankh w (q/2) K' (B_') Prod.fst db Vh:=by
     simp_rw [fun s=> (mining H U f hx r s w).1]; exact canonK H h.hm hx h.hQ h.gears g Q₁ (C') (minted H Θ U f hx hw hP h hX ha r hr) B' w hw (fun i=>Menu.paid (U.hat (f tip) r i) hw)
private lemma labelsSX : ∀ i:I,∃ y:Site (A.B.a.S.side m n), y∈ (vacation H U f hx r i).pole.crest.image (S').ratio.parent:=by
    intro i; obtain ⟨y,h,hP⟩:= leaf_mem H U f hx r hw hP hr i; exact ⟨_,mem_image_of_mem _ hP⟩
omit g in
lemma singledE (x:V): RollsUp (A.B.a.budget m) id (fun t i y=>(Φ t i y).part (B.fire x)) (q/2) db (w0*u x):=by
   have hy :∀ i:I,∃ y:Site (A.B.a.S.side m n), y∈ (vacation H U f hx r i).pole.crest.image (S').ratio.parent:=by
      intro i; obtain ⟨y,h,hP⟩:= leaf_mem H U f hx r hw hP hr i; exact ⟨_,mem_image_of_mem _ hP⟩
   obtain ⟨a,ha,hℓ⟩:= (OutE H h.hm hx h.hQ h.gears h.hA Q₁ _ (minted H Θ U f hx hw hP h hX ha r hr) B' w hw (fun i=> Menu.paid (U.hat (f tip) r i) hw) (fun i=> (Menu.virtue (U.hat (f tip) r i) _).1) x Θ h.spire h.accepts h.fee hy h.rate).funds
   have hp :0 ≤ w0:=by unfold tempo; have hs:= Θ.sane; positivity
   simp_rw [(fun s=>(cashing H U f hx r s w).1)]; exact ⟨a,budget_loosen ha (mul_le_mul_of_nonneg_left (storage H U f hx r hw hP hr x) hp),hℓ⟩
lemma singledK (x: V): RollsUp (A.B.a.budget m) Prod.fst (fun t i y=>(K' t i y).part (B.fire x)) (q/2) db (κ *u x):=by
   obtain ⟨a,ha',hℓ⟩:= (OutK H h.hm hx h.hQ h.gears g h.hA Q₁ _ (minted H Θ U f hx hw hP h hX ha r hr) B' w hw (fun i=> Menu.paid (U.hat (f tip) r i) hw) (fun i=> (Menu.virtue (U.hat (f tip) r i) _).1) x Θ h.spire (labelsSX H Θ g U f hx hw hP h hX ha r hr)).funds
   simp_rw [(fun s=>(mining H U f hx r s w).1)];exact ⟨a,budget_loosen ha' (mul_le_mul_of_nonneg_left (storage H U f hx r hw hP hr x) (Real.sqrt_nonneg _)),hℓ⟩
end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil
