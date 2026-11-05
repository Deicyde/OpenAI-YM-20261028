import YM.FullVolume.Nectar.Funnel
import YM.FullVolume.Nectar.Oust
import YM.FullVolume.Nectar.Tea
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
open Luna.Aank Lotus
variable {B: Marker.Census V}
open UniformSpace
namespace ArmadaP
variable (x:Booker A N m n T){o:V→ Site (A.B.a.S.side (m+1) n)}(U:ArmadaP A N m n T x o B I)
local notation "aQ"=> A.B.a.budget (m+1)
local notation "G₁"=> Glacial I ℝ (Config G (A.B.a.S.side (m+1) n))
local notation "Yx"=> x.val.val.val
local notation "f_"=> fraz (A:=A) (m:=m) (n:=n)
local notation "K₁"=> U.inkLens x
local notation "mK"=> fun i=> (U.track i).support x.val.val.val
variable (C:I→ℝ)
open FullVolume.Amp FullVolume.Nectar FullVolume.Paint.Tower
variable (y:sun→ Booker A N m n T) (mK' : (s:sun) → I→Leaf (y s).val.val.val)
variable {v:ℝ}{b:I→ℝ}(hc:∀ i:I,0<C i) (hk:∀ s i,(mK' s i).turn=U.track i)
    (hX:∀ i,Feel (fun s=> (mK' s i).ingredient) (b i))(hv:∑ i,b i / C i ≤ v)
-- subtype completion public emitter. semantics fn at all real poses, no assuming uniform rotation audits. Any weights on real, not transporting auxiliary earnings. Owl flow for same ingredient use Tunes.
include hc hv hk hX
omit hc hv hk hX in
lemma lion (T:Submodule ℝ G₁) : ∃ e:Completion T →L[ℝ] (G₁), Isometry e ∧ ∀ x:T,e (↑x)=x.val:=by
    let E:=T; let g:= E.subtypeL; let t:=Completion.toComplL (𝕜:=ℝ) (E:=E); let e:= g.extend t; have hx:DenseRange t:= Completion.denseRange_coe; have ht:Isometry t:=Completion.coe_isometry; have h(u):e (t u)=g u:= g.extend_eq hx ht.isUniformInducing u
    refine ⟨e,AddMonoidHomClass.isometry_of_norm e ?_,h⟩
    apply isClosed_property hx (isClosed_eq (e.continuous.norm) continuous_norm); intro x; rw [h]; exact (Completion.norm_coe x).symm
lemma performs : ∃ p:sun→U.inkLens x, PaidBeam (fun i:sun=> ((p i:U.inkLens x): Completion (inkLens x U))) v ∧∀ s:sun,∀ i:I,(leafE x U C (y s) (p s) i).ingredient= (mK' s i).ingredient:=by
    let G2(t:sun)(i:I):= (C i)⁻¹ • (mK' t i).ingredient; have hh i: Feel (fun t=>G2 t i) (b i / C i):=by
       refine ((hX i).scales ((C i)⁻¹)).earns (le_of_eq ?_); rw [abs_of_pos (inv_pos.mpr (hc i)),mul_comm,div_eq_mul_inv]
    obtain ⟨u,hz,ht⟩:=Feel.arrays G2 hh
    have hm(i:I) (t:sun): (f_ (u t) i).val= G2 t i:= funext fun p=> hz i t p
    have hy(t:sun):u t∈ K₁:=by
       intro i
       let Vt:= (y t).val.val.val; let k:= U.track i
       let H := mK' t i; have he:H.turn=k:=hk t i
       have hb: H.crest=k.support Yx:=by unfold Leaf.crest;rw [he]; exact touched (y t) x k
       change UsesFinal _ _ _∧ (∀ p,_→ (f_ (u t) i).val _=0) ∧ GaugeInvariant _∧Measurable _
       rw [hm]; refine ⟨?_,fun U₀ hu=>?_,fun g p=>congr_arg ((C i)⁻¹*·) (H.glows g p), measurable_const.mul H.borel⟩
       · rw [← hb,x.val.val.property.1.point,← (y t).val.val.property.1.point]
         exact fun _ _ hz hp=>congr_arg ((C i)⁻¹*·) (H.scopedR _ _ hz hp)
       change (C i)⁻¹ * H.ingredient U₀=0; exact mul_eq_zero.mpr (Or.inr (of_not_not fun hh=> hu (((heart x (y t) k U₀).symm ▸ (show k.qualifies _ _ from he ▸ H.grant _ hh))))) -- parentheses
    let p(t:sun):inkLens x U:= ⟨u t,hy t⟩; refine ⟨p,?_,fun s i=>?_⟩
    · obtain ⟨f,hf,hK⟩:=lion (A:=A) (m:=m) (n:=n) (U.inkLens x)
      obtain ⟨V,hV,h'⟩:=(ht.larger hv).arrives
      obtain ⟨B',hB,H⟩:= Beam.slate V f hf (fun t:sun=> ⟨(p t: Completion (inkLens x U)),(hK (p t)).trans (h' t)⟩)
      refine ⟨B',hB.trans_le hV,fun i=> hf.injective ?_⟩; rw [H,hK]; exact h' i
    funext V
    have hS(p₁:ℝ)(x:ℝ)(h:p₁≠0): p₁*(p₁⁻¹*x)=x:=mul_inv_cancel_left₀ h _
    change C i * (f_ (u s) i).val _ = _;rw [hm]; exact hS _ _ (hc i).ne'
end ArmadaP
end YM.PhysicalNext.Repeat.Muse.Veil
