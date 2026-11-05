import YM.RemainderComparison.Solos.Stand
/-!
# Loyalty to test address markings
 Needed only for uniform integrability near equality F.B.Flags. For all other uses
 preserve the real rendered leaves. `weight` is before probe restriction.
 Honors support, gauges and flags. Don't require a cost summable over tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
variable (M:ι→Portrait R α) (y:α)
-- place : all tags of leaf (empty if dormant)
variable (M:ι→Portrait R (Audited R₀)) (place :ι→ Finset θ)(Hpc: ∀ (U:Config G f) i, LinearP (place i) (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
/-! # Joint loyalty in AP apertures
 Marker-test consistency and root costs survive polynomial alignments.
 Require stencils, not a smooth-tested representation after the estimate.
-/
open Mosaic.Verse Lacuna Lobby WickReps Lobby.Vesuvius Jolt Flues Progress.DirectedRecipe
open Funk Portal Cargo Trio Slide
open scoped BigOperators
variable (y:Audited R₀)(l:ι→ℝ)(Z:Set ι)(ε:ℝ)
variable {E₁ I :Type} (F:Manor G c ι (Audited R₀) I) (P':BudgetPoint)
local notation "Lt"=> mapWord place
-- Core bonds common.Support movement reports include actual XY α.Util; independent origin.A.LENS
open Pressure.Testing Push.Uniform Sienna Lapis Fare
variable (W' : Set I)
variable {roots:ι→Support c}{S' :Set I}
lemma stitch {α':Type*} {M:Manor G c ι α' I}{p:BudgetPoint}{i:I}(h:M.Sees p roots i) : M.total i →∀ V v a,M.wet p a i V=M.wet p a i v:=by
    intro hp V v a; unfold Manor.wet; rw [if_pos hp]; rw [if_pos hp]; exact (h.stall a hp V).trans (h.stall a hp v).symm
lemma migrant(h:Angel place P' F S')(hp:∀ i∈S',F.Sees P' roots i) : ∀ i∈S',∀ V, PaperP (mapWord place (F.marks i)) (fun a=> F.wet P' a i V):=by
   intro i hi V
   by_cases he: F.total i
   · have hv : Healthy P'.threshold (F.halls i) (1:Config G c):=by
         unfold Healthy; rw [Boulevard.smoky (P:=P') (show (1:Config G c) ∈ Boulevard.sunny P' from (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P'.threshold_pos))]; simp
     rw [show (fun a=> F.wet P' a i V)=(fun a=> F.wet P' a i 1) from funext fun v=> stitch (hp i hi) he _ _ _]
     simp_rw [Manor.onView _ _ hv]; exact (h.wink i hi 1 hv).self_of_nhds
   by_cases ht:Healthy P'.threshold (F.halls i) V
   · simp_rw [Manor.onView _ V ht]; exact (h.wink i hi V ht).self_of_nhds
   unfold Manor.wet; simp_rw [if_neg he,(fun a:Audited R₀=> RG.masked_ne _ _ (F.solvent a i) V ht)]; exact fun _=>LinearP.nil _

lemma garment_cont (o: Site c)(r w:ℕ) (h : 2*w≤ f.val): Continuous (garment h o r : Config G c→ Config G f):=by
    unfold garment Slide.shape; apply continuous_pi; intro i; split_ifs <;> fun_prop

variable {v q qsd r: ℝ}{cI:Type}
variable (O:Manor G c ι (Audited R₀) E₁)(K:Set E₁){fA:Side}{Y:Stars→Side}
local notation "M₀"=> Lobby.mural O F K
variable (C':∀ i:Stars,Pier (Y i) G W x μ L Q o C a χ (Audited R₀))(S':cI→ Pier fA G W x μ L Q o C a χ (Audited R₀))
variable (X:∀ i: Stars,(Y i).val=2*(n+i.val)) (hf:2*n≤ fA.val){m d' z r' k':ℕ}
variable (o':ι→Site c)(Pz:Breeze.Careers ι cI c o' r' k')(wP:ι→ ℝ)
variable {A:Set E₁} (T':Cargo Q O F K roots C' S' r') (hp:∃ I, Cargo.Striped Q O F K A W' roots C' S' T' I)(ht:Underscore Q O F K Z roots C' S' o' Pz T' wP P')
local notation "Q₁" => Manor.vessel (Lobby.mural O F K) T'.marker hf (songs Q T'.bCut) (sun o' Pz wP)
local notation "V↑" => Cargo.residual Q O F K X hf roots C' S' o' Pz T' wP z k
variable (hr : Rigging P' G c r' z k n m a v)
variable (hz:∀ i, ForceData (χ:=χ) P' (S' i) (mapWord place (Pz.pocket i).val))
variable (hh:∀ i,∃ (C₀ d v u B A' b r e:ℝ) (j n:ℕ), Nonempty (Captain (S' i).reader j C₀ d v u A' b r B e n χ)) (hv:P'.threshold=Pressure.temp x)
include hh hp hz hv hr ht
lemma isle : Angel place P' (Q₁ k) Set.univ :=by
    obtain ⟨I,hp⟩:= hp
    constructor; intro i hi U hL; let Y:= T'.marker
    let H:Config G fA:= garment hf (Y.etc i).site r' U
    have hS :∀ y∈ neighbors z (ploy (Y.etc i).site r'), y∈ (Q₁ k).halls i:= fun y hy=> reaches hr.safe _ ((by have h:=hr.sail; omega)) hr.span hy
    have hK: Healthy P'.threshold univ H:=by
        unfold Healthy H garment; rw [allFlag (Slide.cognac hf) (ploy (Y.etc i).site r') U _ (fun x=> hS _ ((neighbors_mem ..).2 ((Slide.village hf _ _).trans (by have h:=hr.sail;omega)))) _ P'.threshold_pos.le hL]; simp
    obtain ⟨q,d,v,u,B,A',b,r,e,j,n,⟨N⟩⟩:= hh i
    let ζ:=Y.sign i; have ht': ForceData (χ:=χ) P' (S' i) (mapWord place ζ):=by unfold ζ Y; rw [ht.vitality]; exact hz i
    have hf':= sings χ P' (S' i) (T'.bCut i) ht' ⟨_,hp.vu' i⟩ (ht.certified.calls i) hv N H hK -- arg order
    refine ((garment_cont _ _ _ hf).tendsto U|>.eventually hf').mono fun V he h=> ?_
    exact LinearP.pitch _ (he h)

variable (ho:Angel place P' O ((night O Z)ᶜ))(hb:Angel place P' F ((night F Z)ᶜ)) (hS:(Lobby.mural O F K).Templary Set.univ roots P' σ q)
variable [Countable cI]
omit hh hp hz hv hr ht
include ho hb
lemma mainstay : Angel place P' M₀ (night M₀ Z)ᶜ:=by
   constructor; intro i hi; rcases i with i|i; exact ho.wink i.val hi
   intro V h; refine (hb.wink i hi V h).mono fun x hx ht=>?_
   have he:=LinearP.pitch (-1) (hx ht); simp only [neg_one_mul] at he; exact he
-- hK caller from allLit subproof.P.Out mainStay cropping.CX.K.Test.Words.
include hh hp hz hv hr ht
omit [Countable cI] in
lemma azure : Angel place P' V↑ (night V↑ Z)ᶜ:=by
    constructor; rintro (i|i|i) hi
    · exact absurd (show Verse.load Z ((V↑).marks (.inl i))=0 from (by change load Z 0=0; simp [Verse.load])) hi
    · exact (isle χ place Z F P' W' O K C' S' hf o' Pz wP T' hp ht hr hz hh hv).wink i (Set.mem_univ _)
    exact (mainstay place Z F P' O K ho hb).wink i hi -- implicit hi
variable (hR:Manor.Spinal (Cargo.residual Q O F K X hf roots C' S' o' Pz T' wP z k) (night (Cargo.residual Q O F K X hf roots C' S' o' Pz T' wP z k) Z)ᶜ roots P' σ qsd)
include hS hR
omit [Countable cI] in
lemma windlet : Hearth place Z (Cargo.lamps Q O F K X hf roots C' S' o' Pz T' wP P' z k):=by
    constructor; rintro (i|i) hi
    · exact (hi (by change Verse.load Z 0=0; simp [Verse.load])).elim
    intro U; let Y:= (V↑); have hm i (h:i∈(night Y Z)ᶜ):=migrant place Y P' (azure χ place Z F P' W' O K C' S' X hf o' Pz wP T' hp ht hr hz hh hv ho hb) (fun i hi=> (hR.grants.choose_spec.2.1 i hi).1) i h U
    let F':= Q₁ k; let E:= T'.marker; have he : (fun a=>Y.wet P' a (.inr (.inl i)) U)=(fun a=> F'.wet P' a i U):= rfl
    have hx : PaperP (mapWord place (E.sign i)) (fun a=> F'.wet P' a i U):= he ▸ (hm (.inr (.inl i)) hi)
    intro h'; specialize hx h'; refine LinearP.wing ?_ hx
    apply LinearP.seats; intro j hj
    obtain ⟨_,hbL,hs⟩:= E.meets i j hj
    have hG : j∉ night M₀ Z:= fun h=> hi (by change load Z (E.sign i)=0; rw [←hs]; exact h)
    change (Lt (E.sign i)).Nodup at h' ; change LinearP (Lt (E.sign i)).toFinset _
    exact hs ▸ (migrant place M₀ P' (mainstay place Z F P' O K ho hb) (fun i hi=> (hS.grants.choose_spec.2.1 i (Set.mem_univ _)).1) j hG U (hs.symm ▸ h'))
end YM.RemainderComparison.Solos
