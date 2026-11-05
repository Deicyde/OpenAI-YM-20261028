import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Oper
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.MergeProof.North.Ariose
import YM.MergeProof.North.Menu
import YM.MergeProof.North.Wraith
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
import YM.SectorNext.RECONNECTED_LOCALITY.Tendril

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}{S:StepData c f}
variable {v:V}{P:V→Motion}{E:V→Site c}{B:V→Equiv.Perm V}
local notation "X"=> Aged V
variable {o:Name V→ Site f}{b:Name V→Site c}
    {L:Name V→ Config G f→ℂ}{K:Name V→ Res G f}{H:Name V→ Res G c}{a t:Bool→ℝ}{g:Name V→ℂ}
    {N:ℕ} {d e u x φ ψ c':ℝ}{w:Name V→ℝ}
    {Y: Config G f→Poly (Aged V)}
local notation "r"=> fun i=> S.ratio.embed (E i)
-- H,K raw ways. final exact operation. preserve on Mom. needed for any lower steps, split raw branch after exponent.
lemma Harps {m:Motion}{B:Equiv.Perm V}{p q:Poly (Aged V)}(h:Harm v B m p q): Harm v B m (octave p) (octave q):=by
   intro s hs; by_cases he: 2 ≤ s.val.card
   · rw [crest _ _ he,crest _ _ (show 2 ≤ (drum B s).val.card from (by rw [drum,pares, card_image_of_injective _ (nome B).injective];exact he))]; exact h s hs
   rw [starlet _ _ (Nat.lt_of_not_ge he),starlet _ _ (show (drum B s).val.card<2 from (by rw [drum,pares, card_image_of_injective _ (nome B).injective]; exact Nat.lt_of_not_ge he)),scalar_z]
-- After Blanket pliable maybe broad generalized.
structure Arc (R:Rep G f)(L:Name V→ Config G f→ℂ)(K:Name V→ℕ→ Config G f→ℂ)(Y:Config G f→ Poly (Aged V))(v:V)(P:V→Motion)(E:V→Site f)(B:V→Equiv.Perm V)(o:Name V→Site f)(w:Name V→ℝ)(d e t a b:ℝ)(pepper:Name V→ℂ): Prop where
    see : ∃ F Z, ∃ (ψ:Name V→ Response G f), Garnish R.p o ψ w e b∧ relates v P E ψ ∧ Towed w id F R.p.B d t ∧ Towed w Prod.fst Z R.p.B e a ∧ (∀ i,Burns o i (F i) R.p.threshold) ∧(∀ i,Flow o i (Z i) R.p.threshold)∧ Horn v P E B F Z ∧ (∀ i U,(Z i U).part (Aged V).quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)∧(∀ i j U,(Z i U).part ((Aged V).fire j)+hook R.activities R.p.threshold (ψ j) i U=profile R.activities (K j) i U)∧ Y= play R (Aged V) Z (fun U=> Mach (Aged V) pepper+∑ i,F i U)
variable {k:Name V→ℕ→ Config G c→ℂ}{L':Name V→ Config G c→ℂ}
    {Z':Config G c→Poly (Aged V)}{ζ Z ξ ν ρ:ℝ}
lemma thru (p:Arc A L' k Z' v P E B b w (u+ζ) e x φ c' g)(hA:A.activities.Valid A.p d ν)(hw:∀ i,0<w i)(hu:0 ≤ c')(hp:Occupancy b N)(ht:0 ≤ u+ζ)(hk:((A.p.B+A.p.B+1:ℕ):ℝ)^4*(φ+N*siteFactor A.p.B*c')≤e-(u+ζ))
    {w':Name V→ℝ}(hw':∀ i,0<w' i)(hB:Repegs b A.p.B w w' ζ Z (Aged V))(hz:0≤ Z)(he:Z*x ≤ ξ)(hh:Z*(Real.exp (φ+ N*siteFactor A.p.B*c')-1)≤ ξ)(hC:∀ i U,(Z' U).part ((Aged V).fire i)=coin A (L' i) (k i) U)(hy:∀ i,Dominated (k i))(hit:∀ U,A.eval U≠0): Serves A L' (fun i=>profile A.activities (k i)) Z' v P E B b w' u ξ:=by
    obtain ⟨F,K,ψ,ha,hr,hT,hW,hF,hH,ho,hI,hP,rfl⟩:=p.see
    let l U:= Mach (Aged V) g+∑ i,F i U; have hn:∀ U: Config G c,(l U).part (Aged V).quiet=0:=by intro U; unfold l; simp_rw [Poly.part_plus,Poly.part_sum,mute, show ∀ i,(F i U).part (Aged V).quiet=0 from (fun i=> (hF i).sil U),sum_const_zero,add_zero]
    obtain ⟨H,hQ,hN,hJ⟩:= curtainC A ψ K l ha hH hI hA hn (fun U s hp=> by unfold l; rw [Poly.part_plus,hush _ _ hp,zero_add]) hw hu hp hF hT hW (by ring) ht hk hw' hB hz he hh hP hC hy hit
    refine ⟨_,_,H,hQ,hN, ?_,hJ⟩
    intro i hi; have ho:= ho i hi; exact ⟨ho.1,fun U=> ⟨fun s=> Harps ((ho.2 U).1 s),fun j=> Harps (reborn v i _ _ _ K ψ _ _ ho.1 (hr _ hi) ((ho.2 U).2) j)⟩⟩
end YM.MergeProof.Ribbons
