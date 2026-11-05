import YM.MergeProof.North.Thumb
import YM.OPE.Replicas.Menu
import YM.OPE.Replicas.Wraith

/-!
# Many slots per cell: port of YM/MergeProof/North/Thumb.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}{S:StepData c f}
variable {v:V}{P:V→Motion}{E:V→Site c}{B:V→Equiv.Perm V}
local notation "X"=> Names V slotsZ
variable {o:(V×slotsZ)→ Site f}{b:(V×slotsZ)→Site c}
    {L:(V×slotsZ)→ Config G f→ℂ}{K:(V×slotsZ)→ Res G f}{H:(V×slotsZ)→ Res G c}{a t:slotsZ→ℝ}{g:(V×slotsZ)→ℂ}
    {N:ℕ} {d e u x φ ψ c':ℝ}{w:(V×slotsZ)→ℝ}
    {Y: Config G f→Poly (Names V slotsZ)}
local notation "r"=> fun i=> S.ratio.embed (E i)
-- H,K raw ways. final exact operation. preserve on Mom. needed for any lower steps, split raw branch after exponent.
lemma Harps {m:Motion}{B:Equiv.Perm V}{p q:Poly (Names V slotsZ)}(h:Harm v B m p q): Harm v B m (octave p) (octave q):=by
   intro s hs; by_cases he: 2 ≤ s.val.card
   · rw [crest _ _ he,crest _ _ (show 2 ≤ (drum B s).val.card from (by rw [drum,pares, card_image_of_injective _ (nome B).injective];exact he))]; exact h s hs
   rw [starlet _ _ (Nat.lt_of_not_ge he),starlet _ _ (show (drum B s).val.card<2 from (by rw [drum,pares, card_image_of_injective _ (nome B).injective]; exact Nat.lt_of_not_ge he)),scalar_z]
-- After Blanket pliable maybe broad generalized.
structure Arc (R:Rep G f)(L:(V×slotsZ)→ Config G f→ℂ)(K:(V×slotsZ)→ℕ→ Config G f→ℂ)(Y:Config G f→ Poly (Names V slotsZ))(v:V)(P:V→Motion)(E:V→Site f)(B:V→Equiv.Perm V)(o:(V×slotsZ)→Site f)(w:(V×slotsZ)→ℝ)(d e t a b:ℝ)(pepper:(V×slotsZ)→ℂ): Prop where
    see : ∃ F Z, ∃ (ψ:(V×slotsZ)→ Response G f), Garnish R.p o ψ w e b∧ relates v P E ψ ∧ Towed w id F R.p.B d t ∧ Towed w Prod.fst Z R.p.B e a ∧ (∀ i,Burns o i (F i) R.p.threshold) ∧(∀ i,Flow o i (Z i) R.p.threshold)∧ Horn v P E B F Z ∧ (∀ i U,(Z i U).part (Names V slotsZ).quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)∧(∀ i j U,(Z i U).part ((Names V slotsZ).fire j)+hook R.activities R.p.threshold (ψ j) i U=profile R.activities (K j) i U)∧ Y= play R (Names V slotsZ) Z (fun U=> Mach (Names V slotsZ) pepper+∑ i,F i U)
variable {k:(V×slotsZ)→ℕ→ Config G c→ℂ}{L':(V×slotsZ)→ Config G c→ℂ}
    {Z':Config G c→Poly (Names V slotsZ)}{ζ Z ξ ν ρ:ℝ}
lemma thru (p:Arc A L' k Z' v P E B b w (u+ζ) e x φ c' g)(hA:A.activities.Valid A.p d ν)(hw:∀ i,0<w i)(hu:0 ≤ c')(hp:Occupancy b N)(ht:0 ≤ u+ζ)(hk:((A.p.B+A.p.B+1:ℕ):ℝ)^4*(φ+N*siteFactor A.p.B*c')≤e-(u+ζ))
    {w':(V×slotsZ)→ℝ}(hw':∀ i,0<w' i)(hB:Repegs b A.p.B w w' ζ Z (Names V slotsZ))(hz:0≤ Z)(he:Z*x ≤ ξ)(hh:Z*(Real.exp (φ+ N*siteFactor A.p.B*c')-1)≤ ξ)(hC:∀ i U,(Z' U).part ((Names V slotsZ).fire i)=coin A (L' i) (k i) U)(hy:∀ i,Dominated (k i))(hit:∀ U,A.eval U≠0): Serves A L' (fun i=>profile A.activities (k i)) Z' v P E B b w' u ξ:=by
    obtain ⟨F,K,ψ,ha,hr,hT,hW,hF,hH,ho,hI,hP,rfl⟩:=p.see
    let l U:= Mach (Names V slotsZ) g+∑ i,F i U; have hn:∀ U: Config G c,(l U).part (Names V slotsZ).quiet=0:=by intro U; unfold l; simp_rw [Poly.part_plus,Poly.part_sum,mute, show ∀ i,(F i U).part (Names V slotsZ).quiet=0 from (fun i=> (hF i).sil U),sum_const_zero,add_zero]
    obtain ⟨H,hQ,hN,hJ⟩:= curtainC A ψ K l ha hH hI hA hn (fun U s hp=> by unfold l; rw [Poly.part_plus,hush _ _ hp,zero_add]) hw hu hp hF hT hW (by ring) ht hk hw' hB hz he hh hP hC hy hit
    refine ⟨_,_,H,hQ,hN, ?_,hJ⟩
    intro i hi; have ho:= ho i hi; exact ⟨ho.1,fun U=> ⟨fun s=> Harps ((ho.2 U).1 s),fun j=> Harps (reborn v i _ _ _ K ψ _ _ ho.1 (hr _ hi) ((ho.2 U).2) j)⟩⟩
end YM.MergeProof.Ribbons.ManyCopies
