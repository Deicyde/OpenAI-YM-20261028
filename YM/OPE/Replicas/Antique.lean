import YM.MergeProof.North.Antique
import YM.OPE.Replicas.Platform
import YM.OPE.Replicas.Price
import YM.OPE.Replicas.Thumb

/-!
# Many slots per cell: port of YM/MergeProof/North/Antique.lean

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
set_option quotPrecheck false
variable {σ ι δ p q k:ℝ}{N':ℕ}
variable {k':(V×slotsZ)→ℕ→ Config G c→ℂ}{L':(V×slotsZ)→ Config G c→ℂ}
    {ζ Z ξ ν ρ:ℝ}
-- stronger raw authorities. attach+Y so users exact bake. with bounds.Full.
lemma ranch (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o (S.ratio.parent ∘ o) L K (fun i=>profile A.activities (k' i)) g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i)))(hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:slotsZ,w (i,j)=w (v,j)) (hp:∀ i:slotsZ, let y:(V×slotsZ):=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (S.ratio.parent (o y)) 1 (L y) (K y) (profile A.activities (k' y)) (g y) (a i) (t i) D) (hP:Occupancy o N)(hd:0 ≤ d)(he:u+1 ≤ R.p.supportExponent)(ha:∀ i:(V×slotsZ),2*w i*a i.snd ≤ d)(hK:∀ i:(V×slotsZ),w i*t i.snd ≤ x)(hY:e+1 ≤ A.p.supportExponent+2)
    (hg:R.Lawful σ δ q p k)(hh: Serves R L K Y v P (fun i=> S.ratio.embed (E i)) B o w u c') (hb:0≤ u) (hi:Arsenal R)(hS:S.IsKernel R.beta G) (hH:Occupancy (S.ratio.parent ∘ o) N')(hM:Unites S D N' u Z ζ e ν ξ) (hQ:let T:=N*siteFactor R.p.B*d+4*c'; T+Real.exp T*T ≤ Z) :
    Arc A L' k' (S.push R.beta Y) v P E B (S.ratio.parent ∘ o) w ζ e ν ξ x g:=by
    obtain ⟨I,hI,M,hX,hU,ψ,hψ,h'ψ,hT,hX'⟩:= propels hD hs hx π hw hy hp hP hd he ha hK hY hg hh hb hi
    obtain ⟨F,O,hR,h₁,hO,h₂,hA,hV,hE,hTT⟩:= hM V slotsZ _ _ _ _ I hI o w M hw hH (hU.fatten hQ)
    have hp0: Horn v P E B F O:=by
       intro i hv; obtain ⟨q,hq⟩:= hX i hv; exact ⟨hq.here,hTT _ _ _ _ _ _ _ hq (fun j=>(hy i hv j).symm)⟩
    refine ⟨F,O,ψ,hψ,h'ψ,hR,hO,h₁,h₂,hp0,hV,fun i j U=> ?_,funext fun U=>?_⟩
    · rw [hE]; exact (congr_fun (hT j i) U).symm
    let s:=Mach X g; let b:=fun U=>∑ i,F i U; let f' U:= s+b U
    rw [show Y=(fun U=>_) from funext hX',convective S _ _ hS (heat M S w hg),hA];
    unfold play; rw [pass_add (mute X g) (show (b U).part (X).quiet=0 from ?_), mul_smul_comm];
    · unfold b; rw [mul_assoc]
    unfold b; rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun j _=> (h₁ j).sil U)
end YM.MergeProof.Ribbons.ManyCopies
