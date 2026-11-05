import YM.MergeProof.North.Menu
import YM.OPE.Replicas.Quark

/-!
# Many slots per cell: port of YM/MergeProof/North/Menu.lean

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
lemma pool (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o b L K H g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i))) (hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:slotsZ,w (i,j)=w (v,j)) (hp:∀ i:slotsZ, let y:(V×slotsZ):=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (b y) 1 (L y) (K y) (H y) (g y) (a i) (t i) D) (hP:Occupancy o N)(hd:0 ≤ d)(he:u+1 ≤ R.p.supportExponent)(ha:∀ i:(V×slotsZ),2*w i*a i.snd ≤ d)(hK:∀ i:(V×slotsZ),w i*t i.snd ≤ x)(hY:e+1 ≤ A.p.supportExponent+2) :
    ∃ (I:Type) (_: Fintype I) (M:I→Hat (Names V slotsZ) R), Cohere v P (fun i=> S.ratio.embed (E i)) B π M ∧ Offer o M w R.p.B u (N*siteFactor R.p.B*d) ∧ ∃ ψ:(V×slotsZ)→Response G c, Garnish A.p b ψ w e x ∧ relates v P E ψ ∧ (∀ i U j,∑ l,owl (M l) D i j U=H i j U-hook A.activities A.p.threshold (ψ i) j U) ∧ (∀ U,∑ i,odour (M i) U=Mach (Names V slotsZ) (fun i=>L i U-g i)) ∧ ∀ j U,∑ i,fragrance (M i) U j=Mach (Names V slotsZ) (fun i=> K i j U):=by
    obtain ⟨I,hI,M,p,hM,hX,Ht⟩:=quay v P E B o b L K H a t g S hD hs hx π hw hy hp; let Z:= Σ j:(V×slotsZ),I j.snd
    have hg(i:Z):=(hM i.1).ran i.2
    have hz:Rooted (fun i=>(M i).s.val) (fun i=> (M i).M.crest) R.p.B R.p.supportExponent (fun i=> Menu.fare (M i) w) d:=by
       intro i; refine ⟨fun x=>?_, Summable.of_finite,?_⟩
       · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (Crew _ hw); rfl
       rw [tsum_fintype,Fintype.sum_sigma,sum_eq_single i];
       · calc
            _ = ∑ v:I _, R.p.mass (M ⟨i,v⟩).M.crest (Menu.fare (M ⟨i,v⟩) w) := sum_congr rfl fun j _=> if_pos (show i∈(M ⟨i,j⟩).s.val from ((hM i).ran j).1.symm ▸ (show i∈((X).fire i).val from mem_singleton_self _))
            _ ≤ _ := (hM i).fare.trans (ha i)
       · intro j _ hj; apply Finset.sum_eq_zero; intro k _; exact if_neg fun hi=> hj (Finset.mem_singleton.mp (show i∈((X).fire j).val from ((hM j|>.ran k).1) ▸ (show i∈ (M ⟨j,k⟩).s.val from hi))|>.symm)
       simp
    have hG: Garnish A.p b p w e x:=by
       have hB i:=(hM i).bill
       refine ⟨fun i t=> (hB i).shaped _,fun i k=> (hB i).marked _,fun i=>?_⟩; obtain ⟨t,ht,hQ⟩:= (hB i).toll
       refine ⟨t,hQ,le_trans ?_ (hK i)⟩
       apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap ht univ) (hw i).le); rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; unfold reservedMass; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr)) (hQ j).1) (hw i).le
    refine ⟨Z,inferInstance,M,Ht, ⟨fun i=>?_,root_hit hP (fun _=>Crew _ hw) hd ?_ (hz.mono (fun _=>Crew _ hw) (fun _=>le_rfl) he le_rfl)⟩,p,hG,hX,fun i U j=>?_,fun U=>?_,fun j U=>?_⟩
    · rw [(hg i).1]; change Finset.image _ {_}⊆_; simp only [image_singleton,singleton_subset_iff]; exact (hg _).2
    · intro i hi; exact ⟨i.1,(hg i).1.symm ▸ (show i.1∈((X).fire i.1).val from mem_singleton_self _),(hg i).2⟩
    · rw [Fintype.sum_sigma,sum_eq_single i]; exact hM i|>.tells j U
      · intro k _ hk; refine sum_eq_zero (fun l _=>?_); unfold owl; split
        next ht=> exact False.elim (hk (((X).fire_inj k i).mp (((hM k).ran l).1.symm.trans ht)))
        next hh=> rfl -- parser
      simp
    · rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> (hM i).note U
    rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> (hM i).verse j U
-- stronger Serves

def Serves (R:Rep G f)(L:(V×slotsZ)→ Config G f→ℂ)(K:(V×slotsZ)→ Res G f)(Y:Config G f→Poly (Names V slotsZ))(v:V)(P:V→Motion)(E:V→Site f)(B:V→Equiv.Perm V)(o:(V×slotsZ)→Site f)(w:(V×slotsZ)→ℝ)(t d:ℝ):Prop:=∃ F Z, Carton o F Z R.p.threshold ∧ Towed w id F R.p.B t d ∧ Towed w Prod.fst Z R.p.B t d ∧ Horn v P E B F Z ∧ Y= restore R L K F Z
end YM.MergeProof.Ribbons.ManyCopies
