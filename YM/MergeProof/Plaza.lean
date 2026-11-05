import YM.MergeProof.Cargo
import YM.MergeProof.Dock
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
variable [Fintype V]{ν:V→ℂ}{H:GaugeDoor R E}{S:StepData c f}
abbrev Specialty (G:Gauge)(n:Side)(V:Type):=V→Box n→ Config G n→ℂ
variable {α:V→ Config G f→ℂ}{κ:Specialty G f V}{k: Specialty G c V}{X:Config G f→Poly B}{o:V→Site f}{q:V→Site c}{w:V→ℝ}
    {N b:ℕ}{d c' t a p k' g δ u v σ:ℝ}{h Y:V→ℝ}
def Expense [Fintype ι] (N:ι→Hat B R)(v:V→ℝ)(X:StepData c f): Config G f→Poly B:= Merge.Photo.given (S:=X) (fun i=> (N i).M) (fun i=>sumFee (N i) v) B (fun i=>sing (N i) v)
-- upstream money guard and e<=. produces compression and tracking account. units exempt and pushed separately
lemma inventory (hv:∀ i,0<w i)(hq:Arsenal R)(hw:Tunes H)(hs:SoundDoor S H) (hg:R.Lawful σ u g δ v)
    (hp:Served R α κ X o w d c') (hx:0 ≤ d)(hb:d+1 ≤ R.p.supportExponent)(hr:∀ i,∃ x:Set Wing,x.Finite∧Tale x (o i) (q i) 1 (α i) (κ i) (k i) (ν i) (h i) (Y i) H)
    (hP:Occupancy o N)(hd:0 ≤ t)(ha:∀ i,2*w i*h i ≤ t)(hC:∀ i,w i*Y i≤a)(hy:p+1 ≤ E.p.supportExponent+2):
    let T:=N*siteFactor R.p.B*t+4*c'
    ∃ (I:Type) (_:Fintype I)(l:I→Hat B R),Offer o l w R.p.B d (T+Real.exp T*T) ∧ ∃ ψ:V→Response G c, Garnish E.p q ψ w p a ∧
       (∀ i U, k i U=fun a'=> ∑ j, owl (l j) H i U a' +hook E.activities E.p.threshold (ψ i) U a')∧∀ U,X U=Poly.pass (Mach B ν)* Expense l w S U:=by
   intro τ
   obtain ⟨F,Z,he,hF,hZ,H0⟩:=hp
   obtain ⟨I,hI,M,hM,θ,hθ,hX,hW,hR⟩:= Booth B hr hv hw hs hP hd hb ha hC hy
   obtain ⟨J,hJ,P,hB,hK,he,hp⟩:= drydock he hF hZ hv hq
   let z:=Sum.elim M P; let P0:= heap z; have ht : Offer o z w R.p.B d τ:= hM.cross hK
   have he₀(U): roll z U=Mach B (fun i=>α i U-ν i)+∑ i,F i U:=by rw [perfumes,Fintype.sum_sum_type]; exact congr_arg₂ _ (hW U) (he U)
   have htU(U x): board z x U=Mach B (fun i=>κ i x U)+Z x U:=by rw [patron,Fintype.sum_sum_type];exact congr_arg₂ _ (hR ..) (hp ..)
   refine ⟨_,inferInstance,P0, counts z w o R.p.B hv ht hx,θ,hθ,fun i U=> ?_,fun U=>?_⟩
   · funext x; rw [show P0=heap z from rfl,freeze,Fintype.sum_sum_type]
     have hp(b):owl (P b) H i U x=0:= by unfold owl; apply if_neg; intro h; have hp:=hB b; rw [h] at hp; simp [Census.fire] at hp
     have hh : ∑ b:J,owl (z (Sum.inr b)) H i U x=0:=sum_eq_zero (fun b _=> hp b); rw [hh, show ∑ j:I,owl (z (.inl j)) H i U x=_ from hX i x U,add_zero, sub_add_cancel]
   let a:= Real.exp (R.exponent U); let s:= Mach B ν
   unfold Expense P0; rw [passIn (heap z) S hg hv U, golden, banded];
   have hW: (roll z U).part B.quiet=0:=by unfold roll;simp [Poly.part_sum,still z _ U]
   rw [H0]; unfold restore; rw [mul_smul_comm]; let p i:= bar R.activities B U i+board z i U
   rw [← mul_assoc,← Extra.Trajectories.pass_add (x:=s) (y:=roll z U) (mute B ν) hW]
   have hy : s+roll z U=Mach B (fun i=>α i U)+∑ i,F i U:=by rw [he₀,← add_assoc]; congr 1; unfold s Mach; rw [← sum_add_distrib]; refine sum_congr rfl fun i _=> ?_; rw [← Extra.Trajectories.send_add,add_sub_cancel]
   rw [hy]; refine congr_arg _ (congr_arg (_*·) (congr_arg (fun l=> field l _) (funext ?_))); intro i; rw [htU]; ring
end YM.MergeProof.Menu
