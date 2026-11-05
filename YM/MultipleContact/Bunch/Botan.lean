import YM.MergeProof.Ballad
import YM.MergeProof.North.Lyme
import YM.MergeProof.Zing
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Corn
import YM.MultipleContact.Bunch.Lyme

/- generalized from YM.MergeProof.North.Botan to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}
local notation "X"=> Aged V slot
variable (j:Name V slot)(w:Name V slot→ℝ) (o:Site f)(z:Site c)(L:Config G f→ℂ)(K:Res G f)(Y:Res G c)
structure Publish (d e:ℝ) (k:ℂ) (D:GaugeDoor R A)(g:ι→Hat (Aged V slot) R)(ψ: Response G c) : Prop where
   ran i: (g i).s=(Aged V slot).fire j ∧ o∈(g i).M.crest
   fare : (∑ i:ι,R.p.mass (g i).M.crest (Menu.fare (g i) w)) ≤ 2*w j*d
   bill : Attainment A.p z ψ e
   note U: ∑ i,odour (g i) U= Poly.send ((Aged V slot).fire j) (L U-k)
   verse i U: ∑ l,fragrance (g l) U i=Poly.send ((Aged V slot).fire j) (K i U)
   tells p U : ∑ l,owl (g l) D j p U=Y p U-hook A.activities A.p.threshold ψ p U
variable {j w o z L K Y} {ψ:Response G c}{d e a:ℝ}{k:ℂ}{D:GaugeDoor R A}{g:ι→Hat (Aged V slot) R}(p:Publish j w o z L K Y d e k D g ψ)
lemma printed (s:(X).Mode)(F:ι→ℂ): ∑ i,Poly.send s (F i)=Poly.send s (∑ i,F i):=by ext i; rw [Poly.part_sum]; simp_rw [Poly.part_send]; split; rfl; simp
namespace Publish
include p
variable (m:Motion)(x:Site c)(B:Equiv.Perm V){S:StepData c f}
local notation "X₀"=> S.ratio.embed x
variable (π : R.activities.Moves m.1 (S.ratio.embed x))
local notation "Z" => shuttled B m X₀ π
lemma updates (hw:∀ i:slot,w (j.1,i)=w (B j.1,i))(hD:SoundDoor S D):
    Publish (nome (slot:=slot) B j) w (affine m.1 (S.ratio.embed x) o) (affine m.1 x z) (stepUp m (S.ratio.embed x) L) (floatUp m (S.ratio.embed x) K) (floatUp m x Y) d e (scalar m k) D (shuttled B m (S.ratio.embed x) π ∘ g) (upwards m x ψ):=by
    obtain ⟨π',hV⟩:=hD.conduct m x π
    let r i:= p.ran i
    -- h computation hats
    have he i : ((Z ∘ g) i).s=(X).fire (nome (slot:=slot) B j):= (congr_arg (drum (slot:=slot) B) (r i).1).trans (go_one B j)
    have hc:= hw j.2; change w (_,j.2)=w (_,j.2) at hc
    have hT : w (nome (slot:=slot) B j)=w j:=hc.symm
    have hf i :=forecast j.1 (B j.1) B m X₀ π rfl hw (g i) ((r i).1.symm ▸ ((which ..).2 (rfl:j.1=j.1)))  
    have hprint (A:ι→ℂ)(c:ℂ)(i:(X).Mode)(hh:∑ j:ι,Poly.send i (A j)=Poly.send i c): ∑ j,A j=c:=by rw [printed] at hh; simpa using (congr_arg (fun p:Poly X=>p.part i) hh)
    refine ⟨fun i=>?_,?_,MergeProof.rise m x p.bill,fun U=>?_,fun i U=>?_,fun i U=>?_⟩
    · refine ⟨he i,?_⟩; change affine _ _ _∈ (Leaf.route π (g i).M).crest; rw [crestSky m (X₀),shading]; exact mem_image_of_mem (turnSites m.1 (X₀)) (r i).2
    · rw [hT]; refine le_trans (Finset.sum_le_sum fun i _=> le_of_eq ?_) p.fare; change R.p.mass (Leaf.route π (g i).M).crest (Menu.fare (Z (g i)) w)=_
      rw [crestSky m X₀,hf i,BudgetPoint.mass,shading,cover_map _ (turn_sep m.1 X₀)]; rfl
    · let U':= pull m.1 X₀ U; have hz : ∑ i,Poly.send ((X).fire j) (prose (g i).M U'*(g i).charge)=Poly.send ((X).fire j) (L U'-k):=by
        have hh:=p.note U'; simp_rw [odour,show ∀ i,(g i).s=(X).fire j from fun i=>(p.ran i).1] at hh; exact hh
      simp_rw [odour,he,printed]; refine congr_arg _ ?_
      change (∑ i, prose (Leaf.route π (g i).M) U * scalar m (g i).charge)=scalar m (L U')-scalar m k
      rw [← scalar_sub, ← hprint _ _ _ hz, ← scales]; apply sum_congr rfl; intro i _; rw [climb_p m (X₀),Motion.scalar_mul]; rfl
    · obtain ⟨i,rfl⟩:= (puff m X₀).surjective i
      let U':= pull m.1 X₀ U; have hz : ∑ l,Poly.send ((X).fire j) (entry (g l).M i U'*(g l).charge)=Poly.send ((X).fire j) (K i U'):=by
        have hh:=p.verse i U'; simp_rw [fragrance,show ∀ i,(g i).s=(X).fire j from fun i=>(p.ran i).1] at hh; exact hh
      simp_rw [fragrance,he,printed]; refine congr_arg _ ?_
      change (∑ l, entry (Leaf.route π (g l).M) _ _ * scalar m (g l).charge)=floatUp _ _ _ _ _
      unfold floatUp stepUp; rw [Equiv.symm_apply_apply,← hprint _ _ _ hz, ← scales]; apply sum_congr rfl; intro l _; rw [Motion.scalar_mul,climb_entry m (X₀)]; unfold floatUp;rw [Equiv.symm_apply_apply];rfl
    obtain ⟨i,rfl⟩:= (puff m x).surjective i
    rw [hooked m x π']; unfold floatUp stepUp; rw [Equiv.symm_apply_apply,← scalar_sub,← p.tells, ← scales]; apply sum_congr rfl; intro j _; unfold owl; rw [he,if_pos rfl,(p.ran j).1,if_pos rfl,Motion.scalar_mul]; change scalar m _* quoted D (Leaf.route π _) _ _= _; rw [carries_quote m x D hD]; unfold floatUp; rw [Equiv.symm_apply_apply]; rfl
end Publish
end YM.MergeProof.BatchRibbons
