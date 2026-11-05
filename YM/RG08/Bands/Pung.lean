import YM.RG08.Bands.Codex
/-!
# Limit of the charge identities on a fixed step. No envelope exponent loss.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I α:Type}{r s:ℕ}{c:Side}{m:ℕ→Side}{K:Row α α}{p:Option Side}{A B C η:ℝ}
section root
variable {F:ℕ→ Shale α r}{f:Shale α r}
lemma declines (h:Hurled F f): ∃ a:ℕ→ℝ, Tendsto a atTop (𝓝 (∑' j, ‖f j‖)) ∧ ∀ i, Quire.Lit (F i) 0 (a i) := by
    obtain ⟨p,hp,H⟩:=h.moment.thus; refine ⟨_,(show Tendsto (fun i=>p i+∑' j, ‖f j‖) atTop _ from by simpa using hp.add_const (∑' j, ‖f j‖)),fun i=>?_⟩
    rw [show F i=F i-f+f from (sub_add_cancel ..).symm]; exact (H i).plus h.old.black (fun i=> (ling_pos _ _).le)
lemma braid_l {F W:Shale α r}{V:Shale α s} (h:Pens F)(hv:Pens W)(hp:Pens V): braidV (F-W) V=braidV F V-braidV W V:= by unfold braidV; rw [show interU (F-W) V=interU F V-interU W V from funext fun i=>_root_.sub_mul ..,Pens.tub_sub _ (inter_pens h hp) (inter_pens hv hp),sew_sub]
lemma braid_b {F W:Shale α r}{V:Shale α s}(h:Pens F)(hv:Pens W)(hp:Pens V): braidV V (F-W)=braidV V F-braidV V W:= by unfold braidV; rw [show interU V (F-W)=interU V F-interU V W from funext fun i=>mul_sub ..,Pens.tub_sub _ (inter_pens hp h) (inter_pens hp hv),sew_sub]
lemma ling_tail (u:ℝ): (ling 0: Beads α r→ℝ)=tailP 0 u:= funext fun i=>by simp [ling,tailP]
lemma braid_rem (a b:ℝ)(F:Shale α r)(V:Shale α s)(h:Quire.Lit F 0 a)(ht: Quire.Lit V 0 b): Quire.Lit (braidV F V) 0 (a*b):= by
    unfold Quire.Lit at *; rw [ling_tail 1] at *; exact braid_pol (k:=0) (η:=1) h ht zero_le_one
lemma windB {U:ℕ→Shale α s}{V:Shale α s}(h:Hurled F f)(hv:Hurled U V): Hurled (fun i=>braidV (F i) (U i)) (braidV f V):= by
    let X i:=braidV (F i-f) (U i); let Y i:=braidV f (U i-V)
    refine ⟨braid_tid h.old hv.old|>.pens,?_⟩; rw [show (fun i=> braidV (F i) (U i)-braidV f V)=X+Y from funext fun i=>by rw [Pi.add_apply]; unfold X Y; rw [braid_l (h.ever i) h.old (hv.ever i),braid_b (hv.ever i) hv.old h.old]; abel]
    obtain ⟨p,hp,Hp⟩:=h.moment.thus; obtain ⟨u,hu,Hu⟩:= declines hv; obtain ⟨w,hw,Hw⟩:= hv.moment.thus
    exact Decline.plus ⟨_,(show Tendsto (fun i=>p i*u i) atTop (𝓝 0) from by simpa using hp.mul hu),fun i=> braid_rem _ _ (F i-f) (U i) (Hp i) (Hu i)⟩ ⟨fun i=> (∑' j, ‖f j‖)*w i,by simpa using! hw.const_mul _,fun i=> braid_rem _ _ f (U i-V) h.old.black (Hw i)⟩ -- syntax ..
end root
section cov
variable {U V:Shale α (r+1)}{F H:Shale α (s+1)}
lemma county_left (h:Pens U)(he:Pens V)(hp:Pens F)(hk:Whole K): countP p K (U-V) F=countP p K U F-countP p K V F:= by
   unfold countP; rw [show interU (U-V) F=interU U F-interU V F from funext fun i=> _root_.sub_mul ..,_root_.sub_mul,Pens.tub_sub _ (bob_pens h hp hk) (bob_pens he hp hk),smul_sub,sew_sub]
lemma county_right (h:Pens F)(he:Pens H)(hp:Pens U)(hk:Whole K): countP p K U (F-H)= countP p K U F-countP p K U H := by
   unfold countP; rw [show interU U (F-H)=interU U F-interU U H from funext fun i=>mul_sub ..,_root_.sub_mul,Pens.tub_sub _ (bob_pens hp h hk) (bob_pens hp he hk),smul_sub,sew_sub]
lemma county_l (h:Quire.Lit U 0 A)(he:Quire.Lit F 0 B)(hp:K.strip η C)(hk:0<η)(hg:0≤C) : Quire.Lit (countP p K U F) 0 (‖syl r s‖*(C*(A*B))) := by
    refine stitching (Ink.scale (Ink.pour _ ?_ (ling_one le_rfl)) _)
    refine budget_mono (budget_scale hg (budget_prod h he)) (fun i=> mul_nonneg (ling_pos ..|>.le) (norm_nonneg _)) fun i=>?_
    simp only [Function.comp_apply,Pi.mul_apply,ling,mul_zero,zero_mul,Real.exp_zero,one_mul,interU,norm_mul]
    rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (stroke_known _ hp hk.le ..) (by positivity)
lemma winding (h:Pens U)(he:Pens F)(hm:Tendsto (fun i=>(m i).val) atTop atTop)(hp:Whole K): Hurled (fun i=> countP (some (m i)) K U F) (countP none K U F):= by
   let A p:=interU U F * (bob p K : Beads α (r+1) × Beads α (s+1)→ℝ); let U' i:= A (some (m i))-A none
   have hA i:Pens (A i):= bob_pens h he hp
   let p i:=∑' j,‖U' i j‖
   have hh:Tendsto p atTop (𝓝 0):= by
      obtain ⟨w,C,hw,H⟩:=hp; have hx j : Tendsto (fun i=> ‖U' i j‖) atTop (𝓝 0):= by
         have ht:=stroke_late K (Whole.safe (A:=K) ⟨_,_,hw,H⟩) m hm (j.1 0) (j.2 0)
         simpa [A,U',bob] using! (((ht.const_mul (interU U F j)).sub_const (A none j)).norm) -- A
      have hg i j: ‖U' i j‖ ≤ (C+C)*‖interU U F j‖:= by
         have ht (p): ‖A p j‖≤ C*‖interU U F j‖:= by unfold A; rw [Pi.mul_apply,norm_mul,mul_comm C]; exact mul_le_mul_of_nonneg_left (stroke_known _ H hw.le ..) (norm_nonneg _)
         rw [add_mul]; exact (norm_sub_le ..).trans (add_le_add (ht _) (ht _))
      simpa using! tendsto_tsum_of_dominated_convergence ((inter_pens h he).mul_left (C+C)) hx (.of_forall fun i j=> by simpa only [norm_norm] using! hg i j)
   refine ⟨count_tid h he hp|>.pens,⟨_,(show Tendsto (fun i=> ‖syl r s‖*p i) atTop (𝓝 0) from by simpa using! hh.const_mul _),fun i=>?_⟩⟩
   unfold countP; rw [← sew_sub,← smul_sub, ←Pens.tub_sub stemPair (bob_pens (p:=some (m i)) h he hp) (bob_pens (p:=none) h he hp)]
   refine stitching (Ink.scale (Ink.pour stemPair ?_ (ling_one le_rfl)) _); rw [show ling 0 ∘ (stemPair (α:=α) (r:=r) (s:=s))=1 from funext fun i=>by simp [ling]]; exact Pens.priced ((hA _).less (hA none))
lemma legs_move {U':ℕ→Shale α (r+1)}{F':ℕ→Shale α (s+1)}(h:Hurled U' U)(hv:Hurled F' F)(hm:Tendsto (fun i=> (m i).val) atTop atTop)(hp:Whole K): Hurled (fun i=> countP (some (m i)) K (U' i) (F' i)) (countP none K U F):= by
   have he:=winding h.old hv.old hm hp; let A i:=countP (some (m i)) K (U' i-U) (F' i); let B i:= countP (some (m i)) K U (F' i-F)
   have hx: (fun i=>countP (some (m i)) K (U' i) (F' i)-countP none K U F)=A+B+(fun i=> countP (some (m i)) K U F-countP none K U F):= funext fun i=>by simp only [A,B,Pi.add_apply]; rw [county_left (h.ever i) h.old (hv.ever i) hp,county_right (hv.ever i) hv.old h.old hp]; abel
   obtain ⟨a,H,hA⟩:=h.moment.thus; obtain ⟨b,hb,hB⟩:= declines hv; obtain ⟨c,hc,hC⟩:=hv.moment.thus
   obtain ⟨w,u,hw,Hw⟩:=hp; let U₁:= max 0 u; have hQ:=strip_mono Hw le_rfl (show u≤U₁ from le_max_right ..)
   let v:= ∑' j,‖U j‖
   refine ⟨he.old,hx ▸ Decline.plus (Decline.plus ⟨fun i=> ‖syl r s‖*(U₁ * (a i*b i)),by simpa using! (((H.mul hb).const_mul U₁).const_mul ‖syl r s‖),fun i=> county_l (hA i) (hB i) hQ hw (le_max_left ..)⟩ ⟨fun i=> ‖syl r s‖*(U₁*(v*c i)),by simpa using! (((hc.const_mul _).const_mul _).const_mul _),fun i=>county_l h.old.black (hC i) hQ hw (le_max_left ..)⟩) he.moment⟩
end cov
end YM.RG08.Bands
