import YM.MergeProof.North.Apiary
import YM.OPE.Replicas.Thumb

/-!
# Many slots per cell: port of YM/MergeProof/North/Apiary.lean

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
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V J : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}
local notation "X"=> Names V slotsZ
variable {v:V}{B:V→Equiv.Perm V}{P:V→Motion}{E:V→Site f}{L:(V×slotsZ)→ Config G f→ℂ}{K:(V×slotsZ)→ Res G f}{u:ℝ}{w w':(V×slotsZ)→ℝ}{o:(V×slotsZ)→Site f}{Y:Config G f→Poly (Names V slotsZ)}
variable {t x c':ℝ} {F:(V×slotsZ)→ Config G f→ℂ}{J:ℕ}{b C d H e:ℝ}{Z:(V×slotsZ)→ℕ→ Config G f→ℂ}
lemma Serves.prune (h:Serves R L K Y v P E B o w d c')(hr:∀ i,0<w i)(hz:∀ i,0 < w' i)(hv:Repegs o R.p.B w w' t x (Names V slotsZ))(hw:0 ≤ x)(he:u+t≤d)(hd:x*c'≤e): Serves R L K Y v P E B o w' u e:=by
   obtain ⟨H,Z,h,hH,hZ,hi,ht⟩:= h; refine ⟨H,Z,h,?_,?_,hi,ht⟩
   · exact ((Towed.peg (hH.shrink he le_rfl hr) (fun i=>(h.exp i).1.toBorne) (fun i=>(h.exp i).2) hv hr hz hw)).shrink le_rfl hd hz
   exact ((Towed.peg (hZ.shrink he le_rfl hr) (fun i=>(h.flag i).1.toBorne) (fun i=>(h.flag i).2) hv hr hz hw)).shrink le_rfl hd hz
-- Top general sym. quiet vacuum bar
lemma bar_moves (hp:R.activities.Valid R.p b C)(m:Motion)(x:Site f)(e:R.activities.Moves m.1 x)(U:Config G f)(i:Box f): Harm v (B v) m (exclaim R.activities X i (pull m.1 x U)) (exclaim R.activities X (puff m x i) U):=by
    let p:=profile R.activities (fun j=> Complex.ofReal ∘ R.activities.K j); have he:p=floatUp m x p:= by
       apply roam m x e
       intro i U; dsimp [stepUp]; rw [e.valuesK, scalar_real]
    have hh:p (puff m x i) U=scalar m (p i (pull m.1 x U)):=by nth_rw 1 [he]; unfold floatUp; rw [Equiv.symm_apply_apply];rfl
    change Harm v _ m (Poly.send (X).quiet _) (Poly.send (X).quiet (p _ _)); rw [hh];
    have hz:= Harm.solo (m:=m) (b:=B v) (c₀:=v) (X).quiet (p i (pull m.1 x U)); rw [show drum (B v) (X).quiet=(X).quiet from Subtype.ext (by simp [drum,pares,Census.quiet])] at hz; exact hz
-- `Arc` with Y shape OLD + canonical ψ. Air from exponent singles? cannot start Arc at Mach g because initiation arbitrary! closure before.Plank. duplicate.
lemma spawn (hp:R.activities.Valid R.p b C)(ψ:(V×slotsZ)→ Response G f)(h:Garnish R.p o ψ w t u)(hr:relates v P E ψ)(hP:∀ i,i≠v→B i v=i)(hm:∀ i,Nonempty (R.activities.Moves (P i).1 (E i))) (hv:Occupancy o J)(hu:0 ≤ u)(hw:∀ i,0 < w i)
     (hX:t ≤ R.p.supportExponent) (hd:0≤d)(he:((R.p.B + R.p.B + 1:ℕ):ℝ)^4 * (C+J*siteFactor R.p.B*u) ≤ t-d)
     (hk:Real.exp (C+J*siteFactor R.p.B*u)-1 ≤ x)(hit:∀ U,R.eval U≠0)(hV: 0 ≤ x)
     (hC:∀ i,Dominated (Z i)) (h':∀ i,hook R.activities R.p.threshold (ψ i) =profile R.activities (Z i))
     (hT:∀ i U,(R.eval U:ℂ)*F i U=coin R (L i) (Z i) U): Serves R L (fun i=>profile R.activities (Z i)) (birth (Names V slotsZ) R F) v P E B o w d x :=by
    let K':= exclaim R.activities (Names V slotsZ); let X':= fun U=> Mach (Names V slotsZ) (fun i=> F i U); let H : Support f→ Config G f→Poly (Names V slotsZ):=fun _ _=>0; let tX:=R.p.threshold
    have hf: ∀ i, Burns o i (H i) tX := fun i=> ⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun _ h=>False.elim (h rfl),fun _=> rfl⟩
    have hh : Towed w id H R.p.B (d+0) x:=by
       refine ⟨0,Summable.of_finite,fun i=> by simp [SumBudget,hV],fun i=> ⟨0,le_rfl,fun U p=> ?_,?_⟩⟩
       · rw [show H i U=0 from rfl,Poly.part_nil,norm_zero]; rfl
       unfold wordsPrice; simpa using hV
    have hg:=starting (Names V slotsZ) R F hp -- order
    obtain ⟨hc,hA,hB,hY⟩:= curtainC R ψ K' X' h (granular _ _ _ hp) (fun i U=> (Poly.part_send ..).trans (if_pos rfl)) hp (a:=1) (H:=H) (fun U=>mute (Names V slotsZ) _) (by intro U i h; unfold X'; rw [hush _ _ h]; simp [H]) hw hu hv hf hh ((vacant _ _ _ hp w hw).shrink hX le_rfl hw) (by ring) (show 0 ≤ d+0 from by simpa) he hw (by simp [Repegs]) zero_le_one (one_mul _|>.le) (by rw [one_mul]; exact hk) (by intro i j U; change (Poly.send (Names V slotsZ).quiet _).part _+_= _; rw [Poly.part_send,if_neg ((Names V slotsZ).fire_hot j),zero_add,h']) (by intro i U; exact congr_arg (fun i'=> (i' U).part ((Names V slotsZ).fire i)) hg.symm|>.trans ((boot _ _ _ _ _).trans (hT ..))) hC hit
    · rw [hg]; refine ⟨_,_,hc,hA,hB,fun i hi=>⟨hP i hi,fun U=>⟨fun _=>Harps ?_,fun j=>Harps (reborn v i _ _ _ _ ψ _ U (hP i hi) (hr i hi) ?_ j)⟩⟩,hY⟩
      · exact fun _ _=> (scalar_z _).symm
      · exact fun j=> bar_moves (B:=fun _=>B i) hp (P i) (E i) (hm i).some U j
end YM.MergeProof.Ribbons.ManyCopies
