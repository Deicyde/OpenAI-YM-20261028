import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Beam
/-!
# Lit stencils transformed with no gauge

Express enough for `Hears` range of all true fields. Specialize also to roll moments. Counterpart to `Wings`: arbitrary forest BRANCH instead of Orchard pulling a root; symmetrical after labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A : Stores S} {H : Forest S.ratio}
   {P : Teller G} {p q : Pilot G S x} {X Y : Support c} (v : Dyed G S)
lemma tight {i : Bond f} (h : Shields X (S.ratio.parent i.1) (20*radiusB x+17)): Span X x S i:= by
  intro j hj; simp only [Next.SectorChange.points,Set.mem_insert_iff,Set.mem_singleton_iff] at hj; rcases hj with rfl | rfl
  · exact h.shrink (by omega)
  exact h.shift (by have hx:= Work.E03.parent_step S i.1 i.2; omega)
lemma hug {i : Frozen p.key x p.park} {j : Frozen q.key x q.park} (hp : Hears X p q) (h : Span X x S i.val.val)
    (he : i.val.val=j.val.val): p.y.1 i=q.y.1 j:= by
  have hx (p:Pilot G S x) (i:Frozen p.key x p.park): p.y.1 i=rods p 0 i.val.val:= Eq.symm (Eq.trans (p.park.off_tree _ i.val) (freeze_held (j:=i) ..))
  rw [hx p, hx q,hp.speaks _ h,he]

lemma hark {i : Active p.key x p.park} {j : Active q.key x q.park} (hp : Hears X p q) (h : Span X x S i.val.val)
    (he : i.val.val=j.val.val): tape p.y.2 i=tape q.y.2 j:= by
  have hx (p:Pilot G S x) (i: Active p.key x p.park) (g : ℝ) : rods p g i.val.val= G.lieExp (g • tape p.y.2 i)* replica S.ratio p.view i.val.val:= by
    unfold rods kid photo; rw [zero_add,show tape (g • p.y.2)=g•tape p.y.2 from colors.map_smul ..]; exact (p.park.off_tree _ i.val).trans (freeze_regular (j:=i) ..)
  have hm (g:ℝ): G.lieExp (g • tape p.y.2 i)=G.lieExp (g • tape q.y.2 j):= by
    apply mul_right_cancel (b:=replica S.ratio p.view i.val.val); rw [← hx,hp.speaks _ h,back_edge (S:=S) _ (show _ from fun _ ht=>(h _ ht).center) hp.reads.configuration,he,hx]
  -- use arbitrarily small positive g; not at any determined nonzero price
  let u:=tape p.y.2 i; let w:=tape q.y.2 j
  let B:= 1+‖u‖+‖w‖; have hb:0<B:=by unfold B; positivity
  let r:=firstRadius G/B; have hr :0<r:=div_pos (first_pos G) hb
  have hu (z:G.Color) (he:‖z‖<B): r • z ∈ firstBall G:= mem_ball_zero_iff.mpr (by rw [norm_smul,Real.norm_of_nonneg hr.le]; exact (mul_lt_mul_of_pos_left he hr).trans_eq (div_mul_cancel₀ _ hb.ne'))
  apply smul_right_injective G.Color hr.ne'; change r • u=r • w; rw [← over_ball (hu u (by unfold B; linarith [norm_nonneg w])),← over_ball (hu w (by unfold B; linarith [norm_nonneg u])), show G.lieExp (r • u)=G.lieExp (r • w) from hm r]
lemma portrait_of (i : Site c) {r : ℕ} (hp : Hears X p q) (h : Shields X i (r+20*radiusB x+17)) :
    Scan S x i r p.key q.key p.park q.park p.tag q.tag p.view q.view p.y.1 q.y.1:= by
  have hf := hp.reads
  have hr (j : Bond c) (hy : separation i j.1 ≤ r): pinPos j⊆X:= by
    intro z hz; apply h
    have hx:= Physical.pin_diam j (show j.1∈pinPos j from mem_insert_self ..) hz; have hp:= separation_triangle i j.1 z; omega
  refine ⟨fun p hp=>hf.seed (h.shift (by omega)),fun k hk=>hf.frame _ (h _ (by omega)),fun j hj=>hf.bond _ (hr j hj),fun j hj=>hf.tree _ (h _ (by omega)) ?_,fun j hj=>hf.configuration _ (hr j hj (by simp [pinPos])) (hr j hj (by simp [pinPos])), fun j k hj hk=> hug hp (tight (h.shift (by omega))) hk⟩
  exact h _ ((separation_triangle _ (S.ratio.parent j.1) _).trans ((Nat.add_le_add hj (Work.E03.parent_step ..)).trans (by omega)))
namespace Dyed
lemma tape_scans (ht : Ready v.things x) (k : Active p.key x p.park) (l : Active q.key x q.park) (hp : Hears X p q) (h : Shields X (S.ratio.parent k.val.val.1) (21*radiusB x+17))
    (he:k.val.val=l.val.val): v.tapeAt p k=v.tapeAt q l:= by
  have hh: tape p.y.2 k=tape q.y.2 l:= hark hp (tight (h.shrink (by omega))) he
  ext j
  change meanLog p.key p.park v.things x p.view p.tag v.chi v.arc p.y.1 (k,j) + _* p.y.2 (k,j) =meanLog q.key q.park v.things x q.view q.tag v.chi v.arc q.y.1 (l,j)+_*q.y.2 (l,j)
  refine congr_arg₂ HAdd.hAdd (PatchReads.mean_eq ht (portrait_of _ hp (h.shrink (by omega))) (Prod.ext he rfl)) ?_
  exact congr_arg (_ * ·) (congr_arg (fun a:G.Color=>a j) hh)
lemma tape_photo (p : Pilot G S x): v.top p= Next.SectorChange.physical p.key p.park p.view p.y.1 (v.tapeAt p):= by unfold top tapeAt; rw [mean_endpoint]; rfl
lemma peak_record (h : Hears X p q) (i:Bond f) (ht : Ready v.things x) (hp : Shields X (S.ratio.parent i.1) (21*radiusB x+17)): top v p i=top v q i:= by
  let o:= S.ratio.parent i.1
  have hm := portrait_of o (r:=0) h (hp.shrink (by omega))
  have he : separation o (S.ratio.parent i.1)≤0:=by simp [o]
  rw [tape_photo v p,tape_photo]; unfold Next.SectorChange.physical
  by_cases hv:i∈p.park.trunks
  · exact (p.park.on_tree _ ⟨i,hv⟩).trans (q.park.on_tree _ ⟨i,(hm.trunks i he).mp hv⟩).symm
  let x₀:p.park.Free:= ⟨i,hv⟩; let y:q.park.Free:= ⟨i,mt (hm.trunks i he).mpr hv⟩
  by_cases hx:chill p.key x p.park x₀
  · let j: Frozen p.key x p.park:=⟨x₀,hx⟩; let k:Frozen q.key x q.park:=⟨y,(hm.freeze_same (i:=x₀) he rfl).1 hx⟩
    exact (show p.park.drape _ i=p.y.1 j from (p.park.off_tree _ x₀).trans (freeze_held (j:=j) ..)).trans ((hm.held j k he rfl).trans (show q.park.drape _ i=q.y.1 k from (q.park.off_tree _ y).trans (freeze_held (j:=k) ..)).symm)
  let k:Active p.key x p.park:=⟨x₀,hx⟩; let l:Active q.key x q.park:=⟨y,mt (hm.freeze_same (i:=x₀) he rfl).2 hx⟩
  have hz: replica S.ratio p.view i=replica S.ratio q.view i:= PatchReads.rep_share hm.outer i he
  refine (p.park.off_tree _ x₀).trans (Eq.trans ?_ (q.park.off_tree _ y).symm)
  exact (show returned _ _ _ p.y.1 (v.tapeAt p) x₀ = G.lieExp _ * replica S.ratio p.view i from freeze_regular (j:=k) ..).trans ((congr_arg₂ HMul.hMul (congr_arg G.lieExp (tape_scans v ht k l h hp rfl)) hz).trans (show returned _ _ q.view _ (v.tapeAt q) y=G.lieExp _ * _ from freeze_regular (j:=l) ..).symm)
end Dyed
end YM.PhysicalNext.InteractingRank.Pump
