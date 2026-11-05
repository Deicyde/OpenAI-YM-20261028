import YM.UVExtension.Steady.Twins
import YM.Push.LOOP_COEFFICIENT.LogDet
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cincture
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set Lattice RG Pressure MeasureTheory Finset ConnectedActivityE6 Blaze Matrix
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
namespace Walt
variable {ι κ π : Type*} {E F G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
   [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedRing A] [NormedAlgebra ℝ A]
    {v:Filter ι} {x:ι→ E} {j k:ℕ} {f g: ι→ Bool→ E→ F} {h:ι→ Bool→ E→ G}
lemma minus (p:Walt v x k f)(q:Walt v x k g): Walt v x k (fun i b y=> f i b y-g i b y):=by
    simp_rw [sub_eq_add_neg]; exact p.sums (q.leaf (-(ContinuousLinearMap.id ℝ F)))
lemma both (p:Walt v x k f)(q:Walt v x k h): Walt v x k (fun i b y=> (f i b y,h i b y)):=by
    apply ((p.leaf (ContinuousLinearMap.inl ℝ F G)).sums (q.leaf (ContinuousLinearMap.inr ℝ F G))).same; filter_upwards with n i; filter_upwards with u; simp
lemma pay {g:ι→ Bool→ E→ ℝ}(p:Walt v x k g)(q:Walt v x k f): Walt v x k (fun i b y=> g i b y • f i b y):= p.twin_bill q (ContinuousLinearMap.lsmul ℝ ℝ)
lemma times {f g : ι→ Bool→ E→ A}(p:Walt v x k f)(q:Walt v x k g): Walt v x k (fun i b y=> f i b y*g i b y):= p.twin_bill q (ContinuousLinearMap.mul ℝ _)
lemma schedule (r:Finset κ) (F:κ→ι→ Bool→ E→ F)(p:∀ i∈r,Walt v x k (F i)): Walt v x k (fun i b y=>∑ j∈r,F j i b y):= by
   induction r using Finset.induction_on with
   | empty => simp only [Finset.sum_empty]; exact ready _
   | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (p _ (mem_insert_self ..)).sums (ih fun j hj=> p j (mem_insert_of_mem hj))
lemma choose (r : ι→Prop) (p:Walt (apart v r) x k f) (q:Walt (apart v (fun n=>¬r n)) x k g): Walt v x k (fun n b y=> if r n then f n b y else g n b y):=by
   apply split r; exact p.same ((eventually_inf_principal.mpr (by filter_upwards with i hi X using Eventually.of_forall fun _=>if_pos hi))); exact q.same ((eventually_inf_principal.mpr (by filter_upwards with i hi X using Eventually.of_forall fun _=>if_neg hi)))
variable (T:Type) [Fintype T]
lemma assemble (H: ι→ Bool→ E→ T→ G)(p:∀ i,Walt v x k (fun n b y=> H n b y i)): Walt v x k H:=by
   apply (schedule Finset.univ (fun j n b y=> Pi.single j (H n b y j)) (fun j _=> (p j).leaf (ContinuousLinearMap.single ℝ (fun _ : T=> G) j))).same; filter_upwards with i b; filter_upwards with y
   ext1 j; rw [Finset.sum_apply,Finset.sum_eq_single j]; change _=(Pi.single j _ : T → G) j; rw [Pi.single_eq_same]
   intro a _ ha; exact Pi.single_eq_of_ne ha.symm _
   simp
-- matrix local instances via Matrix.Norms.Frobenius. use basis lift
variable {T} {J:Type} [Fintype J]
lemma rectangle (H : ι→ Bool→ E→ Matrix T J ℝ)(p:∀ i j,Walt v x k (fun n b y=> H n b y i j)): Walt v x k H:=by
   let N :(T→J→ℝ) →ₗ[ℝ] Matrix T J ℝ:=
    { toFun := Matrix.of
      map_add' := fun i j=>rfl
      map_smul' := fun i j=>rfl }
   exact (assemble T _ (fun i=>assemble J _ (p i))).leaf N.toContinuousLinearMap
lemma cut (a:ι→T)(p:T→ι→Bool→ E→G)(hp:∀ i,Walt (apart v (fun n=>a n=i)) x k (p i)): Walt v x k (fun n b=>p (a n) n b):=by
    suffices he : ∀ i:Finset T,Walt v x k (fun n b y=> ∑ j∈i, if a n=j then p j n b y else 0) from (he univ).same (Eventually.of_forall fun n b=> Eventually.of_forall fun y=> by simp [sum_ite_eq])
    intro i; exact schedule i _ fun j _=> Walt.choose _ (hp j) (ready _)
lemma cup {g:ι→ Bool→ E→ ℝ}(p:Walt v x k g){r:ℝ}(hr:0<r)(q:∀ᶠ i in v,∀ b,r≤g i b (x i)): Walt v x k (fun i b y=> Real.log (g i b y)) ∧ Walt v x k (fun i b y=> (g i b y)⁻¹):=by
   obtain ⟨U,hU⟩:= p.atProbe.1; let K:= Set.Icc r U; have h : IsCompact K:= isCompact_Icc
   have hx : ∀ᶠ n in v,∀ b, g n b (x n)∈ K:=by filter_upwards [q,hU] with i h hx b; exact ⟨h b,(le_abs_self _).trans (hx _)⟩
   exact ⟨company h (fun i hi=> Real.contDiffAt_log.mpr (hr.trans_le hi.1|>.ne')) p hx,company h (fun i hi=> contDiffAt_inv ℝ (hr.trans_le hi.1|>.ne')) p hx⟩
lemma exponential {f:ι→Bool→ E→ℝ}(p:Walt v x k f): Walt v x k (fun i b y=> Real.exp (f i b y)):= p.plant Real.contDiff_exp
lemma matrixUnit {F:ι→ Bool→ E→ Matrix T T ℝ}(p: Walt v x k F){d:ℝ}(hd:0<d)(hp:∀ᶠ i in v,∀ b, d≤(F i b (x i)).det): Walt v x k (fun i b y=> (F i b y)⁻¹):=by
   obtain ⟨m,h⟩:= p.atProbe.1; let K : Set (Matrix T T ℝ):= closedBall 0 m∩ (Matrix.det ⁻¹' (Set.Ici d))
   have hK:IsCompact K:=(isCompact_closedBall _ _).inter_right (isClosed_Ici.preimage continuous_id.matrix_det)
   refine company hK (fun X hx=> ?_) p ((h.and hp).mono fun n h b=> ⟨mem_closedBall.mpr (by rw [dist_zero_right]; exact h.1 b),h.2 b⟩)
   -- smooth by nonsing formula Cramer
   have hi:0<X.det:= hd.trans_le hx.2
   exact (Push.Loops.inv_contDiffAt X (isUnit_iff_ne_zero.mpr hi.ne')).of_le le_top
end Walt
end YM.UVExtension.Steady
