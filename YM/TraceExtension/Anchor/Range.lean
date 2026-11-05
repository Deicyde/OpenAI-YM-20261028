import YM.TraceExtension.Anchor.Derivative
import YM.Next.UV_STRESS.Shell

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Function Filter Set Finset MeasureTheory Analysis Extraction Table Cells Lattice Wilson Next.UVStress
open Asymptotics
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
section
variable {E : Type*}[NormedAddCommGroup E] [NormedSpace ℂ E][FiniteDimensional ℂ E] {H : Schedule}
lemma Fast.sum' {ι:Type*}(s:Finset ι)(F:ι→ℕ→E)(h:∀ i∈s,Fast H (F i)):Fast H (∑ i∈s,F i):=by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; refine ⟨-1,by norm_num,?_⟩; apply isBigO_zero
   | insert i s hi IH=> rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (IH fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma scale_faithful {ι:Type*}[Fintype ι] (f:ℕ → E →ₗ[ℂ] ι→ℂ)(g:E →ₗ[ℂ] ι→ℂ) (hg:Injective g)
    (ht:∀ v i,Tendsto (fun k=>f k v i) atTop (𝓝 (g v i))) {u:ℕ→E}(h:∀ i, Fast H fun k=>f k (u k) i) : Fast H u:= by
    obtain ⟨B,hB⟩:= g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
    let F k : E→L[ℂ] E:=LinearMap.toContinuousLinearMap (B.comp (f k)); have he(x:E): B (g x)=x:=LinearMap.congr_fun hB x
    have hp:Tendsto F atTop (nhds 1):= by
       change Tendsto _ _ (𝓝 (LinearMap.toContinuousLinearMap (LinearMap.id : E →ₗ[ℂ] E)))
       refine Dash.fit_plane _ _ fun x=> ?_; change Tendsto (fun k=>B (f k x)) _ (nhds x); nth_rw 2 [← he x]
       exact (B.continuous_of_finiteDimensional.tendsto (g x)).comp (tendsto_pi_nhds.mpr (ht x))
    have hv: ∀ᶠ k in atTop, ‖u k‖ ≤ 2*‖B.toContinuousLinearMap‖*‖f k (u k)‖ := by
       filter_upwards [Metric.tendsto_nhds.mp hp (1/2) (by norm_num)] with k hk
       rw [dist_eq_norm] at hk
       have hz : ‖F k (u k)-u k‖ ≤ (1/2:ℝ)*‖u k‖ := ((F k-1).le_opNorm (u k)).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)); have hh:=norm_sub_norm_le (u k) (F k (u k)); rw [norm_sub_rev] at hh; linarith only [hh,hz,(show ‖F k (u k)‖≤_ from B.toContinuousLinearMap.le_opNorm (f k (u k)))]
    let w(k):=f k (u k); let W(i:ι)(k:ℕ):ι→ℂ:= Pi.single i (w k i)
    have hE : Fast H w := by
       rw [show w=∑ i,W i by ext k i; simp [W, Pi.single_apply,eq_comm]]
       apply Fast.sum'; intro i _; refine (h i).smaller (isBigO_of_le _ (fun k=> ?_)); unfold W w; apply (Pi.norm_single ..).le
    exact hE.smaller (isBigO_iff.mpr ⟨_,hv⟩)
end
section
variable {G : Gauge}{C : Family G}{S: Table C.book} {D:ℕ}
lemma response_fast (H:S.Hierarchy)(v:ℕ→ S.Field D) (h:∀ I:Watch C,∃ Θ:ℕ→S.Field D→ₗ[ℂ] ℂ, (∀ z:S.Field D,Tendsto (fun k=>Θ k z) atTop (𝓝 (I.tester S D z)))∧ Fast C.S fun k=> Θ k (v k)) : Fast C.S v:=by
  choose f ht hF using h; obtain ⟨s,hS⟩:= Work.A04.finite_faithful _ (observes (C:=C) H D)
  let p k:= LinearMap.pi fun i:s=> f i.val k; let q:= LinearMap.pi fun i:s=>i.val.tester S D
  exact scale_faithful p q hS (fun v i=> ht i.val v) (fun i=>hF i.val)

private lemma fast_close' (H:S.Hierarchy)(P:ℕ→S.Field D) {b : Filter (ℕ×ℕ)} [b.NeBot](h: Book b 0 P): Fast C.S P := by
  apply response_fast H P; intro I
  obtain ⟨c,hc,E,he,hK⟩:= h I
  refine ⟨fun _=>I.tester S D,fun z=>tendsto_const_nhds, he.smaller (isBigO_iff.mpr ⟨1,?_⟩)⟩
  filter_upwards [hK] with k hk; obtain ⟨i,hi⟩:= (hk 0 0 (by simpa using hc.le)).exists
  simpa [smoke,moment,tester_home] using hi
end
end YM.Trace.Pull
