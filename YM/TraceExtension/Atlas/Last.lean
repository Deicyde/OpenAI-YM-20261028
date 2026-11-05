import YM.TraceExtension.Atlas.Global
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀ i,Vane C i}{Z:Arch C}
variable (h₁:Scribe X J V Z F.sector 𝓛 F.room.kernel H)

section uniform
variable {n:ℕ}
-- same horizon.Receptor.Presents derivatives
lemma jets (K:S.Hierarchy)(H:(Bel C.book).Hierarchy)(P:ℝ→change S 4)(ht:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m) (v: Fin n→ (Bel C.book).Field 4)(k:ℕ)(s:Set (Points n))(hs:IsCompact s)(hz:s⊆conf n) (ε:ℝ)(he:0<ε):∀ᶠ r in trail,∀ x∈s,
     ‖iteratedFDeriv ℝ k (fun q=> S.classMoment S (fun _=>4) (r • q) (fun j=>P r (v j))) x-iteratedFDeriv ℝ k (fun q=>(F₀).classMoment (F₀) (fun _=>4) q v) x‖<ε:=by
    let I:=Fin n→ PegC C 4; let M:= PoleC C 4; let r(i:I):= ∏ j: Fin n, (M.repr (v j)) (i j); let V(i:I):= M ∘ i; let c:= ∑ i:I,‖r i‖; have hc:0≤c:= Finset.sum_nonneg fun _ _=>norm_nonneg _
    have hh (A:MultilinearMap ℂ (fun _ : Fin n=> (Bel C.book).Field 4) ℂ): A v= ∑ i:I,r i • (A (V i)):=by
       conv_lhs=> rw [show v= fun j=> ∑ i, M.repr (v j) i • M i from funext (fun i=> ((PoleC C 4).sum_repr _).symm)]
       rw[MultilinearMap.map_sum]; exact Finset.sum_congr rfl (fun i _=> A.map_smul_univ _ _)
    obtain ⟨m,hk,hp,hN,hv⟩:= ((eventually_ge_atTop n).and ((eventually_ge_atTop k).and ((size_ascends.eventually (Work.A05.compact_fits hs hz)).and ((cost_clears.const_mul c).eventually (gt_mem_nhds (by simpa using (show 0 < ε from he))))))).exists
    filter_upwards[ht m,self_mem_nhdsWithin] with t ht hr x hx; have hp': k < m+1:=hp.trans_lt (Nat.lt_succ_self m); let j:Fin (m+1):=⟨n,Nat.lt_succ_of_le hk⟩
    have hp: t • x∈conf n:= Work.A05.smul_conf (show 0<t from hr) (hz hx)
    let Y(p:Points n):= (S.classMoment S (fun _=>4) (t • p)).compLinearMap (fun _=> (P t).toLinearMap); let U(p:Points n):=(F₀).classMoment (F₀) (fun _=>4) p
    have hm (i:I):ContDiffAt ℝ k (fun p=> Y p (V i)) x:= (((S.class_smooth S K.smooth (fun j:Fin n=> ⟨4,P t (V i j)⟩)).contDiffAt ((conf_open _).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)).comp x (contDiffAt_id.const_smul t)
    have hT(i:I):ContDiffAt ℝ k (fun p=> U p (V i)) x:= (((F₀).class_smooth (F₀) H.smooth (fun j:Fin n=> ⟨4,V i j⟩)).contDiffAt ((conf_open _).mem_nhds (hz hx))).of_le (WithTop.coe_le_coe.mpr le_top)
    let f (i:I)p:= r i • Y p (V i); let g (i:I)p:= r i • U p (V i)
    change ‖iteratedFDeriv ℝ k (fun p=> Y p v) x-iteratedFDeriv ℝ k (fun p=> U p v) x‖ < ε
    rw [show (fun p=>Y p v)=(fun p=>∑ i:I, f i p) from funext fun i=>hh (Y i),show (fun p=>U p v)=(fun p=>∑ i:I,g i p) from funext fun i=>hh (U i),iteratedFDeriv_fun_sum_apply (f:=f) (fun i _=> (hm i).const_smul _),iteratedFDeriv_fun_sum_apply (f:=g) (fun i _=> (hT i).const_smul _),← Finset.sum_sub_distrib]; apply lt_of_le_of_lt ((norm_sum_le ..).trans ?_) (show c*costHint m<ε from hv)
    unfold c;rw[Finset.sum_mul]; refine Finset.sum_le_sum fun i _=>?_; unfold f g; simp_rw[iteratedFDeriv_const_smul_apply' (hm i),iteratedFDeriv_const_smul_apply' (hT i),← smul_sub,norm_smul]; exact mul_le_mul_of_nonneg_left (ht j i (⟨k,hp'⟩ : Fin (m+1)) x (hN hx)) (norm_nonneg _)
end uniform
end YM.Trace.Pilot
