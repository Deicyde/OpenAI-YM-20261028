import YM.MultipleContact.Multi.Evidence
/-! Safe word changes along internal coordinates of a single comparable cluster within a strict multicenter patch. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
noncomputable section
namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {b:ℕ}{n d: Fin b → ℕ}
variable [∀i:Fin b,Inhabited (Fin (n i))]
variable {K:Finset (Fin b)} {p:Fin b → Mode}
variable {V:∀i:Fin b,Fin (n i) → S.Tag}{D:∀i:Fin b,Detector S (d i)}{z:Fin b→ E4}
variable {h u:∀i:Fin b,Fin (n i) →E4}{w:∀i:Fin b,S.Field (d i)}
def planted (p:Fin b→Mode) (V:∀i,Fin (n i) → S.Tag)(D:∀i,Detector S (d i))(z:Fin b→E4)(w:∀i,S.Field (d i)) (h:∀i,Fin (n i) → E4):Script.Grammar (Script.Alpha S):=
     ∏ i:Fin b,scaledBranch (p i) (V i) (D i) 1 (z i) (h i) (w i)

lemma clearBranch {i:Fin b}(a:ℝ)(ha:0<a) (hp:p i ≠ .fused → Injective (h i))(hsize:p i ≠ .fused → ∀k,‖h i k‖ ≤ a): Secure S (Metric.closedBall (z i) a) (scaledBranch (p i) (V i) (D i) 1 (z i) (h i) (w i)):=by
      let Q:=Metric.closedBall (z i) a
      have ht(u:S.Field (d i)): Secure S Q (insertion S (z i) u):=insertion_secure S u (Metric.mem_closedBall_self ha.le)
      have hh(j:p i≠.fused):Secure S Q (Scene.packet S (V i) (h i) (z i)):= Scene.packet_secure S _ _ (hp j) (by rintro x ⟨s,rfl⟩;simpa only [Q,Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left] using (hsize j s))
      cases hr:p i <;> unfold scaledBranch
      · exact Secure.diff S (Secure.scalar S (hh (hr.symm ▸ (by decide))) _) (ht _)
      exacts [hh (hr.symm ▸ (by decide)),ht _]

lemma petals (a:ℝ)(ha:0<a) (hi:∀i:Fin b,i∈K → p i≠ .fused → Injective (h i)) (hs:∀i:Fin b,i∈K→ p i≠.fused→∀k,‖h i k‖ ≤ a) (hf:Drama.far a z) :
       Secure S (⋃i∈ K,Metric.closedBall (z i) a) (∏ i∈K,scaledBranch (p i) (V i) (D i) 1 (z i) (h i) (w i)):=by
       refine secure_product S (fun i hi'=>clearBranch a ha (hi i hi') (hs i hi')) ?_
       intro i h' j h'' hij
       apply Set.disjoint_left.mpr
       intro x hx hx'
       apply (hf i j hij).not_ge; rw [← dist_eq_norm]; exact (dist_triangle (z i) x (z j)).trans (by rw [dist_comm (z i)]; nlinarith only [Metric.mem_closedBall.mp hx,Metric.mem_closedBall.mp hx',show (0:ℝ) ≤ a from ha.le]) -- a shadow syntax

lemma precise_rod (Plan : DiffPlan S){a:ℝ}(ha:0<a)(hf:Drama.far a z){i:Fin b}(hi:i∉K)
    (hb:∀l:Fin b,l∈K → p l≠.fused → Injective (h l) ∧ ∀k,‖h l k‖ ≤a) (r:Fin (n i) → E4)(hu:∀k,‖r k‖≤ a):
    Precise S (∏ l∈K, scaledBranch (p l) (V l) (D l) 1 (z l) (h l) (w l)) (Set.range (fun t=>z i+r t)):= by
        refine precise_secure S ?_ (petals a ha (fun i hi h=>(hb i hi h).1) (fun i hi h=>(hb i hi h).2) hf)
        apply Set.disjoint_left.mpr
        intro x hx hx'
        obtain ⟨l,hK,hL⟩:=Set.mem_iUnion₂.mp hx
        obtain ⟨k,hx'⟩:=hx'
        have h: ‖x-z l‖≤ a:= Metric.mem_closedBall.mp hL; have h':‖z i-x‖≤a:=by rw [← hx', norm_sub_rev,add_sub_cancel_left];exact hu k
        exact (hf i l (fun h=>hi (h.symm ▸ hK))).not_ge (by linarith only [h,h',norm_sub_le_norm_sub_add_norm_sub (z i) x (z l),ha])
open Line
variable {a h₀:ℕ}
variable {Plan:DiffPlan S}(H:S.Hierarchy)(hP:Plan.Derivatives S)
include H hP
lemma branch_deriv {V:Fin a→ S.Tag}{D:Detector S h₀}{u:S.Field h₀}{x:Fin a→E4}{z₀:E4} (b:Axis)(j:ℝ)(k:Fin a)
    (p':Grammar (Alpha S)) (t:ℝ) (hp:Precise S p' (Set.range (moved z₀ x k b j t))) (hX:Injective (Cord.polar (k,b) x j t))(hy:∀e∈D.probes, ∀ i:Fin a,∀ l:Fin (Exterior.n e),moved (e.point 0) x k b j t i ≠ e.point l.succ):let v'(l:ℕ):= tags V Plan k b l; ∀ l:ℕ,
    HasDerivAt (fun s:ℝ=>(j^l:ℝ) • evaluation S (scaledBranch .signed (v' l) D 1 z₀ (Cord.polar (k,b) x j s) u * p')) ((j^(l+1):ℝ) • evaluation S (scaledBranch .signed (v' (l+1)) D 1 z₀ (Cord.polar (k,b) x j t) u * p')) t:=by
       rintro v' l
       have hC: ∀s,Cord.polar (k,b) x j s=moved 0 x k b j s:=fun s=> by unfold polar moved; ext1 i; simp only [zero_add,streak,inc,mul_smul]
       have he(v s):scaledBranch .signed v D 1 z₀ (Cord.polar (k,b) x j s) u= residue S D v (moved 0 x k b j s) z₀:=by unfold scaledBranch Scene.residue; rw [hC]; simp
       simp_rw [he]
       have ht l: v' (l+1)=update (v' l) k (Ward.rise Plan b (v' l k)):= by unfold v' Line.tags; rw [update_self,Function.update_idem]; rfl
       rw [pow_succ,← smul_smul,ht]
       exact (residue_deriv H hP (p:=p') D (v' l) z₀ x k b j t ((hC t) ▸ hX) hp hy).const_smul (j^l)

lemma deform (l:ℕ)(k:Fin b)(i:Fin (n k) × Axis)(hp:p k=.signed)(j:ℝ)(x:Fin (n k)→E4)(t:ℝ)(a:ℝ)(ha:0<a)(hf:Drama.far a z) (hb : ∀ i:Fin b, i≠k→ p i ≠ .fused → Injective (h i) ∧ ∀s,‖h i s‖ ≤a)
   (hu:∀s,‖Cord.polar i x j t s‖≤a)(he:Injective (Cord.polar i x j t))(hy:∀e∈(D k).probes, ∀ s:Fin (n k),∀ l:Fin (Exterior.n e),moved (e.point 0) x i.1 i.2 j t s≠ e.point l.succ):
      let V' l:= Function.update V k (tags (V k) Plan i.1 i.2 l); let f (v:∀i,Fin (n i)→ S.Tag)(t:ℝ):= evaluation S (planted p v D z w (Function.update h k (Cord.polar i x j t))); HasDerivAt (fun s=>(j^l:ℝ) • f (V' l) s) ((j^(l+1):ℝ) • f (V' (l+1)) t) t:=by
          intro V' f
          let K:=(Finset.univ:Finset (Fin b)).erase k
          let α (u:∀i:Fin b, Fin (n i) → S.Tag):= ∏ i∈K,scaledBranch (p i) (u i) (D i) 1 (z i) (h i) (w i)
          have use_f(u s): f u s=evaluation S ((scaledBranch .signed (u k) (D k) 1 (z k) (Cord.polar i x j s) (w k)) * α u):= by
              apply congr_arg (evaluation S); unfold planted α K; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]; simp only [update_self,hp]
              congr 1; exact Finset.prod_congr rfl (fun j hj=> by rw [update_of_ne ((Finset.mem_erase.mp hj).1)] )
          have hEq (l): α (V' l) = α V:= by unfold α K V'; exact Finset.prod_congr rfl fun j hj=> by rw [update_of_ne (Finset.mem_erase.mp hj).1] -- parens
          simp_rw [use_f,hEq]; dsimp only [V']; simp only [update_self]
          refine branch_deriv H hP i.snd j i.fst (α V) t ?_ he hy l
          rw [show moved (z k) x i.1 i.2 j t=(fun s=>z k+Cord.polar i x j t s) from (by unfold moved polar; ext s; simp only [streak,inc,mul_smul])]
          apply precise_rod Plan ha hf (i:=k) (K:=K) (Finset.notMem_erase k _) (fun i hi=> hb i ((Finset.mem_erase.mp hi).1))
          exact hu
end YM.MultipleContact.Joins
