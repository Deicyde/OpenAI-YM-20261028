import YM.TraceExtension.Perfect.Stove

/-!
# Uniform local push columns for centered insulin
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {W:Type*}{I:W→Type} [∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]
    {X Y':Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y'][NormedSpace ℝ Y']{N:ℕ}
lemma Calm.mapsF {D:∀ w,I w→ℕ}{f:∀ w,Rays (I w)→ X} (h:Calm D f N)(B:∀ (_:W), X→L[ℝ] Y'){S:ℝ}(he:0≤S)(hp:∀ w x, ‖B w x‖ ≤ S*‖x‖): Calm D (fun w=> B w ∘ f w) N:=by
 obtain ⟨a,C,ha,hC,H⟩:=h.shape; refine ⟨fun w=>(B w).contDiff.contDiffAt.comp _ (h.velvet w),a,S*C,ha,mul_nonneg he hC,fun i j hj=>?_⟩
 apply le_trans ?_ (mul_le_mul_of_nonneg_left (H i j hj) he); unfold cost leaf; rw [(B i).iteratedFDeriv_comp_left (h.velvet i) le_top,Finset.mul_sum]; refine Finset.sum_le_sum fun p _=>?_
 rw [mul_left_comm S]; exact mul_le_mul_of_nonneg_left (hp _ _) (spot_pos ..).le

namespace Lot
variable {P:Patch}{Y:KernelChoices} {G : Gauge}{p:Clip}{α D β v:ℝ} (L:W→ Lot G P Y p α D)
set_option quotPrecheck false
variable (K:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1))
    (o:∀ w,Site (L w).f)(hb:0<β)(hp: ∀ w,(K w).strip β (v/P.L.val))
local notation "K!"=>fun w=> installed (L w).s.ratio (K w)
local notation "F!"=>fun w=>fresh (L w).wood (L w).ρ (K! w) (o w)
include hb hp
lemma svata_c (e:∀ w,Site (L w).c)(j:G.ColorIndex): Calm (fromV L (fun w=> (L w).s.ratio.embed (e w))) (fun w x=> (frameLog ((F! w x).2)) (e w,vac,j)) N:=by
 have he:=(tailor_c L K o hb hp e (N:=N)).prop G.plog (a:=1) G.plog_diff (fun w=>by dsimp only; rw [fresh_zero (L w).law]; rfl)
 exact he.maps (EuclideanSpace.proj j)
lemma harn (e:∀ w,Site (L w).c): Calm (fromV L (fun w=>(L w).s.ratio.embed (e w))) (fun w x=>invite (P:= (L w).s.patch) (L w).patch (pianist (L w).s (e w) (barTag (F! w x)))) N:=by
 classical
 apply Calm.piP; rintro (⟨k,z,a,i⟩|(⟨k,u,i⟩|⟨k,z⟩)); let R w:=(L w).s.ratio; let p(w):= R w|>.embed (e w)
 · simp_rw [host_l]
   cases k
   swap; · exact Calm.frozen _ (0:ℝ)
   let i' w: Plaza (L w).s.patch:= (L w).patch.symm ▸ z
   let b w := wrap (L w).f (i' w).val+p w; let g(w):Body 1 (L w).f:=(b w,a)
   have hq(w):separation (b w) (p w) ≤ spaceFee P:=by
         rw [separation_comm]; exact (space_check (i' w) (p w)).trans_eq (congr_arg _ (L w).patch)
   apply (moss (N:=N) L (tailor_content L K o hb hp g) (spaceFee P) hq|>.maps (EuclideanSpace.proj i)).near
   intro w; exact Eventually.of_forall fun x=> edge_parts (content ((F! w x).1)) (g w) i
 · simp_rw [host_r]; cases k; swap; · exact Calm.frozen _ (0:ℝ)
   let u' w:=(u.map (fun a=> e w+step a)).getD (e w)
   let R w:=(L w).s.ratio; let p(w):= R w|>.embed (e w)
   refine moss L (x:=fun w=> (R w).embed (u' w)) (svata_c L K o hb hp u' i) P.L.val (fun w => ?_)
   have hx : (R w).count=P.L:=congr_arg Patch.L (L w).patch
   apply le_trans (Next.Free.scaled_root (R w) (u' w) (e w)) (le_trans (Nat.mul_le_mul_left _ (show separation (u' w) (e w)≤1 from ?_)) ?_)
   · unfold u'; cases u with
     | none=> simp
     | some a=> simp only [Option.map,Option.getD]; rw [separation,add_comm (e w),add_sub_cancel_right];exact pdist_step _
   rw [Nat.mul_one]; exact (congr_arg Subtype.val hx).le
 simp_rw [host_r]; cases k<;> exact Calm.frozen _ (0:ℝ)

include L
omit hp hb in
lemma sized (w:W): P.Branches Y G:=by
 exact (congr_arg₂ (fun (x:Patch) y=> x.Branches y G) (L w).patch (L w).kit)|>.mp (L w).size.1

lemma polarized (t:∀ w,(L w).s.Choices) (i:∀ w,Lines G (L w).f 1)(z:∀ w,Site (L w).c)(j:Axis)(k:G.ColorIndex) :
    Calm (fromV L (fun w=> (L w).s.ratio.embed (z w))) (fun w x=> fineRelay (L w).s (t w) (F! w x) (desk (i w)) (z w,coord j,k)) N:=by
 rcases isEmpty_or_nonempty W with h|h; · exact ⟨fun w=> isEmptyElim w,1,1,zero_lt_one,zero_le_one,fun w=> isEmptyElim w⟩
 obtain ⟨w₀⟩:=h
 let U w := invite (L w).patch (pianist (L w).s (z w) (outTest (desk (i w))))
 let F := tuneP (P:=P) j k
 let A v:= fderiv ℝ F v
 let Λ (w:W): (BassInput G P→L[ℝ]ℝ)→L[ℝ]ℝ:= ContinuousLinearMap.apply _ _ (U w)
 have hp':= sized L w₀
 have hf(w): ‖U w‖ ≤ 1:=by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun x=>?_); unfold U
    rcases x with ⟨t,x,i⟩|y; rw [host_l]; exact bass_tag ..; rw [host_r]; exact bass_tag ..
 have he:= (harn L K o hb hp z (N:=N)).prop A (a:=0) ((tune_jet hp' j k).fderiv_right (m:=ω) (by simp)) (fun w=>by dsimp only; rw [fresh_zero (L w).law]; rw [show barTag (c:=(L w).c) (f:=(L w).f) (G:=G) 1=0 from by simp [barTag], map_zero,map_zero])
 refine (he.mapsF Λ (S:=1) zero_le_one ?_).near (fun w=>?_)
 · intro w x; rw [one_mul]; exact (x.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (hf w))
 filter_upwards [tunes_the _ (t w) (L w).size.1 (L w).price (fresh_thaw (F:=(L w).wood) (L w).law (o w) (W:= installed _ (K w))) (fresh_zero (L w).law _) (desk (i w)) (z w) j k] with x hx
 dsimp only [Function.comp_apply]; change fderiv ℝ F (invite _ _) (U w)= _
 unfold U F; rw [tuneMove]; exact hx.symm
end Lot
end YM.Trace.Perfect
