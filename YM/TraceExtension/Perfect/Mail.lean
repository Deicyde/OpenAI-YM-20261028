import YM.TraceExtension.Perfect.Merry
import YM.TraceExtension.Perfect.Relay
import YM.Push.LOOP_COEFFICIENT.Tangent
import YM.Work.E03

/-! # Variation carriers for Ward flux. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{S:StepData c f}{G:Gauge}{p u:Clip}{M R:PathData G}{η α D:ℝ}
lemma cant_arm (k : Coats G c)(V:Config G c)(x:BaseSites G c) :
    armor k (cant V x)= cant (Lattice.gauge k V) (armorG k x):=by
  apply edgeColor.injective; funext i; rw [armor_at,cant_at,cant_at,armorG_at,armorG_at]; simp [map_sub, ← G.adjoint_mul, Lattice.gauge]
variable (S)

def bagWalk (a b:Site f):= route 0 (lift (b-a)) 1
lemma bag_there (a b:Site f): stop a (bagWalk a b)=b:=by
 have ht:= Work.E03.stop_route a 0 (lift (b-a)); rw [map_zero,add_zero,wrap_lift,add_sub_cancel] at ht;exact ht

def road (U:Joint G c f)(x:Site c)(y:Site f):G.El:=U.2 x * travel U.1 (S.ratio.embed x) (bagWalk (S.ratio.embed x) y)
lemma road_one (x:Site c)(y:Site f): road S (1:Joint G c f) x y=1:=by
 simp [road]
 have hh : travel (input G f 0) (S.ratio.embed x) (bagWalk (S.ratio.embed x) y)=1:=by unfold input; rw [map_zero]; exact Push.stroll_zero ..
 rw [input_zero] at hh; exact hh
lemma road_home (k : Coats G f)(u : Coats G c)(U:Joint G c f)(x:Site c)(y:Site f): road S (wages S k u U) x y=u x*road S U x y*(k y)⁻¹:=by
 simp only [wages,road,travel_gauge,bag_there]; group

def edgeOf (b:Body 1 f): Edge (Site f) := (b.1,axisEquiv.symm b.2)
def armament (U:Joint G c f): Link G f→L[ℝ] BaseSites G c:= LinearMap.toContinuousLinearMap
   { toFun z := gaugeColor.symm (fun x => ∑ i:Body 1 f, fixRoot S (x,vac) i • G.adjoint (road S U x i.1) (edgeColor z (edgeOf i)))
     map_add' v w :=by
        change gaugeColor.symm _ = gaugeColor.symm _+gaugeColor.symm _; rw [← map_add];congr 1; ext1 x; simp only [map_add,Pi.add_apply,smul_add,Finset.sum_add_distrib]
     map_smul' r v:=by
        change gaugeColor.symm _ = r • gaugeColor.symm _; rw [← map_smul];congr 1;ext1 x; simp only [map_smul,Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm .. }
lemma armament_point (U:Joint G c f)(x:Link G f)(v:Site c): gaugeColor (armament S U x) v=∑ i:Body 1 f, fixRoot S (v,vac) i • G.adjoint (road S U v i.1) (edgeColor x (edgeOf i)) := by
 rw [show armament S U x=gaugeColor.symm _ from rfl,gaugeColor.apply_symm_apply]
lemma edge_parts (x:Link G f)(i:Body 1 f)(k:G.ColorIndex): edgeColor x (edgeOf i) k= x (i.1,i.2,k):=by rcases i with ⟨a,i⟩; obtain ⟨i,rfl⟩:= axisEquiv.surjective i; unfold edgeOf; rw [axisEquiv.symm_apply_apply i];rfl
lemma armament_one (x:Link G f): armament S 1 x=uniformM (fixRoot S) x:=by
 apply gaugeColor.injective; funext i; rw [armament_point]; ext j
 simp_rw [road_one,G.adjoint_one]; let E:= EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) j
 change E _ = _; rw [map_sum]; simp_rw [map_smul]
 change (∑ k:Body 1 f, fixRoot S (i,vac) k * edgeColor x (edgeOf k) j) = (fixRoot S *ᵥ parts G 1 (arm G f 1 x) j) (i,vac); apply Finset.sum_congr rfl; intro k _; rw [edge_parts]; rfl
lemma armament_turn (x:Link G f)(U:Joint G c f)(k : Coats G f)(u:Coats G c):
   armorG u (armament S U x)=armament S (wages S k u U) (armor k x):=by
   apply gaugeColor.injective;funext i; rw [armorG_at,armament_point,armament_point,map_sum]; simp_rw [map_smul]; refine Finset.sum_congr rfl fun j _=> ?_; simp only [armor_at,← G.adjoint_mul, road_home,edgeOf]; simp

def shuttle (t:S.Choices)(U:Joint G c f)(V:Config G c): Link G f→L[ℝ] Link G c:= fineRelay S t U + cant V ∘L armament S U
variable {S} (t:S.Choices){U:Joint G c f}(V:Config G c)
lemma shuttle_turn (h:S.patch.Branches S.kernel G)(k:Coats G f)(u:Coats G c)(hv : Teller S t p M 1 U)(hb:Teller S t p M 1 (wages S k u U))(x:Link G f):
   shuttle S t (wages S k u U) (Lattice.gauge u V) (armor k x)=armor u (shuttle S t U V x):=by
  let Q:=worn S t 1 U
  let L:=wages S k u U; let I:=worn S t 1 L; let B:=armUp k u
  have hP : I ∘ B=ᶠ[𝓝 0] armor u ∘ Q:= quota_k h t k u U hv
  have hx:=hP.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp 0 (by rw [map_zero]; exact hb.wist.differentiableAt (by simp)) B.differentiableAt, fderiv_comp 0 (armor u).differentiableAt (hv.wist.differentiableAt (by simp)),(armor u).fderiv,B.fderiv,map_zero] at hx
  change fderiv ℝ I 0 (armor k x,0)+_=armor u ((fderiv ℝ Q 0 (x,0))+cant V (armament S U x))
  have hB: B (x,0)=(armor k x,0):= Prod.ext rfl (map_zero (armorG u))
  rw [map_add, cant_arm, armament_turn,← hB]; exact congr_arg (·+cant _ _) (DFunLike.congr_fun hx (x,0))
lemma shuttle_zero (h:S.patch.Branches S.kernel G)(hp:Teller S t p M 1 (1:Joint G c f))(x:Link G f):
    shuttle S t (1:Joint G c f) 1 x= uniformM (mean S) x:=by
    let L:=worn S t 1 (1:Joint G c f); let A:= (x,(0:BaseSites G c)); have he (v:ℝ): L (v • A)= content (S.prediction (input G f (v • x)) t):=by
       simp only [L,worn,ribbon,atire,dress_one]
       simp [A,Stationary.extend,gauge_one,show S.prediction (1:Config G f) t=1 from funext (fun _ => Push.settled S h _ t)]
    have hv : fineRelay S t 1 x=uniformM (probe S) x:=by
       change fderiv ℝ L 0 A=_; apply (Push.side L (hp.wist.differentiableAt (by simp)) A).unique
       simp_rw [he]; apply ray_content
       · rw [zero_smul,input_zero]; exact funext (fun i => Push.settled S h i t)
       intro i; simp_rw [input,map_smul]; exact Push.prices S h i t _
    rw [shuttle, _root_.add_apply,hv,ContinuousLinearMap.comp_apply,armament_one,cant_one,first_uniform]; funext i
    simp only [Pi.add_apply,Pi.neg_apply]; change (probe S*ᵥ parts G 1 (arm G f 1 x) i.2.2) (i.1,i.2.1)+_= _
    rw [probe,Matrix.add_mulVec, ← mulVec_mulVec,Pi.add_apply]; exact add_neg_cancel_right ..

end YM.Trace.Perfect

namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{S:StepData c f}{G:Gauge}{p u:Clip}{M R:PathData G}{η α D:ℝ}
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{A:X→Joint G c f}{V:X→Config G c}
lemma steering (t:S.Choices) (w:S.patch.Branches S.kernel G) (x:X→ Link G f) (hx:ContDiffAt ℝ ω x 0)(p:Thaw A 0)(hA:A 0=1)(q:Army V 0):
   ContDiffAt ℝ ω (fun v=> shuttle S t (A v) (V v) (x v)) 0:=by
  have hP := Work.F05.curve_partial (F:=fun v=> worn S t 1 (A v)) (worn_wear w t A p hA)
  let y v := fineRelay S t (A v) (x v)
  have hu: ContDiffAt ℝ ω y 0:= (hP.comp (f:=fun v:X=>(v,0)) 0 (by fun_prop)).clm_apply (show ContDiffAt ℝ ω (fun i:X=> (x i,(0:BaseSites G c))) 0 from hx.prodMk contDiffAt_const)
  let C v := armament S (A v) (x v); let b v := gaugeColor (C v)
  have hZ : ContDiffAt ℝ ω b 0:=by
    apply contDiffAt_pi.mpr; intro i
    change ContDiffAt ℝ ω (fun v=> gaugeColor (armament _ _ (x v)) i) 0
    simp_rw [armament_point]; apply ContDiffAt.sum; intro j _
    refine (show ContDiffAt ℝ ω (fun _ : X=> fixRoot S (i,vac) j) 0 from contDiffAt_const).smul (Push.Loops.adjoint_diff (u:=fun v=> road S (A v) i j.1) ?_ (show ContDiffAt ℝ ω (fun v=> edgeColor (x v) (edgeOf j)) 0 from contDiffAt_pi.mp (edgeColor.contDiff.contDiffAt.comp _ hx) _))
    unfold road; simp_rw [G.mat_mul]; refine ContDiffAt.mul (p.2 _) ?_
    suffices ∀ k a, ContDiffAt ℝ ω (fun z=> G.mat (travel (A z).1 a k)) 0 from this ..
    intro k; induction k with
    | nil=> exact fun _=> contDiffAt_const
    | cons u k IH=> intro a; simp_rw [travel,G.mat_mul]; refine ContDiffAt.mul ?_ (IH _); unfold Step.read; split; · exact p.1.inv _
                    exact p.1 _
  let F v:= cant (V v) (C v)
  have hL : ContDiffAt ℝ ω (edgeColor ∘ F) 0:=by
     apply contDiffAt_pi.mpr; intro i; change ContDiffAt ℝ ω (fun v=> edgeColor (cant (V v) (C v)) i) 0
     simp_rw [cant_at]; exact (contDiffAt_pi.mp hZ i.1).sub (Push.Loops.adjoint_diff (q i) (contDiffAt_pi.mp hZ _))
  have hf : ContDiffAt ℝ ω F 0:= by
      rw [show F=edgeColor.symm ∘ (edgeColor ∘ F) from funext (fun z=> (edgeColor.symm_apply_apply (F z)).symm)]
      exact edgeColor.symm.contDiff.contDiffAt.comp _ hL
  exact hu.add hf

end YM.Trace.Perfect
