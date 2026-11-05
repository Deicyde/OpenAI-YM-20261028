import YM.MergeProof.Gallery
import YM.MergeProof.Hens
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-! repeated segments, no top rebind if multiply by regular exponent at intermediate level (grill). Same estimate will license future. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac  Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V]{J:Census V}{G:Gauge}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
section
variable {n:Side}{x e f t u v:ℝ}{a:V→ℝ}{R:Rep G n}
variable {o:V→Site n}{F L:V→ Config G n→ℂ}{κ:V→Res G n}{g: V→ℕ → Config G n→ℂ}{X: Config G n→Poly J}
lemma Served.relay (h: Served R F (fun i=>profile R.activities (g i)) X o a x e) (hi:∀ i,Dominated (g i))(hr:R.activities.Valid R.p f t)(U) : (∀ i,(X U).part (J.fire i)=coin R (F i) (g i) U) ∧ (X U).part J.quiet=R.eval U:=by
    obtain ⟨H,K,hP,_,_,rfl⟩:= h
    let p v j:= profile R.activities (g v) j; let Z i U:= bar R.activities J U i+Mach J (fun v=>p v i U) + K i U; let Y U:= Mach J (fun v=> F v U) + ∑ i,H i U
    have hh : (Y U).part J.quiet=0:=by unfold Y; simp_rw [Poly.part_plus,mute,Poly.part_sum, fun i=>hop J _ (show rises (H i U) from (hP.exp i).2 U),sum_const_zero,add_zero]
    have ht(i): (Z i U).part J.quiet=profile R.activities (fun j=> Complex.ofReal ∘ R.activities.K j) i U:=by unfold Z; simp_rw [Poly.part_plus,mute,hop J _ (show rises (K i U) from (hP.flag i).2 U),add_zero]; simp [bar,Poly.bead] -- Poly.bead?
    change (∀ i,(play R J Z Y U).part (J.fire i)=_) ∧ _; refine ⟨fun v=>?_,bronze R J Z Y U hr ht hh⟩
    have he(i): (Z i U).part (J.fire v)=p v i U:=by unfold Z; simp_rw [Poly.part_plus,sing,hop₁ J _ (show rises (K i U) from (hP.flag i).2 U),add_zero]; simp [bar,Poly.bead,J.fire_hot v]
    rw [beach R J Z Y U g hr ht hh v ((hi v).summable U) he]; unfold coin; unfold Y; simp_rw [Poly.part_plus,sing,Poly.part_sum,fun i=> hop₁ J _ (show rises (H i U) from (hP.exp i).2 U),sum_const_zero,add_zero]

def couple (X: Config G n→Poly J)(L: V→ Config G n→ℂ)(U: Config G n):= X U*Poly.pass (Mach J (fun i=>L i U))
lemma Served.jelly (h: Served R F κ X o a x e) : Served R (F+L) κ (couple X L) o a x e:=by
   obtain ⟨H,K,h,he,hH,rfl⟩:=h
   refine ⟨H,K,h,he,hH,?_⟩
   funext U; unfold restore couple; let u:= Mach J (fun i=>F i U)+ ∑ i,H i U; let l:= Mach J (fun i=>L i U); have hp : Mach J (fun i=>(F+L) i U)+ ∑ i,H i U=u+l:=by
     have he : Mach J (fun i=>(F+L) i U)=Mach J (fun i=> F i U)+l:=by
        unfold l; unfold Mach; simp only [Pi.add_apply,Extra.Trajectories.send_add, sum_add_distrib]
     rw [he]; unfold u; abel
   rw [hp,pass_add (show u.part J.quiet=0 from by unfold u; simp_rw [Poly.part_plus,mute,Poly.part_sum, fun i=>hop J _ (show rises (H i U) from (h.exp i).2 U),sum_const_zero,add_zero]) (show l.part J.quiet=0 from mute _ _), smul_mul_assoc]
   apply congr_arg; unfold u l; rw [mul_right_comm]
end
end YM.MergeProof.Accent
