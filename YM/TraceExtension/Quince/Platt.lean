import YM.TraceExtension.Foundation.Dilate
import YM.TraceExtension.Quince.Apace
set_option autoImplicit false
noncomputable section
namespace YM.Trace
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Push Local Planned.PrimaryIntegral295 PPX Next Next.Free Next.Foundations WardBin Bid StressFlux
open Extra.Histories
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{d n:ℕ}{F:Frame G d}
section dark
abbrev archV:Signed:=⟨Equiv.refl _,fun _=>true⟩
lemma archν (x:E4) : Ortho.move archV.ortho⁻¹ x = -x :=by ext1 i; rw [signed_move_inv]; simp [archV,sign]
lemma litr (A:Taylor G n) : Taylor.turn archV.ortho A = ((-1:ℝ)^(n+2)) • A:=by
    apply Taylor.value_ext; funext i z; change (Taylor.turn archV.ortho A).value (archV.perm i) z = ((-1:ℝ)^(n+2)) • _; rw [signed_turn_value,archν]; unfold Taylor.value; rw [show -z=(-1:ℝ) • z from by simp, Tensor.homogeneous, smul_smul,pow_succ' _ (n+1)];rfl
lemma arc_code (J:Jet G): axesMove (fun i=>Taylor.turn archV.ortho⁻¹) J=scaleJet J (-1):=by
   ext1 k; change Taylor.turn archV.ortho⁻¹ _=_; have hA := litr (Taylor.turn archV.ortho⁻¹ (J k)); rw [← Taylor.turn_mul,mul_inv_cancel,Taylor.oneTurn] at hA
   let y:=(-1:ℝ)^(k+2); change _= y • _
   conv_rhs=>rw [hA]; rw [smul_smul,show y*y=1 from by unfold y; rw [← mul_pow];simp,one_smul]
   rfl
lemma tier_basis (F:Frame G d)(i:F.Index): tier (F.grades i).1 (F.basis i).val=(F.basis i).val:=by
   have he:MvPolynomial.IsWeightedHomogeneous generation (F.basis i).val (F.grades i).1:=fun x hx=> (by have h:= (pure_grade _ _).1 (F.pure i) hx; rw [weight_slot] at h; exact congr_arg Prod.fst h)
   exact he.weightedHomogeneousComponent_same
lemma basis_turn (F:Frame G d)(i:F.Index): tensor archV.ortho (F.basis i) = ((-1:ℝ)^(F.grades i).1) • (F.basis i):=by
   let T:= F.basis i; let n:=(F.grades i).1
   apply label_ext; intro J; have he(t:ℝ):read (scaleJet J t) (tensor archV.ortho T).val=read (scaleJet J (-t)) T.val:=by
       change read _ (changed _ _) = _; rw [eval_changed,show changedJet _ _=scaleJet (scaleJet J t) (-1:ℝ) from arc_code _,show scaleJet (scaleJet J t) (-1)=scaleJet J (-t) from funext fun k=>by simp only [scaleJet,smul_smul,← mul_pow, neg_mul,one_mul]]
   -- tensor also via deriv_read ht. scale composition derivative k times
   have hz : iteratedDeriv n (fun t=> read (scaleJet J (-t)) T.val) 0=(-1:ℝ)^n • iteratedDeriv n (fun t=> read (scaleJet J t) T.val) 0:=by
       let f(t):= read (scaleJet J t) T.val; change iteratedDeriv n (fun t:ℝ=>f (-t)) 0=(-1:ℝ)^n • iteratedDeriv n f 0; rw [iteratedDeriv_comp_neg]; simp
   apply smul_right_injective ℂ (r:=((n.factorial):ℝ)) (by positivity); rw [Submodule.coe_smul_of_tower,read_smul]
   have ht:tier n (tensor archV.ortho T).val=(tensor archV.ortho T).val:=by
        have hM : tensor archV.ortho T∈Grade (F.grades i):= by rw [← gradePart_self T _ (F.pure i), ← gradePart_turn]; exact gradePart_mem ..
        have hk:MvPolynomial.IsWeightedHomogeneous generation (tensor archV.ortho T).val n:=fun x hx=> (by have h:= (pure_grade _ _).1 hM hx; rw [weight_slot] at h; exact congr_arg Prod.fst h)
        exact hk.weightedHomogeneousComponent_same
   change ((n.factorial):ℝ) • read _ (tensor archV.ortho T).val= ((n.factorial):ℝ) • ((-1:ℝ)^n • read _ T.val); rw [smul_comm ((n.factorial):ℝ),← ht,← show tier n T.val=T.val from tier_basis F i, ← deriv_read,← deriv_read, funext he,hz]
lemma orbit_sign (F:Frame G d)(i:F.Index): F.act archV.ortho (Size.axis F i) = ((-1:ℂ)^(F.grades i).1) • Size.axis F i:=by
   rw [← show F.coords (F.basis i)=Size.axis F i from F.coords_basis i,F.act_coords,basis_turn]; rw[← IsScalarTower.algebraMap_smul ℂ,map_smul];norm_num
lemma sign_rows (F:Frame G d)(v:F.Coeff)(i:F.Index): F.act archV.ortho v i=(-1:ℂ)^(F.grades i).1*v i:=by nth_rw 1 [← Size.sum_axes F v]; rw [map_sum,Finset.sum_apply]; simp_rw [map_smul,orbit_sign]; simp [Size.axis,Pi.single_apply,mul_ite];ring
end dark
end YM.Trace
