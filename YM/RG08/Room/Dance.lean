import YM.RG08.Room.Inks
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Formal velocity fields and determinant variation, off-shell.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Cloud Glyph Finset Matrix
open scoped BigOperators Topology Classical
variable {R : Type*}[CommRing R][Algebra ℝ R]

private lemma branch {I:Type*}(D:Derivation ℝ R R)(p:Finset I)(f:I→R):
    D (∏ i∈p,f i)=∑ i∈p, D (f i)*(∏ j∈p.erase i,f j):=by
 induction p using Finset.induction_on with
 | empty=>simp
 | insert a s hs h=>
   rw [prod_insert hs,sum_insert hs, erase_insert hs,Derivation.leibniz,h];simp only [smul_eq_mul]
   rw [add_comm,mul_comm (D (f a)),Finset.mul_sum];congr 1;apply sum_congr rfl;intro i hi
   rw [erase_insert_of_ne (by rintro rfl; exact hs hi),prod_insert (fun h=>hs (mem_of_mem_erase h))];ac_rfl

variable {I:Type}[Fintype I]
set_option linter.unusedSimpArgs false in
lemma turnover (D:Derivation ℝ R R)(M A:Matrix I I R)(h:∀ i j,D (M i j)=(M*A) i j):D M.det=M.det*(∑ i,A i i):=by
 have he: D M.det=∑ i,Matrix.det (M.updateCol i (fun j=>D (M j i))):=by
   simp_rw [det_apply,map_sum]
   rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro b _ -- reorders RHS? rw sum_comm may match LHS single?
   have hx (a:R):D (Equiv.Perm.sign b • a)=Equiv.Perm.sign b • D a:=by
     simp only [Units.smul_def]; exact map_zsmul D.toLinearMap _ _
   rw [hx,branch,Finset.smul_sum];apply Finset.sum_congr rfl;intro i _
   congr 1
   let f (j:I):=M.updateCol i (fun l=>D (M l i)) (b j) j
   change D (M (b i) i)*(∏ j∈univ.erase i, M (b j) j)=∏ j,f j
   rw [←Finset.mul_prod_erase _ f (Finset.mem_univ i)]
   apply congr_arg₂ (·*·)
   · simp [f]
   apply Finset.prod_congr rfl;intro j hj
   simp [f,Matrix.updateCol, ne_of_mem_erase hj]
 rw [he,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
 have hh:(fun j=>D (M j i))=(fun j=>∑ k,A k i • M j k):=by funext j;rw [h,mul_apply]; apply Finset.sum_congr rfl;intro k _; rw [smul_eq_mul,mul_comm]
 rw [hh,Matrix.det_updateCol_sum,smul_eq_mul,mul_comm]


def drag (v:I→Port I):Derivation ℝ (Port I) (Port I):=∑ i,v i • pin i
def gustaway (s:I)(v:I→Port I):Derivation ℝ (Port I) (Port I):=pin s - drag v

def gate (x:I→Port I):Matrix I I (Port I):=Matrix.of (fun i j=>pin j (x i))
lemma drag_do (v:I→Port I)(f:Port I):drag v f=∑ i,v i * pin i f:=by
 unfold drag; generalize (univ:Finset I)=S
 induction S using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty];rfl
 | insert i S hi h=>rw [sum_insert hi,sum_insert hi]; rw [Derivation.add_apply,Derivation.smul_apply,h];rfl
lemma away (s:I)(v:I→Port I)(f:Port I):gustaway s v f=pin s f-∑ i,v i*pin i f:=by rw [gustaway,←drag_do];rfl

/- Work with dummy coordinate s included in the Jacobian; insist on label-affine velocity
v_s=0 per conservation predicate below. -/
def Moved (s:I)(x v:I→Port I):Prop:=∀ i:I,gustaway s v (x i)=if i=s then 1 else 0

lemma motion {s:I}{x v:I→Port I}(h:Moved s x v)(i j:I):gustaway s v ((gate x) i j)=(gate x*gate v) i j:=by
 have he:=congrArg (fun y=>pin j y) (h i)
 simp only [away,map_sub,map_sum,Derivation.leibniz,smul_eq_mul,apply_ite,Derivation.map_one_eq_zero,map_zero,ite_self] at he
 simp only [away,mul_apply,gate,Matrix.of_apply]
 rw [pin_comm s j]
 have hp(k:I): pin k (pin j (x i))=pin j (pin k (x i)):=pin_comm ..
 rw [sub_eq_zero.mp he];simp_rw [hp,Finset.sum_add_distrib]; abel

def flux (v:I→Port I):Port I:=∑ i,pin i (v i)
set_option maxHeartbeats 800000 in
theorem moving {s:I}{x v:I→Port I}(h:Moved s x v):gustaway s v (gate x).det=(gate x).det*flux v:= by
 unfold flux
 have ht:=turnover (gustaway s v) (gate x) (gate v) (motion h);change _=_*(∑ i,pin i (v i)) at ht;exact ht

-- radius of near-id map, no uniform control needed for this algebra

def Near (x:I→Port I):Prop := ∀ i,tap 0 (x i)=MvPolynomial.X i
lemma gate_flat {x:I→Port I}(h:Near x):PowerSeries.constantCoeff.mapMatrix (gate x)=1:=by
 ext i j :1
 change PowerSeries.constantCoeff (pin j (x i))=(_ : Matrix I I (Inn I)) i j
 have hi:PowerSeries.coeff 0 (x i)=_:=h i;rw [← PowerSeries.coeff_zero_eq_constantCoeff,flight_apply,hi,MvPolynomial.pderiv_X]
 simp [Pi.single_apply, Matrix.one_apply]
lemma gate_unit {x:I→Port I}(h:Near x):IsUnit (gate x).det:=by
 rw [PowerSeries.isUnit_iff_constantCoeff,RingHom.map_det,gate_flat h];simp

def anchored (W : Finset I)(x:I→Port I):Prop:=∀ i,i∉W→x i=rod i

lemma velvet (W:Finset I){x:I→Port I}(h:Near x)(hp:anchored W x)(s:I):∃ v, Moved s x v∧ ∀ i,i∉W → v i=0:=by
 let d : I→Port I:=fun i=>pin s (x i) - (if i=s then 1 else 0)
 let v:I→Port I:=(gate x)⁻¹ *ᵥ d
 have he:gate x *ᵥ v=d:=by unfold v;rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (gate_unit h),one_mulVec]
 have hm:Moved s x v:=by
   intro i
   have hh := congrFun he i
   change ∑ j: I, (gate x) i j * v j=_ at hh
   have hg : ∑ j,v j * (pin j (x i))=(∑ j:I,gate x i j*v j):=by apply Finset.sum_congr rfl;intro j _; exact mul_comm _ _
   rw [away,hg,hh]; unfold d; abel
 refine ⟨v,hm,fun i hi=>?_⟩
 have hx:=hm i;rw [hp i hi,away] at hx;simp only [pins,show (s=i)=(i=s) from propext eq_comm,mul_ite,mul_one,mul_zero,sum_ite_eq',if_pos (mem_univ i)] at hx; exact sub_eq_self.mp hx

lemma changed {s:I}{x v:I→Port I}(h:Moved s x v)(f:Port I): gustaway s v (belt x f)=belt x (pin s f):=by
 have he(i:I): gustaway s v (x i)=if i=s then 1 else 0:=h i
 calc
 _ = ∑ i,belt x (pin i f)*gustaway s v (x i):=by
    simp_rw [away,belt_chain,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    apply congrArg₂ (·-·) rfl; rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _; apply Finset.sum_congr rfl;intro j _;ac_rfl
 _ = _:= by simp_rw [he,mul_ite,mul_one,mul_zero,sum_ite_eq',if_pos (mem_univ _)]

end YM.RG08.Room
