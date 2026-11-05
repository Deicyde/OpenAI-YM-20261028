import YM.RG08.Quarry.Tumble
/-! # Leading external coefficient from any rescaled reader. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Gallery Forms Function Filter Lattice Laurent Room Camera Glyph Finset MvPolynomial Prism
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J:Type}[Fintype I][Fintype J]

def eye (f:Still I):Port I:=liftout (flask f)
lemma eye_same {f g:Still I}(h:f=ᶠ[𝓝 0] g):eye f=eye g:=by unfold eye;rw [flask_same h]
lemma eye_comp (g:Strip I J)(hg:∀ i,Pace (g i))(ht:roll g 0=0)(f:Still I)(hf:Pace f)(he:f 0=0):eye (f ∘ roll g)=belt (fun i=>eye (g i)) (eye f):=by
 let a:Strip Unit I:=fun _=>f
 have h0:roll a 0=0:=by funext _; exact he
 have hx:=DFunLike.congr_fun (pluto a g (fun _=>hf) hg h0 ht) (Room.rod (I:=Unit) ())
 rw [AlgHom.comp_apply,belt_x,belt_x] at hx; exact Eq.symm hx
lemma eye_reader (i:I):eye (fun x:Cellar I=>x i)=Room.rod i:=by
 ext n :1;change tap _ _=tap _ _;rw [eye,look,lamp,hopper]
lemma eye_chart (g:I→J)(f:Still I)(hf:Pace f)(he:f 0=0)(z:J→Dig): breath z (eye (fun x:Cellar J=>f (x ∘ g)))=breath (z ∘ g) (eye f):=by
 change breath z (eye (f ∘ roll (fun i x=>x (g i))))=_
 rw [eye_comp (fun i x=> x (g i)) (fun _=>(contDiff_apply ℝ ℝ _).contDiffAt) rfl f hf he] -- defeq f ∘ roll g?
 simp_rw [eye_reader,fugue,bases_x];rfl

abbrev cost (z:I→Dig)(j:I):ℝ:=PowerSeries.constantCoeff (z j)
omit [Fintype I] in
lemma scouts (z:I→Dig)(p:Inn I):PowerSeries.constantCoeff (MvPolynomial.aeval z p)=MvPolynomial.eval (cost z) p:=by
 induction p using MvPolynomial.induction_on with
 | C a=>simp -- cc algMap
 | add f g hf hg=>rw [map_add,map_add,map_add,hf,hg]
 | mul_X f i hf=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,aeval_X,eval_X,hf]

lemma lead (z:I→Dig)(f:Still I):PowerSeries.constantCoeff (breath z (eye f))= fderiv ℝ f 0 (cost z):=by
 rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply]; change tap 0 _=_;rw [pulses];simp only [zero_add,range_one,sum_singleton,tap,Nat.sub_zero]; change tap 0 (MvPolynomial.aeval z (tap 0 (eye f)))=_; rw [eye,look,flute,Camera.print,Nat.cast_zero,zero_add,inv_one,one_smul]
 -- scouts
 unfold tap; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,scouts,map_sum];simp_rw [Camera.print,_root_.map_mul,eval_C,eval_X,wedge]
 have he : cost z=∑ i:I,cost z i • Pi.single i (1:ℝ):=by ext j;simp [Pi.single_apply]
 conv_rhs=>rw [he]
 rw [map_sum];apply Finset.sum_congr rfl;intro i _;rw [_root_.map_smul];rfl

-- zero all test slots => nothing from eye.
lemma dark (f:Still I):breath (0:I→Dig) (eye f)=0:=by
 ext n :1;change tap _ _= tap _ _;rw [pulses]; apply Eq.trans (sum_eq_zero fun k _=>?_);simp [tap]
 rw [eye,look,flute,Camera.print,_root_.map_smul,map_sum];simp_rw [_root_.map_mul,aeval_X,Pi.zero_apply,zero_mul,sum_const_zero,smul_zero];exact map_zero _
end YM.RG08.Quarry
