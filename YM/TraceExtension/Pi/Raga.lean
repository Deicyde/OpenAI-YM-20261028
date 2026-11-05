import YM.TraceExtension.Pi.Cut
import YM.TraceExtension.Pi.Bound
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory
open Source Source.Drops Labels Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Interval InnerProductSpace Classical
variable {d n k:ℕ}{G:Gauge}{s:Side}{F:Peat G s}
-- Linear test by midpoint plane annotations
abbrev tracks (p:Track): E4→L[ℝ] ℝ:=∑ i, (p i) • Maxwell.compAxis i
lemma axe_t (p:Track)(i): tracks p (basis i)=p i:=by rw[tracks,_root_.sum_apply];simp[basis_eq,Maxwell.compAxis]
variable (p: Track)(i:Axis)(v:G.Color)
abbrev Gtune (k:ℕ)(z:E4):= ((z i * (tracks p z)^k)/((k+1:ℕ):ℝ)) • v
abbrev Ptune (k:ℕ) : Potential G:= fun z a=> ((basis a i * (tracks p z)^k)) • v
def Xtune : Taylor G 0:=∑ a:Axis,p a • leg0 a i v
def Ytune : Taylor G 1:=∑ a:Axis,∑ b:Axis, (2*p a*p b) • leg1 b a i v
private def tent (x : E4)(i:Axis): Taylor G n→ₗ[ℝ] G.Color:={ toFun T:=T.value i x, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
lemma mind_t (z:E4): tracks p z=∑ a,p a*z a:=by unfold tracks; rw[_root_.sum_apply]; rfl
lemma mind_v (z:E4)(x:G.Color): (tracks p z) • x= ∑ a,p a • (z a • x):=by rw[mind_t,Finset.sum_smul]; apply sum_congr rfl fun a _=>?_ ; rw[mul_smul]
lemma glance1 (a:Axis)(x:E4): (Xtune p i v).value a x= (1/2:ℝ) • ((basis a i*tracks p x) • v-(x i*p a) • v):=by
   change tent x a (Xtune p i v)=_; unfold Xtune; rw[map_sum]; simp only [map_smul]; simp_rw [show ∀ z:Axis,tent x a (leg0 z i v)=_ from fun z:Axis=> leg0_value v z i a x];
   have hv: ∑ b:Axis,p b • ((if a=i then x b • v else 0) - if a=b then x i • v else 0)=(basis a i * tracks p x) • v - (x i*p a) • v:=by
        simp_rw [smul_sub,Finset.sum_sub_distrib]; apply congr_arg₂ (·-·)
        · by_cases h:a=i; · rw[mul_smul, mind_v]; simp[h,basis_eq]
          simp [h,basis_eq,Ne.symm h]
        simp [smul_ite]; module
   simp_rw [smul_comm (p _) ((2:ℝ)⁻¹), ← smul_sum,hv];norm_num
lemma glance2 (a:Axis)(x:E4): (Ytune p i v).value a x= (2/3:ℝ) • ((basis a i*(tracks p x)^2) • v- (x i*tracks p x*p a) • v):=by
   change tent x a (Ytune p i v)=_
   unfold Ytune; simp only [map_sum,map_smul];simp_rw [show ∀ y z:Axis,tent x a (leg1 y z i v)=_ from fun y z=> leg1_value v y z i a x]
   have hv : (∑ y,∑ z:Axis, p y • p z • ((if a=i then x y • x z • v else 0)-(if a=y then x i • x z • v else 0)))=(basis a i*tracks p x^2) • v - (x i*tracks p x * p a) • v:=by
      simp_rw [smul_sub, Finset.sum_sub_distrib]; congr 1
      · by_cases ha:a=i
        · rw[mind_t]; simp[ha]; rw [pow_two,sum_mul]; simp_rw [mul_sum,sum_smul]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; simp only [smul_smul]; module
        simp[ha,basis_eq,Ne.symm ha]
      rw [sum_eq_single a]; rotate_left
      · intro i _ hi; simp [hi.symm]
      · simp
      simp only[if_true]; rw[mind_t, mul_sum, sum_mul,sum_smul]; refine sum_congr rfl fun i _=>?_ ; simp only[smul_smul];module
   rw [show (∑ y:Axis,∑ z:Axis,_)=(2/3:ℝ) • (∑ y,∑ z:Axis, p y • p z • ((if a=i then x y • x z • v else 0)-(if a=y then x i • x z • v else 0))) by
       simp_rw [smul_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; module]
   rw[hv]
lemma walk_g(k:ℕ) : ContDiff ℝ ω (Gtune p i v k):=by
   have hp:ContDiff ℝ ω (fun x:E4=> x i):= Maxwell.compAxis i |>.contDiff
   exact ((hp.mul ((tracks p).contDiff.pow _)).div_const _).smul contDiff_const
set_option maxHeartbeats 400000 in
lemma descent_g (k:ℕ)(x:E4)(a:Axis): Place.descent (Gtune p i v k) x a = (((basis a i*tracks p x^k+x i*(k*tracks p x^(k-1)*p a))/((k+1:ℕ):ℝ))) • v:=by
   let U:ℝ:= ((k+1:ℕ):ℝ); let T (x:E4):= x i* tracks p x^k; have ht: HasFDerivAt T _ x:=(Maxwell.compAxis i).hasFDerivAt.mul ((tracks p).hasFDerivAt.pow k)
   have hy:(fun x=> (T x*U⁻¹) • v)= Gtune p i v k:=by funext x; unfold Gtune; rw[div_eq_mul_inv]
   have he:= (ht.mul_const U⁻¹).smul_const v
   unfold Place.descent; rw[← hy,he.fderiv]; dsimp only [_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.smulRight_apply];
   by_cases h:i=a <;> simp [Maxwell.compAxis,h,U] <;> module
lemma radial0 : Ptune p i v 0=Place.descent (Gtune p i v 0):=by funext x a; simp [descent_g,Ptune]
lemma radial1 : Ptune p i v 1= Place.descent (Gtune p i v 1) + radialValue (Xtune p i v):=by
   ext1 z; ext1 a; unfold Ptune radialValue; rw[Pi.add_apply,Pi.add_apply,descent_g,glance1]; norm_num only [Nat.cast_one,Nat.cast_add];module
lemma radial2 : Ptune p i v 2= Place.descent (Gtune p i v 2)+radialValue (Ytune p i v):=by
   ext1 z; ext1 a; unfold Ptune radialValue; rw[Pi.add_apply, Pi.add_apply,descent_g,glance2];norm_num only [Nat.cast_one,Nat.cast_add,Nat.cast_ofNat];module
lemma fume1 : fume (Ptune p i v 1)= -(Place.jump (Gtune p i v 1))+variation (Xtune p i v):=by
   rw[radial1,fume_add,fume_grad (walk_g p i v 1|>.of_le le_top), show fume (radialValue _) = _ from fume_leg (Xtune p i v)]
   · intro a; unfold Place.descent; exact ((walk_g p i v _).continuous_fderiv (by simp)).clm_apply continuous_const
   intro a; exact (Tensor.diag_smooth _ 1).continuous
lemma fume2 : fume (Ptune p i v 2)= -(Place.jump (Gtune p i v 2))+variation (Ytune p i v):=by
   rw[radial2,fume_add, fume_grad (walk_g p i v 2|>.of_le le_top), show fume (radialValue _) = _ from fume_leg (Ytune p i v)]
   · intro a; unfold Place.descent; exact ((walk_g p i v _).continuous_fderiv (by simp)).clm_apply continuous_const
   intro a; exact (Tensor.diag_smooth _ 1).continuous
lemma fume0 : fume (Ptune p i v 0)= -(Place.jump (Gtune p i v 0)):=by rw[radial0,fume_grad (walk_g p i v 0|>.of_le le_top)]
end YM.Trace.Kits
