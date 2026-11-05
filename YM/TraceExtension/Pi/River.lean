import YM.TraceExtension.Pi.Perg
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}
section Rad
variable (A:Taylor G 1)(i a:Axis)
private def flex (x:E4): E4→L[ℝ] G.Color := (ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)).symm ((A.val i).curryLeft x)
private lemma flux (x y:E4): flex A i x y= A.val i ![x,y]:=by
   let U:=ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)
   change U (U.symm ((A.val i).curryLeft x)) (fun _=>y)=_; rw [U.apply_symm_apply,ContinuousMultilinearMap.curryLeft_apply]; congr 1; ext1 k; fin_cases k<;>rfl
private lemma flashV (x y:E4): flex A i x y=flex A i y x:=by
    rw[flux,flux]; exact (A.property.1 i ![x,y] (Equiv.swap (0:Fin 2) 1)).symm.trans (congr_arg (A.val i) (funext fun k=> by fin_cases k<;>simp))
private lemma flower (x:E4): flex A i x x=A.value i x:=by rw[flux]; exact congr_arg (A.val i) (funext fun k=>by fin_cases k<;>rfl)
def breeze : E4→L[ℝ] G.Color:= (2:ℝ) • flex A i (basis a)
lemma bearV (x:E4): Maxwell.grad a (A.value i) x= breeze A i a x:=by
    unfold Maxwell.grad Analysis.D Taylor.value; rw[Tensor.differential_diagonal _ (A.property.1 i),breeze,_root_.smul_apply,flux]; change ((1+1:ℕ)) • _=_; norm_cast; congr 1; rw [ContinuousMultilinearMap.curryLeft_apply]; congr 1; ext1 k; fin_cases k<;>rfl
lemma flower_ad (x:E4)(t:ℝ): A.value i (x+t • basis a)= A.value i x+t • breeze A i a x+(t^2) • A.value i (basis a):=by
   simp_rw [← flower]; rw[map_add,map_smul,flashV A i _ x,map_add,map_smul,flashV A i x (basis a),flashV A i _ (basis a),map_add,map_smul,breeze,_root_.smul_apply]; module
lemma curl1_b (i j : Axis): curl1 a i j A=breeze A j a (basis i)-breeze A i a (basis j):=by rw[curl1,curled_deriv,bearV,bearV]; unfold breeze; simp only[_root_.smul_apply,flashV A j (basis i),flashV A i (basis j)]
end Rad
section Line
private theorem stab (z:E4): ∑ i:Axis, z i •basis i=z:=by ext1 k;simp
variable (V:Axis→ E4→L[ℝ] G.Color)
def replica : Taylor G 0:=∑ i:Axis,∑ j:Axis,leg0 i j (V j (basis i))
lemma curl_b (i j) : curl0 i j (replica V)= V j (basis i)-V i (basis j):=by unfold replica; simp_rw[map_sum,curl0_leg,sub_smul, Finset.sum_sub_distrib]; simp [basis_eq,mul_ite,ite_smul]
private def fellV (i:Axis)(x:E4): Taylor G 0→ₗ[ℝ] G.Color:={toFun A:= A.value i x, map_add':=by intros;rfl, map_smul':=by intros;rfl}
lemma recoil (x:E4)(k:Axis): (replica V).value k x= (1/2:ℝ) • (V k x - ∑ i, x i • V i (basis k)):=by
   change fellV k x (replica V)= _; unfold replica; simp_rw [map_sum]; change (∑ i:Axis,∑ j:Axis,(leg0 i j _).value k x)=_
   simp_rw [leg0_value,← Finset.smul_sum, Finset.sum_sub_distrib];
   simp; conv_rhs=> rw[← stab x]
   simp only[map_sum,map_smul]
private def moist (x:E4):= (1/2:ℝ) • ∑ i:Axis,x i • (V i x)
private lemma hotM : ContDiff ℝ ω (moist V):=by unfold moist; have h(i:Axis): ContDiff ℝ ω (fun x:E4=> x i • V i x):= (Maxwell.compAxis i).contDiff.smul (V i).contDiff; exact (ContDiff.sum (fun i _=>h i)).const_smul _
lemma splitH : (fun z i=> V i z)= radialValue (replica V)+Place.descent (moist V):=by
    funext z i; change V i z=(replica V).value i z + fderiv ℝ (moist V) z (basis i); have hv(j:Axis): HasFDerivAt (fun z:E4=> z j • V j z) ((z j) • (V j)+(Maxwell.compAxis j).smulRight (V j z)) z:= (Maxwell.compAxis j).hasFDerivAt.smul (V j).hasFDerivAt
    rw [show moist V= (1/2:ℝ) • (∑ i:Axis,fun z:E4=>z i • V i z) from funext fun z=>by simp[moist], ((HasFDerivAt.sum (u:=univ) (fun i _=> hv i)).const_smul (1/2:ℝ)).fderiv, recoil]; simp[Finset.sum_add_distrib];module
end Line
section Shift
variable {s:Side}{P:Support s}{F:Peat G s}
lemma fume_scale (V:Potential G)(t:ℝ): fume (t • V)= t • fume V:=by
    ext1 z; ext1 i; unfold fume; simp only[Pi.smul_apply]; apply intervalIntegral.integral_smul
lemma fume_rep (V:Axis→E4→L[ℝ] G.Color): fume (fun z i=> V i z)= variation (replica V) - Place.jump (moist V):=by
    rw [splitH V, fume_add, fume_grad (hotM V|>.of_le le_top),show fume (radialValue _) = _ from fume_leg _, sub_eq_add_neg]
    · intro i; exact (Tensor.diag_smooth _ 1).continuous
    intro i; exact ((hotM V).continuous_fderiv (by simp)).clm_apply continuous_const
private def rocH (U: Axis→G.Color): E4→L[ℝ] G.Color:= ∑ i:Axis, (Maxwell.compAxis i).smulRight (U i)
lemma fume_const (U:Axis→G.Color): fume (fun z:E4=> U)= -Place.jump (rocH U):=by
    rw[← fume_grad ((rocH U).contDiff)]; congr 1; funext z i; simp[Place.descent,rocH]
lemma coon0 (A:Taylor G 0)(i:Axis)(t:ℝ)(v z:E4): A.value i (z+t • v)=A.value i z+t • A.value i v:=by
    obtain ⟨h,hx⟩:= (ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)).surjective (A.val i)
    unfold Taylor.value; rw[← hx]; change h _=h z+t • h v; rw [map_add,map_smul]
abbrev revD (w:E4){G:Gauge} (V: Potential G):Potential G:=fun z=> V (z+w)
lemma fume_r (V:Potential G)(w:E4): revD w (fume V)=fume (revD w V):=by
   ext1 z; ext1 i; unfold revD fume; simp_rw [show ∀ t:ℝ, z+w+t •basis i=z+t • basis i+w from fun t=>by abel]
lemma ride_0 (A:Taylor G 0)(t:ℝ)(v:E4): revD (t • v) (variation A)= variation A - Place.jump (rocH (fun i=> t • A.value i v)):=by
    rw [← fume_leg A,fume_r,show revD (t • v) (_:Potential G)=(fun z i=>A.value i z)+(fun (_z:E4) i=> t • A.value i v) from funext fun z=> funext fun i=>coon0 A i t v z,fume_add,fume_const,sub_eq_add_neg]; exact fun _=>(Tensor.diag_smooth _ 1).continuous; exact fun _=>continuous_const
abbrev bentV (A:Taylor G 1)(a:Axis):=replica fun i=> breeze A i a
lemma bendV (A:Taylor G 1)(a i j:Axis): curl1 a i j A=curl0 i j (bentV A a):=by rw [curl1_b]; exact (curl_b (fun i=> breeze A i a) i j).symm
lemma ride_1 (A:Taylor G 1)(a:Axis)(t:ℝ): let v:=t •basis a; let V i:= breeze A i a
    revD v (variation A)= variation A+t • (variation (bentV A a)-Place.jump (moist V))- Place.jump (rocH (fun i=> (t^2) • A.value i (basis a))):=by
   intro v V; have hG(i:Axis): Continuous (fun x=>A.value i x + t • V i x):=(Tensor.diag_smooth _ 1).continuous.add ((V i).continuous.const_smul t)
   rw [← fume_leg A,fume_r,show revD v (_:Potential G)=(fun z i=>A.value i z) + t • (fun z i=> V i z) +(fun (_z:E4) i=>(t^2) • A.value i (basis a)) from funext fun z=>funext fun i=>flower_ad A i a z t, fume_add (G:=G), fume_add (G:=G),fume_scale (G:=G), fume_rep V, fume_const,sub_eq_add_neg (_ + t • _) (Place.jump (rocH _))]; rotate_left
   all_goals first| exact hG| exact fun _=>continuous_const| rfl| exact fun _=> (Tensor.diag_smooth _ 1).continuous| exact fun j=>(V j).continuous.const_smul t
end Shift
end YM.Trace.Kits
