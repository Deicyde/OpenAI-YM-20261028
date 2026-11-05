import YM.TraceExtension.Pi.Raga
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory
open Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Interval Classical InnerProductSpace
variable {G:Gauge}{n:Side}{F:Peat G n}{P:Support n}
section polar
lemma sheen_symm (F:Peat G n)(h:Cleric F)(a b:Link G n): sheen F a b = sheen F b a:= evenQ h ..
lemma sheen_add_r (F:Peat G n)(a b c:Link G n): sheen F a (b+c)=sheen F a b+sheen F a c:=by simp[ sheen, iteratedFDeriv_two_apply]
lemma sheen_neg_r (F:Peat G n)(a b:Link G n): sheen F a (-b)= - sheen F a b:=by simp[sheen,iteratedFDeriv_two_apply]
lemma sheen_sub_r (F:Peat G n)(a b c:Link G n): sheen F a (b-c)=sheen F a b-sheen F a c:=by simp[sheen,iteratedFDeriv_two_apply]
lemma sheen_scale_r (F:Peat G n)(t:ℝ)(a b:Link G n): sheen F a (t • b)=t*sheen F a b:=by simp[sheen,iteratedFDeriv_two_apply]
lemma sC_add (o:Site n)(u v:Potential G): stepC o (u+v) = stepC o u+stepC o v:=by apply map_add
lemma sC_neg (o:Site n)(u:Potential G): stepC o (-u)= -stepC o u:=by apply map_neg
end polar
variable (p:Track)(i:Axis)(a:G.ColorIndex)(d:ℕ)
-- polynomial midpoint planes
abbrev midV (x: E4):ℝ:= tracks p x + p i/2
def elimA (v: G.Color) (j:ℕ)(x:E4)(k:Axis):= (basis k i * (midV p i x)^j) • v
abbrev XR(j:ℕ): Link G n:=stepC 0 (elimA p i (G:=G) (EuclideanSpace.basisFun G.ColorIndex ℝ a) j)
lemma paintf (k:Axis)(z:E4)(v:G.Color)(j:ℕ): fume (Ptune p i v j) z k=(∫ t:ℝ in 0..1,basis k i *((tracks p z+t*p k)^j)) • v := by
    unfold fume; unfold Ptune; simp_rw[map_add,map_smul,axe_t,smul_eq_mul]; rw[intervalIntegral.integral_smul_const]
lemma cupG0 (v:G.Color): elimA p i v 0=fume (Ptune p i v 0):=by funext z k; rw[paintf];simp [elimA]
lemma cupG1 (v:G.Color): elimA p i v 1=fume (Ptune p i v 1):=by
    funext z k; unfold elimA; rw[paintf]; by_cases h:k=i
    · subst k; simp only[basis_eq,if_true,one_mul,pow_one]; rw[intervalIntegral.integral_add, intervalIntegral.integral_mul_const]; rotate_left
      · exact intervalIntegrable_const
      · apply Continuous.intervalIntegrable; fun_prop
      unfold midV; congr 1; simp; ring
    simp [basis_eq,Ne.symm h]
lemma cupG2 (v:G.Color): elimA p i v 2=fume (Ptune p i v 2)- (p i^2/12) • elimA p i v 0:=by
    funext z k; rw[Pi.sub_apply,Pi.sub_apply,Pi.smul_apply,Pi.smul_apply,paintf]; unfold elimA; by_cases he:k=i
    · subst k; simp only[basis_eq,if_true,one_mul,pow_zero,one_smul]; unfold midV
      let x:= tracks p z; let k:=p i
      have h:∫ t:ℝ in 0..1,(x+t*k)^2= x^2+x*k+k^2/3:=by
         rw[show (fun t:ℝ=>(x+t*k)^2)=_ from (show _=(fun t:ℝ=>x^2+t*(2*x*k)+t^2*k^2) from funext fun i=>by ring), intervalIntegral.integral_add, intervalIntegral.integral_add]; all_goals try (apply Continuous.intervalIntegrable; fun_prop)
         rw[intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const];norm_num; ring
      rw[h]; change (x + k/2)^2 • v= (x ^ 2 + x*k + k^2/3) • v - (k^2/12) • v; module
    simp [basis_eq,Ne.symm he]
lemma sC_weights (o:Site n)(v:Potential G)(c:ℝ) : stepC o (c • v)= c • stepC o v:=by exact map_smul (edgeColor (G:=G) (n:=n)).symm c _
lemma sC_sub (o:Site n)(u v:Potential G): stepC o (u-v)=stepC o u-stepC o v:=by apply map_sub
variable (h:Cleric F)(hp:LocalOn P F)(hs:Nonwrapping P 0)(hG:G.Simple)(hn:2 ≤ n.val)
include h hp hs hG hn
abbrev bang0 := ivy (0:Site n) (Xtune p i (G:=G) (EuclideanSpace.basisFun G.ColorIndex ℝ a))
abbrev bang1 := ivy (0:Site n) (Ytune p i (G:=G) (EuclideanSpace.basisFun G.ColorIndex ℝ a))
lemma stitch0 (x: Link G n): sheen F x (XR p i a 0)=0:=by unfold XR; rw[cupG0,fume0,sC_neg,sheen_neg_r,show sheen F x _=0 from cellar hn hs hp h hG _ _,neg_zero]
lemma stitch1(x:Link G n) : sheen F x (XR p i a 1)=sheen F x (bang0 p i a):=by unfold XR; rw[cupG1,fume1,sC_add,sheen_add_r,sC_neg,sheen_neg_r,show sheen F x _=0 from cellar hn hs hp h hG _ _,neg_zero,zero_add];rfl
lemma stitch2(x:Link G n) : sheen F x (XR p i a 2)=sheen F x (bang1 p i a):=by unfold XR; rw [cupG2, fume2, sC_sub, sC_weights,sC_add, sheen_sub_r,sheen_scale_r,show sheen F x (XR p i a 0)=0 from stitch0 p i a h hp hs hG hn _,mul_zero,sub_zero,sheen_add_r,sC_neg,sheen_neg_r,show sheen F x _=0 from cellar hn hs hp h hG _ _,neg_zero,zero_add];rfl
end YM.Trace.Kits
