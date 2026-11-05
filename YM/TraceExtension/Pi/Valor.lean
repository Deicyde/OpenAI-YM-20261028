import YM.TraceExtension.Pi.Lens
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}{n:Side} (d i b:Axis)(a:G.ColorIndex)
open Complex
set_option maxHeartbeats 700000 in
lemma tier_five(w s t i j:Axis)(J: Jet G): unitK J (pairDeriv G w s t i j)=↑(inner ℝ (curl0 w s (J 0)) (curl1 t i j (J 1))):=by
   let P:= pairDeriv G w s t i j
   have hv(u:ℝ): Labels.read (scaleJet J u) P.val=u^(5:ℕ) • Labels.read J P.val:= scaled_grade u J P (productPol_grade _ _)
   have hx:= deriv_read J P.val 5;
   have he: leading 5 (fun t=> Labels.read (scaleJet J t) P.val)=Labels.read J P.val:=by rw [funext hv,lead_monomial]; simp
   rw[leading,hx, inv_smul_smul₀ (by positivity)] at he; exact he.trans (pairDeriv_value ..)
lemma lag_sum(S:Signed)(x:RawOne G)(h:G.Simple): (∑ b,lag (S.perm d) (S.perm i) b a (x.val b))=∑ b,lag d i b a (x.val b):=by
    rw[← Equiv.sum_comp S.perm]; refine sum_congr rfl fun b _=>?_; have hx: tensor S.ortho (x.val b)=sign S b • x.val (S.perm b):= x.property.2 ..
    have hz: x.val (S.perm b)=sign S b • tensor S.ortho (x.val b):=by rw [hx]; exact (sign_sign S b (x.val (S.perm b))).symm
    rw[hz];exact clamp _ _ _ _ S _ h
lemma prism (x:RawOne G)(h:G.Simple): archK a x.val=(12:ℂ)*∑ b,lag 0 1 b a (x.val b):=by
    let U : ℂ:=∑ b, lag 0 1 b a (x.val b); rw[arch_pay]; unfold suite
    have ht(i d:Axis) (hp:d≠i): (∑ b,lag d i b a (x.val b))= U:=by
       obtain ⟨s,hm,he⟩:=permTrip 0 1 d i (by decide) hp; let S:=platey s; have hS:= lag_sum 0 1 a S x h; change ∑ b,lag (s 0) (s 1) b a (x.val b)=_ at hS; rwa [hm,he] at hS
    rw [show (∑ d:Axis,∑ i:Axis,_)=(∑ d:Axis,∑ i:Axis,if d=i then 0 else U) from ?_]; rotate_left
    · refine sum_congr rfl fun d _=>sum_congr rfl fun i _=>?_ ; by_cases h:d=i<;> simp only[h,↓reduceIte]; exact ht i d h
    change _=12*U; simp only [Fin.sum_univ_four]; simp; ring
-- faster algebra using closed forms curl from Θ. define θ.
abbrev cof (p:Track)(i r t:Axis):ℝ:= (p r)*(basis t i)-(p t)*(basis r i)
private lemma ivg (a b:Axis)(v:ℝ): basis a b*v=if b=a then v else 0:=by simp[basis_eq,ite_mul]
lemma recoil0 (p:Track)(v:G.Color)(r t:Axis): curl0 r t (Xtune p i v)= cof p i r t • v:=by
    rw[curl0_value,glance1,glance1,axe_t,axe_t]; unfold cof; module
lemma recoil1 (p:Track)(v:G.Color)(r t k:Axis): curl1 k r t (Ytune p i v)= (2*p k*cof p i r t) • v:=by
    rw[curl1,curled_deriv]; let U:= Ytune p i v
    have hx(z j:Axis):Maxwell.grad z (U.value j) (basis k)=
          (2/3:ℝ) • (((basis j i)*(2*p k*p z)) • v - (basis z i*p k*p j + basis k i*p z*p j) • v):=by
       have he:= (tracks p).hasFDerivAt (x:=basis k); have hu:= (Maxwell.compAxis i).hasFDerivAt (x:=basis k)
       unfold Maxwell.grad Analysis.D; rw [funext (glance2 p i v j)]
       let c:ℝ:=2/3; let F(x:E4):= c • ((basis j i*(tracks p x)^2) • v-(x i*tracks p x*p j) • v)
       have ht: HasFDerivAt F _ (basis k):= ((((he.pow 2).const_mul (basis j i)).smul_const v).sub (((hu.mul he).mul_const _).smul_const v)).const_smul c
       change fderiv ℝ F (basis k) (basis z)=_; rw[ht.fderiv, axe_t];
       simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,nsmul_eq_mul, Nat.cast_ofNat,axe_t]; rw[show Maxwell.compAxis i (basis z)= basis z i from rfl,show Maxwell.compAxis i (basis k)=basis k i from rfl]; unfold c;module
    rw [hx,hx]; unfold cof;module
lemma crest_der (s x y k l:Axis)(p:Land): lotR i a p (pairDeriv G s x y k l)= - I* ↑(cof (p 1) i s x * (p 0 y *cof (p 0) i k l)+cof (p 0) i s x * (p 1 y *cof (p 1) i k l)):= by
   unfold lotR;change (-I*(1/2:ℂ))*(unitK _ _+unitK _ _)=_
   rw [tier_five, tier_five,rose_in, rose_out, rose_in,rose_out, recoil0,recoil0,recoil1,recoil1]; simp_rw [real_inner_smul_left,real_inner_smul_right,OrthonormalBasis.inner_eq_one]; push_cast;ring
end YM.Trace.Kits
