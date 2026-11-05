import YM.TraceExtension.Pi.Slide
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory
open Source Source.Drops Labels Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Interval Classical InnerProductSpace
variable {d n k:ℕ}{G:Gauge}{s:Side}{F:Peat G s}{o:Site s}
section polynomial
-- lattice averages of continuous homogeneous fields υ_{-p}. positive links only.
def fume (f:Potential G)(x:E4)(e:Axis):= ∫ t:ℝ in 0..1, f (x+t • basis e) e
lemma fume_leg (A:Taylor G n): fume (fun x i=> A.value i x)=variation A:=by
    funext x i; unfold fume variation; simp_rw [Taylor.value, show ∀ t:ℝ,Tensor.diagonal (A.val i) (x+t • basis i) = _ from fun t=> slice_diagonal (A.val i) x (basis i) t]; rw [intervalIntegral.integral_finsetSum]; rotate_left
    · intro v _; apply Continuous.intervalIntegrable; fun_prop
    refine sum_congr rfl fun k _=>?_ ; rw [intervalIntegral.integral_smul_const];rfl
lemma fume_add {V W:Potential G}(h:∀ i,Continuous (fun x=>V x i))(he:∀ i, Continuous fun x=>W x i): fume (V+W)=fume V+ fume W:=by
    funext x i; unfold fume; simp only [Pi.add_apply]; apply intervalIntegral.integral_add
    · exact ((h i).comp (f:=fun t:ℝ=> x+t • basis i) (by fun_prop)).intervalIntegrable ..
    exact ((he i).comp (f:=fun t:ℝ=> x+t • basis i) (by fun_prop)).intervalIntegrable ..
lemma fume_grad {V:E4→ G.Color}(h:ContDiff ℝ 2 V): fume (Place.descent V)= -Place.jump V:=by
    funext x i; let f:=fun t:ℝ=> V (x+t • basis i)
    let g(t:ℝ):=Place.descent V (x+t • basis i) i; have hv(t:ℝ): HasDerivAt f (g t) t:= ((show DifferentiableAt ℝ V (x+t • basis i) from h.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t (show HasDerivAt (fun t:ℝ=> x+t • basis i) (basis i) t from by
      simpa using (((hasDerivAt_id' t).smul_const (basis i)).const_add x))
    unfold fume; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=f) (f':=g) (fun t _=>hv t)]; rotate_left
    · unfold g Place.descent; let Z:= fderiv ℝ V
      apply Continuous.intervalIntegrable; exact ((h.continuous_fderiv (by norm_num)).comp (f:=fun t:ℝ=> x+t • basis i) (by fun_prop)).clm_apply continuous_const
    simp [f,Place.jump]
end polynomial
variable {P:Support s}
section value
lemma evenQ (h: Cleric F)(x y:Link G s): iteratedFDeriv ℝ 2 (F∘input G s) 0 ![x,y]= iteratedFDeriv ℝ 2 (F ∘ input G s) 0 ![y,x]:=by simp only[iteratedFDeriv_two_apply]; exact h.dye.isSymmSndFDerivAt_of_omega x y
lemma shadeL (h: LocalOn P F)(he: Cleric F)(x v w:Link G s)(hx: ∀ i:Edge (Site s), i.1∈ P→ i.1+step i.2∈ P→edgeColor v i=edgeColor w i):
    iteratedFDeriv ℝ 2 (F∘input G s) 0 ![x,v]=iteratedFDeriv ℝ 2 (F∘input G s) 0 ![x,w]:=by
    let R:= F ∘input G s; let B(z: ℝ × ℝ)(v:Link G s):= z.1 • x+z.2 • v
    let b(v:Link G s):ℝ × ℝ→L[ℝ] Link G s:=(ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x+(ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v
    have hh(v:Link G s): iteratedFDeriv ℝ 2 R 0 ![x,v]= iteratedFDeriv ℝ 2 (R ∘ (b v)) 0 ![((1:ℝ),0),(0,1)]:=by
       rw[wired (b v) (f:=R) (by rw[map_zero]; exact he.dye.analyticAt),map_zero]; congr 1;ext1 i; fin_cases i <;> simp [b]
    have hv: R ∘ b v=R∘ b w:=by
       funext i; apply h; intro j hv hw; change input G s _ j=input G s _ j; rw[input_color,input_color]; congr 1; change edgeColor (B i v) j=edgeColor (B i w) j; unfold B; simp only [map_add,map_smul,Pi.smul_apply,Pi.add_apply,hx _ hv hw]
    rw [hh v,hh w,hv]
lemma cellar (hn:2≤ s.val)(ht:Nonwrapping P o)(h:LocalOn P F)(he: Cleric F)(hp:G.Simple)(v: E4→ G.Color)(x:Link G s): iteratedFDeriv ℝ 2 (F∘input G s) 0 ![x,stepC o (Place.jump v)]=0:=by
    let t(i:Site s):= v (Place.seat (lift (i-o))); let y:= gaugeColor (n:=s) (G:=G)|>.symm t; let L:= cant (1:Config G s) y
    rw[shadeL h he _ _ L (fun i hi _=>?_ )]; rotate_left
    · rw[cant_at,show edgeColor (stepC o _) i=_ from congr_fun (edgeColor.apply_symm_apply _) i,Pi.one_apply,G.adjoint_one]; unfold Place.jump; simp [t,y,lift_end hn ht _ hi i.2]
    have hh:= dyed_beam he hp; change Kbody F*mail (1:Config G s) =0 at hh
    have hτ: damage (pocket _) (F∘ input G s) 0= Kbody F:=by unfold Kbody beamH; rw[show bal 1 F= F ∘ input G s from funext fun i=>by simp[bal] ]
    have hz:= detracts (pocket _) (F∘ input G s) 0 x L; rw[hτ,cash_pocket,cash_pocket] at hz; rw [← hz, ← show mail 1 *ᵥ y= L from mailed .., Matrix.mulVec_mulVec,hh, zero_mulVec,dotProduct_zero]
end value
end YM.Trace.Kits
