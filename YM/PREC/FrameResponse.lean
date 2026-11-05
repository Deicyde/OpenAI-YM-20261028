import YM.Tree.Cut

/-!
# Candidate derivative of actual predictor

`mean` and `probe` are real counting cochain matrices, root identity on
physical additive gauge differences. The identifications with analytic kernels
and with ACTUAL derivatives of the minimizing stochastic kernel require more
work. These lemmas do not linearize the physical resolution.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Precision
open Lattice Wilson RG Matrix Exterior Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {c f : Side} {G : Gauge}

def integralLink (x : Site f) (w : Walk) : form 1 f →ₗ[ℝ] ℝ where
  toFun v := linkSum (fun e => v (e.1,coord e.2)) x w
  map_add' a b := by
    induction w generalizing x with
    | nil => simp [linkSum]
    | cons d w ih => simp only [linkSum]; rw [ih]; split <;> simp [*] <;> abel
  map_smul' t a := by
    induction w generalizing x with
    | nil => simp [linkSum]
    | cons d w ih => simp only [linkSum]; rw [ih]; split <;> simp [*,mul_add]

lemma telescopes (v : form 0 f) (x : Site f) (w : Walk) :
    integralLink x w (d 0 f *ᵥ v)=v (stop x w,vac)-v (x,vac) := by
  change linkSum (fun e => (d 0 f *ᵥ v) (e.1,coord e.2)) x w=_
  induction w generalizing x with
  | nil => simp [linkSum,stop]
  | cons b w ih =>
    rw [linkSum,stop,ih]; rcases b with ⟨i,y|y⟩ <;> simp [Step.used,d_sites,Step.vec,sub_eq_add_neg] <;> abel

section one
variable (S : StepData c f)

/-- offset of patch point in FINE units from actual root. -/
def atPoint (x : Site c) (a : S.patch.Points) := wrap f a.val+S.ratio.embed x

lemma reach (x : Site c) (a b : S.patch.Points) (i : Lattice.Order) :
    stop (atPoint S x a) (route a.val b.val i)=atPoint S x b := by
  unfold atPoint
  have hh (b : Site f) (v : Cover) (w : Walk) : stop (wrap f v+b) w=wrap f (stop v w)+b := by
    induction w generalizing v with
    | nil => rfl
    | cons d l ih => rw [stop,stop, ← ih,map_add,wrap_vec, add_right_comm (wrap f v)]
  rw [hh, route_end]

lemma crossSite (x : Site c) (a : S.patch.Points) (i : Axis) :
    stop (atPoint S x a) (S.repath i)=atPoint S (x+step i) a := by rw [StepData.stop_repath,atPoint,atPoint,S.leap,add_assoc]

/-- frame derivative uniform-centered. `β_{yx}` E Bfder
is MINUS the outgoing weighted path sum. -/
def tau (x : Site c) (a : S.patch.Points) : form 1 f →ₗ[ℝ] ℝ :=
    -((Fintype.card S.patch.Points:ℝ)⁻¹ • ∑ b : S.patch.Points,
      (Fintype.card Lattice.Order:ℝ)⁻¹ • ∑ i : Lattice.Order, integralLink (atPoint S x a) (route a.val b.val i))

def adjusted (x : Site c) (a : S.patch.Points) := tau S x a-∑ b, S.patch.weight b • tau S x b

def fixRoot : Matrix (Body 0 c) (Body 1 f) ℝ := LinearMap.toMatrix' (LinearMap.pi (fun i : Body 0 c => adjusted S i.1 S.patch.center))

def mean : Matrix (Body 1 c) (Body 1 f) ℝ := LinearMap.toMatrix' (LinearMap.pi (fun i : Body 1 c =>
    ∑ a, S.patch.weight a • integralLink (atPoint S i.1 a) (S.repath (axisEquiv.symm i.2))))

def probe : Matrix (Body 1 c) (Body 1 f) ℝ := mean S+d 0 c * fixRoot S

lemma psi_proj (v : form 0 f) (x : Body 0 c) :
    (fixRoot S *ᵥ (d 0 f *ᵥ v)) x=v ((S.ratio.embed x.1),vac)- ∑ a,S.patch.weight a*v (atPoint S x.1 a,vac) := by
  let F a := v (atPoint S x.1 a,vac)
  have he (a) : tau S x.1 a (d 0 f *ᵥ v)=F a -(Fintype.card S.patch.Points:ℝ)⁻¹*∑ i,F i := by
    simp only [tau,LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.sum_apply, telescopes, reach]
    simp only [smul_eq_mul,sum_const,card_univ,nsmul_eq_mul, F]
    field_simp -- expand avg
    simp [Finset.sum_sub_distrib]
  simp only [fixRoot, LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted,LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, he]
  simp_rw [smul_eq_mul, mul_sub (S.patch.weight _), Finset.sum_sub_distrib,
    ← Finset.sum_mul, S.patch.weight_sum, one_mul]
  unfold F
  rw [show atPoint S x.1 _=S.ratio.embed x.1 by rw [atPoint,show S.patch.center.val=0 from rfl,map_zero,zero_add]]
  abel

lemma mean_site (v : form 0 f) (x : Body 1 c) :
    (mean S *ᵥ (d 0 f *ᵥ v)) x = ∑ a, S.patch.weight a * (v (atPoint S (x.1+step (axisEquiv.symm x.2)) a,vac) - v (atPoint S x.1 a,vac)) := by
  simp only [mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply, LinearMap.smul_apply, telescopes, crossSite, smul_eq_mul]

def centered (v : form 0 f) : form 0 c := fun x => v (S.ratio.embed x.1, x.2)

lemma root_gradient (v : form 0 f) : probe S *ᵥ (d 0 f *ᵥ v)=d 0 c *ᵥ centered S v := by
  funext ⟨x,i⟩
  obtain ⟨a,rfl⟩ := axisEquiv.surjective i
  rw [probe,Matrix.add_mulVec, ← Matrix.mulVec_mulVec,Pi.add_apply, mean_site]
  simp only [show axisEquiv.symm (coord a)=a from axisEquiv.symm_apply_apply _,coord_map,d_sites,psi_proj, mul_sub,Finset.sum_sub_distrib]; unfold centered; abel

/-! Analytic matches without stronger rate conditions; not claims. -/

/-- germ of predictor always initial up choice on open flat patch. -/
def differentiates (T : StepData c f) (G : Gauge) : Prop :=
    (∀ i : T.Choices, ∀ e, ContDiffAt ℝ ω (fun v : fieldDir G f 1 => G.mat (T.prediction (RG.increment 1 (collect G v)) i e)) 0) ∧
    (∀ i : T.Choices, ∀ x : fieldDir G f 1, ∀ e : Edge (Site c),
      HasDerivAt (fun s : ℝ => G.mat (T.prediction (RG.increment 1 (s • collect G x)) i e))
        (G.colorMat (WithLp.toLp 2 (fun j : G.ColorIndex => (probe T *ᵥ parts G 1 x j) (e.1, coord e.2)))) 0)
end one
end YM.Precision
