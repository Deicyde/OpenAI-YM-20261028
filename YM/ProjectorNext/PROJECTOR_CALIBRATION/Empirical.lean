import YM.ProjectorNext.PROJECTOR_CALIBRATION.Force

/-!
# Smooth reads on a finite cover stencil

Track ALL endpoints of positive links, irrespective of whether the cylinder
is evaluated in cover or at the torus. Left derivatives of these reads have
authentic values; they too have smooth matrix formulas before any masks; no
wrapping hypotheses needed until differentiating a PLACED read with respect
to torus variables. No claim derivatives have affordable bounds from this
calculus alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Filter Function
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge}

instance (s : Finset Cover) : Fintype (UsedEdges s) := by
  haveI : Finite (UsedEdges s) := Finite.of_injective (fun i : UsedEdges s => Prod.mk (⟨i.val.1,i.property.1⟩ : s) i.val.2) (by
    rintro ⟨⟨x,i⟩,h⟩ ⟨⟨y,j⟩,k⟩ he; obtain ⟨e1,e2⟩ := Prod.mk.inj he
    have e3 : x=y := congr_arg Subtype.val e1
    exact Subtype.ext (Prod.ext e3 e2))
  exact Fintype.ofFinite _

abbrev Scan (G : Gauge) (s : Finset Cover) := UsedEdges s → G.Mat

def reel (G : Gauge) (s : Finset Cover) (U : CoverConfig G) : Scan G s := fun i => G.mat (U i.val)

def pushLink (U : CoverConfig G) (D : Edge Cover → G.Color) (t : ℝ) : CoverConfig G := fun i =>
    G.lieExp (t • D i) * U i

variable {E K B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- representation on the given stencil by a smooth function of matrices. -/
def Empirical (s : Finset Cover) (f : CoverConfig G → E) := ∃ g : Scan G s → E,
    ContDiff ℝ ω g ∧ ∀ U, f U = g (reel G s U)

def Small (G : Gauge) (f : CoverConfig G → E) := ∃ s : Finset Cover, Empirical s f

variable {s q : Finset Cover} {f g : CoverConfig G → E} {v : CoverConfig G → K}
namespace Empirical

lemma enlarge (h : Empirical s f) (hS : s⊆q) : Empirical q f := by
  let p : UsedEdges s → UsedEdges q := fun i => ⟨i.val,hS i.property.1,hS i.property.2⟩
  obtain ⟨x,hx,hf⟩ := h
  exact ⟨(fun A => x (A ∘ p)), hx.comp (contDiff_pi.mpr fun i => contDiff_apply ..), hf⟩

lemma constant (x : E) : Empirical s fun _ : CoverConfig G => x := ⟨_,contDiff_const, fun _ => rfl⟩

lemma link (i : UsedEdges s) : Empirical s fun U : CoverConfig G => G.mat (U i.val) :=
    ⟨(fun U => U i),contDiff_apply ..,fun _ => rfl⟩

protected lemma comp (h : Empirical s f) {L : E → B} (ht : ContDiff ℝ ω L) : Empirical s (fun U => L (f U)) := by
  obtain ⟨x,hx,hf⟩ := h; exact ⟨_,ht.comp hx,fun i => congr_arg L (hf i)⟩

protected lemma pair (h : Empirical s f) (hv : Empirical s v) : Empirical s fun U => (f U,v U) := by
  obtain ⟨x,hx,hf⟩ := h; obtain ⟨z,hz,hv⟩ := hv; exact ⟨_,hx.prodMk hz,fun i => Prod.ext (hf i) (hv i)⟩

lemma vector {I : Type*} [Fintype I] (f : I → CoverConfig G → E) (h : ∀ i, Empirical s (f i)) :
    Empirical s fun U i => f i U := by
  choose x hx he using h
  exact ⟨_,contDiff_pi.mpr hx,fun U => funext fun i => he i U⟩

lemma supported (h : Empirical s f) : LocalOn s f := by
  obtain ⟨x,-,he⟩ := h
  intro U V hh; rw [he,he]
  exact congr_arg x (funext fun i : UsedEdges s => congr_arg G.mat (hh i.val i.property.1 i.property.2))



/-- Compositions with any tested matrix law, also useful for reads other than
Hol. Only need germ around each needed point. -/
lemma substituted (h : Empirical s f) {T : K → CoverConfig G} {a : K}
    (he : ∀ i : UsedEdges s, ContDiffAt ℝ ω (fun y => G.mat (T y i.val)) a) :
    ContDiffAt ℝ ω (fun y => f (T y)) a := by
  obtain ⟨x,hx,h⟩ := h
  simp_rw [h]
  exact hx.contDiffAt.comp a (contDiffAt_pi.mpr he : ContDiffAt ℝ ω (fun y => reel G s (T y)) a)

end Empirical

namespace Small



lemma link (e : Edge Cover) : Small G fun (U : CoverConfig G) => G.mat (U e) :=
    ⟨{e.1,e.1+step e.2},Empirical.link (s:={e.1,e.1+step e.2}) ⟨e,by simp,by simp⟩⟩

lemma constant (x : E) : Small G fun _ => x := ⟨∅,Empirical.constant _⟩

protected lemma comp (h : Small G f) {L : E → B} (ht : ContDiff ℝ ω L) : Small G (fun U => L (f U)) := by
  obtain ⟨s,h⟩ := h; exact ⟨s,h.comp ht⟩

protected lemma pair (h : Small G f) (hv : Small G v) : Small G fun U => (f U,v U) := by
  obtain ⟨s,h⟩ := h; obtain ⟨q,hv⟩ := hv
  exact ⟨s∪q,(h.enlarge Finset.subset_union_left).pair (hv.enlarge Finset.subset_union_right)⟩

lemma two (h : Small G f) (hv : Small G v) (L : E → K → B) (ht : ContDiff ℝ ω (uncurry L)) :
    Small G fun U => L (f U) (v U) := (h.pair hv).comp ht

lemma linear (h : Small G f) (L : E →L[ℝ] B) : Small G fun U => L (f U) := h.comp L.contDiff

lemma add (h : Small G f) (hh : Small G g) : Small G fun U => f U+g U :=
    two h hh (fun x y => x+y) (contDiff_fst.add contDiff_snd)
lemma sub (h : Small G f) (hh : Small G g) : Small G fun U => f U-g U :=
    two h hh (fun x y => x-y) (contDiff_fst.sub contDiff_snd)

protected lemma mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {Y Z : CoverConfig G → A}
    (h : Small G Y) (hh : Small G Z) : Small G fun U => Y U * Z U :=
    two h hh (fun x y => x*y) (contDiff_fst.mul contDiff_snd)

lemma vector {I : Type*} [Fintype I] (f : I → CoverConfig G → E) (h : ∀ i, Small G (f i)) :
    Small G fun U i => f i U := by
  classical
  choose s hs using h
  exact ⟨_,Empirical.vector f fun i => (hs i).enlarge (show s i ⊆ Finset.univ.biUnion s from
    fun x hx => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩)⟩

lemma sum {I : Type*} (w : Finset I) (u : I → CoverConfig G → E) (h : ∀ i∈w, Small G (u i)) :
    Small G fun U => ∑ i∈w,u i U := by
  classical
  induction w using Finset.induction_on with
  | empty => simp; exact Small.constant _
  | insert a w ha ih => simp only [Finset.sum_insert ha]; exact (h a (by simp)).add (ih fun i hi => h i (by simp_all))

lemma matStar {U : CoverConfig G → G.Mat} (h : Small G U) : Small G fun y => star (U y) :=
    h.comp (L:=fun u => star u) (starL' ℝ (A:=G.Mat)).contDiff

lemma path (a : Walk) (x : Cover) : Small G fun U : CoverConfig G => G.mat (travel U x a) := by
  induction a generalizing x with
  | nil => exact Small.constant _
  | cons l a ih =>
    simp only [travel,G.mat_mul]; apply Small.mul _ (ih _)
    unfold Step.read; split
    · simp only [G.mat_inv]; exact Small.matStar (Small.link _)
    exact Small.link _

lemma curvature {T : CoverConfig G → G.El} (h : Small G fun U => G.mat (T U)) :
    Small G fun U => G.curvature (T U) := by
  simp only [Gauge.curvature,G.mat_inv]
  exact h.comp (L:=fun z => G.projectColor.toContinuousLinearMap ((1/2:ℝ) • (z-star z)))
    (G.projectColor.toContinuousLinearMap.contDiff.comp ((contDiff_const (c:=(1/2 : ℝ))).smul (contDiff_id.sub (starL' ℝ (A:=G.Mat)).contDiff)))

lemma adjoint {T : CoverConfig G → G.El} {Y : CoverConfig G → G.Color}
    (h : Small G fun U => G.mat (T U)) (hp : Small G Y) : Small G fun U => G.adjoint (T U) (Y U) := by
  refine (h.pair hp).comp (L:=fun z => G.projectColor.toContinuousLinearMap
    (z.1*G.colorMat.toContinuousLinearMap z.2*star z.1)) ?_
  refine G.projectColor.toContinuousLinearMap.contDiff.comp ?_
  exact (contDiff_fst.mul (G.colorMat.toContinuousLinearMap.contDiff.comp contDiff_snd)).mul ((starL' ℝ (A:=G.Mat)).contDiff.comp contDiff_fst)

lemma slot (a : RG.Slot) : Small G a.eval := Small.adjoint (T:=fun U => travel U 0 a.walk) (Small.path ..)
    (Small.curvature (T:=fun U => faceValue U (a.offset,a.plaq)) (Small.path ..))

lemma staple (ν : Axis) (x : Cover) (q : PlaqAxes) : Small G fun U => Calibration.staple U ν x q := by
  have hf (x : Cover) : Small G fun U : CoverConfig G => G.mat (faceValue U (x,q)) := Small.path ..
  have he (x : Cover) (l : Axis) : Small G fun U : CoverConfig G => G.curvature ((U (x,l))⁻¹*faceValue U (x,q)*U (x,l)) := by
    apply Small.curvature; simp_rw [G.mat_mul,G.mat_inv]; exact (((Small.link _).matStar).mul (hf _)).mul (Small.link _)
  simp_rw [Calibration.staple]
  refine Small.add ?_ ?_
  all_goals split
  · exact (Small.curvature (hf _)).sub (he _ _)
  · exact Small.constant _
  · exact (he _ _).sub (Small.curvature (hf _))
  exact Small.constant _
lemma gradient (x : Cover) (ν : Axis) : Small G fun U => Calibration.gradient U x ν := Small.sum _ _ fun i _ => Small.staple ν x i
lemma sample (x : Position) : Small G fun U => Calibration.sample U x := Small.adjoint (T:=fun U => travel U 0 (base x)) (Small.path ..) (Small.gradient ..)

end Small

variable (f) in
def left (e : Edge Cover) (c : G.Color) (U : CoverConfig G) := deriv (fun t => f (pushLink U (Pi.single e c) t)) 0

namespace Empirical

private def speed (e : Edge Cover) (c : G.Color) (s : Finset Cover) (y : Scan G s) : Scan G s := fun i =>
    G.colorMat ((Pi.single e c : Edge Cover → G.Color) i.val) * y i

private lemma instant (v : G.Color) (x : G.El) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • v) * x))
    (G.colorMat v * G.mat x) 0 := by
  simp only [G.mat_mul,G.mat_lieExp,map_smul]
  simpa using! (hasDerivAt_exp_smul_const (G.colorMat v) (0:ℝ)).mul_const (G.mat x)

private lemma speed_exact (e : Edge Cover) (c : G.Color) (U : CoverConfig G) (s : Finset Cover) :
    HasDerivAt (fun t => reel G s (pushLink U (Pi.single e c) t)) (speed e c s (reel G s U)) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  exact instant (G:=G) _ _

@[simp] lemma at_nil (U : CoverConfig G) (D : Edge Cover → G.Color) : pushLink U D 0=U := by
  funext i; apply G.mat_injective; simp [pushLink]

private lemma formula {x : Scan G s → E} (e : Edge Cover) (c : G.Color)
    (h : ContDiff ℝ ω x) (he : ∀ U, f U = x (reel G s U)) (U : CoverConfig G) :
    HasDerivAt (fun t => f (pushLink U (Pi.single e c) t))
      (fderiv ℝ x (reel G s U) (speed e c s (reel G s U))) 0 := by
  simp_rw [he]
  exact ((h.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt_of_eq
    0 (speed_exact ..) (by rw [at_nil])

theorem authentic (h : Empirical s f) (U : CoverConfig G) (e : Edge Cover) (c : G.Color) :
    HasDerivAt (fun t => f (pushLink U (Pi.single e c) t)) (left f e c U) 0 := by
  obtain ⟨x,hx,h⟩ := h
  have he := formula e c hx h U
  rw [left,he.deriv]; exact he

theorem linear (h : Empirical s f) (U : CoverConfig G) (e : Edge Cover) :
    IsLinearMap ℝ (fun c => left f e c U) := by
  obtain ⟨x,hx,h⟩ := h
  have he (c : G.Color) : left f e c U = _ := (formula e c hx h U).deriv
  simp_rw [he]
  constructor
  · intro a b
    rw [← map_add]; apply congr_arg; funext i
    change G.colorMat _ * _ = _ * _ + _ * _
    by_cases hi : i.val=e <;> simp [hi,add_mul]
  intro a b
  rw [← map_smul]; apply congr_arg; funext i
  change G.colorMat _ * _ = a • (_ * _)
  by_cases hi : i.val=e <;> simp [hi]

theorem retains (h : Empirical s f) (e : Edge Cover) (c : G.Color) : Empirical s (left f e c) := by
  obtain ⟨x,hx,h⟩ := h
  refine ⟨_, (hx.fderiv_right (m:=ω) (by simp)).clm_apply (g:=speed e c s) ?_,fun U => (formula e c hx h U).deriv⟩
  apply contDiff_pi.mpr; intro i
  exact contDiff_const.mul (contDiff_apply _ _ i)
end Empirical

lemma Small.derivative (h : Small G f) (e : Edge Cover) (c : G.Color) : Small G (left f e c) := by
  obtain ⟨s,hs⟩ := h; exact ⟨s,hs.retains e c⟩

end YM.ProjectorNext.Calibration
