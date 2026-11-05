import Mathlib.Topology.Compactification.OnePoint.Basic
import YM.SNAG.Kernels



/-!
# Smooth modes with unital bump algebra on Ω compactification

Contraction via *strictly larger* radius than sup; realize sqrt still smooth+const (just continuity at ∞ not enough; locally constant there). Then CFC for whole.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SNAG
open Function Set Filter Spectral Boundary Probe MeasureTheory Measure Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators ContDiff
variable {H : Hilbert} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]

structure Tail (f : C(OnePoint X,ℂ)) : Prop where
  smooth : ContDiff ℝ ∞ (fun x : X => f x)
  quiet : ∀ᶠ x : X in coclosedCompact X, f x=f OnePoint.infty

def R (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] : StarSubalgebra ℂ C(OnePoint X,ℂ) where
  carrier := {f | Tail f}
  mul_mem' {f g} (hf : Tail f) (hg : Tail g) := ⟨hf.smooth.mul hg.smooth,(hf.quiet.and hg.quiet).mono fun _ hi =>
    congr_arg₂ (· * ·) hi.1 hi.2⟩
  add_mem' {f g} (hf : Tail f) (hg : Tail g) := ⟨hf.smooth.add hg.smooth,(hf.quiet.and hg.quiet).mono fun _ hi =>
    congr_arg₂ (· + ·) hi.1 hi.2⟩
  star_mem' {f} (h : Tail f) := ⟨Complex.conjCLE.contDiff.comp h.smooth,h.quiet.mono fun _ hi => congr_arg star hi⟩
  algebraMap_mem' _ := ⟨contDiff_const,Eventually.of_forall fun _ => rfl⟩

def off (f : ↑(R X)) : ℂ := f.val OnePoint.infty

def test (f : ↑(R X)) : Probe X :=
  have h : Tail f.val := f.property
  have hh : HasCompactSupport (fun x : X => f.val x-off f) :=
    hasCompactSupport_iff_eventuallyEq.mpr (h.quiet.mono fun _ hi => show _-_=(0:ℂ) from sub_eq_zero.mpr hi)
  hh.toSchwartzMap (h.smooth.sub contDiff_const)


lemma teste (f : ↑(R X)) (x : X) : test f x=f.val x-off f := rfl

/-- Add back single compact test layer. -/
def adds (f : Probe X) (h : HasCompactSupport ⇑f) : ↑(R X) :=
  have hv : ∀ᶠ x : X in coclosedCompact X, f x=0 := hasCompactSupport_iff_eventuallyEq.mp h
  let V := OnePoint.continuousMapMk ⟨⇑f,f.continuous⟩ 0 (by
    exact tendsto_const_nhds.congr' (hv.mono fun _ hi => hi.symm))
  ⟨V,show Tail V from ⟨f.smooth _,hv⟩⟩
lemma comes (f : Probe X) (h : HasCompactSupport ⇑f) : test (adds f h)=f := by
  ext1 i; rw [teste]; change f i-0=f i; rw [sub_zero]

lemma separates (p q : OnePoint X) (h : p≠q) : ∃ f : C(OnePoint X,ℂ), f∈ R X ∧ f p≠f q := by
  classical
  have he (x : X) (r : ℝ) (hr : 0 < r) : ∃ f : ↑(R X), off f=0 ∧ f.val x=1 ∧ ∀ i : X, r ≤ dist i x → f.val i=0 := by
    let F : ContDiffBump x := ⟨r/2,r,by positivity,by linarith⟩
    let g : Probe X := (F.hasCompactSupport.comp_left ofReal_zero).toSchwartzMap (ofRealCLM.contDiff.comp F.contDiff)
    let C := adds g (show _ from F.hasCompactSupport.comp_left ofReal_zero)
    refine ⟨C,rfl,?_,?_⟩
    · change (F x:ℂ)=1; rw [F.one_of_mem_closedBall (Metric.mem_closedBall_self F.rIn_pos.le)]; norm_num
    intro i hi
    change (F i:ℂ)=0
    apply congr_arg _ (show F i=0 from notMem_support.mp ?_)
    rwa [F.support_eq, Metric.mem_ball, not_lt]
  induction p using OnePoint.rec <;> induction q using OnePoint.rec
  · exact absurd rfl h
  · rename_i x
    obtain ⟨f,h₁,h₂,-⟩ := he x 1 zero_lt_one
    refine ⟨f,f.property,?_⟩; change off f≠_; rw [h₁,h₂];norm_num
  · rename_i x
    obtain ⟨f,h₁,h₂,-⟩ := he x 1 zero_lt_one
    change f.val OnePoint.infty=0 at h₁
    exact ⟨f,f.property,by rw [h₂,h₁];norm_num⟩
  rename_i x y
  have hp : 0 < dist y x := dist_pos.mpr (fun s => h (congr_arg OnePoint.some s.symm))
  obtain ⟨f,h₁,h₂,h₃⟩ := he x _ hp
  exact ⟨f,f.property,by rw [h₂,h₃ y le_rfl]; norm_num⟩

abbrev embed : R X →⋆ₐ[ℂ] C(OnePoint X,ℂ) := (R X).subtype
lemma here : DenseRange (embed (X := X)) := by
  have he : (R X).SeparatesPoints := by
    intro p q hp
    obtain ⟨f,hf,hq⟩ := separates _ _ hp
    exact ⟨_,⟨_,hf,rfl⟩, hq⟩
  have hh := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (R X) he
  intro x
  rw [show Set.range (embed (X := X))=(R X: Set _) by simp [embed]]
  change x∈ (R X).topologicalClosure; rw [hh]; trivial

/-- Multiply star shuffle; source levels separate. -/
lemma thick (u : ↑(R X)) (v : ↑(R X)) (p : X) :
    (test (u*v)-off v • test u-off u • test v) p=test u p * test v p := by
  simp [teste,off];ring

variable [MeasurableSpace X] [BorelSpace X] (S : Orbit H X)
def records (u : ↑(R X)) : H.Op := off u • 1 + send S (test u)

def optic : R X →⋆ₐ[ℂ] H.Op where
  toFun := records S
  map_zero' := by
    rw [records,show off (0:R X)=0 from rfl,show test (0:R X)=0 by ext1; simp [teste,off],map_zero];simp
  map_one' := by
    rw [records,show off (1:R X)=1 from rfl,show test (1:R X)=0 by ext1; simp [teste,off],map_zero]; simp
  map_mul' a b := by
    let A := test a
    let B := test b
    unfold records
    rw [show off (a*b)=off a*off b from rfl,mul_smul,right_distrib,left_distrib,left_distrib]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,mul_one,one_mul]
    have hz : send S A*send S B=_ := compose S (thick a b)
    dsimp only [A,B] at hz
    rw [hz,map_sub,map_sub,map_smul,map_smul,smul_comm (off b) (off a)];abel
  map_add' a b := by
    unfold records; rw [show off (a+b)=off a+off b from rfl,show test (a+b)=test a+test b by ext1; simp [off, teste]; ring,map_add]; simp [add_smul]; abel
  commutes' c := by
    unfold records
    rw [show off _ = c from rfl, show test _=0 by ext1; rw [teste];change c-c=0; rw [sub_self],map_zero];simp [Algebra.algebraMap_eq_smul_one]
  map_star' u := by
    rw [records,records, show off (star u)=star (off u) from rfl,
      show test (star u)=bar (test u) from SchwartzMap.ext (fun x => by simp [off, teste]), starify]; simp

lemma in_map (p : Probe X) (h : HasCompactSupport ⇑p) : optic S (adds p h)=send S p := by
  change records S _=_
  rw [records,comes,show off (adds p h)=0 from rfl];simp
end YM.SNAG
