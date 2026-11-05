import YM.WilsonBulk.Slice.Casing

/-!
# Centering criterion for RG joint force in Tape
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology BigOperators Classical
open Finset Matrix PowerSeries Function
variable {α β κ ι A M : Type} [Fintype α] [Fintype β] [Fintype κ] [Fintype ι]
variable [CommRing A] [CommRing M] [Algebra ℝ A] [Algebra ℝ M]

section
omit [Fintype α]
variable {V W : Matrix α β ℝ}
lemma quill_fuse (x : β→A) : quill (V+W) x= quill V x+ quill W x := by ext; simp [quill, add_smul, sum_add_distrib]
lemma quill_diff (x : β→A) : quill (V-W) x=quill V x-quill W x := by ext; simp [quill,sub_smul,sum_sub_distrib]
lemma quill_scale (x : β→A) (r : ℝ) : quill (r • V) x=r • quill V x := by ext; simp [quill,Finset.smul_sum,smul_smul]
lemma knot_scales (x y : β→A) (r : ℝ) : knot x (r • y)=r • knot x y := by simp only [knot,Pi.smul_apply,mul_smul_comm,Finset.smul_sum]
omit [Algebra ℝ A] in
lemma knot_sub (x y z : β→A) : knot x (y-z)=knot x y - knot x z := by simp [knot,mul_sub,Finset.sum_sub_distrib]
end
omit [Fintype κ] [Fintype ι] -- later isolate

-- blocked full force
def atelier (K : Matrix α α ℝ) (X : Matrix β α ℝ) (p : ℝ) (x : α→A) (y : β→A) :=
  forceQ K x + p • ((1/2:ℝ) • knot (y-quill X x) (y-quill X x))
lemma atelier_map (F : A→ₐ[ℝ]M) (K : Matrix α α ℝ) (X : Matrix β α ℝ) (p : ℝ) (x : α→A) (y : β→A) : F (atelier K X p x y)=atelier K X p (fun i=>F (x i)) (fun i=>F (y i)) := by
  simp only [atelier,map_smul,map_add,forceQ,furrow,knot,map_sum,map_mul, Pi.sub_apply,quill,map_sub]

variable {K B U : Matrix α α ℝ} {X : Matrix β α ℝ} {p : ℝ} {C : Matrix β β ℝ}
abbrev rear (K : Matrix α α ℝ) (X : Matrix β α ℝ) (p : ℝ) := K+p • (X.transpose * X)
omit [Fintype α] in
lemma rear_symm (h : K.IsSymm) : (rear K X p).IsSymm := by simp [Matrix.IsSymm,rear,h.eq]
lemma atelier_alter (x : α→A) (y : β→A) : atelier K X p x y=forceQ (rear K X p) x+(p/2) • knot y y - p • knot y (quill X x) := by
  have he : knot (quill X x) (quill X x)= furrow (X.transpose*X) x x := by rw [knot_move X,quill_chain,knot_symmetric]
  simp only [atelier,forceQ,furrow,rear,quill_fuse,quill_scale,knot_sub,knot_radd,knot_scales]; rw [knot_symmetric (y-quill X x) y, knot_symmetric (y-quill X x) (quill X x),knot_sub,knot_sub,knot_symmetric (quill X x) y,he, furrow]
  module
variable [DecidableEq β]
lemma atelier_bull (V : Matrix α β ℝ) (H : Matrix α α ℝ) (hv : H=rear K X p) (hK : H.IsSymm) (ht : H*V=p • X.transpose) (hg : p • ((1:Matrix β β ℝ)-X*V)=C) (x : α→A) (y : β→ A) :
    atelier K X p (x+quill V y) y= forceQ H x+forceQ C y := by
  have e x : furrow H x (quill V y)=p • knot y (quill X x) := by
    unfold furrow; rw [quill_chain,ht,quill_scale,knot_scales,knot_move, transpose_transpose, knot_symmetric]
  rw [atelier_alter,← hv,force_plus hK,e, quill_add,knot_radd,← hg]; unfold forceQ; rw [e]
  simp only [furrow,quill_scale,knot_scales,quill_diff,quill_chain,knot_sub,quill_one]
  module
end YM.WilsonBulk.Sheet
