import YM.WilsonBulk.Slice.Preserve

/-!
# Precision and Hessian real to any chamber
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical BigOperators
open Finset Function Filter Matrix
variable {α β κ ι : Type} {A B : Type} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B]
  [Fintype α] [Fintype β]

section
omit [Fintype β]
-- multiplication across real-coeff matrix edges

def quill (V : Matrix β α ℝ) (x : α→A) (i : β) := ∑ k,V i k • x k
lemma quill_map (V : Matrix β α ℝ) (x : α→A) (F : A→ₗ[ℝ]B) (i : β) : F (quill V x i)=quill V (F ∘ x) i := by simp [quill,Function.comp]
lemma quill_real (V : Matrix β α ℝ) (x : α→ℝ) : quill V x= V*ᵥ x := rfl
lemma quill_add (V : Matrix β α ℝ) (x y : α→A) : quill V (x+y)= quill V x+quill V y := by ext; simp [quill,smul_add,sum_add_distrib]
lemma quill_sub (V : Matrix β α ℝ) (x y : α→A) : quill V (x-y)= quill V x-quill V y := by ext; simp [quill,smul_sub,sum_sub_distrib]
lemma quill_one [DecidableEq α] (x : α→A) : quill (1:Matrix α α ℝ) x=x := by ext; simp [quill,Matrix.one_apply,ite_smul]
lemma quill_zero (V : Matrix β α ℝ) : quill V (0:α→A)=0 := by ext; simp [quill]
lemma fulcrum (V : Matrix α α ℝ) (x : α→A) (i : α) (D : Derivation ℝ A A) : D (quill V x i) = quill V (fun i=>D (x i)) i := quill_map V x D.toLinearMap _

def knot (x y : α→A) := ∑ i,x i * y i
abbrev furrow (V : Matrix α α ℝ) (x y : α→A) := knot x (quill V y)
abbrev forceQ (V : Matrix α α ℝ) (x : α→ A) := (1/2:ℝ) • furrow V x x
lemma forceQ_map (V : Matrix α α ℝ) (x : α→A) (F : A→ₐ[ℝ] B) : F (forceQ V x)=forceQ V (fun i=>F (x i)) := by simp only [forceQ, furrow,knot,map_smul,map_sum,map_mul,quill]
section
omit [Algebra ℝ A]
lemma knot_symmetric (x y : α→A) : knot x y=knot y x := by simp_rw [knot, mul_comm (x _)]
lemma knot_ladd (x y z : α→A) : knot (x+y) z=knot x z+knot y z := by simp [knot,Pi.add_apply,sum_add_distrib, add_mul]
lemma knot_radd (x y z : α→A) : knot x (y+z)=knot x y+knot x z := by simp [knot,Pi.add_apply,sum_add_distrib,mul_add]
end
lemma D_furrow (V : Matrix α α ℝ) (x y : α→A) (D : Derivation ℝ A A) : D (furrow V x y)=furrow V (fun i=>D (x i)) y+furrow V x (fun i=>D (y i)) := by simp only [furrow,knot,map_sum,D_leib,fulcrum, Finset.sum_add_distrib]
lemma half_twice (x : A) : (1/2:ℝ) • (x+x)=x := by rw [smul_add,← add_smul, show (1/2:ℝ)+1/2=1 by norm_num,one_smul]
end
lemma quill_chain (V : Matrix κ β ℝ) (T : Matrix β α ℝ) (x : α→A) : quill V (quill T x)=quill (V*T) x := by ext1 i; simp only [quill,Matrix.mul_apply, Finset.sum_smul,Finset.smul_sum,smul_smul]; rw [sum_comm]
lemma knot_move (V : Matrix β α ℝ) (x : α→A) (y : β→A) : knot y (quill V x)=knot (quill V.transpose y) x := by
  simp only [knot,quill,mul_sum, sum_mul,transpose_apply,mul_smul_comm,smul_mul_assoc]; rw [sum_comm]
section
omit [Fintype β]
variable {V : Matrix α α ℝ}
lemma furrow_symm (hv : V.IsSymm) (x y : α→A) : furrow V x y=furrow V y x := by unfold furrow; rw [knot_move V,hv.eq,knot_symmetric]
lemma force_D (hv : V.IsSymm) (x : α→A) (D : Derivation ℝ A A) : D (forceQ V x)=furrow V (fun i=>D (x i)) x := by unfold forceQ; rw [Derivation.map_smul,D_furrow,furrow_symm hv x,half_twice]
lemma force_plus (hv : V.IsSymm) (x y : α→A) : forceQ V (x+y)=forceQ V x + forceQ V y + furrow V x y := by
  unfold forceQ furrow; rw [quill_add,knot_ladd,knot_radd,knot_radd,(show knot y _=knot x _ from furrow_symm hv y x), show knot x (quill V x)+knot x (quill V y)+(knot x (quill V y)+knot y (quill V y)) =knot x (quill V x)+knot y (quill V y)+(knot x (quill V y)+knot x (quill V y)) by abel]; rw [smul_add,half_twice,smul_add]
-- local Hessian exponent
open PowerSeries
lemma force_top (V : Matrix α α ℝ) : forceQ V (fun i=> (privateName i:StageD α ι))= C (forceQ V ((fun i=>MvPolynomial.X (Sum.inl i)) : α→ Formula (Chamber α ι))) := by
  -- parentheses syntax
  exact (forceQ_map V ((fun i=> MvPolynomial.X (Sum.inl i)) : α → Formula (Chamber α ι)) (post _)).symm
lemma force_player (hv : V.IsSymm) (i : α) : inflow (ι:=ι) i (forceQ V privateName) = quill V privateName i := by rw [force_D hv]; unfold furrow knot; simp [inflow,privateName,ite_mul]
end
lemma force_transfer (V : Matrix β β ℝ) (T : Matrix β α ℝ) (x : α→ A) : forceQ V (quill T x)=forceQ (T.transpose* V * T) x := by
  unfold forceQ furrow; rw [knot_symmetric (quill T _),knot_move,quill_chain,quill_chain,knot_symmetric]
end YM.WilsonBulk.Sheet
