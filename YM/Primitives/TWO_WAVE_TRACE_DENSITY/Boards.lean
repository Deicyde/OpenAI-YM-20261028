import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Transfer

/-!
# Whole cell arrays, including input field and free vertical slots
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Function Matrix
open scoped BigOperators Classical

variable {n : Side} {α β τ : Type} {k : ℕ} {R : Type}

abbrev Board (α : Type) (n : Side) (R:Type) := Leaf n α→R

def up {τ τ' : Type} (e : τ→τ') (i : Leaf n τ) : Leaf n τ' := (i.1,e i.2)
-- Query either sector.
abbrev lead (β : Type) (i : Leaf n α) := up (Sum.inl (β:=β)) i
abbrev peg (α : Type) (i : Leaf n β) := up (Sum.inr (α:=α)) i

def here {τ τ':Type} (e : τ→τ') (v : Board τ' n R) : Board τ n R := fun i=> v (up e i)

def mingle (a : Board α n R) (b : Board β n R) : Board (α⊕β) n R :=
    fun i=>Sum.elim (fun j=>a (i.1,j)) (fun j=>b (i.1,j)) i.2

lemma pair_mingle (a : Board (α⊕β) n R) : mingle (here Sum.inl a) (here Sum.inr a) = a := by
  ext1 i; rcases i with ⟨x,i|j⟩ <;> rfl

-- cell-only operator joins




lemma ray_add (p : Site n) (v w:α→ℂ) : ray p v+ray p w=ray p (v+w):=by ext1 i; simp [ray,mul_add]


variable [Fintype α] [Fintype β]




section module
variable [Ring R]






end module




-- pack into normalized E × F coordinates

def desks (α β:Type) [Fintype α] [Fintype β] (n : Side) :
    Board (α⊕β) n ℝ ≃L[ℝ] Board α n ℝ × Board β n ℝ :=
    LinearEquiv.toContinuousLinearEquiv {
      toFun v := (here Sum.inl v,here Sum.inr v)
      invFun v:= mingle v.1 v.2
      left_inv v:=pair_mingle v
      right_inv _:= Prod.ext rfl rfl
      map_add' _ _:= rfl
      map_smul' _ _:= rfl }

lemma desks_peg (i : Leaf n β) : desks α β n (spot (peg α i))=(0,spot i) := by
  classical
  apply Prod.ext <;> ext1 j
  · change spot _ (lead β j)=0
    by_cases hh:lead β j=peg α i <;> simp [spot,lead,peg,up] at *
  change spot _ (peg α j)=spot i j
  have he: Injective (fun x : Leaf n β=> peg α x):=fun i j h=>by
    rcases i with ⟨x,y⟩; rcases j with ⟨z,w⟩; simpa [peg,up] using h
  simp [spot,Pi.single_apply,he.eq_iff]
end YM.Primitives.TwoWave
