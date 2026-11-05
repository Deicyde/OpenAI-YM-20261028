import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Coordinate and signed permutation conventions

Time is axis 3 throughout (spatial axes `i.castSucc`).
The flip flag is indexed by the **input** axis. This action will be used on
sites/paths in native coordinates and on spacetime arguments.
-/
set_option autoImplicit false

namespace YM

abbrev Axis := Fin 4
abbrev SpaceAxis := Fin 3
abbrev timeAxis : Axis := Fin.last 3
abbrev Four (R : Type*) := Axis → R

@[ext] structure Signed where
  perm : Equiv.Perm Axis
  flip : Axis → Bool
  deriving DecidableEq

namespace Signed

instance : Fintype Signed := Fintype.ofEquiv (Equiv.Perm Axis × (Axis → Bool))
  { toFun a := ⟨a.1,a.2⟩, invFun b := (b.perm,b.flip), left_inv _ := rfl, right_inv _ := rfl }

instance : One Signed := ⟨⟨Equiv.refl _, fun _ => false⟩⟩
instance : Mul Signed := ⟨fun a b =>
  ⟨b.perm.trans a.perm, fun i => (a.flip (b.perm i)).xor (b.flip i)⟩⟩
instance : Inv Signed := ⟨fun a => ⟨a.perm.symm, fun i => a.flip (a.perm.symm i)⟩⟩

@[simp] theorem one_perm : (1 : Signed).perm = Equiv.refl _ := rfl
@[simp] theorem one_flip (i : Axis) : (1 : Signed).flip i = false := rfl
theorem mul_perm (a b : Signed) : (a*b).perm = b.perm.trans a.perm := rfl
@[simp] theorem mul_perm_apply (a b : Signed) (i : Axis) : (a*b).perm i = a.perm (b.perm i) := rfl
@[simp] theorem mul_flip (a b : Signed) (i : Axis) :
    (a*b).flip i = (a.flip (b.perm i)).xor (b.flip i) := rfl
@[simp] theorem inv_perm (a : Signed) : a⁻¹.perm = a.perm.symm := rfl
@[simp] theorem inv_flip (a : Signed) (i : Axis) : a⁻¹.flip i = a.flip (a.perm.symm i) := rfl

instance : Group Signed where
  one_mul x := Signed.ext (by ext; simp) (by funext; simp)
  mul_one x := Signed.ext (by ext; simp) (by funext; simp)
  mul_assoc a b c := Signed.ext (by ext; simp) (by funext; simp)
  inv_mul_cancel x := Signed.ext (by ext; simp) (by funext; simp)

variable {R : Type*}

def mirror (i : Axis) : Signed := ⟨Equiv.refl _, fun j => decide (i = j)⟩

@[simp] theorem mirror_inv (i : Axis) : (mirror i)⁻¹ = mirror i := rfl

section
variable [AddGroup R]

def act (s : Signed) (x : Four R) : Four R := fun i =>
  if s.flip (s.perm.symm i) then -x (s.perm.symm i) else x (s.perm.symm i)

@[simp] theorem act_at (s : Signed) (x : Four R) (i : Axis) :
    s.act x (s.perm i) = if s.flip i then - x i else x i := by simp [act]

@[simp] theorem act_one (x : Four R) : act 1 x = x := by funext; simp [act]

theorem act_mul (s r : Signed) (x : Four R) : (s*r).act x = s.act (r.act x) := by
  funext i
  obtain ⟨j,rfl⟩ := (s*r).perm.surjective i
  rw [act_at, mul_perm_apply, act_at, act_at, mul_flip]
  cases s.flip _ <;> cases r.flip _ <;> simp

@[simp] theorem act_inv (s : Signed) (x : Four R) : s.act (s⁻¹.act x) = x := by rw [← act_mul]; simp
@[simp] theorem inv_act (s : Signed) (x : Four R) : s⁻¹.act (s.act x) = x := by rw [← act_mul]; simp
end

section
variable [AddCommGroup R]

@[simp] theorem act_add (s : Signed) (x y : Four R) : s.act (x+y) = s.act x + s.act y := by
  ext i
  dsimp only [Pi.add_apply, act]; split <;> simp [add_comm]

def actEquiv (s : Signed) : Four R ≃+ Four R where
  toFun := act s
  invFun := act s⁻¹
  left_inv := s.inv_act
  right_inv := s.act_inv
  map_add' := act_add _

@[simp] theorem act_zero (s : Signed) : s.act (0 : Four R) = 0 := (actEquiv (R := R) s).map_zero
@[simp] theorem act_neg (s : Signed) (x : Four R) : s.act (- x) = - s.act x := (actEquiv (R := R) s).map_neg _
@[simp] theorem act_sub (s : Signed) (x y : Four R) : s.act (x-y) = s.act x - s.act y := (actEquiv (R := R) s).map_sub _ _

theorem act_injective (s : Signed) : Function.Injective (s.act (R := R)) := s.actEquiv.injective
end
end Signed
end YM
