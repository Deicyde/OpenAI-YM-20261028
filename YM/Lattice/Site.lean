import YM.Space.Index
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.PNat.Basic

/-!
# Discrete torus and lift to the cover

Euclidean candidate . Centered representatives are in `(-n/2,n/2]`;
affine tests on a nonwrapping support use only the strict inner box so the tie convention
has no effect there. These are lattice units. In particular `separation` measures a native
torus max-distance, not a *length* on the covering lattice.
-/

set_option autoImplicit false
namespace YM.Lattice

abbrev Side := ℕ+
abbrev Per (n : Side) := ZMod n.val
abbrev Site (n : Side) := Four (Per n)
abbrev Cover := Four ℤ
abbrev Edge (X : Type*) := X × Axis

variable {n : Side}

/-- Native unit edge increment. -/
def step {S : Type*} [Zero S] [One S] (i : Axis) : Four S := Pi.single i 1

@[simp] theorem step_apply {S : Type*} [Zero S] [One S] (i j : Axis) :
    (step i : Four S) j = if j = i then 1 else 0 := by
  simp [step, Pi.single_apply]

theorem site_card (n : Side) : Fintype.card (Site n) = n.val ^ 4 := by
  simp [Site, Four, Per, Axis, ZMod.card]

def wrap (n : Side) : Cover →+ Site n where
  toFun p := fun i => (p i : ZMod _)
  map_add' x y := by ext; simp
  map_zero' := by ext; simp

@[simp] theorem wrap_step (n : Side) (i : Axis) : wrap n (step i) = step i := by
  ext j
  change Int.cast ((step i : Cover) j) = _
  rw [step_apply, step_apply]; split <;> simp

@[simp] theorem wrap_signed (n : Side) (x : Cover) (s : Signed) :
    s.act (wrap n x) = wrap n (s.act x) := by
  funext i
  obtain ⟨j,rfl⟩ := s.perm.surjective i
  simp only [wrap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Signed.act_at]; split <;> simp

def lift (x : Site n) : Cover := fun i => ZMod.valMinAbs (x i)

@[simp] theorem wrap_lift (x : Site n) : wrap n (lift x) = x := by
  funext i; exact ZMod.coe_valMinAbs (x i)

theorem lift_centers (x : Site n) (i : Axis) :
    - (n.val : ℤ) < 2 * lift x i ∧ 2 * lift x i ≤ n.val := by
  rw [mul_comm]
  exact ZMod.valMinAbs_mem_Ioc (x i)

theorem lift_eq_iff {x : Site n} {y : Cover} :
    lift x = y ↔ x = wrap n y ∧ ∀ i, -(n.val : ℤ) < 2*y i ∧ 2*y i ≤ n.val := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · subst y
    exact ⟨(wrap_lift x).symm, lift_centers x⟩
  · funext i
    apply (ZMod.valMinAbs_spec _ _).mpr
    exact ⟨congr_fun h1 i, by rw [mul_comm]; exact h2 i⟩

theorem wrap_injOn (n : Side) : Set.InjOn (wrap n)
    {y | ∀ i, - (n.val : ℤ) < 2*y i ∧ 2*y i ≤ n.val} := by
  intro x hx y hy h
  rw [← lift_eq_iff.mpr ⟨rfl, (hx : ∀ i : Axis, _ ∧ _)⟩,
    ← lift_eq_iff.mpr ⟨rfl, hy⟩]
  rw [h]

/-- Native torus modulus. -/
def pdist (x : Site n) := Finset.univ.sup fun i : Axis => (lift x i).natAbs

/-- Canonical lifted max-distance; the separation on the torus. -/
def separation (x y : Site n) := pdist (x-y)

@[simp] theorem separation_self (x : Site n) : separation x x = 0 := by
  simp [separation, pdist, lift]

theorem component_le (x : Site n) (i : Axis) : (lift x i).natAbs ≤ pdist x :=
  Finset.le_sup (s := Finset.univ) (f := fun i => (lift x i).natAbs) (Finset.mem_univ i)

@[simp] theorem pdist_neg (x : Site n) : pdist (-x) = pdist x := by
  unfold pdist
  simp only [lift, Pi.neg_apply, ZMod.natAbs_valMinAbs_neg]

theorem separation_comm (x y : Site n) : separation x y = separation y x := by
  unfold separation; rw [← pdist_neg, neg_sub]

theorem pdist_triangle (x y : Site n) : pdist (x+y) ≤ pdist x + pdist y := by
  unfold pdist
  apply Finset.sup_le
  intro i _
  exact (ZMod.natAbs_valMinAbs_add_le (x i) (y i)).trans <|
    (Int.natAbs_add_le ..).trans <| Nat.add_le_add (component_le x i) (component_le y i)

theorem separation_triangle (x y z : Site n) :
    separation x z ≤ separation x y + separation y z := by
  unfold separation; rw [← sub_add_sub_cancel x y z]; exact pdist_triangle _ _

@[simp] theorem pdist_invariant (s : Signed) (x : Site n) : pdist (s.act x) = pdist x := by
  have h (r : Signed) (x : Site n) : pdist (r.act x) ≤ pdist x := by
    apply Finset.sup_le; intro i _
    obtain ⟨j,rfl⟩ := r.perm.surjective i
    simp only [lift, Signed.act_at]
    split
    · rw [ZMod.natAbs_valMinAbs_neg]; exact component_le x j
    exact component_le x j
  exact le_antisymm (h s x) (by simpa only [s.inv_act] using h s⁻¹ (s.act x))

@[simp] theorem separation_translate (x y z : Site n) :
    separation (x+z) (y+z) = separation x y := by simp [separation]
@[simp] theorem separation_signed (x y : Site n) (s : Signed) :
    separation (s.act x) (s.act y) = separation x y := by
  unfold separation; rw [← s.act_sub, pdist_invariant]

end YM.Lattice
