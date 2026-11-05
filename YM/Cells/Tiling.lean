import YM.Cells.Interior

/-!
# Per-cell orientations on torus

T denotes an actual tiling. All seams have same kind; offsets arbitrary.
Widths positive steps; for link seams centers at sites only required in centered
applications. For other placements still use twice-center/corner convention so
there is no fractional translation of a cylinder. Even number of cells per axis;
no restriction to powers of two. Source .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side}
structure Tiling (n : Side) where
  period : Side
  units : Ratio period n
  widthHalf : Side -- count/2 (in cells)
  even : period.val = 2*widthHalf.val
  kind : Kind
  base : Site n

namespace Tiling
variable (T : Tiling n)

abbrev Cell := Site T.period
abbrev side := T.units.count

def starts (v : T.Cell) := T.base + T.units.root v

/-- Cell with strict (relative) seam margins (>0 in half steps). -/
def chamber (v : T.Cell) : Set (Site n) := {x | ∀ i : Axis, T.kind.Strict T.side.val (x i - T.starts v i).val}

@[simp] theorem starts_zero : T.starts 0=T.base := by rw [starts, map_zero,add_zero]

def bandCut (p : T.Cell) (a : Axis) : Cut n where
  half := T.side*T.widthHalf
  even := by rw [T.units.exact_size,T.even, PNat.mul_coe]; ring
  pos := a
  kind := T.kind
  baseLine := T.starts p a

private lemma divides : 2 ∣ T.period.val := by rw [T.even]; simp

def parity (x : Per T.period) : ZMod 2 := ZMod.castHom T.divides (ZMod 2) x

@[simp] theorem parity_add (x y : Per T.period) : T.parity (x+y) = T.parity x + T.parity y := by rw [parity,map_add]; rfl
@[simp] theorem parity_sub (x y : Per T.period) : T.parity (x-y) = T.parity x - T.parity y := by rw [parity,map_sub]; rfl
@[simp] theorem parity_neg (x : Per T.period) : T.parity (-x) = - T.parity x := by rw [parity,map_neg]; rfl
@[simp] theorem parity_one : T.parity 1 = 1 := by unfold parity; exact map_one _
@[simp] theorem parity_zero : T.parity 0 = 0 := by unfold parity; exact map_zero _

/-- Orientation linear signature. -/
def omega (v : T.Cell) : Signed := ⟨Equiv.refl _,fun j => decide (T.parity (v j) ≠ 0)⟩

/-- Extra displacement when an axis reverses inside the cell; use this for either orientation origin. -/
def bias (v : T.Cell) : Site n := fun i => if (T.omega v).flip i then (T.side.val : Per n) - (T.kind.shift : Per n) else 0

def translateBy (v : T.Cell) : Site n := T.starts v - (T.omega v).act T.base + T.bias v

def copyMap (v : T.Cell) (x : Site n) := affine (T.omega v) (T.translateBy v) x

lemma copy_formula (v : T.Cell) (x : Site n) (i : Axis) : T.copyMap v x i - T.starts v i =
    if (T.omega v).flip i then (T.side.val : Per n) - (T.kind.shift : Per n) - (x i - T.base i) else x i-T.base i := by
  unfold copyMap affine translateBy bias
  have he (z : Site n) : (T.omega v).act z i = if (T.omega v).flip i then -z i else z i :=
    Signed.act_at _ _ i
  simp only [Pi.add_apply, Pi.sub_apply,he]; split_ifs <;> ring

theorem enumerate (v : T.Cell) : MapsTo (T.copyMap v) (T.chamber 0) (T.chamber v) := by
  rintro x hx i
  rw [copy_formula]
  specialize hx i; rw [T.starts_zero] at hx
  split
  · let a := x i-T.base i
    have he : a.val < T.side.val := Kind.strict_lt hx
    have hd : T.side.val ≤ n.val := by
      rw [T.units.exact_size]; exact le_mul_of_one_le_left (Nat.zero_le _) T.period.property
    cases h : T.kind with
    | link =>
      simp only [Kind.Strict,Kind.shift, Nat.cast_one]
      change (T.side.val - (1 : Per n) - a).val < T.side.val
      have hs : T.side.val - (1 : Per n) - a = ((T.side.val - (1+a.val) : ℕ) : Per n) := by
        rw [Nat.cast_sub (by omega)]; simp [Per]; abel
      rw [hs,ZMod.val_natCast_of_lt (by omega)]; omega
    | site =>
      rw [h] at hx
      have hs : 0<a.val := hx.1
      have hv : T.side.val - (Kind.site.shift : Per n)-a = ((T.side.val - a.val : ℕ) : Per n) := by
        rw [Nat.cast_sub (by omega)]; simp [Kind.shift,Per]
      unfold Kind.Strict
      change 0 < (T.side.val - (Kind.site.shift : Per n)-a).val ∧ _
      change (0 < _ ∧ (T.side.val - (Kind.site.shift : Per n)-a).val < T.side.val)
      rw [hv,ZMod.val_natCast_of_lt (by omega)]; omega
  exact hx

/-- Reverse cell index in a specified axis about bandCut. -/
def mate (p : T.Cell) (a : Axis) (v : T.Cell) : T.Cell := update v a (2*p a-1-v a)

@[simp] theorem mate_here (p : T.Cell) (a : Axis) (v : T.Cell) : T.mate p a v a=2*p a-1-v a := by simp [mate]
@[simp] theorem mate_off (p : T.Cell) (a : Axis) (v : T.Cell) {b} (h : b≠a) : T.mate p a v b=v b := by simp [mate,h]
@[simp] theorem mate_invol (p : T.Cell) (a : Axis) (v : T.Cell) : T.mate p a (T.mate p a v) = v := by
  ext i; by_cases h : i=a <;> simp [h]

/-- Prove rather than assume signed orientation covariance. -/
theorem turn (p : T.Cell) (a : Axis) (v : T.Cell) :
    T.omega (T.mate p a v) = (T.bandCut p a).flip*T.omega v := by
  refine Signed.ext ?_ ?_
  · rfl
  ext i
  by_cases h : i=a
  · subst i
    have hx (x : ZMod 2) : (x = 0) ↔ ¬(-1-x=0) := by 
      have hy : x=0 ∨ x=1 := by fin_cases x <;> simp [ZMod]
      rcases hy with e|e <;> subst x <;> decide
    simp only [Signed.mul_flip,omega,bandCut,Cut.flip,Signed.mirror,Equiv.refl_apply, decide_true]
    have hz (x : ZMod 2) : x+x=0 := by fin_cases x <;> decide
    simp only [mate_here,two_mul,T.parity_sub,T.parity_add,T.parity_one,hz,zero_sub]
    by_cases hu : T.parity (v a)=0
    · simp [hu]
    have vv := not_not.mp (mt (hx _).2 hu)
    simp [hu]; simpa using vv
  simp [omega,mate_off T p a v h, bandCut, Cut.flip, Signed.mirror,Ne.symm h]

lemma root_const_coord (v w : T.Cell) (i : Axis) (h : v i = w i) : T.units.root v i = T.units.root w i := by
  change (((T.side.val • lift v : Cover) i : ℤ) : Per n) = (((T.side.val • lift w : Cover) i : ℤ) : Per n)
  simp [lift,h]

lemma root_step (a : Axis) : T.units.root (step a) = T.side.val • step a := by
  rw [← wrap_step _ a, Ratio.root_embed, T.units.embed_wrap, map_nsmul, wrap_step]

theorem starts_mate (p : T.Cell) (a : Axis) (v : T.Cell) :
    T.starts (T.mate p a v) a = 2*T.starts p a - T.side.val - T.starts v a := by
  have he : (T.mate p a v) a = (p+p-step a-v : T.Cell) a := by simp; ring
  unfold starts
  simp only [Pi.add_apply]
  rw [T.root_const_coord _ _ _ he,map_sub,map_sub,map_add,T.root_step]
  simp; ring

theorem starts_mate_off (p : T.Cell) (a : Axis) (v : T.Cell) {b} (h : b≠a) :
    T.starts (T.mate p a v) b = T.starts v b := by
  unfold starts
  simp only [Pi.add_apply, T.root_const_coord _ _ _ (mate_off T p a v h)]

lemma flip_here (p : T.Cell) (a : Axis) (v) :
    (T.omega (T.mate p a v)).flip a = !(T.omega v).flip a := by
  rw [turn T]; simp [omega, bandCut, Cut.flip,Signed.mirror]

lemma flip_off (p : T.Cell) (a : Axis) (v) {b} (h : b≠a) :
    (T.omega (T.mate p a v)).flip b = (T.omega v).flip b := by
  simp [omega,h]

lemma after (p : T.Cell) (a : Axis) (v) (x : Site n) :
    T.copyMap (T.mate p a v) x = (T.bandCut p a).reflect (T.copyMap v x) := by
  funext i
  by_cases he : i=a
  · subst i
    have hh := T.copy_formula v x a
    have ht := T.copy_formula (T.mate p a v) x a
    have hx := (T.bandCut p a).reflect_here (T.copyMap v x)
    change _ = (T.bandCut p a).reflect (T.copyMap v x) ((T.bandCut p a).pos)
    rw [hx]
    change T.copyMap _ x a = 2*T.starts p a - (T.kind.shift : Per n)-T.copyMap v x a
    rw [flip_here,T.starts_mate p a v] at ht
    cases h : (T.omega v).flip a
    · simp only [h,Bool.not_false,↓reduceIte,Bool.false_eq_true] at hh ht
      rw [sub_eq_iff_eq_add] at hh ht
      rw [ht,hh]; ring
    simp only [h,Bool.not_true,↓reduceIte,Bool.false_eq_true] at hh ht
    rw [sub_eq_iff_eq_add] at hh ht
    rw [ht,hh]; ring
  rw [Cut.reflect_there _ _ he]
  apply sub_left_injective (b := T.starts v i)
  dsimp only
  rw [T.copy_formula v x i,← T.starts_mate_off p a v he,T.copy_formula,T.flip_off p a v he]

lemma within (p : T.Cell) (a : Axis) (v : T.Cell) (hp : (v a - p a).val < T.widthHalf.val) :
    T.chamber v ⊆ (T.bandCut p a).sector := by
  intro x hx
  have hk := hx a
  let Δ := x a-T.starts v a
  let t := (v a-p a).val
  have hh : T.starts v a = T.starts p a + (t : Per n)*T.side.val := by
    unfold starts
    have ht : v a = (p + t • (step a : T.Cell) : T.Cell) a := by
      change v a = p a + t • (step a : T.Cell) a
      simp only [nsmul_eq_mul, step_apply,↓reduceIte,mul_one,t]
      rw [ZMod.natCast_zmod_val]
      abel
    simp only [Pi.add_apply]
    rw [T.root_const_coord _ _ _ ht,map_add,map_nsmul,T.root_step]
    simp [add_assoc]
  have he := Kind.strict_lt hk
  change Δ.val < _ at he
  change t < T.widthHalf.val at hp
  have hd : t*T.side.val+Δ.val < T.side.val*T.widthHalf.val := calc
    _ < (t+1)*T.side.val := by rw [add_mul,one_mul]; omega
    _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hp
  have hw : t*T.side.val+Δ.val < n.val := by
    exact hd.trans_le (by rw [(T.bandCut p a).even]; change T.side.val * T.widthHalf.val ≤ 2*(T.side * T.widthHalf).val; rw [PNat.mul_coe]; omega)
  have hl : (T.bandCut p a).distance x = t*T.side.val+Δ.val := by
    rw [← ZMod.val_natCast_of_lt (n := n.val) hw]
    change (x a - T.starts p a).val = _
    have hy : x a - T.starts p a = ((t*T.side.val+Δ.val : ℕ) : Per n) := by
      simp only [Nat.cast_add,Nat.cast_mul, ZMod.natCast_zmod_val]
      unfold Δ; rw [hh]; abel
    rw [hy]
  change Kind.Strict T.kind _ _
  rw [hl]
  cases h : T.kind with
  | site => rw [h] at hk; have hv : 0 < Δ.val := hk.1; exact ⟨by positivity,hd⟩
  | link => exact hd

variable {G : Gauge}

def hand (v : T.Cell) := Odd ({i : Axis | (T.omega v).flip i} : Finset _).card
open scoped Classical in
def copy (v : T.Cell) (F : Config G n → ℂ) (U : Config G n) :=
  let W := F (pull (T.omega v) (T.translateBy v) U)
  if T.hand v then star W else W

def rootTest (β : ℝ) (F : Config G n → ℂ) :=
  ‖moment β (fun U => ∏ i : T.Cell, T.copy i F U)‖ ^ (Fintype.card T.Cell : ℝ)⁻¹
end Tiling
end YM.Cells
