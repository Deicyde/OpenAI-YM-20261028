import YM.Cells.Tiling


/-!
# Integer arithmetic of interiors and smaller centered grids

For strict margins inside the actual tori and comparing arbitrary offsets
with finer aligned centered grids. Spec sizes in native lattice units. Include
holes on site tiling faces. Supplies also to weak/stress copy tasks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open Lattice Function Set Filter
open scoped Topology
variable {n : Side} (T : Tiling n)

def coordinated (v : T.Cell) (x : Site n) (a : Axis) : ℕ := (x a-T.starts v a).val

def margin (v : T.Cell) (k : ℕ) : Set (Site n) := {x | x ∈ T.chamber v ∧
    ∀ a, k ≤ T.coordinated v x a ∧ (T.coordinated v x a)+k+T.kind.shift ≤ T.side.val}



lemma indent (v : T.Cell) (x : Site n) (a) : T.starts v a + (T.coordinated v x a : Per n)=x a := by
  simp [coordinated,Per]

lemma mount (v : T.Cell) (a : Axis) : T.units.root v a=(((v a).val*T.side.val : ℕ) : Per n) := by
  have he : v a = ((v a).val • (step a : T.Cell)) a := by simp [Per]
  rw [T.root_const_coord _ _ a he, map_nsmul,T.root_step]; simp [Per]

lemma narrow : T.side.val < n.val := by
  have hp := T.widthHalf.property
  rw [T.units.exact_size,T.even]
  have he := mul_le_mul_of_nonneg_left (show 1 ≤ T.widthHalf.val from hp) (show 0 ≤ (2:ℕ) by omega)
  exact lt_mul_of_one_lt_left T.side.property (lt_of_lt_of_le (show 1 < 2*(1:ℕ) by norm_num) he)

def grid (x : Site n) (a : Axis) := (x a - T.base a).val
def whole (x : Site n) (a : Axis) : ℕ := T.grid x a/T.side.val
def residue (x : Site n) (a : Axis) : ℕ := T.grid x a % T.side.val
lemma whole_lt (x) (a : Axis) : T.whole x a < T.period.val := by
  exact (Nat.div_lt_iff_lt_mul T.side.property).2 ((show T.grid x a<n.val from ZMod.val_lt _) |>.trans_eq (T.units.exact_size))
def which (x : Site n) (a : Axis) : Per T.period := ↑(T.whole x a)

lemma axis_whole (x : Site n) (a : Axis) : (T.which x a).val = T.whole x a :=
  ZMod.val_natCast_of_lt (T.whole_lt x a)

lemma residual (x : Site n) (a : Axis) : T.coordinated (T.which x) x a = T.residue x a := by
  unfold coordinated
  have he : x a-T.starts (T.which x) a=(T.residue x a : Per n) := by
    have hp : T.grid x a = (T.whole x a)*T.side.val + T.residue x a := by
      simp [whole,residue, Nat.div_add_mod']
    suffices ht : x a - T.base a=(((T.whole x a)*T.side.val+T.residue x a : ℕ):Per n) by
      rw [starts,Pi.add_apply, T.mount,T.axis_whole]
      rw [Nat.cast_add] at ht; rw [← sub_sub,ht]; ring
    rw [← hp]; simp [grid,Per]
  rw [he,ZMod.val_natCast_of_lt (show T.residue x a < n.val from (Nat.mod_lt (grid T x a) T.side.property).trans (narrow T))]

lemma small {x : Site n} {v : T.Cell} (hx : x∈T.chamber v) (a : Axis) : T.coordinated v x a < T.side.val := Kind.strict_lt (hx a)

lemma identified_loc {x : Site n} {v : T.Cell} (hx : x∈T.chamber v) (a : Axis) : T.grid x a=(v a).val*T.side.val+T.coordinated v x a := by
  have he : (v a).val*T.side.val+T.coordinated v x a<n.val := calc
    _ < ((v a).val+1)*T.side.val := by rw [add_mul,one_mul]; exact Nat.add_lt_add_left (small T hx a) _
    _ ≤ _ := T.units.exact_size.symm ▸ Nat.mul_le_mul_right _ (show (v a).val+1≤T.period.val from ZMod.val_lt _)
  unfold grid
  rw [← ZMod.val_natCast_of_lt he]
  have hp := T.indent v x a
  rw [starts, Pi.add_apply, mount] at hp
  apply congr_arg ZMod.val
  rw [Nat.cast_add, sub_eq_iff_eq_add]; exact Eq.trans hp.symm (by abel)

lemma which_chamber {x : Site n} {v : T.Cell} (hx : x∈T.chamber v) : T.which x=v := by
  ext a
  have hv : T.whole x a = (v a).val := by
    unfold whole; rw [identified_loc T hx,mul_comm (v a).val]
    exact Eq.trans (Nat.mul_add_div T.side.property _ _) (Nat.add_eq_left.mpr (Nat.div_eq_of_lt (T.small hx _))) -- lemma direction
  rw [which, hv]
  simp [Per]

lemma pointed (v : T.Cell) (y : Site n) : ∃ x, T.copyMap v x=y := by
  refine ⟨Signed.act (T.omega v)⁻¹ (y-T.translateBy v),?_⟩; simp [copyMap,affine]


private lemma copy_rev_loc (x : Site n) (v : T.Cell) (b : Axis) (hp : (T.omega v).flip b=true) :
    (((T.coordinated v (T.copyMap v x) b : ℕ) : Per n))=((T.side.val:ℕ):Per n) - (T.kind.shift : Per n) - ((T.coordinated 0 x b:ℕ):Per n) := by
  simpa [coordinated, Per,hp] using T.copy_formula v x b
private lemma copy_me_loc (x : Site n) (v : T.Cell) (b : Axis) (hp : (T.omega v).flip b=false) :
    T.coordinated v (T.copyMap v x) b=T.coordinated 0 x b := by
  unfold coordinated; rw [T.copy_formula,if_neg (by simp [hp]),T.starts_zero]

lemma reflected_chamber (x : Site n) (v : T.Cell) : x∈T.chamber 0 ↔ T.copyMap v x∈T.chamber v := by
  constructor
  · exact fun H => T.enumerate v H
  intro h i
  have he : T.kind.Strict _ _ := h i
  change T.kind.Strict _ (T.coordinated 0 _ i)
  cases e:(T.omega v).flip i
  · rw [← copy_me_loc T x v i e]; exact he
  let a := T.coordinated v (T.copyMap v x) i
  have hu : a<T.side.val := Kind.strict_lt he
  have hr : (T.coordinated 0 x i:Per n)=T.side.val - T.kind.shift - (a:Per n) :=
    eq_sub_of_add_eq (add_comm .. |>.trans (by rw [show (a:Per n)=_ from copy_rev_loc T x v i e]; ring)) -- order
  have ht : T.kind.shift ≤ 1 := by cases T.kind <;> unfold Kind.shift <;> decide
  have hs := T.narrow
  have hw : T.coordinated 0 x i=T.side.val-(T.kind.shift+a) := by
    have hC : T.kind.shift+a ≤ T.side.val := by omega
    have hh : (T.coordinated 0 x i:Per n) = ((T.side.val-(T.kind.shift+a):ℕ):Per n) := by rw [hr,Nat.cast_sub hC,Nat.cast_add];ring
    have hv := congr_arg ZMod.val hh
    simpa only [ZMod.val_natCast_of_lt (by omega : T.side.val-(T.kind.shift+a)<n.val),ZMod.val_natCast_of_lt (show T.coordinated 0 x i < n.val from ZMod.val_lt _)] using hv
  rw [hw]; cases h' : T.kind with
  | link => change T.side.val - (1+a) < T.side.val; omega
  | site =>
    rw [h'] at he; have hb : 0 < a := he.1
    change 0 < T.side.val-(0+a) ∧ T.side.val-(0+a)<T.side.val;omega

lemma reflected_margin (x : Site n) (v : T.Cell) (k) : x∈T.margin 0 k ↔ T.copyMap v x∈T.margin v k := by
  by_cases hw : x∈T.chamber 0
  · have hm := (reflected_chamber T x v).mp hw
    simp only [margin,Set.mem_setOf_eq,hw,hm,true_and]; apply forall_congr'; intro i
    rcases e:(T.omega v).flip i with _|_
    · rw [copy_me_loc T _ v i e]
    let a := T.coordinated v (T.copyMap v x) i
    let b := T.coordinated 0 x i
    have hg : b<T.side.val := T.small hw i
    have ht : T.kind.shift ≤ 1 := by cases T.kind <;> unfold Kind.shift <;> decide
    have hc : T.kind.shift+b ≤ T.side.val := by omega
    have hs := T.narrow
    have hl : (a:Per n)=((T.side.val-(T.kind.shift+b):ℕ):Per n) := by rw [copy_rev_loc T x v i e,Nat.cast_sub hc,Nat.cast_add]; unfold b; ring
    have hv : a=T.side.val-(T.kind.shift+b) := by
      have ha : a<n.val := ZMod.val_lt _
      have H := congr_arg ZMod.val hl; simpa only [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt (by omega : T.side.val-(T.kind.shift+b) <n.val)] using H
    change k≤b ∧ b+_+_≤ _ ↔ k≤a ∧ a+_+_≤ _
    omega
  simp only [margin,Set.mem_setOf_eq, ← reflected_chamber, hw, false_and]
end YM.Cells.Tiling
