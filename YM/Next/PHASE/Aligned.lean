import YM.Cells.Proximity

/-!
# Subdividing link tilings and retaining margins

Use one coarse array for the replica estimate, with a finer (aligned) tiling
for the *replication roots* of groups of exterior fields. Offsets are chosen on
the native torus. The seam conventions and reflections, in particular `-1` in
the residue formula, are link-seam conventions. No lower bound on the finer
width besides positive integral width is needed here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Next.Phase
open Cells Lattice Function
open scoped Topology

variable {n : Side} (T Y : Tiling n)

/-- Margin in whichever cell contains this site (link convention in use). -/
def Inside (T : Tiling n) (K : ℕ) (x : Site n) : Prop :=
  x ∈ T.margin (T.which x) K

lemma inside_residue (h : T.kind = .link) (K : ℕ) (x : Site n) :
    Inside T K x ↔ ∀ a, K ≤ T.residue x a ∧ T.residue x a + K < T.side.val := by
  constructor
  · intro hx a
    have he := (show _ ∧ _ from hx).2 a
    rw [T.residual,h] at he
    exact he
  intro H
  refine ⟨fun a => ?_, fun a => ?_⟩
  · change T.kind.Strict T.side.val (T.coordinated (T.which x) x a)
    rw [T.residual,h]
    exact Nat.mod_lt _ T.side.property
  rw [T.residual,h]
  exact H a

/-- Coordinate measured from the base, as residue modulo the tile side (not modulo the torus). -/
def stripe (T : Tiling n) (x : Site n) (a : Axis) : Per T.side := T.hom (x a - T.base a)

lemma stripe_val (x : Site n) (a : Axis) : (stripe T x a).val = T.residue x a := by
  have he : stripe T x a = ((T.grid x a : ℕ) : Per T.side) := calc
    _ = T.hom ((T.grid x a : ℕ) : Per n) := by rw [Tiling.grid, ZMod.natCast_zmod_val]; rfl
    _ = _ := map_natCast ..
  rw [he]; exact ZMod.val_natCast ..

lemma inside_stripe (h : T.kind = .link) (K : ℕ) (x : Site n) :
    Inside T K x ↔ ∀ a, K ≤ (stripe T x a).val ∧ (stripe T x a).val + K < T.side.val := by
  simp_rw [stripe_val]
  exact inside_residue T h K x

lemma stripe_newly (o x : Site n) (a : Axis) :
    stripe (T.newly o) x a = T.hom (x a - o a) := rfl

lemma shared_cell (offset : Y.base = T.base) (tiles : Y.side.val ∣ T.side.val)
    {x y : Site n} (e : Y.which x = Y.which y) : T.which x = T.which y := by
  obtain ⟨c,H⟩ := tiles
  funext i
  have hh : Y.whole x i = Y.whole y i := by rw [← Y.axis_whole, ← Y.axis_whole,e]
  have he (x : Site n) : T.whole x i = Y.whole x i / c := by
    rw [Tiling.whole, H]
    rw [Tiling.whole, Nat.div_div_eq_div_mul, Tiling.grid, Tiling.grid,offset]
  apply ZMod.val_injective T.period.val
  rw [T.axis_whole, T.axis_whole, he, he, hh]

private lemma remainder_room {K C a b u : ℕ} (h : C=a*b) (hu : u<C)
    (hw : u % a + K < a) : u+K<C := by
  subst C
  have he : u/a < b := Nat.div_lt_of_lt_mul hu
  have hh : a*(u/a+1) ≤ a*b := Nat.mul_le_mul_left _ he
  rw [mul_add,mul_one] at hh
  have hx := Nat.mod_add_div u a
  omega

lemma shared_inside (offset : Y.base = T.base) (ty : Y.kind=.link) (tx : T.kind=.link)
    (tiles : Y.side.val ∣ T.side.val) (K : ℕ) (x : Site n) (H : Inside Y K x) :
    Inside T K x := by
  rw [inside_residue T tx]
  intro a
  obtain ⟨h₁,h₂⟩ := (inside_residue Y ty K x).mp H a
  have he : T.residue x a % Y.side.val = Y.residue x a := by
    rw [Tiling.residue, Tiling.residue, Nat.mod_mod_of_dvd _ tiles, Tiling.grid,Tiling.grid,offset]
  rw [← he] at h₁ h₂
  exact ⟨h₁.trans (Nat.mod_le ..), remainder_room tiles.choose_spec (Nat.mod_lt _ T.side.property) h₂⟩

lemma stripe_reflected (offset : Y.base = T.base) (tiles : Y.side.val ∣ T.side.val)
    (tx : T.kind=.link) (v : T.Cell) (x : Site n) (a : Axis) :
    stripe Y (T.copyMap v x) a =
      if (T.omega v).flip a then -1 - stripe Y x a else stripe Y x a := by
  have hz : ((T.side.val : ℕ) : Per Y.side)=0 := by
    obtain ⟨i,h⟩ := tiles; rw [h,Nat.cast_mul,ZMod.natCast_self,zero_mul]
  have he : Y.hom (T.starts v a-T.base a)=0 := by
    rw [Tiling.starts,Pi.add_apply,T.mount,add_sub_cancel_left,map_natCast,Nat.cast_mul,hz,mul_zero]
  unfold stripe
  rw [offset,← sub_add_sub_cancel (T.copyMap v x a) (T.starts v a) (T.base a), map_add,he,add_zero,T.copy_formula]
  split_ifs
  · rw [tx]; simp only [Kind.shift, Nat.cast_one, map_sub Y.hom, map_natCast Y.hom, map_one Y.hom]
    rw [hz]; abel
  rfl

private lemma link_val {p : Side} (x : Per p) : (-1-x).val = p.val-(1+x.val) := by
  have hv := ZMod.val_lt x
  have hr : (-1-x) = ((p.val-(1+x.val):ℕ) : Per p) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add,Nat.cast_one,ZMod.natCast_self,ZMod.natCast_zmod_val]
    abel
  rw [hr,ZMod.val_natCast_of_lt]; omega

lemma inside_reflected (offset : Y.base = T.base) (tiles : Y.side.val ∣ T.side.val)
    (tx : T.kind=.link) (ty : Y.kind=.link) (v : T.Cell) (K : ℕ) (x : Site n) :
    Inside Y K (T.copyMap v x) ↔ Inside Y K x := by
  rw [inside_stripe Y ty,inside_stripe Y ty]
  apply forall_congr'; intro a
  rw [stripe_reflected T Y offset tiles tx]
  split
  · have ht := ZMod.val_lt (stripe Y x a); rw [link_val]; omega
  rfl

lemma separation_copy (v : T.Cell) (x y : Site n) :
    separation (T.copyMap v x) (T.copyMap v y) = separation x y := by
  simp [Tiling.copyMap,affine]

/-- Move the fields *and* adjust the offset; retain a budgeted part of the margin. -/
lemma inside_after (tx : T.kind=.link) (x : Site n) (w u : Cover) (k : ℕ) (h : Inside T (5*k) x)
    (hs : ∀ a, (w a).natAbs ≤ k) (hu : ∀ a, (u a).natAbs ≤ k) :
    Inside (T.newly (T.base + wrap n w)) (3*k) (x + wrap n u) := by
  rw [inside_stripe (T.newly (T.base + wrap n w)) tx]
  intro a
  let c : ℤ := ↑(stripe T x a).val + u a - w a
  have ht := (inside_stripe T tx _ _).mp h a
  have hg := hs a; have he := hu a
  have hh : 0 ≤ c := by unfold c; omega
  have hp : c.toNat < T.side.val := by unfold c; omega
  have hf : stripe (T.newly (T.base + wrap n w)) (x + wrap n u) a = ((c.toNat:ℕ) : Per T.side) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hh]
    unfold c; push_cast
    rw [stripe_newly, ZMod.natCast_zmod_val]
    unfold stripe
    change T.hom ((x a + (u a:Per n)) - (T.base a + (w a:Per n))) = _
    rw [map_sub,map_add,map_add,map_intCast,map_intCast,map_sub]; abel
  change 3*k ≤ (stripe (T.newly _) _ _).val ∧ (stripe (T.newly _) _ _).val+3*k < T.side.val
  have hv : (stripe (T.newly (T.base+wrap n w)) (x+wrap n u) a).val=c.toNat :=
    (congrArg (fun x : Per T.side => x.val) hf).trans (ZMod.val_natCast_of_lt hp)
  rw [hv]
  dsimp only [c] at *; omega

/-- Given any desired base, a translation by *less than one tile side* suffices
 to fit the specified fields: only base residues matter. -/
lemma shift_into {ι : Type*} [Fintype ι] (y : ι → Site n) (o : Site n) (ty : Y.kind=.link)
    (K : ℕ) (hk : 0 < K) (h : Fintype.card ι*(2*K)<Y.side.val) :
    ∃ w : Cover, (∀ a, (w a).natAbs < Y.side.val) ∧ ∀ i, Inside (Y.newly (o + wrap n w)) K (y i) := by
  classical
  let f := Fintype.equivFin ι
  obtain ⟨b,hb⟩ := Y.fits_together (y ∘ f.symm) K hk h
  let w : Cover := fun a => ↑(Y.hom (b a-o a)).val
  have he (x : Site n) (a : Axis) : stripe (Y.newly (o + wrap n w)) x a = stripe (Y.newly b) x a := by
    rw [stripe_newly,stripe_newly,Pi.add_apply]
    rw [map_sub,map_add]
    change Y.hom (x a) - (Y.hom (o a) + Y.hom ((w a:ℤ):Per n)) = _
    rw [map_intCast]; unfold w
    rw [Int.cast_natCast,ZMod.natCast_zmod_val,map_sub,map_sub]
    abel
  refine ⟨w,fun a => ?_,fun i => ?_⟩
  · change Int.natAbs (↑(Y.hom (b a-o a)).val : ℤ) < _
    rw [Int.natAbs_natCast]; exact ZMod.val_lt _
  have hx : Inside (Y.newly b) K (y i) := by
    unfold Inside
    simpa using hb (f i)
  rw [inside_stripe (Y.newly (o+wrap n w)) ty]
  simp_rw [he]; exact (inside_stripe (Y.newly b) ty _ _).mp hx

end YM.Next.Phase
