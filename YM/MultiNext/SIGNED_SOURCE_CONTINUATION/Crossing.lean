import YM.Corona.Spend
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newtown
import YM.Next.FREE_KERNELS.Differences
import YM.Work.B06



set_option warningAsError false

/-!
# Periodized fine calculus tested on colors & true lifted ordinates

Connect bridge at B70's `Ratio`, `TypeFace 1` and `installed`. This is
**one** instance of PMOM third clause, for use in Promise. Doesn't
postulate plane-wave alias stencils and doesn't claim PMOM.2 here, uses
positive order Deep inputs wherever reading installed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Newt
open Function Filter Finset Lattice Wilson RG Labels Laurent Bloch Exterior Precision Matrix
open Pattern Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {n c : Side} {m m' e : Type*} [Fintype m] [Fintype m'] [Fintype e] (g : Ratio c n) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Counting matrix action with color vectors
def load (p : Matrix m m' ℝ) (v : m' → E) (i) := ∑ j,p i j • v j
omit [Fintype m] in
lemma load_mul (p : Matrix m m' ℝ) (q : Matrix m' e ℝ) (v : e → E) : load (p*q) v=load p (load q v) := by
  funext i; simp_rw [load, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul, Finset.sum_comm (s:=Finset.univ (α:=e))]
lemma load_id [DecidableEq m] (v : m → E) : load (1:Matrix m m ℝ) v=v := by
  funext i; simp [load, Matrix.one_apply, ite_smul]

variable [DecidableEq m] (P : Cross g.count m m') (v : Co c m' → E)
private lemma loaded (A : Co n m → E) (i : Axis) (x : Co n m) :
    load ((knock m i).acts n) A x=A (x.1+Lattice.step i,x.2)-A x := by
  let a := (x.1+Lattice.step i,x.2)
  have h (v) : ((knock m i).acts n) x v=((if a=v then 1 else 0) - (if x=v then 1 else 0)) := by
    have he := knock_entry m n i x (fun x => if x=v then 1 else 0)
    simp only [mulVec,dotProduct,mul_ite, mul_zero, mul_one, sum_ite_eq', mem_univ,↓reduceIte] at he; exact he
  unfold load; simp_rw [h,sub_smul, Finset.sum_sub_distrib,ite_smul,one_smul,zero_smul]
  simp [a]

/-- Distinguish coarse displacement indexing and every tag. installed really
has these position differences acting before evaluating. -/
lemma spatial (s : List Axis) (hi : Odd g.count.val) (h : ∀ u : List Axis,u.length ≤ s.length →
    Whole (advanceC g.count P u)) (x : Site n) (i : m) (z) :
    Newt.iterate (fun z => load (installed g P) v (wrap n z+x,i)) s z=
      load (installed g (advanceC g.count P s.reverse)) v (wrap n z+x,i) := by
  have he (s : List Axis) (v : Co n m → E) :
      Newt.iterate (fun z => v (wrap n z+x,i)) s z=load (motion m n s.reverse) v (wrap n z+x,i) := by
    have hx (s : List Axis) a : motion m n (s++[a])=motion m n s * (knock m a).acts n := by
      induction s with
      | nil => simp [motion_walk,motion_zero]
      | cons j s ih => simp_rw [List.cons_append,motion_walk,ih,Matrix.mul_assoc]
    induction s generalizing v with
    | nil => rw [List.reverse_nil,motion_zero,load_id]; rfl
    | cons a l ih =>
      rw [Newt.iterate,List.reverse_cons,hx, load_mul]
      rw [show Newt.jump (fun z => v (wrap n z+x,i)) a=(fun z => load ((knock m a).acts n) v (wrap n z+x,i)) from ?_]
      · exact ih _
      funext z; rw [loaded]; unfold Newt.jump; simp only [map_add,wrap_step]; rw [add_right_comm]
  rw [he,flow_movement _ _ _ hi (by simpa using h),load_mul]

variable {g}
lemma wrapped (v : Cover) (n : Side) : pdist (wrap n v) ≤ size v := by
    refine Finset.sup_le fun j _ => (Corona.lap _ _).trans ?_
    exact single_le_sum (f:=fun i => (v i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ j)
/-- Pay (1+position/L)^D not the unscaled on general positions. -/
lemma positions (g : Ratio c n) (x : Site n) (z y : Cover) :
    (1:ℝ)+(separation (g.parent (wrap n z+x)+wrap c y) (g.parent x):ℝ) ≤
      3*(1+((g.count.val:ℝ)⁻¹*size z))*(1+size y) := by
  let v := wrap n z+x; let L : ℝ := g.count.val
  have hL : 1 ≤ L := by unfold L; exact_mod_cast g.count.property
  have he : separation v x ≤ size z := by unfold v separation; rw [add_sub_cancel_right]; exact wrapped ..
  have hx : (g.count.val : ℕ)*separation (g.parent v) (g.parent x) ≤ g.count.val+size z+g.count.val := by
    have h := Corona.foreshorten g v x
    omega
  have hv : (separation (g.parent v) (g.parent x) : ℝ) ≤ 2+L⁻¹*(size z:ℝ) := by
    have hp : L * (separation (g.parent v) (g.parent x):ℝ) ≤ L+size z+L := by unfold L; exact_mod_cast hx
    have hT := mul_le_mul_of_nonneg_left hp (inv_pos.mpr (zero_lt_one.trans_le hL)).le
    rw [←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul] at hT
    calc
      _ ≤ _ := hT
      _ = _ := by field_simp; ring
  have hy : separation (g.parent v+wrap c y) (g.parent v) ≤ size y := by unfold separation; rw [add_sub_cancel_left]; exact wrapped ..
  have hw := separation_triangle (g.parent v+wrap c y) (g.parent v) (g.parent x)
  have h : (separation (g.parent v+wrap c y) (g.parent x):ℝ) ≤ ((size y:ℝ)+separation (g.parent v) (g.parent x)) := by
    exact_mod_cast (hw.trans (Nat.add_le_add_right hy _))
  change _≤3*(1+L⁻¹*_)*(1+(size y:ℝ))
  change 1+(separation (g.parent v+wrap c y) (g.parent x) : ℝ) ≤ _
  have hy : 0 ≤ (size y:ℝ) := by positivity
  have hx : 0 ≤ L⁻¹*(size z:ℝ) := by positivity
  nlinarith only [hv,hy,hx,mul_nonneg hx hy,h]
end YM.MultiNext.SignedSource.Newt
