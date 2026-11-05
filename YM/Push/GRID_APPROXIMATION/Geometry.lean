import YM.Next.EXTRACTION.Base
import YM.Push.GRID_APPROXIMATION.Cone
import YM.Work.F02.Path

/-!
# Common grid geometry for the backward cones

Center link seams, odd subdivision, no assumption that periods beat k
informally. In particular the cone bound from Calendar is independent of
N,p, not obtained from a bound at each fixed finite volume.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Wilson Lattice Cells MeasureTheory Filter Set Function
open scoped Topology BigOperators

variable {G : Gauge} (S : Schedule) {h m k N : ℕ} (p : ℕ)

/-- Grid tiling of the given level of the history, centered at 0 without
changing blocking offsets. -/
abbrev tilesAt (q : h ≤ m) := Cells.center S p q 0
abbrev anchor (q : h ≤ m) := (S.toDepth q p).embed

lemma tile_translate (q : h ≤ m) (i : Site (S.side h p)) :
    (tilesAt S p q).translateBy i = anchor S p q i := by
  have he := copy_home S q (p:=p) 0 i
  simpa only [Tiling.copyMap,affine,Signed.act_zero,zero_add] using he

lemma anchor_next (q : h ≤ m) (i : Site (S.side h p)) :
    (S.oneStep m p).embed (anchor S p q i) = anchor S p (Nat.le_succ_of_le q) i := by
  have he : (S.toDepth (Nat.le_succ_of_le q) p).count.val = (S.block m).val * (S.toDepth q p).count.val := by
    let x := (S.side h p).val
    have h1 := (S.toDepth q p).exact_size
    have h2 := (S.oneStep m p).exact_size
    have h3 := (S.toDepth (Nat.le_succ_of_le q) p).exact_size
    apply Nat.eq_of_mul_eq_mul_left (S.side h p).property
    calc
      _ = (S.side (m+1) p).val := h3.symm
      _ = (S.side m p).val * (S.block m).val := h2
      _ = _ := (congr_arg (· * (S.block m).val) h1).trans ((Nat.mul_assoc _ _ _).trans (congr_arg ((S.side h p).val * ·) (Nat.mul_comm _ _)))
  change (S.oneStep m p).embed (wrap _ ((S.toDepth q p).count.val • lift i)) =
    wrap _ ((S.toDepth _ p).count.val • lift i)
  rw [(S.oneStep m p).embed_wrap,he,mul_smul]; rfl

/-- Exact ball interpretation of a *centered* tile, applicable also to the
one-site width. -/
lemma tiling_window (q : h ≤ m) (i : Site (S.side h p)) :
    (tilesAt S p q).chamber i = window (anchor S p q i) ((S.toDepth q p).count.val/2) := by
  let T := tilesAt S p q
  let n := S.side m p
  let d := (S.toDepth q p).count.val
  let r := d/2
  let o := anchor S p q i
  have he : d=2*r+1 := by
    obtain ⟨u,hu⟩ := S.toDepth_odd q p
    change d = 2*u+1 at hu; unfold r; omega
  have ht : d < n.val := T.narrow
  have hx (a : Axis) : T.starts i a = -(r:Per n) + o a := by
    change 0-(r:Per n)+o a = _
    rw [zero_sub]
  change T.chamber i = window o r
  apply Set.Subset.antisymm
  · intro y hy
    let w : Cover := fun a => ↑(T.coordinated i y a) - (r:ℕ)
    have hv (a : Axis) : T.coordinated i y a < d := T.small hy a
    refine ⟨w,show w∈box _ from ?_,?_⟩
    · rw [box_test]; constructor <;> intro a <;> have := hv a <;> unfold w <;> omega
    funext a
    have hp := T.indent i y a
    rw [hx] at hp
    change ((w a:ℤ):Per n) + o a = y a
    unfold w; push_cast; rw [← hp]; abel
  · rintro y ⟨w,hw,rfl⟩ a
    change Kind.link.Strict d _
    obtain ⟨hw,hW⟩ := box_test.mp (show w∈box r from hw)
    let j := w a + (r:ℤ)
    have hj : 0≤j := by unfold j; have := hw a; omega
    have hj' : j.toNat < d := by unfold j; have := hW a; omega
    change (((w a:ℤ):Per n) + o a - T.starts i a).val < d
    rw [hx, show ((w a:ℤ):Per n)+o a - (-r + o a) = ↑j.toNat by
      conv_rhs => rw [← Int.cast_natCast,Int.toNat_of_nonneg hj ]
      unfold j; push_cast; abel,
      ZMod.val_natCast_of_lt (hj'.trans ht)]; exact hj'

lemma window_fits (q : h ≤ m) (i : Site (S.side h p)) (r : ℕ) (he : 2 * r < (S.toDepth q p).count.val) :
    window (anchor S p q i) r ⊆ (tilesAt S p q).chamber i := by
  rw [tiling_window S p q i]
  rintro x ⟨a,ha,rfl⟩
  exact ⟨a,box_larger ha (by omega),rfl⟩

section physical
variable (A : Levels G)

/-- radius on new native lattice level. -/
def expansion (r m : ℕ) := (A.S.block m).val*r + 10 * ((A.clock.J (m+1)+3)*(A.S.block m).val)

def grows (k r : ℕ) (q : k ≤ m) : ℕ := Nat.leRecOn (C:=fun _ => ℕ) q (fun {i} u => expansion A u i) r

@[simp] lemma begin_radius (k r : ℕ) : grows A k r (show k ≤ k from le_rfl) = r := Nat.leRecOn_self _

lemma grows_next (k r : ℕ) (q : k ≤ m) : grows A k r (Nat.le_succ_of_le q) =
    expansion A (grows A k r q) m := by unfold grows; rw [Nat.leRecOn_succ q]

/-- physical remainder estimate from *all* possible finer steps. -/
def tail (i : ℕ) := 30 * A.S.a i * ((A.clock.J i:ℝ)+5)
lemma tail_pos (i) : 0 < tail A i := by unfold tail; have := A.S.a_pos i; positivity

lemma tail_next (m : ℕ) : tail A (m+1) ≤ (2:ℝ)/3 * tail A m := by
  let s := A.S
  have hp := A.S.a_pos m
  have hk : (3:ℝ) ≤ (s.block m).val := by exact_mod_cast s.block_large m
  have hs : s.a (m+1) ≤ s.a m/3 := by rw [s.a_step]; gcongr
  have hb : (A.clock.J (m+1):ℝ) ≤ (A.clock.J m:ℝ)+1 := by exact_mod_cast A.fits.stepSlow m
  unfold tail
  calc
    _ ≤ 30 * (s.a m/3) * (((A.clock.J m:ℝ)+1)+5) := by have hx := s.a_pos m; gcongr
    _ ≤ _ := by
      have ht : 0 ≤ s.a m * (A.clock.J m:ℝ) := mul_nonneg hp.le (Nat.cast_nonneg _)
      dsimp only [s] at *; linarith

lemma tail_zero : Tendsto (tail A) atTop (𝓝 0) := by
  have ht (m : ℕ) : tail A m ≤ tail A 0 * ((2:ℝ)/3)^m := by
    induction m with
    | zero => simp
    | succ i ih => calc
        _ ≤ _ := tail_next A i
        _ ≤ ((2:ℝ)/3)*(tail A 0*((2:ℝ)/3)^i) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by rw [pow_succ]; ring
  refine squeeze_zero (fun i => (tail_pos A i).le) ht ?_
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r:= (2:ℝ)/3) (by norm_num) (by norm_num)).const_mul (tail A 0)

lemma scales_next (m r : ℕ) : A.S.a (m+1) * expansion A r m + tail A (m+1) ≤ A.S.a m * r + tail A m := by
  have hv := tail_next A m
  have hh : A.S.a (m+1)*expansion A r m = A.S.a m*(r:ℕ) + A.S.a m*(10*((A.clock.J (m+1):ℝ)+3)) := by
    unfold expansion
    rw [A.S.a_step]; push_cast; field_simp
  have he : A.S.a m*(10*((A.clock.J (m+1):ℝ)+3)) ≤ tail A m/3 := by
    have hs : (A.clock.J (m+1):ℝ) ≤ (A.clock.J m:ℝ)+1 := by exact_mod_cast A.fits.stepSlow m
    calc
      _ ≤ A.S.a m*(10*((A.clock.J m:ℝ)+5)) := mul_le_mul_of_nonneg_left (by linarith) (A.S.a_pos m).le
      _ = _ := by unfold tail; ring
  linarith

lemma scales_budget (k r : ℕ) (q : k ≤ m) : A.S.a m * grows A k r q + tail A m ≤ A.S.a k * r + tail A k := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ i q ih => rw [grows_next A k r q]; exact le_trans (scales_next A _ _) ih

/-- One prerequisite, obtainable for all sufficiently large k at h fixed. -/
def room (h k r : ℕ) := 2*(A.S.a k*r + tail A k) < A.S.a h

lemma plenty (h r : ℕ) : ∀ᶠ k : ℕ in atTop, room A h k r := by
  have ht : Tendsto (fun k => 2*(A.S.a k*r+tail A k)) atTop (𝓝 0) := by
    simpa using (((A.S.shrinks.mul_const (r:ℝ)).add (tail_zero A)).const_mul 2)
  exact ht.eventually (gt_mem_nhds (A.S.a_pos h))

lemma room_fits (r : ℕ) (hk : h ≤ k) (q : k ≤ m) (he : room A h k r) (i : Site (A.S.side h p)) :
    window (anchor A.S p (hk.trans q) i) (grows A k r q) ⊆ (tilesAt A.S p (hk.trans q)).chamber i := by
  apply window_fits
  have hh := scales_budget A k r q
  have ht := A.S.embeds_scale (A.S.toDepth (hk.trans q) p)
  have hv : (((2*grows A k r q):ℕ):ℝ) < (A.S.toDepth (hk.trans q) p).count.val := by
    apply lt_of_mul_lt_mul_left _ (A.S.a_pos m).le
    rw [ht]; unfold room at he; push_cast
    linarith only [he,hh,tail_pos A m]
  exact_mod_cast hv
end physical
end YM.Push.GridApprox
