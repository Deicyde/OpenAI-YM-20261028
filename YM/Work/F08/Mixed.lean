import YM.Work.F08.Rows

/-!
Mixed composition of a fine-to-fine row P with a cross row Q (and, on
the other side of a cross row, composition with ordinary coarse rows).
Following from row to column: each fine displacement `a` chooses exactly one
residue for Q, and propagates the coarse origin by `carry r a`. Thus at
fixed output row residue we can use `routed` to keep a pre-L width and
price, without paying the number of residues. We check the signs and the origin
update also in the physical tori, without assuming sizes large versus paths.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F08
open Lattice Bloch Laurent
open scoped BigOperators

variable {c f L : Side}

/-- New fine residue after stepping `a` on the cover from residue `r`. -/
def arrives (r : Site L) (a : Cover) := wrap L (lift r + a)

/-- Existence of the induced shift in block origin (in coarse units). -/
lemma carry_exists (r : Site L) (a : Cover) :
    ∃ w : Cover, lift r + a = lift (arrives r a) + L.val • w :=
  cover_of_eq _ _ (wrap_lift (arrives r a))

def carry (r : Site L) (a : Cover) := (carry_exists r a).choose

lemma carry_spec (r : Site L) (a : Cover) :
    lift r + a = lift (arrives r a) + L.val • carry r a := (carry_exists r a).choose_spec

/-- Uniform step bound: an integral fine step pays for every coarse
carry. Also covers L=1. -/
lemma carry_size (r : Site L) (a : Cover) : size (carry r a) ≤ size a := by
  apply Finset.sum_le_sum
  intro i _
  let w := carry r a i
  let n : ℤ := L.val
  let u := lift r i
  let v := lift (arrives r a) i
  have he : u + a i = v + n * w := by
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, Pi.smul_apply, nsmul_eq_mul, w, n, u, v] using
      congrFun (carry_spec r a) i
  have hn : 0 < n := Int.natCast_pos.mpr L.pos
  have hc : |u - v| ≤ n - 1 := by
    have h1 : -n < 2*u ∧ 2*u ≤ n := lift_centers r i
    have h2 : -n < 2*v ∧ 2*v ≤ n := lift_centers (arrives r a) i
    rw [abs_sub_le_iff]; omega
  have hb : n * |w| ≤ |a i| + (n - 1) := calc
    _ = |n * w| := by rw [abs_mul, abs_of_pos hn]
    _ = |a i + (u - v)| := by rw [show n * w = a i + (u - v) from by omega]
    _ ≤ _ := (abs_add_le ..).trans (add_le_add_right hc _)
  have hw : |w| ≤ |a i| := by
    by_contra! ht
    have hlt : |a i| + 1 ≤ |w| := by omega
    have hge : 1 ≤ n := by omega
    have hmore : |a i| + n ≤ n * |w| := calc
      |a i| + n ≤ n * |a i| + n := by
        have hh := mul_le_mul_of_nonneg_right hge (abs_nonneg (a i))
        rw [one_mul] at hh
        exact add_le_add_left hh _
      _ = n * (|a i| + 1) := by ring
      _ ≤ n * |w| := mul_le_mul_of_nonneg_left hlt hn.le
    omega
  rw [← Int.natCast_natAbs, ← Int.natCast_natAbs (a i)] at hw
  change w.natAbs ≤ (a i).natAbs
  exact_mod_cast hw

lemma moves_site (g : Ratio c f) (x : Site f) (a : Cover) :
    x + wrap f a = g.assemble (g.parent x + wrap c (carry (g.residue x) a),
      arrives (g.residue x) a) := by
  let r := g.residue x
  let b := carry r a
  let t := arrives r a
  have he : g.embed (g.parent x + wrap c b) = g.embed (g.parent x) + wrap f (g.count.val • b) :=
    (g.root.map_add _ _).trans (by rw [g.root_embed, g.root_embed, g.embed_wrap])
  change _ = g.embed (g.parent x + wrap c b) + wrap f (lift t)
  rw [he]
  calc
    x + wrap f a = (g.embed (g.parent x) + wrap f (lift r)) + wrap f a := by
      rw [show g.embed (g.parent x) + wrap f (lift r) = x from g.unpack_at x]
    _ = g.embed (g.parent x) + wrap f (lift t + g.count.val • b) := by
      rw [show lift t + g.count.val • b = lift r + a from (carry_spec r a).symm,
        map_add, add_assoc]
    _ = _ := by rw [map_add]; abel

lemma moves_parent (g : Ratio c f) (x : Site f) (a : Cover) :
    g.parent (x + wrap f a) = g.parent x + wrap c (carry (g.residue x) a) := by
  rw [moves_site, g.assemble_parent]

lemma moves_residue (g : Ratio c f) (x : Site f) (a : Cover) :
    g.residue (x + wrap f a) = arrives (g.residue x) a := by
  rw [moves_site, g.assemble_res]

variable {α β ξ : Type*}

def fineCompose [Fintype β] (P : Row α β) (Q : Cross L β ξ) : Cross L α ξ :=
  fun i j z ↦ ∑ b, routed (carry i.1) (P i.2 b) (fun a ↦ Q (arrives i.1 a, b) j) z

lemma installed_sift (g : Ratio c f) (P : Cross g.count α β) (x : Site f) (y : Site c)
    (i : α) (j : β) : installed g P (x,i) (y,j) =
    sift (P (g.residue x, i) j) c (g.parent x) y := by
  rw [installed, Matrix.submatrix_apply, split_co]
  rfl

variable [Fintype β] {η A B : ℝ}

lemma strip_fine {P : Row α β} {Q : Cross L β ξ} (he : 0 ≤ η)
    (hP : P.strip η A) (hQ : Q.strip η B) :
    (fineCompose P Q).strip η (Fintype.card β * (A * B)) := by
  rintro ⟨r,i⟩ j
  exact width_sum_finite fun b ↦
    width_routed he (carry_size r) (hP i b) (fun a ↦ hQ (arrives r a,b) j)

lemma installed_fine (g : Ratio c f) {P : Row α β} {Q : Cross g.count β ξ} (he : 0 ≤ η)
    (hP : P.strip η A) (hQ : Q.strip η B) :
    installed g (fineCompose P Q) = P.acts f * installed g Q := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [installed_sift]
  let r := g.residue x
  let entry (b : β) (a : Cover) := Q (arrives r a, b) j
  let column (b : β) (w : Site f) := sift (Q (g.residue w,b) j) c (g.parent w) y
  change sift (fun z ↦ ∑ b, routed (carry r) (P i b) (entry b) z) c (g.parent x) y =
    ∑ b, ∑ w, sift (P i b) f x w * column b w
  have hb (b : β) (a) : Width η B (entry b a) := hQ _ _
  have hs (b : β) := (width_routed he (carry_size r) (hP i b) (hb b)).summable he
  rw [sift_sum_finite hs]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [sift_action ((hP _ _).summable he), sift_routed he (carry_size r) (hP _ _) (hb b)]
  refine tsum_congr fun a ↦ ?_
  unfold entry column r
  rw [moves_parent, moves_residue]

lemma installed_compose (g : Ratio c f) {P : Cross g.count α β} {Q : Row β ξ} (he : 0 ≤ η)
    (hP : P.strip η A) (hQ : Q.strip η B) :
    installed g (composeRows P Q) = installed g P * Q.acts c := by
  unfold installed
  rw [acts_compose he hP hQ]; rfl

end YM.Work.F08
