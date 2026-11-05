import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alphabet



/-!
# The local trace alphabet has a summable price, even over long strings

Internal indices use the projected-parent separation and keep BOTH window
and dependence halos (a caller's chosen multiple l of B about each
link-cost site). `Ac.Hit`: the marked *site-hit absolute sum*, not merely
∑_x divided by torus volume. The question that these supports are
sufficient for the actual calculations is proved separately. Only finite
range used here for the length charge, no assumptions about sparsity of
D rows within it. Works also for torus with wraps, repeated same key.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Set Matrix MeasureTheory FreeResolvent Lattice
open Next.SectorChange
open scoped Topology BigOperators Classical

section geometry
variable {ι : Type} {c : Side} {l R B k : ℕ} (p : ι → Site c)

/-- Cost ball at actual output anchor, even if the computed matrix happens to be 0. -/
def lens (l B : ℕ) (i : ι) := halo (l*B) {p i}
/-- Jump accessibility in the true cost-distance on output. -/
def nearby (R : ℕ) (i j : ι) := separation (p i) (p j) ≤ R

/-- For admitted jumps we also price the *cover itself*; for nonadmitted jumps the
terms being budgeted here are proved identically zero, and we still keep their Support
but need not bound its cover to carry the absolutely summable bills.

Chain costs include the lens at every intermediate key, no permutation/Stirling
shortcut, and all queried sites must be assigned their dependence halos. -/
def pocket (l B : ℕ) : {k : ℕ} → ι → ι → (Fin k→ι) → Support c
  | 0, i,j,_ => lens p l B i ∪ lens p l B j
  | k+1, i,j,x => lens p l B i ∪ pocket l B (k:=k) (x 0) j (Fin.tail x)

lemma lens_spec {i : ι} {x} : x ∈ lens p l B i ↔ separation (p i) x ≤ l*B := by simp [lens,halo_spec]
lemma lens_root (i : ι) (l B : ℕ) : p i ∈ lens p l B i := (lens_spec p).mpr (by simp)
lemma first_lens (i j : ι) (x : Fin k→ι) : lens p l B i ⊆ pocket p l B i j x := by cases k <;> exact Finset.subset_union_left

lemma pocket_span {i j : ι} (x : Fin k→ι) (hx : jumps (nearby p B) i j x) {s} (he : s ∈ pocket p l B i j x) :
    separation (p i) s ≤ (k+1+l)*B := by
  induction k generalizing i with
  | zero =>
    rw [pocket,Finset.mem_union] at he
    rcases he with h|h
    · apply ((lens_spec _).mp h).trans; gcongr; omega
    apply (separation_triangle _ (p j) _).trans
    nth_rw 1 [Nat.add_mul]
    simpa using Nat.add_le_add (show separation _ _ ≤ B from hx) ((lens_spec _).mp h)
  | succ k ih =>
    rcases (show nearby p B i (x 0) ∧ _ from hx) with ⟨hi,hj⟩
    rw [pocket,Finset.mem_union] at he
    rcases he with h|h
    · apply ((lens_spec _).mp h).trans; gcongr; omega
    apply (separation_triangle _ (p (x 0)) _).trans
    rw [show k+1+1+l=1+(k+1+l) by omega, Nat.add_mul 1,one_mul]
    exact Nat.add_le_add hi (ih (Fin.tail x) hj h)

def tilePrice (l : ℕ) := (l+l+1)^4
lemma lens_price (hB : 0<B) (l) (i : ι) : coverNumber B (lens p l B i) ≤ tilePrice l := Corona.tile (p i) l B hB
lemma pocket_cost (hB : 0<B) (h : 1 ≤ l) (i j : ι) (x : Fin k → ι) (hx : jumps (nearby p B) i j x) :
    coverNumber B (pocket p l B i j x) ≤ (k+2)*tilePrice l := by
  have hs (i j : ι) (he : nearby p B i j) : p j ∈ lens p l B i := (lens_spec p).mpr (he.trans (by simp [Nat.le_mul_of_pos_left B h]))
  induction k generalizing i with
  | zero =>
    rw [pocket]; exact (Corona.meets_sum (hs i j hx) (lens_root p j l B) B).trans
      ((Nat.add_le_add (lens_price p hB ..) (lens_price p hB ..)).trans (by omega))
  | succ k ih =>
    rw [pocket]
    rcases (show nearby p B i (x 0) ∧ _ from hx) with ⟨hi,hj⟩
    apply (Corona.meets_sum (hs i _ hi) (first_lens _ _ _ _ (lens_root p (x 0) l B)) _).trans
    specialize ih (x 0) (Fin.tail x) hj
    exact (Nat.add_le_add (lens_price p hB l i) ih).trans_eq (by rw [show k+1+2=1+(k+2) by omega, Nat.add_mul 1,one_mul])

lemma pocket_through (Z : Support c) {P T S S' : Square ι} {i j : ι} (x : Fin k → ι)
    (hz : pocket p l B i j x ⊆ Z) (hs : jumps (nearby p B) i j x)
    (hP : ∀ i j, lens p l B i ⊆ Z → nearby p B i j → P i j=T i j)
    (hS : ∀ i j, lens p l B i ⊆ Z → nearby p B i j → S i j=S' i j) :
    road P S i j x = road T S' i j x := by
  induction k generalizing i P T with
  | zero => exact hP i j ((first_lens ..).trans hz) hs
  | succ k ih =>
    unfold jumps at hs
    rw [road,road,hP _ _ ((first_lens ..).trans hz) hs.1]; congr 1
    exact ih _ ((show pocket p l B (x 0) j _ ⊆ _ from Finset.subset_union_right).trans hz) hs.2 hS
end geometry

section distance
variable {ι : Type} {c : Side} [Fintype ι] [DecidableEq ι] {p : ι → Site c} {A : Square ι} {W : ι → Set ι} {B : ℕ}

def Reaches (p : ι → Site c) (B : ℕ) (A : Square ι) := ∀ i j, ¬ nearby p B i j → A i j=0
omit [Fintype ι] [DecidableEq ι] in
lemma Reaches.trans (h : Reaches p B A) {b} (he : B ≤ b) : Reaches p b A := fun i j hx => h i j (fun hp => hx (hp.trans he))
omit [Fintype ι] [DecidableEq ι] in
lemma Reaches.neg (h : Reaches p B A) : Reaches p B (-A) := fun i j hx => by simp [h i j hx]
omit [DecidableEq ι] in
lemma Reaches.mix {C : Square ι} {r : ℕ} (h : Reaches p B A) (hc : Reaches p r C) : Reaches p (B+r) (A*C) := by
  intro i j hij; rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hi : nearby p B i k
  · have he : ¬ nearby p r k j := fun hk => hij ((separation_triangle _ (p k) _).trans (Nat.add_le_add hi hk))
    rw [hc _ _ he,mul_zero]
  rw [h i k hi,zero_mul]
omit [Fintype ι] [DecidableEq ι] in
lemma Reaches.add (h : Reaches p B A) {C : Square ι} (g : Reaches p B C) : Reaches p B (A+C) :=
  fun i j he => by simp [h i j he,g i j he]
omit [Fintype ι] [DecidableEq ι] in
lemma Reaches.scale (h : Reaches p B A) (v : ℝ) : Reaches p B (v • A) := fun i j he => by simp [h i j he]
omit [Fintype ι] [DecidableEq ι] in
lemma Reaches.symm (h : Reaches p B A) : Reaches p B A.transpose := fun i j he => h j i
  (fun hx => he ((separation_comm (p i) _).trans_le hx))
omit [Fintype ι] in
lemma Reaches.one (p : ι → Site c) (B : ℕ) : Reaches p B 1 := by
  intro i j h
  rw [Matrix.one_apply_ne]; rintro rfl; apply h; simp [nearby]

/-- Half B is room for the needed binary products. Uses *possible*
address, not just actual nonzero tests. -/
def Aperture (p : ι → Site c) (B : ℕ) (W : ι → Set ι) (A : Square ι) :=
    Reaches p (B/2) A ∧ ∀ i j, j ∈ W i → nearby p (B/2) i j
namespace Aperture
lemma glance (h : Aperture p B W A) (u : ℝ) : Reaches p (B/2) (pie W A u) := by
  intro i j hij
  exact pie_miss W A u i j (fun hj => hij ((separation_comm ..).trans_le (h.2 j i hj)))
lemma light (h : Aperture p B W A) (u : ℝ) : Reaches p B (defect W A u) := by
  unfold defect; rw [sub_eq_add_neg]
  exact (((h.1.add ((Reaches.one p _).scale u)).mix (h.glance u)).trans (by omega)).add (Reaches.one p B).neg
lemma cloud (h : Aperture p B W A) : Reaches p (B/2) (Schur.clouded W A) := by
  rw [sym_cloud]; exact ((h.glance 0).add (h.glance 0).symm).scale _
lemma spare (h : Aperture p B W A) : Reaches p B (excess W A) := by
  rw [excess,sub_eq_add_neg]; exact ((h.1.mix h.cloud).trans (by omega)).add (Reaches.one p _).neg

lemma away (h : Aperture p B W A) (z : Letter ι 1) (hp : ¬ jumps (nearby p B) z.2.1 z.2.1 z.2.2) (u : ℝ) :
    scroll W A z.2.1 z.2.2 u = 0 := by
  unfold scroll; rw [road_drop _ _ ((h.glance u).trans (by omega)) (h.light u).neg _ _ z.2.2 hp,neg_zero]

lemma quiet (h : Aperture p B W A) (z : Letter ι 0) (hp : ¬ jumps (nearby p B) z.2.1 z.2.1 z.2.2) :
    errata W A z = 0 := by unfold errata; dsimp only; rw [road_drop _ _ h.spare.neg h.spare.neg _ _ z.2.2 hp,neg_zero,zero_div]
end Aperture
end distance
end YM.AnalyticBridge.RelativeLogdet
