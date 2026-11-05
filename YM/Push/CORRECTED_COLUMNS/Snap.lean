import YM.Next.EXTRACTION.Mixture
import YM.Push.CORRECTED_COLUMNS.Program

/-!
# Fixed k clusters at actual sites, both ordered limits

On the ONE extraction. Even if only need the fused-filter consequence,
include the mesh limits with named coefficient data at every p. May translate
the cluster on its grid (e.g. by even cell counts, since the width side is
also an integral number of k spacings). No point claim for projection ties
between independently translated copies. Uses the same label budget data.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open Function Set Filter MeasureTheory Lattice Wilson RG Cells Extraction Next.Extract
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S T : Table C.book} {d : ℕ} {X : Columns C S d} {f : Extraction.Order}
variable {M : ℕ → Table C.book}

-- Limit labels (even on every p, not just on `per`). Used to name the precise values, no choice inside.
structure Settled (f : Extraction.Order) (Y : Tests X) (z : ℕ → AxisX X → ℕ → C.label d)
    (t : ℕ → AxisX X → C.label d) : Prop where
  rows (k i p) : Tendsto (fun j => Y.tune k (f.mesh j) p i) atTop (𝓝 (z k i p))
  outer (k i) : Tendsto (fun j => z k i (f.per j)) atTop (𝓝 (t k i))

lemma Settled.respond {Y : Tests X} {z t} (h : Settled f Y z t) (k i) :
    f.limits (fun _ => True) (fun N p => Y.tune k N p i) (t k i) :=
  ⟨Eventually.of_forall fun _ => trivial, z k i,fun p _ => h.rows k i p,h.outer k i⟩

section
variable (h : RawLimits C f T M)
include h

private lemma rows {n : ℕ} (v : Fin n → Cover) (k p : ℕ) {d : Caps n} (L : ℕ → C.book.Vector d) {w : C.book.Vector d}
    (hp : Order.grid C k v ∈ Cyclic C.S p n) (ht : Tendsto (fun j => L (f.mesh j)) atTop (𝓝 w)) :
    Tendsto (fun j => C.ensemble d (fun i => Cells.location C.S k (f.mesh j) p (v i)) (L (f.mesh j))) atTop
      (𝓝 ((M p).value d (Order.grid C k v) w)) := by
  let x := Order.grid C k v
  -- every deeper grid uses same x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hW := mixture_mesh h.mesh p (isCompact_singleton (x:=x)) (singleton_subset_iff.mpr hp) ht ε hε
  filter_upwards [hW, f.mesh.cofinal.eventually_ge_atTop k] with i hi hN
  let N := f.mesh i
  let D (j) := (C.S.toDepth hN p).count.val • v j
  have he : Order.grid C N D = x := by
    ext1 j; exact (Positions.lifted C.S hN (p:=p) (v j)).2
  have hw j : Cells.location C.S k N p (v j) = wrap _ (D j) := (Positions.lifted _ hN _).1
  have hv := hi D (by rw [show f.mesh i=N from rfl, he]; simp)
  rw [he] at hv
  rw [dist_eq_norm]
  change ‖C.ensemble d (fun j => Cells.location C.S k N p (v j)) _- (M p).value d x w‖ < ε
  simp_rw [hw]; exact hv

private lemma outer {n : ℕ} (v : Fin n → Cover) (k : ℕ) {d : Caps n} (L : ℕ → C.book.Vector d) {w : C.book.Vector d}
    (hx : Order.grid C k v ∈ generic n) (ht : Tendsto (fun j => L (f.per j)) atTop (𝓝 w)) :
    Tendsto (fun j => (M (f.per j)).value d (Order.grid C k v) (L (f.per j))) atTop
        (𝓝 (T.value d (Order.grid C k v) w)) := by
  let x := Order.grid C k v
  apply Metric.tendsto_nhds.mpr; intro ε hε
  filter_upwards [mixture_volume h (isCompact_singleton (x:=x)) (singleton_subset_iff.mpr hx) ht ε hε] with j hj
  rw [dist_eq_norm]; exact hj _ (mem_singleton _)
end

section
variable (Y : Tests X) {z : ℕ → AxisX X → ℕ → C.label d} {t : ℕ → AxisX X → C.label d}
variable (ha : RawLimits C f T M) (H : Settled f Y z t)
include H ha

/-- Joint fixed-label passage with a *single* injection of a subcluster: here
positions are fixed in the k-grid. Works even when v translated past strict
period corner. All periods requested when cyclic there. -/
theorem travels {n : ℕ} (k : ℕ) (v : Fin n → Cover) (y : Fin n → AxisX X) (hx : Order.grid C (Y.B.depth k) v∈generic n) :
    let q := Order.grid C (Y.B.depth k) v
    (∀ p, q∈Cyclic C.S p n → Tendsto (fun j => moment (C.beta (f.mesh j) p) (fun U => ∏ i,
      C.O (f.mesh j) p (d:=d) (Y.tune k (f.mesh j) p (y i)) (Cells.location C.S (Y.B.depth k) (f.mesh j) p (v i)) U))
      atTop (𝓝 ((M p).read q fun i => ⟨d,z k (y i) p⟩))) ∧
    Tendsto (fun j => (M (f.per j)).read q fun i => ⟨d,z k (y i) (f.per j)⟩) atTop
      (𝓝 (T.read q fun i => ⟨d,t k (y i)⟩)) := by
  intro q
  let D : Caps n := fun _ => d
  refine ⟨fun p hp => rows ha v (Y.B.depth k) p (d:=D) (fun N i => Y.tune k N p (y i)) (w:=fun i => z k (y i) p) hp
    (tendsto_pi_nhds.mpr fun i => H.rows k (y i) p), outer ha v _ (d:=D) (fun p i => z k (y i) p) hx ?_⟩
  exact tendsto_pi_nhds.mpr fun i => H.outer k (y i)

omit H ha in
-- all subclusters fit all periods even through translation, modulo cyclic rule
private lemma subgrid {n : ℕ} (k i) (w : Fin n → Mark X i) (h : Injective w) (r : Cover) :
    let v j := Y.B.address k (X.row i).expected (w j) + r
    let q := Order.grid C (Y.B.depth k) v
    q ∈ generic _ ∧ ∀ p, q ∈ Cyclic C.S p n := by
  intro v q
  have H : Y.place k i∈generic _ := (Y.room k i).1
  have he j a : q j a=Y.place k i (w j) a+C.S.gridPoint (Y.B.depth k) r a := by
    unfold q; simp only [Order.grid,points_apply,Schedule.gridPoint,WithLp.ofLp_toLp, v,
      Pi.add_apply, Int.cast_add,mul_add]; rfl
  refine ⟨fun a j l hq => h (H a ?_),fun p => ?_⟩
  · change q j a=q l a at hq
    rw [he,he] at hq; exact add_right_cancel hq
  have hz : Y.place k i∈Cyclic C.S p _ := (no_wrap_tie C.S
    (Positions.hosted p _ (fun j => (Y.room k i).2 j))).2 H
  intro j l hi a H
  apply hz _ _ (h.ne hi) a
  unfold periodic at *; rw [he, he, add_sub_add_right_eq_sub] at H; exact H

theorem copied (k i c) {n : ℕ} (w : Fin n → Mark X i) (hw : Injective w) (r : Cover) :
    let v j := Y.B.address k (X.row i).expected (w j)+r
    let q := Order.grid C (Y.B.depth k) v
    let y j := Columns.Trials.names (X:=X) i c (w j)
    (∀ p, Tendsto (fun j => moment (C.beta (f.mesh j) p) (fun U => ∏ i,
      C.O (f.mesh j) p (d:=d) (Y.tune k (f.mesh j) p (y i)) (Cells.location C.S (Y.B.depth k) (f.mesh j) p (v i)) U))
      atTop (𝓝 ((M p).read q fun i => ⟨d,z k (y i) p⟩))) ∧
    Tendsto (fun j => (M (f.per j)).read q fun i => ⟨d,z k (y i) (f.per j)⟩) atTop
      (𝓝 (T.read q fun i => ⟨d,t k (y i)⟩)) := by
  intro v q y
  have hj := subgrid Y k i w hw r
  obtain ⟨he,h⟩ := travels Y ha H k v y hj.1
  exact ⟨fun p => he p (hj.2 p),h⟩

theorem returned (k i c) {n : ℕ} (w : Fin n → Mark X i) (hw : Injective w) :
    f.limits (fun _ => True) (fun N p => moment (C.beta N p) (fun U => ∏ j, Y.letter k N p i c (w j) U))
      (T.read (points fun j => Y.place k i (w j)) fun j => ⟨d,t k (Columns.Trials.names (X:=X) i c (w j))⟩) := by
  have hp := copied Y ha H k i c w hw 0
  dsimp only at hp
  simp_rw [add_zero] at hp
  obtain ⟨h,hP⟩ := hp
  let W v := (M v).read (points fun j => Y.place k i (w j)) fun j => ⟨d,z k (Columns.Trials.names (X:=X) i c (w j)) v⟩
  exact ⟨Eventually.of_forall fun _ => trivial,W,fun i _ => h i,hP⟩
end
end YM.Push.Corrected
