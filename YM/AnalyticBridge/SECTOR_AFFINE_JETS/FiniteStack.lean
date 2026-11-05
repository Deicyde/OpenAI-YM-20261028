import YM.Push.FREE_RESOLVENT.Weights
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine

/-!
# The analytic stack: summing labels even when cut kernels still use a series

Cut on actual slot lengths, don't assume only a finite number of labels
can produce them. For proving smoothness and entry estimates we can work via
a finite grouping by slot. This has no effect on the actual covariance
construction or label paths recorded in it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Stack
open Filter Function Lattice Wilson RG Precision Pressure Tree
open YM.Next.Fluctuations YM.Next.SectorChange
open Finset
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

private def alphabet := (univ : Finset (Axis × Bool)).image (fun (p : Axis × Bool) => Lattice.Step.mk p.1 p.2)
private lemma stroke (d : Lattice.Step) : d ∈ alphabet := mem_image.mpr ⟨(d.dir,d.neg),mem_univ _,rfl⟩

private def strings : ℕ → Finset Walk
  | 0 => {[]}
  | n+1 => insert [] ((alphabet ×ˢ strings n).image fun (d,l) => d::l)

private lemma leg (l : Walk) (n : ℕ) (h : l.length ≤ n) : l ∈ strings n := by
  induction l generalizing n with
  | nil => cases n <;> simp [strings]
  | cons d l ih =>
    obtain _|n := n
    · simp at h
    · exact mem_insert_of_mem (mem_image.mpr ⟨(d,l),mem_product.mpr ⟨stroke _,ih n (by simpa using h)⟩,rfl⟩)

def allShort (n : ℕ) :=
  (((strings n) ×ˢ (univ : Finset PlaqAxes)).image (fun (p,q) => RG.Slot.mk p q)).filter fun x => x.length≤n

lemma short_iff (x : RG.Slot) (n : ℕ) : x∈allShort n ↔ x.length ≤ n := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  intro h
  refine mem_filter.mpr ⟨mem_image.mpr ⟨(x.walk,x.plaq),mem_product.mpr ⟨leg _ _ ?_,mem_univ _⟩,rfl⟩, h⟩
  exact (Nat.le_add_right x.walk.length 4).trans h

variable {G : Gauge} {n : Side} {σ C Λ : ℝ} {c : Clip} {P : PathData G}

def subCost (P : PathData G) (p : PlaqAxes) (z : RG.Slot) (i : ℕ) : ℝ :=
  if (P.row p i).2=z then (P.row p i).1 else 0

lemma sums (h : P.Bounds c σ C Λ) (p : PlaqAxes) (z : RG.Slot) : Summable (subCost P p z) := by
  refine Summable.of_norm_bounded (YM.Work.F03.row_abs_summable P h p) ?_
  intro i; unfold subCost; split
  · exact le_of_eq (Real.norm_eq_abs _)
  rw [norm_zero]; exact abs_nonneg _

def grouped (P : PathData G) (p : PlaqAxes) (z : RG.Slot) : ℝ := ∑' i, subCost P p z i

/-- Sum-budget before plane-wave or periods. All multiplicities by actual
coefficient; no occupancy bound on number in a box of offsets. -/
lemma grouped_le (A : Finset RG.Slot) (h : P.Bounds c σ C Λ) (p : PlaqAxes) :
    (∑ z ∈ A, |grouped P p z| * Real.exp (σ*z.length)) ≤ C := by
  let Q (z : RG.Slot) (i : ℕ) := ‖subCost P p z i‖
  let W (z : RG.Slot) := Real.exp (σ*z.length)
  have ha z : Summable (Q z) := (sums h p z).norm
  have he z : HasSum (fun i => Q z i * W z) ((∑' i, Q z i)*W z) := (ha z).hasSum.mul_right _
  let D (i : ℕ) := ∑ z ∈ A, Q z i * W z
  have hd : HasSum D (∑ z ∈ A, (∑' i, Q z i)*W z) := by
    exact hasSum_sum (s:=A) fun i _ => he i
  have hx i : D i ≤ |(P.row p i).1| * Real.exp (σ*(P.row p i).2.length) := by
    by_cases hu : (P.row p i).2 ∈ A
    · unfold D; rw [Finset.sum_eq_single_of_mem _ hu]
      · simp [Q,W,subCost]
      intro b hb hp
      simp [Q,subCost,hp.symm]
    have hh : D i=0 := Finset.sum_eq_zero (fun b hb => by
      simp [Q,subCost,show (P.row p i).2≠b from fun h => hu (h.symm ▸ hb)])
    rw [hh]; exact (h.rows p).1 i
  apply le_trans _ ((hd.tsum_eq.symm.le.trans (hd.summable.tsum_le_tsum hx (h.rows p).2.1)).trans
    (h.rows p).2.2)
  apply sum_le_sum; intro i _
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact norm_tsum_le_tsum_norm (ha i)

lemma finite_price (p : Cell n) (r : ℕ) (U : Config G n) (b : LogArray G (Cell n)) (h : P.Bounds c σ C Λ) :
    barrel P r U b p = ∑ z ∈ allShort r, grouped P p.2 z •
      G.adjoint (travel U p.1 z.walk) (b (YM.Work.F03.slotFace z p.1)) := by
  let H (z : RG.Slot) := G.adjoint (travel U p.1 z.walk) (b (YM.Work.F03.slotFace z p.1))
  have he z : HasSum (fun i => subCost P p.2 z i • H z) (grouped P p.2 z • H z) :=
    (sums h p.2 z).hasSum.smul_const _
  have hv : HasSum (fun i => ∑ z ∈ allShort r, subCost P p.2 z i • H z)
      (∑ z ∈ allShort r, grouped P p.2 z • H z) := hasSum_sum (s:=allShort r) fun i _ => he i
  unfold barrel
  refine Eq.trans ?_ hv.tsum_eq
  refine tsum_congr fun i => ?_
  let z := (P.row p.2 i).2
  dsimp only; split
  next hp =>
    rw [sum_eq_single_of_mem z ((short_iff z r).mpr hp)]
    · simp only [z, H, subCost,↓reduceIte]
    intro j hj he
    simp [subCost,(show (P.row p.2 i).2 ≠ j from Ne.symm he)]
  next hp =>
    symm; refine sum_eq_zero (fun j hj => ?_)
    have hz : j≠z := fun e => hp ((short_iff z r).mp (e ▸ hj))
    rw [subCost,if_neg hz.symm,zero_smul]
end YM.AnalyticBridge.SectorAffine.Stack
