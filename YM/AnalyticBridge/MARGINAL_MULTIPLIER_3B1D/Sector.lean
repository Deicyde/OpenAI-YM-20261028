import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Core
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Tunnel
import YM.Next.SCHEDULE.GridCost
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore

/-!
Bind one local multiplier into the exact Gaussian-sector identity (including
where flag data conflict). This is an extraction with an explicit remaining
factor, **not** the assertion that the full correction factors over windows.
The inverse in the local charge in particular is a marginal inverse. No
summation regrouping over b or exchange with integrals in this identity.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open YM.Next.SectorChange
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Precision Tree Matrix
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

structure Leaf (G : Gauge) (A : Stores S) (x : ℝ) (F : Forest S.ratio) (I J ρ : Type) where
  hot : I ↪ Active A x F
  cold : J ↪ Frozen A x F
  rows : ρ ↪ Rows.Receipt G S

namespace Leaf
variable {x α : ℝ} {A : Stores S} {F : Forest S.ratio} {I J ρ : Type}
    (L : Leaf G A x F I J ρ)

def both : I ⊕ J ↪ F.Free where
  toFun := Sum.elim ((↑) ∘ L.hot) ((↑) ∘ L.cold)
  inj' := by
    rintro (i|i) (j|j) he
    · exact congr_arg Sum.inl (L.hot.injective (Subtype.ext he))
    · exact ((L.hot i).2 ((show (L.hot i).val = (L.cold j).val from he).symm ▸ (L.cold j).2)).elim
    · exact ((L.hot j).2 ((show (L.cold i).val = (L.hot j).val from he) ▸ (L.cold i).2)).elim
    · exact congr_arg Sum.inr (L.cold.injective (Subtype.ext he))
def location : Location f I J := ⟨L.both.trans (Function.Embedding.subtype _)⟩
def active : I × G.ColorIndex ↪ Rows.In x A F (G:=G) := L.hot.prodMap (Function.Embedding.refl _)
def free : (I ⊕ J) × G.ColorIndex ↪ Key F G := L.both.prodMap (Function.Embedding.refl _)

def cov (T : Tube G S) (k : S.Choices) (V : Config G c) : Gaussian.Table (I × G.ColorIndex) :=
  (fog A F T x V k).submatrix L.active L.active
def gram (T : Tube G S) (k : S.Choices) (V : Config G c) : Gaussian.Table (I × G.ColorIndex) :=
  (Rows.gram T x V k (shots S x) A F).submatrix L.active L.active

def paper (T : Tube G S) (k : S.Choices) (β : ℝ) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) : Kernel G c I J ρ where
  cov := L.cov T k
  gram := L.gram T k
  flat := (Native.kinetic T F k x).submatrix L.free L.free
  mean V i := tape (meanLog A F T x V k q d Y) (L.hot i)
  draw _ := z ∘ L.active
  signal V := Rows.eta T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) (coupling β) ∘ L.active
  offset V i := (coupling β)⁻¹ * Rows.direct T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) (L.rows i)
  holds i := Y (L.cold i)

/-- Actual slots must agree HERE. Does not assert equality of germs: hard
criteria/flags needn't even be differentiable through the base point, and
moving-coordinate curves when used price derivatives along those curves. -/
structure Binds (T : Tube G S) (k : S.Choices) (β : ℝ) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F))
    (V : Config G c) (h : Kernel G c I J ρ) : Prop where
  cov : h.cov V = (L.paper T k β q d Y z).cov V
  gram : h.gram V = (L.paper T k β q d Y z).gram V
  flat : h.flat = (L.paper T k β q d Y z).flat
  mean : h.mean V = (L.paper T k β q d Y z).mean V
  draw : h.draw V = (L.paper T k β q d Y z).draw V
  signal : h.signal V = (L.paper T k β q d Y z).signal V
  offset : h.offset V = (L.paper T k β q d Y z).offset V
  holds : h.holds = (L.paper T k β q d Y z).holds

def Includes (X : Support f) : Prop := ∀ i : F.Free, i.val.1∈inspected X → i.val.1+Lattice.step i.val.2 ∈ inspected X → i∈Set.range L.both
variable {T : Tube G S} {k : S.Choices} {q : Chi} {d β : ℝ} {Y : LinkArray G (Frozen A x F)} {z : Prices G (Active A x F)} {V : Config G c} {h : Kernel G c I J ρ}
variable {L}
lemma Binds.literal : L.Binds T k β q d Y z V (L.paper T k β q d Y z) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def axis {x : ℝ} (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (V : Config G c) (k : S.Choices) (q : Chi) (d β : ℝ) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) := meanLog A F T x V k q d Y + coupling β • z
def field {x : ℝ} (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (V : Config G c) (k : S.Choices) (q : Chi) (d β : ℝ) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) := physical A F V Y (tape (axis T F A V k q d β Y z))

variable [Fintype I] [Fintype J] [Fintype ρ]
lemma Binds.charts (he : L.Binds T k β q d Y z V h) (i : I) : h.stage (coupling β) V i = tape (axis T F A V k q d β Y z) (L.hot i) := by
  rw [Kernel.stage,he.mean,he.draw]; rfl
lemma Binds.same {X : Support f} (he : L.Binds T k β q d Y z V h) (hh : L.Includes X) :
    Agrees (inspected X) (h.atLinks S L.location (coupling β) V) (field T F A V k q d β Y z) := by
  intro i h₁ h₂
  by_cases hv : i∈F.trunks
  · have hQ : field T F A V k q d β Y z i=1 := F.on_tree _ ⟨i,hv⟩
    rw [hQ]; exact h.empty_link _ _ _ _ _ (fun ⟨j,hj⟩ => (L.both j).2 (show L.location.address j∈F.trunks from hj.symm ▸ hv))
  obtain ⟨j|j,hj⟩ := hh ⟨i,hv⟩ h₁ h₂
  · change L.both (.inl j)=⟨i,hv⟩ at hj
    rw [← show L.location.address (.inl j)=i from congr_arg Subtype.val hj,h.west_link]
    change _ = F.drape _ (L.hot j).val.val
    rw [F.off_tree]; unfold returned thaw; rw [freeze_regular,he.charts j]; rfl
  · rw [← show L.location.address (.inr j)=i from congr_arg Subtype.val hj,h.east_link]
    change _ = F.drape _ (L.cold j).val.val
    rw [F.off_tree]; unfold returned thaw; rw [freeze_held,he.holds]; rfl

lemma Binds.health {X : Support f} (he : L.Binds T k β q d Y z V h) (hh : L.Includes X) (t : ℝ) :
    Healthy t X (h.atLinks S L.location (coupling β) V) ↔ Healthy t X (field T F A V k q d β Y z) := by
  have hp := flags_agree t _ _ X (he.same hh)
  simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,hp]

-- Choose local activity list by the *actual* field. K selections always a subset of the same term's b.
variable (L)
structure Reads (R : Rep G f) (s o b : Finset ℕ) : Prop where
  portion : o ⊆ b
  E i (hi : i∈s) : L.Includes (R.activities.reg i).support
  K i (hi : i∈o) : L.Includes (R.activities.forced i).support

def lights (s : Finset ℕ) (R : Rep G f) (U : Config G f) := s.filter (fun i => Healthy R.p.threshold (R.activities.reg i).support U)

def surcharge (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) (Z : ChartRatio G) (β : ℝ) :=
    let Q := Rows.gram T x V k (shots S x) A F; let H := Native.kinetic T F k x;
    -(Fintype.card (Frozen A x F):ℝ)*Real.log (spare Z β) - (1/2)*(Real.log Q.det-Real.log H.det)+
      (1/2)*Real.log (1+(Q*fog A F T x V k-1)).det

def untouched (L : Leaf G A x F I J ρ) := Finset.univ \ (Finset.univ.map L.hot)

/-- Remainder still uses the same *full* covariance/mean for Fsct/Frco,
with the boundary charges (not `inverse_restrict = restrict_inverse` etc).
No quotients by activities, indicator functions, or partition functions. -/
def pending (T : Tube G S) (k : S.Choices) (V : Config G c) (Z : ChartRatio G) (q : Chi) (d : ℝ) (p : BudgetPoint)
    (D : Allocation G S x α) (R : Rep G f) (h : Kernel G c I J ρ) (s o b : Finset ℕ) (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) :=
  let U := field T F A V k q d R.beta Y z; let a := axis T F A V k q d R.beta Y z; let y := tape a
  let C := fog A F T x V k; let m := meanLog A F T x V k q d Y
  let rights := if R.activities.admissible R.p U b then ∏ i ∈ b \ o, R.activities.K i U else 0
  (∏ i ∈ L.untouched, extended q Z d (y i)) * (∏ i∈L.untouched, broad q d (y i)) * D.bill A k U V * S.likelihood U k * rights *
    Real.exp (-(averaged (fun s => reduced R (till x) (pull s 0 U))) - (R.activities.additive R.p U - ∑ i ∈ s, R.activities.regularOccurrence R.p i U) + coarseTail T x p V R.beta -
      R.beta * averaged (Rows.residual T x V k (shots S x) A F q d Y U a) +
      (Rows.adjustment T x V k (shots S x) A F q d Y C m (coupling R.beta) z - h.correction V) +
      (surcharge T x A F k V Z R.beta - h.ledger (spare Z R.beta) V))

variable {L}
lemma Binds.reserve {Z : ChartRatio G} (he : L.Binds T k β q d Y z V h) :
    reserve q Z d (tape (axis T F A V k q d β Y z)) = (∏ i∈L.untouched,extended q Z d (tape (axis T F A V k q d β Y z) i)) * Real.exp (h.chartLog q Z d (coupling β) V) := by
  let y := tape (axis T F A V k q d β Y z)
  have hx := Finset.prod_sdiff (f:=fun i => extended q Z d (y i)) (Finset.subset_univ (Finset.univ.map L.hot))
  rw [Finset.prod_map] at hx
  rw [Kernel.chartLog,Real.exp_sum]; simp_rw [he.charts]; exact hx.symm
lemma Binds.doors (he : L.Binds T k β q d Y z V h) :
    doors q d (tape (axis T F A V k q d β Y z)) = (∏ i∈L.untouched, broad q d (tape (axis T F A V k q d β Y z) i)) * doors q d (h.stage (coupling β) V) := by
  let y := tape (axis T F A V k q d β Y z)
  have hx := Finset.prod_sdiff (f:=fun i => broad q d (y i)) (Finset.subset_univ (Finset.univ.map L.hot))
  rw [Finset.prod_map] at hx; simp_rw [Next.SectorChange.doors, he.charts]; exact hx.symm

variable {R : Rep G f} {s o b : Finset ℕ} {δ w : ℝ}
lemma Binds.regular (he : L.Binds T k R.beta q d Y z V h) (hR : R.activities.Valid R.p δ w) (hs : Reads L R s o b) :
    let U := field T F A V k q d R.beta Y z
    ∑ i ∈ lights s R U, h.light S L.location R i V = ∑ i ∈ s, R.activities.regularOccurrence R.p i U := by
  intro U; unfold lights; rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun i hi => ?_
  unfold Activities.regularOccurrence; split
  next hp => rw [masked_eq _ _ _ _ hp]; exact (hR.regular.smooth i).sites _ _ (agrees_mono (he.same (hs.E i hi)) (by unfold inspected; exact fun x hx => Finset.mem_union_left _ hx))
  next hp => rw [masked_ne _ _ _ _ hp]
lemma Binds.forced (he : L.Binds T k R.beta q d Y z V h) (hR : R.activities.Valid R.p δ w) (hs : Reads L R s o b) :
    let U := field T F A V k q d R.beta Y z
    R.activities.gasOccurrence R.p b U = (if R.activities.admissible R.p U b then ∏ i∈ b \ o, R.activities.K i U else 0) * ∏ i∈o,h.heavy S L.location R i V := by
  intro U; unfold Activities.gasOccurrence; split
  next hp => refine (Finset.prod_sdiff hs.portion).symm.trans (congr_arg (_ * ·) ?_); exact Finset.prod_congr rfl fun i hi =>
    ((hR.forced.reads i).allReads _ _ _ _ _ (he.same (hs.K i hi))).symm
  rw [zero_mul]

set_option maxHeartbeats 450000 in
lemma price_one (Z : ChartRatio G) (p : BudgetPoint) (D : Allocation G S x α) (he : L.Binds T k R.beta q d Y z V h) (hR : R.activities.Valid R.p δ w) (hs : Reads L R s o b) :
    let U := field T F A V k q d R.beta Y z
    let a := axis T F A V k q d R.beta Y z; let y := tape a
    let cost := surcharge T x A F k V Z R.beta; let m := meanLog A F T x V k q d Y
    let v := reserve q Z d y * doors q d y * D.bill A k U V * S.likelihood U k
    let E := -(averaged (fun s => reduced R (till x) (pull s 0 U))) - R.activities.additive R.p U + coarseTail T x p V R.beta -
      R.beta * averaged (Rows.residual T x V k (shots S x) A F q d Y U a) +
      Rows.adjustment T x V k (shots S x) A F q d Y (fog A F T x V k) m (coupling R.beta) z
    L.pending T k V Z q d p D R h s o b Y z * h.multiplier S L.location R q Z d (lights s R U) o V =
      Real.exp cost * (v * R.activities.gasOccurrence R.p b U * Real.exp E) := by
  intro U a y cost m v E
  let P := (h.expense S L.location R q Z d (lights s R U) V)
  let rights := if R.activities.admissible R.p U b then ∏ i ∈ b \ o, R.activities.K i U else 0
  let T0 := (∏ i ∈ L.untouched, extended q Z d (y i)) * (∏ i∈L.untouched, broad q d (y i)) * D.bill A k U V * S.likelihood U k * rights
  have hf : L.pending T k V Z q d p D R h s o b Y z = T0 * Real.exp ((cost+h.chartLog q Z d (coupling R.beta) V+E)-P) := by
    unfold pending P; dsimp only; apply congr_arg (fun x => T0 * Real.exp x)
    unfold Kernel.expense; rw [he.regular hR hs]; unfold E cost; abel
  unfold v; rw [show reserve q Z d y = _ from he.reserve,show doors q d y = _ from he.doors, show R.activities.gasOccurrence R.p b U = _ from he.forced hR hs,hf]
  calc
    _ = (T0 * (doors q d (h.stage (coupling R.beta) V) * ∏ i ∈ o,h.heavy S L.location R i V)) *
        (Real.exp (cost+h.chartLog q Z d (coupling R.beta) V+E -P)*Real.exp P) := by unfold Kernel.multiplier P; ring
    _ = _ := by rw [← Real.exp_add, sub_add_cancel,Real.exp_add,Real.exp_add]; unfold T0; change (_ * _ * _ * _ * rights) * _ * _ = _*(_*_*(rights*_) * _); ring

/-- Pointwise split with all compulsory factors retained, even where density
vanishes or charts overlap. No positivity assumption on the incoming gas. -/
theorem priced_identity {s o : Finset ℕ → Finset ℕ} {h : Finset ℕ → Kernel G c I J ρ} (Z : ChartRatio G) (p : BudgetPoint) (D : Allocation G S x α)
    (he : ∀ b, L.Binds T k R.beta q d Y z V (h b)) (hR : R.activities.Valid R.p δ w) (hs : ∀ b, Reads L R (s b) (o b) b) :
    let U := field T F A V k q d R.beta Y z
    (∑' b, L.pending T k V Z q d p D R (h b) (s b) (o b) b Y z * (h b).multiplier S L.location R q Z d (lights (s b) R U) (o b) V) =
      Real.exp (surcharge T x A F k V Z R.beta) * sleeves T x V k A R (shots S x) F D q Z d p (fog A F T x V k) (meanLog A F T x V k q d) Y z := by
  intro U
  have hh := fun b => price_one Z p D (he b) hR (hs b)
  dsimp only at hh
  unfold sleeves; dsimp only
  unfold U; simp_rw [hh, tsum_mul_left,tsum_mul_right,tsum_mul_left]; rfl
end Leaf
end YM.AnalyticBridge.MarginalMultiplier3b1d
