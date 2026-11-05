import YM.Next.RANK.Alarm
import YM.Next.RANK.Beamers
import YM.Next.RANK.Stepped
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Arc.Audit
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds

/-!
# Cover cuts for one moment use

Always cut the actual cover Row, bounding even all its lifted
entries (no replacing by power cut on a periodic table). Base costs
in effective coarse-cell displacements; leave buffer on both sides
to buy orientation choices. API allows ANY cut keeping at least
base-radius cover costs to `leastHem` and going no further than
`lastHem` (always on ℓ¹ of coarse cell cover displacement; e.g.
can use with certain shifted thresholds with required inclusion).
Not claiming any such choice by itself commutes with canonical
orientation/translations on the stencil copies. Need pay/delay/test
that in any future preparation. We allow every one meeting these
explicit perturbation conditions. Must also retain paths. For symmetry
of the polynomial operation use only centered lifted cover rows.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut
open AnalyticBridge.LocalGaussianLaws Sweep Arc 
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Laurent Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local Work.F08
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

def leastHem (x : ℝ) := radiusB x / 10000
def lastHem (x : ℝ) := radiusB x / 8

/-- Predicate on the actual expression's Z-lifts (and types).
No weighting the omitted coordinates to align on a periodic tile. -/
structure ShapeCut (α β : Type*) (x : ℝ) where
  retain : α → β → Cover → Prop
  copay : ∀ i j z, Laurent.size z ≤ leastHem x → retain i j z
  spatial : ∀ i j z, retain i j z → Laurent.size z ≤ lastHem x

section cover
variable {α β I J : Type*} {x s M : ℝ}
def ShapeCut.draw (Y : ShapeCut α β x) (P : Row α β) : Row α β := (fun i j z => if Y.retain i j z then P i j z else 0 : Row α β)

lemma cut_bounds {P : Row α β} (h : P.strip s M) (hs : 0 ≤ s) (Y : ShapeCut α β x) :
    (Y.draw P).strip s M ∧ (minusRows P (Y.draw P)).strip 0 (Real.exp (-s * (leastHem x))*M) := by
  constructor
  · intro i j; unfold Width; apply budget_minor (h i j) (fun _ => by positivity)
    intro z; unfold ShapeCut.draw; split
    · exact le_rfl
    rw [norm_zero,mul_zero]; positivity
  intro i j
  have hb := strip_tail h (leastHem x) hs i j; rw [zero_sub] at hb
  unfold Width
  refine budget_minor hb (fun _ => by positivity) ?_
  intro z
  unfold minusRows FreeResolvent.shorten ShapeCut.draw
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  by_cases hx : Y.retain i j z
  · rw [if_pos hx, sub_self,norm_zero]; positivity
  rw [if_neg hx, if_neg (mt (Y.copay i j z) hx)]

variable [Fintype β]
def ticket (β : Type*) [Fintype β] (M : ℝ) := (Fintype.card β:ℝ)*M
lemma ticket_nonneg (β : Type*) [Fintype β] (hM : 0≤M) : 0≤ticket β M := mul_nonneg (Nat.cast_nonneg _) hM

def cheque (β : Type*) [Fintype β] (s M x : ℝ) := ticket β M * Real.exp (-s*(leastHem x))
lemma cheque_sign (β : Type*) [Fintype β] {M s x : ℝ} (hM : 0≤M) : 0≤cheque β s M x := mul_nonneg (ticket_nonneg _ hM) (Real.exp_pos _).le

lemma order_exp {P : Row α β} (h : P.strip s M) (hs : 0≤s) (Y : ShapeCut α β x) (n : Side) (i : Co n α) :
    (∑ j : Co n β, |(Y.draw P).acts n i j|) ≤ ticket β M ∧
      (∑ j : Co n β, |(P.acts n - (Y.draw P).acts n) i j|) ≤ cheque β s M x := by
  obtain ⟨he,hb⟩:= cut_bounds h hs Y
  have hA := physical_rows (strip_mono he hs le_rfl) le_rfl n |>.bound i -- strip 0
  have hP := physical_rows hb le_rfl n |>.bound i
  rw [acts_minus hs h he] at hP
  refine ⟨?_,?_⟩
  · simpa only [Cost.weight_zero,one_mul,ticket] using! hA
  simpa only [Cost.weight_zero,one_mul,cheque,ticket,mul_assoc,mul_comm M (Real.exp _)] using! hP

omit [Fintype β] in
lemma enough_room {P : Row α β} (Y : ShapeCut α β x) (n : Side) (i : Co n α) (j : Co n β)
    (hi : lastHem x < separation i.1 j.1) : (Y.draw P).acts n i j = 0 := by
  change (∑' z:Cover, if j.1=i.1+wrap n z then (Y.draw P) i.2 j.2 z else (0:ℝ)) = 0
  suffices he : ∀ z:Cover, (if j.1=i.1+wrap n z then (Y.draw P) i.2 j.2 z else (0:ℝ))=0 by simp_rw [he]; exact tsum_zero
  intro z; unfold ShapeCut.draw; split
  next h =>
    rw [if_neg]; intro hm
    have hh : separation i.1 (i.1 + wrap n z) ≤ lastHem x := by
      have ht: (native n).d i.1 (i.1+wrap n z) ≤ size z := (native_le_taxi ..).trans (wrap_bound ..)
      apply le_trans (show separation i.1 (i.1+wrap n z) ≤ size z from ?_) (Y.spatial _ _ _ hm)
      change ((separation _ _:ℕ):ℝ) ≤ _ at ht; exact_mod_cast ht
    rw [h] at hi; omega
  rfl
end cover

section symmetric
variable {α I : Type*} {P : Row α α}

def fixedPoint (P : Row α α) := scaleRows (2:ℝ)⁻¹ (plusRows P (transRows P))

lemma fixed_stencil (P : Row α α) : transRows (fixedPoint P)=fixedPoint P := by
  funext i j z; simp only [transRows,fixedPoint,scaleRows,plusRows,minusRows,neg_neg]; ring
lemma completeFixed {s M : ℝ} (h : P.strip s M) (hs : 0≤s) :
    (fixedPoint P).strip s M ∧ ∀ (n : Side) (E : I → Co n α),
      ((P.acts n).submatrix E E).IsSymm →
      ((fixedPoint P).acts n).submatrix E E=(P.acts n).submatrix E E := by
  obtain hp := strip_scale (strip_plus h (strip_trans h)) (2:ℝ)⁻¹
  refine ⟨?_,?_⟩
  · rwa [Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ)⁻¹), show (2:ℝ)⁻¹*(M+M)=M from by ring] at hp
  intro n E ht
  ext i j; unfold fixedPoint; rw [acts_scale, acts_plus h (strip_trans h) hs,acts_trans]
  have hx : (P.acts n) (E j) (E i)=(P.acts n) (E i) (E j) := (congr_fun (congr_fun ht i) j)
  simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul]
  rw [hx]; ring

-- Additional restriction for covariance cuts: can use any specific
-- orientation table paying this. For support updates over reoriented
-- W need stronger, not deduced here.
def swizzles {x : ℝ} (Y : ShapeCut α α x) := ∀ i j z,Y.retain i j z ↔ Y.retain j i (-z)
lemma ticketMatch (n : Side) (E : I → Co n α) {x : ℝ} {P : Row α α} (hP : transRows P=P) (Y : ShapeCut α α x) (h : swizzles Y) :
    (((Y.draw P).acts n).submatrix E E).IsSymm := by
  have he : transRows (Y.draw P) = Y.draw P := by
    funext i j z; have hx : P i j z=P j i (-z) := congr_arg (fun (P:Row α α)=> P i j z) hP.symm
    unfold ShapeCut.draw transRows; rw [h i j z,hx]
  unfold Matrix.IsSymm; rw [Matrix.transpose_submatrix, ← acts_trans, he] -- name?
end symmetric

-- Earnings before x: exp-tail affordable for planned cover data
lemma closure (a ε : ℝ) (ha : 0 < a) : ∀ᶠ x in atTop, Real.exp (-a*(leastHem x)) ≤ x^(-ε) := by
  filter_upwards [Extra.Iteration.Scales.first (a/20000) ε (by positivity), Work.E01.radiusB_tendsto.eventually_ge_atTop 20000] with x hx hy
  apply le_trans _ hx; apply Real.exp_monotone
  have he : (radiusB x:ℝ) ≤ 20000 * (leastHem x:ℝ) := by unfold leastHem; exact_mod_cast (by omega : radiusB x ≤ 20000 * (radiusB x / 10000))
  nlinarith only [mul_le_mul_of_nonneg_left he ha.le]
lemma currency (β : Type*) [Fintype β] (s M ε : ℝ) (hs : 0<s) (_hm : 0≤M) :
    ∀ᶠ x in atTop,cheque β s M x ≤ x^(-ε) := by
  let D:= ticket β M
  filter_upwards [closure s (ε+1) hs,eventually_gt_atTop (max 0 D)] with x ht hx
  have he : 0<x := (le_max_left ..).trans_lt hx
  have hb : D ≤ x := (le_max_right ..).trans hx.le
  unfold cheque
  exact (mul_le_mul hb ht (Real.exp_pos _).le he.le).trans_eq (by nth_rw 1 [← Real.rpow_one x]; rw [← Real.rpow_add he]; ring_nf)
end YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut
