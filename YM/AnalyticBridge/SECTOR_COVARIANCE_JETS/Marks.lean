import YM.Push.FREE_RESOLVENT.Layout
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Tier



set_option warningAsError false

/-!
# Counted slots and actual dependence in V

Marks as in TestD (FREE_RESOLVENT). Price even composite stencils from their
actual support, *including every external derivative position*. Anchor at
initial-site, scaled parent metric: bounded shift from other orientations, not
used to change the window criterion itself. No derivative of the data record.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
  Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Next.Fluctuations
  Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows
  Next.SectorChange.Wisps Next.SectorChange.Tier FreeResolvent.Mark FreeResolvent.TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

/-- Atom coordinates, includes color components even on copies. -/
abbrev Atom (G : Gauge) (c : Side) := Bond c × G.ColorIndex
abbrev atom (i : Atom G c) : Directions G c := axisPrice i
abbrev hearth (i : Atom G c) : Site c := i.1.1
abbrev meterMark (G : Gauge) (c : Side) (d : ℝ) := positions (FreeResolvent.native c) (hearth (c:=c) (G:=G)) d

lemma atom_small (i : Atom G c) : ‖atom i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j
  rw [show atom i = _ from on_axis i]; by_cases h : j=i.1
  · rw [h, Pi.single_eq_same, OrthonormalBasis.norm_eq_one]
  rw [Pi.single_eq_of_ne h,norm_zero]; exact zero_le_one

/-- Each active unit direction in the row construction becomes the same fine
atom in the full bond array (not a root-norm-rescaled direction). -/
lemma fresh_atom (W : Stencils S) (A : Stores S) (F : Forest S.ratio) (j : In (G:=G) x A F) :
    fresh x W A F (axisPrice j) = atom (c:=f) (G:=G) (j.1.val.val,j.2) := by
  funext e; unfold fresh atom
  rw [on_axis,on_axis]
  by_cases h : e=j.1.val.val
  · subst e; rw [dif_pos j.1.val.property, dif_pos j.1.property, Pi.single_eq_same]; rw [Pi.single_eq_same]
  rw [Pi.single_eq_of_ne h]
  split <;> rename_i he
  · split
    next hz =>
      have hu : (⟨⟨e,he⟩,hz⟩:Active A x F) ≠ j.1 := fun hv => h (congr_arg (fun i : Active A x F => i.val.val) hv)
      rw [Pi.single_eq_of_ne hu]
    rfl
  rfl

-- conservative predicate exact on all V arrays
abbrev Peers {E : Type*} (o : Site c) (r : ℕ) (a b : Bond c → E) :=
  ∀ i : Bond c, separation o i.1 ≤ r → a i=b i

def Housed {E H : Type*} (o : Site c) (r : ℕ) (f : (Bond c → E) → H) := ∀ a b, Peers o r a b → f a=f b

def enclosure (G : Gauge) (o : Site c) (r : ℕ) : Directions G c →L[ℝ] Directions G c :=
  (LinearMap.pi fun i => if separation o i.1 ≤ r then (LinearMap.proj i : Directions G c →ₗ[ℝ] G.Color) else 0).toContinuousLinearMap

lemma enclosure_here (o : Site c) (r : ℕ) (B : Directions G c) : Peers o r B (enclosure G o r B) := by
  intro i he; unfold enclosure; change _=(if separation o i.1 ≤ r then (LinearMap.proj i : Directions G c →ₗ[ℝ] G.Color) else 0) B
  rw [if_pos he]; rfl

lemma enclosure_away (o : Site c) (r : ℕ) {i : Atom G c} (h : ¬separation o (hearth i) ≤ r) :
    enclosure G o r (atom i)=0 := by
  funext u; change (if separation o u.1 ≤ r then (LinearMap.proj u : Directions G c →ₗ[ℝ] G.Color) else 0) (atom i)=0
  split
  next he =>
    change atom _ u=_; unfold atom; rw [on_axis]
    have hx : u ≠ i.1 := fun hv => h (show separation o i.1.1 ≤ r from hv ▸ he)
    rw [Pi.single_eq_of_ne hx]
  rfl

lemma jet_home {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {o : Site c} {r : ℕ}
    {F : Directions G c → E} (h : Housed (E:=G.Color) o r F) (l : List (Atom G c))
    {B : Directions G c} (he : ContDiffAt ℝ l.length F B) (hf : jet atom F l B ≠ 0) :
    ∀ i ∈ l, separation o (hearth i) ≤ r := by
  let Q y := F (B+y)
  let L := enclosure G o r
  have hv : ContDiffAt ℝ l.length Q 0 := by
    apply ContDiffAt.comp (f:=fun y => B+y) 0 (by simpa using he) (contDiffAt_const.add contDiffAt_id)
  have hk : Q ∘ L = Q := by
    funext u; change F _=F _
    exact (h _ _ fun i hi => congr_arg (fun z => B i + z) (enclosure_here o r u i hi)).symm
  intro i hi
  by_contra ha
  apply hf
  unfold jet
  have hh : iteratedFDeriv ℝ l.length Q 0 = iteratedFDeriv ℝ l.length F B := by
    simp only [Q,iteratedFDeriv_comp_add_left,add_zero]
  rw [← hh]
  have hx := Next.Foundations.jets_linear L hv
  rw [show iteratedFDeriv ℝ l.length Q 0 = _ from (hk ▸ hx)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  obtain ⟨z,hz⟩ := List.mem_iff_get.mp hi
  apply ContinuousMultilinearMap.map_coord_zero (i:=z)
  change L (atom (l.get z))=0; rw [hz]; exact enclosure_away _ _ ha

lemma volume_in (σ : ℝ) (hσ : 0<σ) (G : Gauge) (A : Stores S) (F : Forest S.ratio) (x : ℝ) :
    (FreeResolvent.native c).Volume (front (G:=G) A F (x:=x)) σ (keyFee S G σ) := ⟨front_price σ hσ A F G⟩
lemma volume_downwards (σ : ℝ) (hσ : 0<σ) (S : StepData c f) (G : Gauge) :
    (FreeResolvent.native c).Volume (down (G:=G) S) σ (slotFee S G σ) := ⟨down_price σ hσ S G⟩
def sparkCount (G : Gauge) (σ : ℝ) := ((Fintype.card G.ColorIndex:ℝ)*Fintype.card Axis)*wealth σ
lemma spark_nn (G : Gauge) (σ : ℝ) : 0 ≤ sparkCount G σ := mul_nonneg (by positivity) (wealth_nn σ)
lemma volume_atom (σ : ℝ) (hσ : 0<σ) (c : Side) (G : Gauge) :
    (FreeResolvent.native c).Volume (hearth (c:=c) (G:=G)) σ (sparkCount G σ) := by
  constructor; intro o
  let u y := rate (-σ) (separation o y)
  change (∑ i : (Site c × Axis) × G.ColorIndex, u i.1.1) ≤ _
  rw [Fintype.sum_prod_type]
  calc
    _ = ((Fintype.card G.ColorIndex:ℝ)*Fintype.card Axis) * ∑ i : Site c, u i := by
      simp [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc, mul_left_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by unfold u; simp_rw [separation_comm o]; exact land hσ _) (by positivity)

-- monotone in mark size, no requirement >0 in proof
lemma cheaper (o : Site c) (l : List (Atom G c)) {δ d : ℝ} (h : δ≤d) :
    (meterMark G c δ).pay l o ≤ (meterMark G c d).pay l o := by
  induction l with
  | nil => exact le_rfl
  | cons t l ht => exact mul_le_mul ((FreeResolvent.native c).weight_mono h ..) ht (pay_pos ..).le ((FreeResolvent.native c).weight_nn ..)

/-- Local-support price from the whole jet positions. Used *per path*,
before collapsing with row's true-length budget. Both endpoints. -/
lemma local_fare {o y : Site c} (l : List (Atom G c)) {r n : ℕ} {p q δ : ℝ}
    (h : p ≤ q) (hp : 0 ≤ p) (hδ : 0 ≤ δ) (hl : l.length ≤ n)
    (hs : p ≠ 0 → separation o y ≤ r ∧ ∀ i∈l, separation o (hearth i) ≤ r) :
    let C := meterMark G c δ
    let H := Real.exp ((1+2*n)*δ*r) * q
    C.pay l o * ((FreeResolvent.native c).weight δ o y*p) ≤ H ∧
    C.pay l y * ((FreeResolvent.native c).weight δ y o*p) ≤ H := by
  intro C H
  by_cases he : p=0
  · have h : 0 ≤ H := mul_nonneg (Real.exp_pos _).le (hp.trans h)
    simp only [he,mul_zero,h,and_self]
  let D := FreeResolvent.native c
  obtain ⟨hv,ht⟩ := hs he
  have hf : D.d o y ≤ r := by change ((separation o y):ℝ) ≤ _; exact_mod_cast hv
  have hk (z : Site c) (hz : D.d z o ≤ r) : C.pay l z * (D.weight δ o y * p) ≤ H := by
    have ha (i : Atom G c) (h : i∈l) : D.d z (hearth i) ≤ 2*r := by
      apply (D.triangle z o _).trans
      have he : D.d o (hearth i) ≤ r := by change ((separation ..):ℝ) ≤ _; exact_mod_cast ht i h
      linarith
    have hu : 0 ≤ q := hp.trans h
    apply le_trans (mul_le_mul (FreeResolvent.Affine.plumb D z hearth l hδ _ ha)
      (mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left hf hδ)) h hp (Real.exp_pos _).le)
      (mul_nonneg (D.weight_nn ..) hp) (Real.exp_pos _).le)
    rw [← mul_assoc, ← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ hu
    apply Real.exp_monotone
    have hi : (l.length:ℝ) ≤ n := by exact_mod_cast hl
    nlinarith only [mul_le_mul_of_nonneg_right hi (show 0 ≤ δ*r from mul_nonneg hδ (Nat.cast_nonneg _))]
  constructor
  · exact hk o (by rw [FreeResolvent.Cost.self]; positivity)
  rw [FreeResolvent.Cost.weight_symm]; exact hk y ((D.comm ..).trans_le hf)
end YM.AnalyticBridge.Covariance
