import YM.Branch.Center
import YM.RG.History



/-!
# Per-site budgets from the actual represented data

E eq:mCr (11827+). Distinguish queries in pulled U across actual oriented channels
and treat `kept` selectors BEFORE wrapping averaging. Uses exact footprint masks.
No absorbing fixed-L in here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG
open Lattice Wilson MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius ENNReal BigOperators

variable {n : Side} {G : Gauge}

/-! A deliberately weaker global budget only for extensive estimates, never
used to transfer the family back to hit bounds. -/
theorem sumRoot {a : ℕ → Support n} (ha : ∀ i, (a i).Nonempty)
    {b : ℕ → ℝ} {p : BudgetPoint} {w : ℝ} (hb : ∀ i, 0 ≤ b i)
    (hB : ∀ x : Site n, SumBudget (fun i => if x ∈ a i then p.mass (a i) (b i) else 0) w) :
    (∑' i,b i) ≤ Fintype.card (Site n)*w := by
  let q (x : Site n) i := if x ∈ a i then p.mass (a i) (b i) else 0
  have h (x : Site n) : SumBudget (q x) w := hB x
  calc
    _ ≤ ∑' i, ∑ j, q j i := (Activities.summable_charge ha hb hB).tsum_le_tsum (fun i ↦ by
      obtain ⟨x,hx⟩ := ha i
      have hg : b i ≤ q x i := by unfold q; rw [if_pos hx]; exact p.loMass _ _ (hb i)
      exact hg.trans <| Finset.single_le_sum (fun j _ => (h j).1 i) (Finset.mem_univ _)) (summable_sum (fun i _ => (h i).2.1))
    _ = _ := Summable.tsum_finsetSum (fun i _ => (h i).2.1)
    _ ≤ ∑ _ : Site n,w := Finset.sum_le_sum fun _ _ ↦ (h _).2.2
    _ = _ := by simp

lemma volumeE (a : Activities G n) {δ w} {p : BudgetPoint} (H : a.Valid p δ w) (U : Config G n) :
    |a.additive p U| ≤ Fintype.card (Site n)*δ := by
  let E := fun i => a.regularOccurrence p i U
  have he := (Activities.ESeries H).absolute U
  obtain ⟨b,hb,h⟩ := H.boundE
  let P (x : Site n) i := if (a.reg i).site=x then p.mass (a.reg i).support (b i) else 0
  have hs : ∀ i, Summable (P i) := fun i => (h i).2.1
  calc
    _ ≤ ∑' i, ‖E i‖ := norm_tsum_le_tsum_norm he
    _ ≤ ∑' i, ∑ j, P j i := by
      refine he.tsum_le_tsum ?_ (summable_sum fun i _ ↦ hs i); intro i
      simp only [P,Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      refine le_trans ?_ (p.loMass _ _ (hb i).1)
      by_cases hh : Healthy p.threshold (a.reg i).support U
      · simp only [Activities.regularOccurrence,masked_eq _ _ _ _ hh]; exact (hb i).2 _ hh [] (Nat.zero_le _) (by simp)
      simp only [Activities.regularOccurrence,masked_ne _ _ _ _ hh,norm_zero]; exact (hb i).1
    _ = _ := Summable.tsum_finsetSum (fun i _ => hs i)
    _ ≤ ∑ _ : Site n,δ := Finset.sum_le_sum fun _ _ ↦ (h _).2.2
    _ = _ := by simp

/-- absolute atom on a healthy stencil costs a full threshold on each leg -/
lemma healthy_leg {k : ℕ} (a : Atom G k) (x : Site n) (U : Config G n) (t : ℝ)
    (h : Healthy t (a.footprint x) U) (i) : ‖(a.leg i).atSite U x‖ ≤ t := by
  let S := a.leg i
  have he : faceValue (expandAt x U) (S.offset,S.plaq) = faceValue U (wrap n S.offset+x,S.plaq) := travel_at ..
  have hp : S.offset∈S.stencil := Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_cons_self))
  have hq : wrap n S.offset+x∈a.footprint x := Finset.mem_image.mpr ⟨_, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩),rfl⟩
  change ‖S.eval (expandAt x U)‖ ≤ t
  rw [Slot.eval,G.norm_adjoint]
  apply (G.curvature_norm _).trans; rw [he]
  by_contra! hh; exact Finset.disjoint_left.mp h hq ((flags_spec ..).mpr ⟨_, List.mem_toFinset.mpr (List.mem_cons_self),hh⟩)

lemma healthy_atom {k : ℕ} (a : Atom G k) (p : BudgetPoint) (U : Config G n) x :
    |a.placed p U x| ≤ a.magnitude*p.threshold^k := by
  by_cases h : Healthy p.threshold (a.footprint x) U
  · have hh i j : |(a.leg i).atSite U x j| ≤ p.threshold := calc
      _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) ((a.leg i).atSite U x)| := by simp only [EuclideanSpace.basisFun_inner]
      _ ≤ _ := (abs_real_inner_le_norm _ _).trans <| by rw [OrthonormalBasis.norm_eq_one,one_mul]; exact healthy_leg a _ _ _ h i
    unfold Atom.placed; rw [masked_eq _ _ _ _ h]
    unfold Atom.unmasked Atom.poly Atom.magnitude
    rw [Finset.sum_mul]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    convert Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hh j (i j)) using 1
    simp
  unfold Atom.placed; rw [masked_ne _ _ _ _ h]; unfold Atom.magnitude; simp only [abs_zero]
  have := p.threshold_pos
  positivity

lemma atomVolume {k : ℕ} (a : ℕ → Atom G k) (p : BudgetPoint) {σ B : ℝ} (U : Config G n) x
    (hh : 0<σ) (hb : SumBudget (fun i ↦ (a i).budget σ) B) :
    |PathData.atomSeries a p U x| ≤ B*p.threshold^k := by
  have he := hb.2.1
  have h := hb.2.2
  calc
    _ ≤ ∑' i, |(a i).placed p U x| := norm_tsum_le_tsum_norm ((PathData.atom_dominated a p x hh hb).absolute _)
    _ ≤ ∑' i,(a i).budget σ*p.threshold^k := by
      refine ((PathData.atom_dominated a p x hh hb).absolute _).tsum_le_tsum
        (fun i => (healthy_atom (a i) p U x).trans ?_) (he.mul_right _)
      exact mul_le_mul_of_nonneg_right (Atom.lower_budget _ _ hh) (pow_nonneg p.threshold_pos.le _)
    _ ≤ _ := by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h (pow_nonneg p.threshold_pos.le _)

def PathData.loopsPrice (p : BudgetPoint) (β C Λ : ℝ) := β*(C*p.threshold^3+C*p.threshold^4)+ Λ*p.threshold^2

lemma PathData.volume_price (R : PathData G) (C : Clip) (p : BudgetPoint) (β : ℝ) (hb : 0 ≤ β) (U : Config G n)
    {σ A Λ : ℝ} (h : R.Bounds C σ A Λ) :
    |R.principal C p β U-β * ∑ x,R.baseTerm C p U x| ≤ Fintype.card (Site n)*PathData.loopsPrice p β A Λ := by
  have hk (x : Site n) : |atomSeries R.cubic p U x+atomSeries R.quartic p U x| ≤ A*p.threshold^3+A*p.threshold^4 :=
    (abs_add_le _ _).trans <| add_le_add (atomVolume _ _ _ _ h.width h.three) (atomVolume _ _ _ _ h.width h.four)
  unfold principal; rw [mul_add,add_assoc, add_sub_cancel_left]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul, abs_of_nonneg hb]
  have H := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum fun i _ => hk i)
  have hh := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum fun i _ => atomVolume R.loop p U i h.width h.two)
  apply (add_le_add (mul_le_mul_of_nonneg_left H hb) hh).trans_eq
  unfold loopsPrice; simp; ring

lemma PathData.base_nonneg (R : PathData G) (C : Clip) (p : BudgetPoint) (U : Config G n) x :
    0 ≤ R.baseTerm C p U x := by
  have h := C.quadratic_pos; have he := C.tail_pos; have hg := p.threshold_pos
  have ht := G.chord_nonneg (faceValue U x)
  unfold baseTerm clipped; split <;> split <;> positivity

lemma PathData.whole (R : PathData G) (C : Clip) (p : BudgetPoint) (β : ℝ) (hb : 0 ≤ β) (U : Config G n)
    {σ A Λ : ℝ} (h : R.Bounds C σ A Λ) :
    -(Fintype.card (Site n)*PathData.loopsPrice p β A Λ) ≤ R.inChannels C p β U := by
  change _ ≤ Branch.avg _
  apply (Branch.avg_const (n:=Signed) _).symm.le.trans (Branch.avg_mono fun i => ?_)
  let V := pull i 0 U
  have H := (abs_le.mp (R.volume_price C p β hb V h)).1
  change _ ≤ R.principal C p β V
  linarith [mul_nonneg hb (Finset.sum_nonneg (fun x (_ : x∈Finset.univ) => R.base_nonneg C p V x))]
end YM.RG
