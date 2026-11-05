import YM.Push.LOCAL_SPLITTING.Raw

/-!
# Pre-side income estimates for Raw conversion

Use a fixed exponent reserve for the forced meetings. No derivative, anchor,
or period dependence in the constants beyond displayed finite parameters.
These inequalities do not supply the input mass estimate on a one-step raw
expansion. The calendar numerical delay conditions are genuine qualifications.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

def atomRadius (T : SectionData F) : ℕ := T.stencil.sup fun x => Finset.univ.sup fun i => (x i).natAbs
def atomTiles (T : SectionData F) : ℕ := (atomRadius T + atomRadius T + 1)^4

theorem atomTiles_price (T : SectionData F) (B : BudgetPoint) (o : Site n) : coverNumber B.B (T.footprint o) ≤ atomTiles T := by
  apply le_trans (Corona.cover_mono _ B.B) (Corona.tile o (atomRadius T) B.B B.B_pos)
  intro x hx; obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx; apply halo_spec.mpr
  refine ⟨o,Finset.mem_singleton_self _,?_⟩
  rw [separation_comm,separation,add_sub_cancel_right]; apply Finset.sup_le; intro i _
  exact (Corona.lap r i).trans ((show (r i).natAbs ≤ atomRadius T from
    (Finset.le_sup (f:=fun j => (r j).natAbs) (Finset.mem_univ i)).trans (Finset.le_sup (f:=fun v : Cover => Finset.univ.sup fun j => (v j).natAbs) hr)).trans (Nat.le_mul_of_pos_right _ B.B_pos))

def reservedMass (B : BudgetPoint) (X : Support n) (a : ℝ) := Real.exp ((B.supportExponent+2)*coverNumber B.B X) * a

def factor (A : Hol G) (T : SectionData F) (u w : ℝ) := Real.exp ((u+2)*atomTiles T) * atomPrice A F w

def hitWidth (B : BudgetPoint) : ℝ := ((B.B+B.B+1)^4 : ℕ)

theorem width_one_le (B : BudgetPoint) : 1 ≤ hitWidth B := by unfold hitWidth; exact_mod_cast (show 1 ≤ (B.B+B.B+1)^4 from Nat.one_le_pow _ _ (by omega))

theorem exp_gain (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at he; linarith

theorem price_meeting {B : BudgetPoint} {a v : ℝ} (hp : 0 ≤ v) (h : hitWidth B * v ≤ 1) (ha : 0 ≤ a) (X : Support n) :
    mergePrice B v X a ≤ hitWidth B * v * reservedMass B X a := by
  let D := (coverNumber B.B X : ℝ)
  let q := hitWidth B * v
  have hq : 0 ≤ q := mul_nonneg (zero_le_one.trans (width_one_le _)) hp
  have he : (X.card:ℝ) * v ≤ D*q := by rw [show D*q=D*hitWidth B*v from (mul_assoc ..).symm]; exact mul_le_mul_of_nonneg_right (by unfold D hitWidth; exact_mod_cast Corona.pays X B.B) hp
  have ht : (X.card:ℝ) * v ≤ D := he.trans (mul_le_of_le_one_right (by positivity) h)
  have hy : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  unfold mergePrice BudgetPoint.mass reservedMass
  apply le_trans (mul_le_mul_of_nonneg_left (exp_gain _) (by positivity))
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (he.trans (mul_le_mul_of_nonneg_right hy hq)) (Real.exp_le_exp.mpr ht) (by positivity) (by positivity : 0 ≤ Real.exp D*q)) (by positivity))
  rw [add_mul,show (2:ℝ)*↑(coverNumber B.B X) = D+D from (two_mul _), Real.exp_add,Real.exp_add]; dsimp only [q]; ring_nf; exact le_rfl

theorem price_join {X : Support n} (T : SectionData F) (A : Hol G) (o : Site n) {B : BudgetPoint} {a w : ℝ}
    (hx : o∈ X) (ht : T.Sound A) (hw : 0 ≤ w) (ha : 0 ≤ a) :
    reservedMass B (joint T o X) (atomPrice A F w * a) ≤ factor A T B.supportExponent w * reservedMass B X a := by
  have ho : o ∈ T.footprint o := Finset.mem_image.mpr ⟨0,ht.anchored,by simp⟩
  have he : (coverNumber B.B (joint T o X):ℝ) ≤ ↑(coverNumber B.B X)+(atomTiles T:ℝ) := by
    exact_mod_cast (Corona.meets_sum hx ho B.B).trans (Nat.add_le_add_left (atomTiles_price ..) _)
  have hc := atomPrice_ge_one A F hw
  apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he (by positivity [B.exponent_pos] : 0 ≤ B.supportExponent+2))) (show 0 ≤ atomPrice A F w * a from by positivity))
  unfold factor reservedMass; rw [mul_add,Real.exp_add]; exact le_of_eq (by ring)

/-- Stage-order income priced at the old bulk supports with +2 reserve and
one simple width delay. `b` is the raw forced bill (before the new merges),
also on the actual labels. This theorem proves conversion costs, not the
one-step RG bound supplying `a,b,e`.
-/
theorem income_of_reserved {R : Rep G n} {M : Raw F n} {A : Hol G} {T : SectionData F} {X : ℕ → Support n} {o : Site n} {a b v w paid : ℝ} {e : ℕ → ℝ}
    (ht : T.Sound A) (hX : ∀ i,o ∈ X i) (he : M.cost o X R.p e)
    (h : SumBudget (fun i => reservedMass R.p (X i) (e i)) a) (hF : ForceCost R.p R.activities M.forced (Real.sqrt v*b))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ v) (hw : 0 ≤ w) (hv : hitWidth R.p * Real.sqrt v ≤ 1)
    (hcharge : 2*factor A T R.p.supportExponent w*a + b ≤ paid) : Raw.Income M o X A T R w v (Real.sqrt v) paid := by
  let C := factor A T R.p.supportExponent w
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (atomPrice_ge_one _ _ hw))
  have hs := sumBudget_mul_left h hC
  have hκ : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hκ' : Real.sqrt v ≤ 1 := (le_mul_of_one_le_left hκ (width_one_le _)).trans hv
  have hgain : hitWidth R.p*v ≤ Real.sqrt v := by nth_rw 1 [← Real.mul_self_sqrt hp, ← mul_assoc]; exact mul_le_of_le_one_left hκ hv
  have hy i := price_join T A o (B:=R.p) (hX i) ht hw (he i).1
  have ht i : 0 ≤ atomPrice A F w * e i := mul_nonneg (zero_le_one.trans (atomPrice_ge_one _ _ hw)) (he i).1
  refine ⟨C*a,b,C*a,mul_nonneg hC ha,hb,mul_nonneg hC ha, by linarith, ⟨e,he, sumBudget_mono hs (fun i => (ht i).trans (R.p.loMass _ _ (ht i))) (fun i => ?_) le_rfl, sumBudget_mono (sumBudget_mul_left hs hκ) (fun i => mergePrice_nonneg _ _ hp (ht i)) (fun i => ?_) le_rfl⟩,hF⟩
  · refine le_trans ?_ (hy i)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (ht i)
  exact (price_meeting hp (hgain.trans hκ') (ht i) _).trans (mul_le_mul hgain (hy i) (mul_nonneg (Real.exp_pos _).le (ht i)) hκ)
end YM.Push.Local
