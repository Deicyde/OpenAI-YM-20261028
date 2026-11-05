import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sector
import YM.Push.ABSOLUTE_SUMS.Packet

/-!
# Compulsory profile prices through the actual stencils

Complement h's away from these packets still another bill. No
multiplying a tag probability at each *use* or through a rotated
pullback. Use one factor per physical site and coarse bond, in this
case at all tested sites/bonds through the wide halo. At every use the
realized per-tag weights include the likelihood denominators; no
"summing over" an unrelated choice-list at a per-vertex test site.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Mask
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure  Oriented Channel Tags Animals Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} (A : Stores S)

/-- Charge all locations needed for any tests at d (projected), including both endpoints. -/
def readFine (X : Support c) (S : StepData c f) := univ.filter fun i => ¬Disjoint X (startPos S i)
def readBonds (X : Support c) := univ.filter fun i : Bond c => ¬Disjoint X (pinPos i)

def fine (χ : Chi) (p : Cell f) (t : ℝ) (U : Config G f) :=
    let h:=χ.innerShare (t/4) (toll U p)
    if p∈A.costs then 1-h else h

def noise (χ : Chi) (p : Bond c) (t W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
    let h:=χ.innerShare (W*t) (wire (S.prediction U k) V p)
    if p∈A.aisles then 1-h else h

def profiles (χ : Chi) (d : ℕ) (x W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
    let X:=A.dome d
    let t:=fiery G x S.patch.L
    (∏ p∈readFine X S,fine A χ p t U)*∏ p∈readBonds X,noise A χ p t W U k V

def tickets (d : ℕ) (U : Config G f) (k : S.Choices) :=
    let X:=A.dome d
    (∏ p∈X, siteMass U k p)*∏ b ∈ readBonds X,pinMass U k b

lemma fine_range (χ : Chi) (p : Cell f) (t : ℝ) (U : Config G f) :
    fine A χ p t U ∈ Set.Icc 0 1 := by
  have he : χ.innerShare (t/4) (toll U p)∈ Set.Icc 0 1 := χ.range _
  unfold fine; dsimp only
  split
  next h => exact ⟨sub_nonneg.mpr he.2,sub_le_self _ he.1⟩
  next => exact he

lemma noise_range (χ : Chi) (p : Bond c) (t W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    noise A χ p t W U k V ∈ Set.Icc 0 1 := by
  have he : χ.innerShare (W*t) (wire (S.prediction U k) V p)∈ Set.Icc 0 1 := χ.range _
  unfold noise; dsimp only
  split
  next h => exact ⟨sub_nonneg.mpr he.2,sub_le_self _ he.1⟩
  next => exact he

lemma profiles_range (χ : Chi) (d : ℕ) (x W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    profiles A χ d x W U k V∈Set.Icc 0 1 := by
  have hf := fun p => fine_range A χ p (fiery G x S.patch.L) U
  have hn := fun b => noise_range A χ b (fiery G x S.patch.L) W U k V
  exact ⟨mul_nonneg (prod_nonneg fun _ _ => (hf _).1) (prod_nonneg fun _ _ => (hn _).1),
    mul_le_one₀ (prod_le_one (fun _ _ => (hf _).1) (fun _ _ => (hf _).2))
      (prod_nonneg fun _ _ => (hn _).1) (prod_le_one (fun _ _ => (hn _).1) (fun _ _ => (hn _).2))⟩

lemma ticket_nonneg (d : ℕ) (U : Config G f) (k : S.Choices) : 0 ≤ tickets A d U k :=
  mul_nonneg (prod_nonneg fun _ _ => site_nn ..) (prod_nonneg fun _ _ => pin_nn ..)

/-- Incidence is enough here; other defaults need not hold globally. -/
lemma masks_wide (χ : Chi) (d : ℕ) (x W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c)
    (hW : 0<W) (hx : 0<fiery G x S.patch.L) (hm : profiles A χ d x W U k V ≠ 0) (hk : tickets A d U k ≠ 0)
    (he : ∀ i∈A.dome d,i∈A.flags ↔ i∈RG.flags (temp x) V) : Tags.Wide A d U k V x W := by
  have ht (p) (hf : p∈readFine (A.dome d) S) : fine A χ p (fiery G x S.patch.L) U ≠ 0 := fun h =>
    left_ne_zero_of_mul hm (Finset.prod_eq_zero hf h)
  have hu (b : Bond c) (hb : b∈readBonds (A.dome d)) : noise A χ b (fiery G x S.patch.L) W U k V ≠ 0 := fun h =>
    right_ne_zero_of_mul hm (Finset.prod_eq_zero hb h)
  refine ⟨?_,?_,?_,he⟩
  · intro i hi
    exact lt_of_le_of_ne (site_nn ..) fun h => left_ne_zero_of_mul hk (Finset.prod_eq_zero hi h.symm)
  · intro p hp
    have hh := ht p (mem_filter.mpr ⟨mem_univ _,hp⟩)
    unfold fine at hh; dsimp only at hh
    constructor
    · intro hA; rw [if_pos hA] at hh; exact (χ.exterior_gt _ _ (G.chord_nonneg _) (by positivity) hh).le
    intro hA; rw [if_neg hA] at hh; linarith [χ.chosen_lt _ _ (by positivity) hh]
  intro b hb
  have hh := hu b (mem_filter.mpr ⟨mem_univ _,hb⟩)
  unfold noise at hh; dsimp only at hh
  constructor
  · intro hA; rw [if_pos hA] at hh; exact (χ.exterior_gt _ _ (G.chord_nonneg _) (by positivity) hh).le
  intro hA; rw [if_neg hA] at hh; linarith [χ.chosen_lt _ _ (by positivity) hh]

/-- Use these counts even along nonconnected Stores, can charge the
canonical stores once with total volume of the *neighborhoods*. -/
lemma dome_count (d : ℕ) : (A.dome d).card ≤ A.shares * Animals.ballCost (d+1) := by
  let V:=seeds S A
  have he : d=d*1 := by simp
  calc
    _ ≤ ∑ v∈V, (skin S d 1 v).card := by
      nth_rw 1 [he]; rw [← Packets.support_reads S A]; exact Finset.card_biUnion_le
    _ ≤ ∑ _v∈V, Animals.ballCost (d+1) := by
      refine Finset.sum_le_sum fun i _ => ?_
      apply le_trans _ (neighbors_card (d+1) (anchor S i))
      refine card_le_card fun y hy => (neighbors_mem ..).mpr ?_
      simpa only [mul_one] using price_skin S d 1 i y hy
    _ = _ := by simp [V, seeds_card]

lemma readBonds_count (d : ℕ) :
    (readBonds (A.dome d)).card ≤ A.shares*Animals.ballCost (d+1+1)*Fintype.card Axis := by
  have ht : readBonds (A.dome d) ⊆ A.dome (d+1) ×ˢ univ := by
    intro b hb; have hh:= (mem_filter.mp hb).2
    obtain ⟨y,hy,hb⟩ := Finset.not_disjoint_iff.mp hh
    obtain ⟨w,hw,h⟩ := halo_spec.mp hy
    apply mem_product.mpr
    refine ⟨halo_spec.mpr ⟨w,hw,(separation_triangle _ y _).trans (add_le_add h ?_)⟩,mem_univ _⟩
    rw [separation_comm]; exact Packets.price_one S (.inr (.inl b)) y hb
  exact (card_le_card ht).trans (by rw [Finset.card_product,card_univ]; gcongr; exact dome_count A _)

def tollFee (p : Patch) (d : ℕ) : ℝ :=
    (Animals.ballCost (d+1):ℝ) * (Fintype.card p.FrameTag:ℝ) +
      (Animals.ballCost (d+1+1):ℝ) * (Fintype.card Axis:ℝ) * (Fintype.card p.Points:ℝ)

theorem tickets_le (d : ℕ) (U : Config G f) (k : S.Choices) :
    tickets A d U k ≤ Real.exp (tollFee S.patch d * A.shares) := by
  unfold tickets; dsimp only
  let a : ℝ := Fintype.card S.patch.FrameTag
  let b : ℝ := Fintype.card S.patch.Points
  have he (i : Site c) : siteMass U k i ≤ Real.exp a := (site_cap ..).trans (by
    change a ≤ _; linarith [Real.add_one_le_exp a])
  have hp (i : Bond c) : pinMass U k i ≤ Real.exp b := (pin_cap ..).trans (by
    change b ≤ _; linarith [Real.add_one_le_exp b])
  apply le_trans (mul_le_mul (prod_le_prod (fun i _ => site_nn ..) (fun i _ => he i))
    (prod_le_prod (fun i _ => pin_nn ..) (fun i _ => hp i))
    (prod_nonneg fun _ _ => pin_nn ..) (prod_nonneg fun _ _ => (Real.exp_pos _).le))
  rw [Finset.prod_const,Finset.prod_const,← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_monotone
  let r := Animals.ballCost (d+1)
  let r' := Animals.ballCost (d+1+1)
  have h : ((A.dome d).card:ℝ) ≤ A.shares*(r:ℝ) := by exact_mod_cast dome_count A d
  have hx : ((readBonds (A.dome d)).card:ℝ) ≤ A.shares*(r':ℝ)*Fintype.card Axis := by exact_mod_cast readBonds_count A d
  apply (add_le_add (mul_le_mul_of_nonneg_right h (by unfold a; positivity))
    (mul_le_mul_of_nonneg_right hx (by unfold b; positivity))).trans
  unfold r r' tollFee a b; exact le_of_eq (by ring)
end YM.ConnectedActivityE6.Mask
