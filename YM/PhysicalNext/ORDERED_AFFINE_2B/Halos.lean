import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.Further.CURVED_GAUSSIAN_JETS.WeightsD
import YM.Further.CURVED_GAUSSIAN_JETS.Zones
import YM.Next.MAXWELL.Silt
import YM.PhysicalNext.ORDERED_AFFINE_2B.Padding



/-!
# Support prices for the scalar and linear letters

In E Frco, at its own coefficient anchor. Even determining the
zeroth-order subtraction or eta at a matched field retains full
read sets/actual Y; charge all and each V slot. `Support` is the project's
connected B-cover convention, in the OUTPUT lattice. Constants may depend
on L but payments never on the period (nor tree/tags), even after this
per-position hit aggregation. Not buying the multiplier expansion! In
particular affine scalar costs below are NOT exponentially suppressed; one
needs other e.g. no-hole analysis/energy. `debit` has a useful sign only
in value; no exponential of it in this subledger. Keep the exact polynomial
and t/g scales with real g, band here is β actual on the SC step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Halos
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.SectorAffine AnalyticBridge.Covariance
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps
open Push.SectorMeasure Matrix Footprint Fixed
open Push.Uniform (Multiplicity)
open Further Further.CurvedGaussianJets.Tracks
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ}
    {V : Config G c} {A : Stores S} {F : Forest S.ratio} {k : S.Choices} {T : Tube G S}
    {q : Chi} {d ε M s σ : ℝ} {n P : ℕ} {o : Site c} {l : List (Directions G c)}
    {Y : LinkArray G (Frozen A x F)}

section counts
variable {ι : Type} [Fintype ι] {a : ι → Site c}

lemma inverse_count (h : (FreeResolvent.native c).Volume a 1 M) : Multiplicity a ⌈M⌉₊ := by
  intro o; have he := (h.bound o).trans (Nat.le_ceil M)
  let L := (Finset.univ.filter (fun i:ι=>a i=o))
  let D := FreeResolvent.native c
  have hi : (L.card:ℝ) ≤ (⌈M⌉₊:ℝ) := calc
    _ = ∑ i ∈ L, D.weight (-1) o (a i) := by
      rw [Finset.sum_congr rfl (g:=fun _=>1) ?_]; simp
      intro i hi; rw [show a i=o from (Finset.mem_filter.mp hi).2]; simp [FreeResolvent.Cost.weight, D, FreeResolvent.native]
    _ ≤ ∑ i, D.weight (-1) o (a i) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>D.weight_nn ..)
    _ ≤ _ := he
  exact_mod_cast hi

def useBox {ι : Type} (p : ι → Site c) (B : ℕ) (i : ι) := halo (12*B) {p i}

def issue (p : ι → Site c) (B : ℕ) (σ E : ℝ) (o : Site c) := ∑ i, if o ∈ useBox p B i then Real.exp (σ * coverNumber B (useBox p B i)) * E else 0

def flatTax (σ : ℝ) (u B : ℕ) : ℝ := (((12*B+12*B+1)^4*u:ℕ):ℝ)*Real.exp (σ*((25:ℝ)^4))

lemma invoice (o : Site c) {E σ : ℝ} (hE : 0≤E) (hs : 0≤σ) {u B : ℕ} (h : Multiplicity a u) (hb : 0<B) :
    issue a B σ E o ≤ flatTax σ u B*E := by
  let D := disk a o (12*B)
  unfold issue flatTax
  rw [← Finset.sum_filter,show (Finset.univ.filter _ : Finset ι)=D from ?hd,mul_assoc]
  rotate_left
  · ext i; simp [D,disk,useBox,halo_spec]
  refine (Finset.sum_le_sum (g:=fun _=> Real.exp (σ*(25:ℝ)^4) * E) ?_).trans ?_
  · intro i _; refine mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ hs)) hE
    exact_mod_cast Corona.tile (a i) 12 B hb
  rw [Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.exp_pos _).le hE)
  exact_mod_cast size_disk o (12*B) h

-- multiplicity even on the larger key universe without active reindex
def moves (G : Gauge) (L : Side) := (L.val+L.val+1)^4 * (Fintype.card Axis * Fintype.card G.ColorIndex)
lemma allowed (G : Gauge) (S : StepData c f) : Multiplicity (Terrain.home S (G:=G)) (moves G S.patch.L) := by
  apply CurvedGaussianJets.Tracks.projection_count (a:=fun i : Covariance.Atom G f => i.1.1) S.ratio
  intro o
  rw [← Fintype.card_prod, ← Finset.card_univ]
  let f (i : Covariance.Atom G f) : Axis × G.ColorIndex := (i.1.2,i.2)
  refine Finset.card_le_card_of_injOn f (fun _ _=> Finset.mem_univ _) fun i hi j hj hv=> ?_
  have he : i.1.1 = j.1.1 := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  exact Prod.ext (Prod.ext he (congr_arg Prod.fst hv)) (show (f i).2=(f j).2 from congr_arg Prod.snd hv)
end counts

/-- E `p` at the fine hatted scale. -/
def overhead (G : Gauge) (L : Side) (x : ℝ) := Real.exp ((Real.log (Real.log (betaF G x L)))^2)



def cap (G : Gauge) (n P : ℕ) (d : ℝ) := 1 + ∑ i ∈ Finset.range (n+1), |sumCost G (SelectedOrderedKernels.narrow n d) P i|
lemma cap_pos (G : Gauge) (n P : ℕ) (d : ℝ) : 0<cap G n P d := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun _ _=>abs_nonneg _)


def singlePay (G : Gauge) (n P : ℕ) (d s x M : ℝ) (L : Side) := cap G n P d * (M*(2*overhead G L x))*Real.exp (-s*radiusB x)
def debitPay (G : Gauge) (n P : ℕ) (d x M : ℝ) (L : Side) := cap G n P d * (2^n*(M*(2*overhead G L x))^2/2)

-- All eligible basis directions with origins at their respective
-- output anchors (cost under other origins in Pay). Also padded
-- once to the full alphabet for endpoints even outside Active.


/-- Simultaneous estimate of all post-normalization linear or affine
row-debit envelopes. Supports at output units; `r=12` includes the full
query halo and partners (`Footprint.delay`). `Ack` here via any o, not
requiring o=an encountered key. The sqrt-price is what a connected/local
Mayer estimate can use for one-coordinate Z insertions, each coefficient
retaining its complete dependence. No inferencing summability across
*other* products. -/
theorem ink (ht : 0 < radiusB x) (hσ : 0 ≤ σ) (hm : 0<M) (P n : ℕ) (o : Site c) (A : Stores S) (F : Forest S.ratio) :
    let B := radiusB x; let p := Terrain.home S (G:=G); let a := Wisps.down S (G:=G)
    let X := flatTax σ (moves G S.patch.L) B
    let m := cap G n P d * (M * (2 * overhead G S.patch.L x))
    issue p B σ (singlePay G n P d s x M S.patch.L) o ≤ X*(m*Real.exp (-s*B)) ∧
    issue p B σ (Real.sqrt (singlePay G n P d s x M S.patch.L)) o ≤ X*(Real.sqrt m * Real.exp (-(s/2)*B)) ∧
    let c := debitPay G n P d x M S.patch.L
    issue a B σ c o ≤ flatTax σ (⌈priceFiber S.patch G 1⌉₊) B*c := by
  intro B p a X m; let L := S.patch.L
  have hC := cap_pos G n P d
  have hp : 0 < overhead G L x := Real.exp_pos _
  have hh : 0 ≤ m := by unfold m; unfold L at hp; positivity
  have he : 0 ≤ singlePay G n P d s x M L := mul_nonneg hh (Real.exp_pos _).le
  have hk : 0 ≤ debitPay G n P d x M L := by unfold debitPay; positivity
  have hg : Real.sqrt (singlePay G n P d s x M L)=Real.sqrt m * Real.exp (-(s/2)*B) := by
    change Real.sqrt (m*_)=_
    rw [Real.sqrt_mul hh]; apply congr_arg
    exact Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le |>.mpr (by rw [←Real.exp_add]; congr 1; ring)
  exact ⟨invoice o he hσ (allowed G S) ht,(invoice o (Real.sqrt_nonneg _) hσ (allowed G S) ht).trans_eq (congr_arg (X*·) hg),
    invoice o hk hσ (inverse_count (fiber_volume S G zero_lt_one A F x).2) ht⟩
end YM.PhysicalNext.OrderedAffine2B.Halos
