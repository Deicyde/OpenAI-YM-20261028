import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Guards
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Contraction


set_option warningAsError false

/-!
# Local change-of-measure and Jacobian accounts

Use the actual endpoint ``either projection'' convention, and uniform
probability reference on tags. Price with powers of `1+B`, not periods.
At `D=200` the radius for local broad ratios is E H304. Frozen deficit
factors (`|spare|`, i.e. $s_g$ and $j(0)$) counted at the same F
in the chartCost equality (comes later). No leap from cardinality to a
bound on their logs at arbitrary beta allowed. These are location rules,
not claims that all the reader dependency halos equal the locations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory Precision
open YM.SectorNext
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Packet broad/J addresses (not all the active variables, which could
be volume-extensive). -/
def openAt (O A : Stores S) (D : ℕ) (x : ℝ) (F : Forest S.ratio) : Finset (Active A x F) :=
    let H := O.dome ((D+104)*radiusB x)
    Finset.univ.filter fun i => ∃ y∈Next.SectorChange.points S i.val.val, y ∈ H

/-- Packet's frozen deficits. Written on the frozen list of A, including
the full held $Y$ link for each. -/
def freezeAt (O A : Stores S) (x : ℝ) (F : Forest S.ratio) : Finset (Frozen A x F) :=
    Finset.univ.filter fun i => chill O x F i.val




/-- Use also for H200 locations of the paired logarithms, includes the
actual oriented endpoints. -/
def pairsAt (O : Stores S) (F : Forest S.ratio) (d : ℕ) (x : ℝ) : Finset F.Free :=
    Finset.univ.filter fun i => ∃ y ∈ Next.SectorChange.points S i.val,y ∈ O.dome (d*radiusB x)

/-- Exactly the two factors on each active address, including patched
Jacobian. Do not require log bounds for synthetic Y away from weak
positions, or demand the exponent correction without clouds. -/
def jacob {ι : Type} [Fintype ι] (J : ChartRatio G) (q : Chi) (d : ℝ) (p : Finset ι) (a : LogArray G ι) :=
    ∏ i∈p,(extended q J d (a i)*broad q d (a i))



lemma jacob_range {ι : Type} [Fintype ι] (J : ChartRatio G) (q : Chi) (d : ℝ) (p : Finset ι) (a : LogArray G ι)
    (h : LocalRatio J) (hp : 0<d) (hs : 4*d<J.radius) : jacob J q d p a ∈ Icc 0 1 := by
  have hl (i) := gentle_extended h q hp hs (a i)
  have hh i := broad_range q (a i) d
  have hk i : 0≤extended q J d (a i)*broad q d (a i) := mul_nonneg (hl _).1.le (hh _).1
  unfold jacob; refine ⟨Finset.prod_nonneg (fun i _ => hk i), ?_⟩
  have he x : extended q J d (a x)*broad q d (a x) ≤ 1 :=
    (mul_le_of_le_one_right (hl _).1.le (hh _).2).trans (hl _).2
  exact (Finset.prod_le_prod (fun i _ => hk i) (fun i _ => he i)).trans_eq (by simp)

lemma jacob_keeps {ι : Type} [Fintype ι] (J : ChartRatio G) (q : Chi) (d : ℝ) (p : Finset ι) (a : LogArray G ι)
    (i : ι) (he : i∈p) (hd : 0<d) (hh : jacob J q d p a ≠ 0) : ‖a i‖ < 2*d := by
  refine broad_span q hd _ ?_
  intro hok
  exact hh (Finset.prod_eq_zero he (by rw [hok,mul_zero]))

/-- Geometric price in the altitude ledger; provision per fixed-D use.
For bond locations allow also projecting back one lattice separation step
from far endpoint. -/
def streets (d : ℕ) (x : ℝ) (O : Stores S) := 4*((2*d+1:ℕ):ℝ)^4 * Remainder.Scales.b x ^ 4 * O.shares



lemma lanes (O : Stores S) (d x) : ((O.dome (d*radiusB x)).card:ℝ) ≤ streets d x O := by
  apply le_trans (Nat.cast_le (α:=ℝ).mpr (Corona.halo_size O.place _))
  have hp := Nat.cast_le (α:=ℝ).mpr (Work.E01.place_card O)
  unfold streets Remainder.Scales.b; push_cast at *
  have hk : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
  have hv : (d:ℝ)*radiusB x+d*radiusB x+1 ≤ (2*d+1)*(1+(radiusB x:ℝ)) := by
    have h := Nat.cast_nonneg (α:=ℝ) (radiusB x)
    linarith
  have hh := mul_le_mul hp (pow_le_pow_left₀ (by positivity) hv 4) (by positivity) (by positivity)
  exact hh.trans_eq (by ring)

lemma frame_street (O : Stores S) (d x) : ((Visits.near O d x).sites.card:ℝ) ≤ streets (d+100) x O := lanes ..

private lemma align (O : Stores S) (d x) (hx : 1≤radiusB x) {y w : Site c} (hp : separation w y ≤ 1)
    (he : w∈O.dome (d*radiusB x)) : y∈O.dome ((d+1)*radiusB x) :=
  enter_dome O he (by rw [add_mul, one_mul]; omega)

lemma bond_street (O : Stores S) (d x) (hx : 1≤radiusB x) :
    ((Visits.near O d x).bonds.card:ℝ) ≤ (Fintype.card Axis:ℝ)*streets (d+101) x O := by
  let H := O.dome ((d+101)*radiusB x)
  have he : (Visits.near O d x).bonds ⊆ H ×ˢ Finset.univ := by
    intro i hi; apply Finset.mem_product.mpr; refine ⟨?_,Finset.mem_univ _⟩
    obtain ⟨y,hy,hr⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
    refine align O (d+100) x hx ?_ hy
    simp only [pinPos,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with hp|hp <;> rw [hp]
    · simp
    rw [separation_comm]; exact Work.E03.sep_step .. 
  have ht := Nat.cast_le (α:=ℝ).mpr (Finset.card_le_card he)
  rw [Finset.card_product,Finset.card_univ,Nat.cast_mul] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_right (lanes O _ _) (by positivity)).trans_eq (mul_comm _ _))

/-- H_D fine-bond costs via the true `splitSites` (all components -
this is a location price not an eigenvalue count). -/
lemma bond_pairs (O : Stores S) (F : Forest S.ratio) (d x) (hx : 1≤radiusB x) :
    ((pairsAt O F d x).card:ℝ) ≤ (S.patch.L.val:ℝ)^4*(Fintype.card Axis:ℝ)*streets (d+1) x O := by
  let H := O.dome ((d+1)*radiusB x)
  let X := pairsAt O F d x
  let g := S.ratio
  let e := Equiv.prodCongr g.splitSites (Equiv.refl Axis)
  let j := (Function.Embedding.subtype (fun i : Bond f => i ∉ F.trunks)).trans e.toEmbedding
  have he : X.map j ⊆ (H ×ˢ (Finset.univ : Finset (Site g.count))) ×ˢ (Finset.univ : Finset Axis) := by
    intro i hi; obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨y,hy,hr⟩ := (Finset.mem_filter.mp ha).2
    apply Finset.mem_product.mpr; refine ⟨Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,Finset.mem_univ _⟩
    exact align O d x hx ((separation_comm ..).trans_le (meetings a.val hy)) hr
  have ht := Nat.cast_le (α:=ℝ).mpr (Finset.card_le_card he)
  rw [Finset.card_map,Finset.card_product,Finset.card_product,Finset.card_univ,Finset.card_univ,site_card] at ht
  push_cast at ht
  exact ht.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (lanes O _ _) (by positivity))
    (by positivity)).trans_eq (by unfold g StepData.ratio; simp only; ring))

lemma frozen_inc (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (u : Frozen A x F) :
    u∈freezeAt O A x F ↔ u.val ∈ pairsAt O F 10 x := by
  simp [freezeAt,pairsAt,Next.SectorChange.points,chill]

lemma frozen_street (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (hx : 1≤radiusB x) :
    ((freezeAt O A x F).card:ℝ) ≤ (S.patch.L.val:ℝ)^4*(Fintype.card Axis:ℝ)*streets 11 x O := by
  apply le_trans (b:=((pairsAt O F 10 x).card:ℝ)) ?_ (bond_pairs O F 10 x hx)
  let j := Function.Embedding.subtype (chill A x F)
  have he : (freezeAt O A x F).map j ⊆ pairsAt O F 10 x := by
    intro i hi; obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi; exact (frozen_inc ..).mp ha
  exact Nat.cast_le (α:=ℝ).mpr (by simpa only [← Finset.card_map j] using Finset.card_le_card he)
end YM.AnalyticBridge.Annulus
