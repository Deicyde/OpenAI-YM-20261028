import YM.FullVolume.Sector.Jac
/-! Force Hit invoice on full same dictionary -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
namespace Tune
variable (U:Tune H v δ)
-- continuation of raw labels. Reimburse Sales optional once.
local notation "Λ" => U.pole
local notation "t'"=> U.notes
local notation "B₀" => radiusB x₀
local notation "Q'" => stella Q
local notation "A'" => topStorm S.patch
variable {p:Lyre.Signal 0} {ν:ℝ}
local notation "g"=> Q.goal L x₀
local notation "g₀"=> plainP U p ν
local notation "g₁"=> totalP U p ν
open Gas Ursell Trees Multiple Letter OmitClusters
variable {e α:ℝ} (hc:Clear Q L μ ν x₀ v p)
set_option quotPrecheck false
local notation "D'₀"=> (stella Q).mark L μ x₀
-- same C ceiling as armK with (stage)constant enlargement. growth → μ opaque exponential
abbrev prismD (Q: ConnectedActivityE6.Target G P)(L:Side)(μ x₀:ℝ):= 2*(stella Q|>.mergeScale L μ x₀ 0)
abbrev softW (Q : ConnectedActivityE6.Target G P) (L:Side)(μ x:ℝ):= Real.exp (-((stella Q).mark L μ x))*(prismD Q L μ x * (1-1/2)⁻¹)
local notation "Z" => prismD Q L μ x₀
local notation "o₀" => (stella Q).overture L μ x₀ 0
-- emission cost even though nonrestoring letter keeps zero heads.
include hc U
set_option maxHeartbeats 400000 in
lemma clout (hv:e+3*α≤Q.exp) (hx:0≤ e) (hs:0<α) (ht: Z≤1/2) (hw : degreePrice (radiusB x₀) Z α≤1/2) : Ac.Hit H.library B₀ (U.paysL α ν p) e (softW Q L μ x₀):=by
  let A z:= U.feeI 0 α ν p (z:H.ThinP).val; let B z:= U.feeI 1 α ν p (z:H.ThickP).val
  have hp : 0<o₀ := by have hh:=H.laws.intake.height; rw [H.laws.data.funds.length_eq] at hh; exact (Q').overture_pos _ _ (by linarith only [hh])
  let z:= Z; have hz : z=40*o₀:=by unfold z prismD Target.mergeScale; ring
  have hy:2*(o₀) ≤ Z:=by rw [show Z=z from rfl,hz]; nlinarith
  have hr:0< Z:= (mul_pos (by norm_num) hp).trans_le hy
  have hh : degreePrice B₀ (2*o₀) α ≤1/2:=by refine le_trans ?_ hw; unfold degreePrice Trees.stretch; gcongr
  have hW t :0≤ H.shapeW t:= H.positive_volume _
  have hA i:0≤ A i:= U.paidI; have hB i:0≤ B i:= U.paidI
  have hC : Trees.Ready H.smallAt B₀ A (e+α) (2*o₀) α (1/2):=by
    refine ⟨mul_pos (by norm_num) hp,hs,hh,by norm_num,hA,fun i=>?_⟩
    have ht := budget_pull (fun p:H.ThinP=>p.val) Subtype.val_injective (U.marque (p:=p) (ε:=α) hc 0 i)
    refine budget_mono ht (fun i=> ?_) fun p=> ?_
    · split; exact mul_nonneg (hA _) (Real.exp_nonneg _); rfl
    split
    next hi=> rw [if_pos (show i∈H.unionP p.val from hi)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [hv] : e+α+α ≤ Q.exp-α) (show 0 ≤ (coverNumber B₀ (H.smallAt p):ℝ) from Nat.cast_nonneg _))) (hA _)
    exact ht.1 _
  have hh : Ac.Hit H.largeAt B₀ B (e+α) (2*((Q').quantum L μ x₀ 0 0 1 0)) := by
    intro i; have ht := budget_pull (fun p:H.ThickP=>p.val) Subtype.val_injective (U.marque (p:=p) (ε:=α) hc 1 i); refine budget_mono ht (fun p=>?_) fun p=>?_
    · split; exact mul_nonneg (hB _) (Real.exp_nonneg _); rfl
    split
    next hi=> rw [if_pos (show i ∈H.unionP p.val from hi)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [hv,hs] : e+α≤ Q.exp-α) (show 0 ≤ (coverNumber B₀ (H.largeAt p):ℝ) from Nat.cast_nonneg _))) (hB _)
    exact ht.1 _
  have hZ: (Q').quantum L μ x₀ 0 0 1 0= o₀*Real.exp (- (stella Q).mark L μ x₀):=by simpa only [Target.overture,Nat.cast_one,mul_one] using (Q').quantum_form L μ x₀ 0 0 1 0
  intro x
  have he:= OmitClusters.restore H.seam H.smallAt H.largeAt A B (radiusB x₀) hA hB (fun i=>i.2.1) (fun i=>i.2.1) (le_refl (1:ℝ)) (σ:=1/2) (by norm_num) (by norm_num) (show 0≤(stella Q).mark L μ x₀ from H.laws.acquired.marked) hx hs H.testS hC hh ?_ hr ht hw (by norm_num: (1:ℝ)/2<1) x 0
  swap
  · rw [hZ]; have hX:= Real.exp_pos (Q.mark L μ x₀)
    rw [Real.exp_neg]; change _≤z; rw [hz]
    norm_num; -- set mon arithmetic
    field_simp
    nlinarith
  have hν (p:H.Chapter): 0 ≤ OmitClusters.grade H.seam A B p:= by cases p with
    | inl p=> exact hB p
    | inr p=> exact Ursell.clusters_nonneg H.seam hA _
  have hf (y):0 ≤ paysL U α ν p y:=by
    unfold paysL; split
    next h=> unfold manyW; exact prod_nonneg fun i _=>div_nonneg (pow_nonneg (hν i.val) _) (by positivity)
    exact le_rfl
  rw [show ((1:ℝ)^0)⁻¹=1 by norm_num,one_mul] at he
  refine budget_mono he (fun i=>?_) (fun i=>?_)
  · split; exact mul_nonneg (hf _) (Real.exp_nonneg _); rfl
  split
  next hxx =>
    unfold paysL; split
    next hh => rw [if_pos (show OmitClusters.restores i ∧ 0 ≤ Multiple.card _ from ⟨H.regains _ hh.2 hh.1, Nat.zero_le _⟩)]; unfold Multiple.connected; rw [if_pos (show Ac.Spark (test H.smallAt H.largeAt) i.1 ∧ x∈ Finset.biUnion i.fst (test H.smallAt H.largeAt) from ⟨hh.2,hxx⟩)]; exact (mul_comm ..).le
    rw [zero_mul]; exact he.1 _
  exact he.1 _
end Tune
end YM.ConnectedActivityE6.Empire
