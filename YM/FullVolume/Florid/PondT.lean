import YM.FullVolume.Florid.Lake
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
open Merge Tickets Merge.Palette Lyre Tune
namespace Crew
-- authentic epochs.affine Camera geometry. φ held input hats all.FULL.Reached.
variable {A:Type}[Fintype A](V:A→Mill U)
open Daisy PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Jams Ovens
variable (p:Tickets (sign (faces V) S))
local notation "V₁"=> Merge.Palette.team (faces V) p
local notation "Λ"=>U.pole
local notation "T₀"=> radiusB x₀
local notation "Q'" => Empire.stella Q
variable {ν α:ℝ} {s:Lyre.Signal 0} (hc:Clear Q L μ ν x₀ v s)(hr: Lyre.Clarity H 0 C δ ν)(hσ:Margin G L x₀ α δ)(hv:2≤v)
variable (X:Coat T F)(he:X.x=x₀)(ht:X.width=o.K)
variable (i:Molecule S)
local notation "f₀"=> U.plainP s ν
local notation "f₁"=> U.totalP s ν
local notation "d" => pleas V p α ν s i
variable (Cy:A→ℝ)(hh:∀ i,0≤Cy i)
local notation "A₀"=>accountK V Cy s
open Merge Switch FullVolume.Ray.Weigh
open Gas Ursell Trees Multiple Letter OmitClusters
set_option quotPrecheck false
variable (Y: Mixed.Accounts S Q.halo (radiusB x₀) (Daisy.swing (stella Q) L μ R.beta x₀ ν) H.birth (accountK V Cy s) (ConnectedActivityE6.lengths T R) (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)))
variable (hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))
def scoreD (Q: Target G P)(L:Side)(μ x:ℝ):= (Daisy.swing (stella Q) L μ 1 x 0).ceiling 0 0 0 0
-- S.reason stamp large enough.Final Konto.s
abbrev figureS (Q:Target G P)(L:Side)(μ x:ℝ) := (40:ℝ)* Crew.scoreD Q L μ x
local notation "o₀"=>scoreD Q L μ x₀
local notation "Z"=> figureS Q L μ x₀
abbrev zerosV (Q:Target G P)(L:Side)(μ x:ℝ):= Real.exp (-(stella Q|>.mark L μ x))*(figureS Q L μ x*(1-1/2)⁻¹)
-- emission cost even though nonrestoring letter keeps zero heads.
variable {e:ℝ}
include Y hA hh
set_option maxHeartbeats 400000 in
lemma grange (hp : 0 < scoreD Q L μ x₀) (hv:e+3*α≤Q.exp) (hx:0≤ e) (hs:0<α) (ht: Z≤1/2) (hw : degreePrice (radiusB x₀) Z α≤1/2) : Ac.Hit H.library T₀ (tokens V Cy α ν s) e (zerosV Q L μ x₀):=by
  let A! z:= laude V Cy 0 α ν s (z:H.ThinP).val; let B z:= laude V Cy 1 α ν s (z:H.ThickP).val
  let z:= Z; have hz : z=40*o₀:=by exact rfl
  have hy:2*(o₀) ≤ Z:=by rw [show Z=z from rfl,hz]; nlinarith
  have hr:0< Z:= (mul_pos (by norm_num) hp).trans_le hy
  have hh : degreePrice T₀ (2*o₀) α ≤1/2:=by refine le_trans ?_ hw; unfold degreePrice Trees.stretch; gcongr
  have hW t :0≤ H.shapeW t:= H.positive_volume _
  have hA i:0≤ A! i:= Crew.crestK V _ _ Cy ‹∀ i,0≤Cy i›; have hB i:0≤ B i:= Crew.crestK V _ _ Cy ‹∀ i,0≤Cy i›
  have hC : Trees.Ready H.smallAt T₀ A! (e+α) (2*o₀) α (1/2):=by
    refine ⟨mul_pos (by norm_num) hp,hs,hh,by norm_num,hA,fun i=>?_⟩
    have ht := budget_pull (fun p:H.ThinP=>p.val) Subtype.val_injective (foes V Cy ‹∀ i,0≤Cy i› (α:=α) Y ‹_› 0 i)
    refine budget_mono ht (fun i=> ?_) fun p=> ?_
    · split; exact mul_nonneg (hA _) (Real.exp_nonneg _); rfl
    split
    next hi=> rw [if_pos (show i∈H.unionP p.val from hi)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [hv] : e+α+α ≤ Q.exp-α) (show 0 ≤ (coverNumber T₀ (H.smallAt p):ℝ) from Nat.cast_nonneg _))) (hA _)
    exact ht.1 _
  have hh : Ac.Hit H.largeAt T₀ B (e+α) (2*((Daisy.swing Q' L μ 1 x₀ 0).ceiling 0 0 1 0)) := by
    intro i; have ht := budget_pull (fun p:H.ThickP=>p.val) Subtype.val_injective (foes V Cy ‹∀ i,0≤Cy i› (α:=α) Y ‹_› 1 i); refine budget_mono ht (fun p=>?_) fun p=>?_
    · split; exact mul_nonneg (hB _) (Real.exp_nonneg _); rfl
    split
    next hi=> rw [if_pos (show i ∈H.unionP p.val from hi)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [hv,hs] : e+α≤ Q.exp-α) (show 0 ≤ (coverNumber T₀ (H.largeAt p):ℝ) from Nat.cast_nonneg _))) (hB _)
    exact ht.1 _
  have hZ: (Daisy.swing Q' L μ 1 x₀ 0).ceiling 0 0 1 0= o₀*Real.exp (- (stella Q).mark L μ x₀):=by
    unfold scoreD Mixed.Costs.ceiling Reserves.extract; simp only [Nat.cast_one,Nat.cast_zero,mul_zero,mul_one,sub_zero]; change _*Real.exp (0- (Empire.stella Q).mark L μ x₀)*_= (_*Real.exp (0:ℝ)*_)*_; rw [zero_sub,Real.exp_zero]; ring
  intro x
  have he:= OmitClusters.restore H.seam H.smallAt H.largeAt A! B (radiusB x₀) hA hB (fun i=>i.2.1) (fun i=>i.2.1) (le_refl (1:ℝ)) (σ:=1/2) (by norm_num) (by norm_num) (show 0≤(stella Q).mark L μ x₀ from H.laws.acquired.marked) hx hs H.testS hC hh ?_ hr ht hw (by norm_num: (1:ℝ)/2<1) x 0
  swap
  · rw [hZ]; have hX:= Real.exp_pos (Q.mark L μ x₀)
    rw [Real.exp_neg]; change _≤z; rw [hz]
    norm_num; -- set mon arithmetic
    field_simp
    nlinarith
  have hν (p:H.Chapter): 0 ≤ OmitClusters.grade H.seam A! B p:= by cases p with
    | inl p=> exact hB p
    | inr p=> exact Ursell.clusters_nonneg H.seam hA _
  have hf (y):0 ≤ Crew.tokens V Cy α ν s y:=by
    unfold Crew.tokens; split
    next h=> unfold manyW; exact prod_nonneg fun i _=>div_nonneg (pow_nonneg (hν i.val) _) (by positivity)
    exact le_rfl
  rw [show ((1:ℝ)^0)⁻¹=1 by norm_num,one_mul] at he
  refine budget_mono he (fun i=>?_) (fun i=>?_)
  · split; exact mul_nonneg (hf _) (Real.exp_nonneg _); rfl
  split
  next hxx =>
    unfold Crew.tokens; split
    next hh => rw [if_pos (show OmitClusters.restores i ∧ 0 ≤ Multiple.card _ from ⟨H.regains _ hh.2 hh.1, Nat.zero_le _⟩)]; unfold Multiple.connected; rw [if_pos (show Ac.Spark (test H.smallAt H.largeAt) i.1 ∧ x∈ Finset.biUnion i.fst (test H.smallAt H.largeAt) from ⟨hh.2,hxx⟩)]; exact (mul_comm ..).le
    rw [zero_mul]; exact he.1 _
  exact he.1 _
end Crew
end YM.ConnectedActivityE6.Empire.Imago
