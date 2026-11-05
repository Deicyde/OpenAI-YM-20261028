import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Density
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Silhouette
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Garden
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Fanfare




/-!
# Recovered F average BEFORE log

Independent Forest at each SITE OF COARSE PERIOD, pick parent block from
that Forest. (Could quotient the duplicate choices; don't need this.) Same
measure, same scalar, no area penalty. This step is important when using
the downstream EXP/GAS with real Moves. Do it at exact push.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Greenbelt
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels Turn
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter Pond
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (s : Signed) (b : Site c)

lemma identityF {g : Ratio c f} (A D : Forest g) (hh:A.up=D.up) (hp:A.height=D.height) : A=D := by obtain ⟨i,j,u,k,l⟩ := A; cases D; subst_vars; rfl

-- not global instance
private lemma stepFinite : Finite Step := Finite.of_injective (fun i : Step=> (i.dir,i.neg)) (fun ⟨i,x⟩ ⟨j,y⟩ h=> by simpa using h)
attribute [local instance] stepFinite
scoped instance rank {g : Ratio c f} : Finite (Forest g) := Finite.of_injective (β:=(Site f→Step)×(Site f→Fin (4*g.count.val+1)))
    (fun A=> (A.up,fun i=> ⟨A.height i,Nat.lt_add_one_of_le (A.bound i)⟩)) (fun A D he=> identityF A D (congr_arg Prod.fst he) (funext fun i=> congr_arg (fun x=> (x.2 i).val) he))
scoped instance {g : Ratio c f} : Fintype (Forest g) := Fintype.ofFinite _

abbrev Reserve (S : StepData c f) := Site c → Forest S.ratio

def allot (r : Reserve S) : Forest S.ratio where
  up i := (r (S.ratio.parent i)).up i
  height i:= (r (S.ratio.parent i)).height i
  bound i:= (r _).bound i
  rise i hi:= by let Y:=r (S.ratio.parent i); change (r (S.ratio.parent (i+(Y.up i).vec))).height _ < Y.height i; rw [Y.stays i hi]; exact Y.rise i hi
  stays i hi := (r _).stays i hi

def orbitForest (S : StepData c f) : Equiv.Perm (Forest S.ratio) := Equiv.ofBijective (Locations.forest s b) (Finite.injective_iff_bijective.mp fun A D he=> by
  apply identityF A D
  · funext i; obtain ⟨i,rfl⟩ := (StepData.sendSites s (S.ratio.embed b)).surjective i; have hk := congr_fun (congr_arg Forest.up he) i
    change Step.rotate _ s⁻¹=Step.rotate _ _ at hk; apply_fun (·.rotate s) at hk
    simp only [Step.rotate_mul,mul_inv_cancel,Step.rotate_one] at hk; exact hk
  funext i; obtain ⟨i,rfl⟩ := (StepData.sendSites s (S.ratio.embed b)).surjective i; exact congr_fun (congr_arg Forest.height he) i)
def orbitKey (S : StepData c f) : Equiv.Perm (Reserve S) := Equiv.arrowCongr (StepData.sendSites s b).symm (orbitForest s b S)

lemma site_orbit (i : Reserve S) (x : Site c) : orbitKey s b S i x=Locations.forest s b (i (affine s b x)) := rfl
lemma f_orbit (i : Reserve S) : allot (orbitKey s b S i)=Locations.forest s b (allot i) := by
  apply identityF
  · funext j; change (orbitKey s b S i (S.ratio.parent j)).up j=_
    rw [site_orbit,← Locations.parent_map]; rfl
  funext j; change (orbitKey s b S i (S.ratio.parent j)).height j=_
  rw [site_orbit,← Locations.parent_map]; rfl

lemma likely_constant {A : Type} [Fintype A] [Nonempty A] (b : ℝ) : likely (fun _ : A => b)=b := by unfold likely; simp
lemma likely_mul {A : Type} [Fintype A] (c : ℝ) (f : A→ℝ) : likely (fun i => c*f i)= c*likely f := by unfold likely; rw [← Finset.mul_sum,mul_left_comm]
lemma likely_congr {A : Type} [Fintype A] {f g : A→ℝ} (p : Equiv.Perm A) (h : ∀ i,f (p i)=g i) : likely f=likely g := by unfold likely; rw [← Equiv.sum_comp p f]; simp_rw [h]
lemma hasAvg {κ ι : Type} [Fintype ι] (f : ι → κ → ℝ) (g : ι→ℝ) (p : ∀ i,HasSum (f i) (g i)) : HasSum (fun x=>likely (fun i=>f i x)) (likely g) := ((hasSum_sum (s:=univ) fun i _=> p i).mul_left _)

private theorem likely_product {A B K : Type} (s : Finset A) (Y : A → Finset B) (h : (s:Set A).PairwiseDisjoint Y)
    [Fintype B] [Fintype K] [Nonempty K] [P : Fintype (B→K)] (f : A→(B→K)→ℝ) (he : ∀ i ∈ s,∀ r r', (∀ j∈Y i,r j=r' j) → f i r=f i r') :
    @likely _ P (fun r=> ∏ i∈s,f i r)= ∏ i∈s,@likely _ P (f i) := by
  let Q : Fintype (B→K):=@Pi.instFintype B _ _ _ _; rw [show P=Q from Subsingleton.elim ..]; exact jurisdictions s Y h f he

variable {P : Teller G} {T : Tube G S} {W α μ C : ℝ} {R : Rep G f} {L : Side}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

-- Does not depend on Cash, so actual target
variable (T)
variable (α : ℝ) (χ : Chi) (K : ℝ) (Ñ : ChartRatio G)
-- give one common field X with dummy seed (planted fresh)
def prism (V : Config G c) (F : Forest S.ratio) : Coat T F := ⟨⟨∅,∅,∅⟩,α,χ,K,V, Classical.arbitrary _,1⟩
def poolA (V : Config G c) (R : Rep G f) (W a : ℝ) (l : ℕ) (p : Molecule S) := likely (fun F : Reserve S=> proceedsA R (prism T α χ K V (allot F)) W a l Ñ p)
def permitsA (V : Config G c) (p : Finset (Molecule S)) := p.biUnion (fun Q=> (roster Q).flags)= RG.flags (Pressure.temp α) V

def festival (V : Config G c) (R : Rep G f) (W a : ℝ) (l : ℕ) (p : Finset (Molecule S)) := if joints T R l (radiusB α) p ∧ permitsA (S:=S) α V p then ∏ i∈p,poolA T α χ K Ñ V R W a l i else 0

variable (H : Cash W α μ L Q o C T R)
include H
lemma repays (V : Config G c) (Z : Finset (Molecule S)) : likely (fun r: Reserve S=> ejections R (prism T α χ o.K V (allot r)) W o.a Q.halo Q.table Z) = festival T α χ o.K Q.table V R W o.a Q.halo Z := by
  letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  let X (r:Reserve S):= prism T α χ o.K V (allot r)
  let f p r:= proceedsA R (X r) W o.a Q.halo Q.table p
  by_cases hp : joints T R Q.halo (radiusB α) Z ∧ permitsA α V Z
  · unfold festival; rw [if_pos hp]
    have he (r: Reserve S) : ejections R (X r) W o.a Q.halo Q.table Z=∏ p∈Z, f p r := if_pos hp
    simp_rw [show ∀ r:Reserve S,ejections R (prism T α χ o.K V (allot r)) W o.a Q.halo Q.table Z=_ from he]
    have hL : (Z:Set (Molecule S)).PairwiseDisjoint (ground R T Q.halo (radiusB α)) := hp.1.2
    change likely _ = ∏ i∈Z, likely (f i)
    apply likely_product Z _ hL f; intro i _ r u h
    exact Horticulture.Travels.sails (X r) (X u) i rfl rfl rfl rfl rfl rfl H fun j hj=> by change (r _).up _= (u _).up _; rw [h _ hj]
  unfold festival; rw [if_neg hp]
  have he (r: Reserve S) : ejections R (X r) W o.a Q.halo Q.table Z=0 := if_neg hp
  change likely _=0; simp_rw [show ∀ r:Reserve S,ejections R (prism T α χ o.K V (allot r)) W o.a Q.halo Q.table Z=0 from he]; apply likely_constant

lemma organizes {F : Tree.Forest S.ratio} (V : Config G c) (X : Coat T F) (hX : X.x=α) (hV : X.V=V) : HasSum
    (fun Z : Finset (Molecule S)=> overhead X R Q.table * festival T α χ o.K Q.table V R W o.a Q.halo Z) (S.push R.beta R.eval V) := by
  letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  let Y (r : Reserve S):=prism T α χ o.K V (allot r)
  have he r : overhead (Y r) R Q.table = overhead X R Q.table := TreeColor.overhead_eq _ X hX.symm H.laws.intake.ready hV.symm ..
  have hp r := Matter.real_push (Y r) H rfl
  simp_rw [he] at hp
  have hk : HasSum (fun z=> likely (fun r => overhead X R Q.table * ejections R (Y r) W o.a Q.halo Q.table z)) (likely (fun _ : Reserve S => S.push R.beta R.eval V)) := hasAvg _ _ hp
  unfold Y at hk; simp_rw [likely_constant,likely_mul, repays T α χ H] at hk; exact hk

lemma retaining (e : R.activities.Moves s (S.ratio.embed b)) (V : Config G c) (p : Molecule S) : poolA T α χ o.K Q.table (pull s b V) R W o.a Q.halo p=poolA T α χ o.K Q.table V R W o.a Q.halo (caravan R e p) := by
  apply likely_congr (orbitKey s b S)
  intro i
  let X := prism T α χ o.K V (allot i)
  let Y := prism T α χ o.K (pull s b V) (Locations.forest s b (allot i))
  rw [f_orbit]
  exact Turn.trumpets R e H (X:=X) (Y:=Y) rfl rfl rfl rfl rfl rfl _
end YM.PhysicalNext.Repeat.Greenbelt
