import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations
import YM.Extra.WILSON_STARTUP.Taylor
import YM.Next.MAXWELL.Pole
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Ratios
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Variables
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay
import YM.SectorNext.RECONNECTED_LOCALITY.Gaussian
import YM.SectorNext.VACUUM_NORMALIZATION.Relative


/-!
# Tag law for the transfer

Shuffle local tree tags **independently by physical coarse site**.
Each site draws forestry data once, including when inactive; compile
all further reads on the same tag. `canopy` gives one choice with a seed
for every Forest (uniform local tags chosen among all whole-ticket trees
but use only their prescription for that block), and across any signed
orientation a Perm. No assumption on magnitude of these tag counts --
later pay prices using total mass, and keep these tags even when
testing subset meetings & disjoint factorisation in body estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice RG Pressure Tree Wilson Next.SectorChange Finset Bid
     Push.SectorMeasure AnalyticBridge.GaussianFieldAlignment
     Function Filter Next.Rank Tapes Perch SectorNext.Vacuum
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
structure Orchard (S : StepData c f) where
  put : ℕ
  table : Fin (put+1) → Forest S.ratio
abbrev Orchard.Seeds (X : Orchard S) := Site c → Fin (X.put+1)
namespace Orchard
def grow (X : Orchard S) (t : Seeds X) : Forest S.ratio where
  up i := (X.table (t (S.ratio.parent i))).up i
  height i := (X.table (t (S.ratio.parent i))).height i
  bound i := Forest.bound ..
  rise i h := by
    let F:= X.table (t (S.ratio.parent i)); exact (show (X.table _).height (i+(F.up i).vec)<_ by rw [F.stays i h]; exact F.rise i h)
  stays i h := (X.table (t (S.ratio.parent i))).stays i h

def alone (S : StepData c f) (F : Forest S.ratio) : Orchard S:=⟨0,fun _=> F⟩

lemma crowns (X : Orchard S) {v u : X.Seeds} (i : Bond f) (h : v (S.ratio.parent i.1)=u (S.ratio.parent i.1)) : i ∈ (X.grow v).trunks ↔ i∈ (X.grow u).trunks:= by
  suffices ht : ∀ v u : X.Seeds, v (S.ratio.parent i.1)=u (S.ratio.parent i.1) → i∈(X.grow v).trunks→ i∈(X.grow u).trunks from ⟨ht _ _ h,ht _ _ h.symm⟩
  intro v u h hU; rw [Forest.trunk_mem_iff]; obtain ⟨j,hj,hv⟩ := (Forest.trunk_mem_iff ..).1 hU
  have hh : S.ratio.parent i.1=S.ratio.parent j:= by
    let F:= X.grow v; let p:= F.up j
    have h₁ := (X.grow v).stays j hj; change S.ratio.parent (j+p.vec)=_ at h₁; change p.used j=i at hv; rw [← hv]
    cases he : p with
    | mk k x =>
       rw [he] at h₁
       cases x <;> simp only [Step.used,Bool.false_eq_true,↓reduceIte,Step.vec, ← sub_eq_add_neg] at h₁ ⊢
       exact h₁
  rw [hh] at h; refine ⟨j,hj,?_⟩; convert hv using 2; dsimp only [grow]; rw [h]

def solo (X : Orchard S) : ℝ := (↑(Fintype.card X.Seeds):ℝ)⁻¹
lemma solo_one (X : Orchard S) : (∑ _i : X.Seeds, solo X)=1:= by unfold solo; simp; apply mul_inv_cancel₀; positivity

private lemma forest_inj (a b : Forest S.ratio) (h : a.up=b.up) (he : a.height=b.height): a=b := by cases a; cases b; congr
private instance (S : StepData c f) : Nonempty (Forest S.ratio) := Tree.select _ S.patch.odd_side
private instance forestType (S : StepData c f) : Fintype (Forest S.ratio) := by
  let e : Step ↪ Axis×Bool := ⟨fun s=> match s with | ⟨a,b⟩ => (a,b), by rintro ⟨_,_⟩ ⟨_,_⟩; simp ⟩
  let v (F : Forest S.ratio) (i : Site f) : (Axis×Bool) × Fin (4*S.patch.L.val+1):=(e (F.up i),⟨F.height i,Nat.lt_succ_of_le (F.bound i)⟩)
  refine Fintype.ofInjective v fun a b h=>forest_inj a b (funext fun i=> e.injective (congr_arg Prod.fst (congr_fun h i))) (funext fun i=> Fin.ext_iff.mp (congr_arg Prod.snd (congr_fun h i)))

private def wolf (S : StepData c f) := Fintype.card (Forest S.ratio)-1
private def train (S : StepData c f) : Fin (wolf S+1) ≃ Forest S.ratio:=
  (finCongr (Nat.sub_add_cancel Fintype.card_pos)).trans (Fintype.equivFin _).symm

def canopy (S : StepData c f) : Orchard S:=⟨wolf S, train S⟩

private def flip (S : StepData c f) (s : Signed) (b : Site c) : Equiv.Perm (Forest S.ratio) := by
  let F := Locations.forest (S:=S) s b
  refine Equiv.ofBijective F (Finite.injective_iff_bijective.mp ?_); intro i j h
  apply forest_inj
  · funext u; obtain ⟨u,rfl⟩:= (StepData.sendSites s (S.ratio.embed b)).surjective u
    have he := congr_arg (fun t : Forest S.ratio=> (t.up u).rotate s) h; unfold F Locations.forest Locations.up at he
    rw [Step.rotate_mul,Step.rotate_mul,mul_inv_cancel,Step.rotate_one,Step.rotate_one] at he; exact he
  funext u; obtain ⟨u,rfl⟩:= (StepData.sendSites s (S.ratio.embed b)).surjective u; exact congr_arg (fun t : Forest S.ratio=> t.height u) h
lemma transportable (S : StepData c f) (s : Signed) (b : Site c) : ∃ E : Equiv.Perm (Seeds (canopy S)), ∀ t,(canopy S).grow (E t)=Locations.forest s b ((canopy S).grow t):=by
  let Z:= ((train S).trans (flip S s b)).trans (train S).symm
  refine ⟨Equiv.arrowCongr (StepData.sendSites s b).symm Z,fun t=>?_⟩
  apply forest_inj
  · funext u
    change ((train S) ((train S).symm (Locations.forest s b (train S (t (affine s b (S.ratio.parent u))))))).up u= ((train S (t (S.ratio.parent (affine s (S.ratio.embed b) u)))).up _).rotate s⁻¹
    rw [Equiv.apply_symm_apply, Locations.parent_map]; rfl
  funext u
  change ((train S) ((train S).symm (Locations.forest s b (train S (t (affine s b (S.ratio.parent u))))))).height u= (train S (t (S.ratio.parent (affine s (S.ratio.embed b) u)))).height _
  rw [Equiv.apply_symm_apply, Locations.parent_map]; rfl
end Orchard
structure Streak (X : Orchard S) where
  roots : X.Seeds
  tag : S.Choices
namespace Streak
variable {X : Orchard S}
def wood (k : Streak X) := X.grow k.roots
def entered (S : StepData c f) (X : Orchard S) : Streak X ≃ X.Seeds × S.Choices:= ⟨fun t=> (t.roots,t.tag), fun t=> ⟨t.1,t.2⟩,fun _=>rfl,fun _=>rfl⟩
instance (X : Orchard S) : Fintype (Streak X) := Fintype.ofEquiv _ (entered S X).symm
def share (j : Streak X) := Orchard.solo X*tagRef j.tag
lemma share_nn (j : Streak X) : 0≤share j:=by unfold share Orchard.solo tagRef; positivity
lemma full (h : S.patch.Branches S.kernel G) : ∑ k : Streak X, k.share=1:= by
  rw [← Equiv.sum_comp (entered S X).symm share,Fintype.sum_prod_type]; change (∑ _i:X.Seeds,∑ j, Orchard.solo X*tagRef j)=_
  simp_rw [← Finset.mul_sum]; have hp : ∑ k:S.Choices, tagRef k=1:= reference_is_prob h; simp_rw [hp]; rw [Finset.mul_sum]; simp_rw [mul_one]; exact Orchard.solo_one X
end Streak
end YM.PhysicalNext.InteractingRank
