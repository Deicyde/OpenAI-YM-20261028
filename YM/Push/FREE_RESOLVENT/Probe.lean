import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Push.FREE_RESOLVENT.Weights
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.F08.Mixed

/-!
# Common period stencil for the rooted derivative

Explicit Walk rows on the cover (including repeated & reversed edges)
reblocked into the *coarse* displacement convention. Preserve all frame
weights, stencil locations `atPoint`, orientation choices in the averages.
No normalization by n! Works including seams; no appeal to smooth p away
from harmonic. Prices for this slice-routed calculation can be fixed-L;
use width-existence for finite patch costs here since the pre-L loop exchange
estimate would use a different joint completion and weights.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Work.F08
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {n L c f : Side} {S : StepData c f} {α β ι : Type*}

-- internal per-output-type stencil calculus
namespace Draw

abbrev Brushes (α : Type*) := α → Cover → ℝ
abbrev Line (L : Side) := Brushes (Co L (TypeFace 1))

def Ready (P : Brushes α) := ∀ i s, ∃ M : ℝ, 0 ≤ M ∧ Width s M (P i)
variable {P Q : Brushes α}

lemma Ready.leans (h : Ready P) (i : α) : Summable (P i) := by
  obtain ⟨m,-,hm⟩ := h i 0; exact hm.summable le_rfl

lemma Ready.zero : Ready (0 : Brushes α) := fun _ _ => ⟨0,le_rfl,by simp [Width,RG.SumBudget]⟩
lemma Ready.prod (r : ℝ) (h : Ready P) : Ready (r • P) := by
  intro i s
  obtain ⟨m,hm,hp⟩ := h i s
  refine ⟨‖r‖*m,mul_nonneg (norm_nonneg _) hm,?_⟩
  have h : Row.strip (α:=Unit) (β:=Unit) (fun _ _ => P i) s m := fun _ _ => hp
  exact strip_scale h r () ()
lemma Ready.neg (h : Ready P) : Ready (-P) := by
  rw [← neg_one_smul ℝ P]; exact h.prod _
lemma Ready.sub (h : Ready P) (g : Ready Q) : Ready (P-Q) := by
  intro i s; obtain ⟨m,hm,hp⟩ := h i s; obtain ⟨r,hr,hq⟩ := g i s
  have h : Row.strip (α:=Unit) (β:=Unit) (fun _ _ => P i) s m := fun _ _ => hp
  have g : Row.strip (α:=Unit) (β:=Unit) (fun _ _ => Q i) s r := fun _ _ => hq
  exact ⟨m+r, add_nonneg hm hr, strip_minus h g () ()⟩
lemma Ready.add (h : Ready P) (g : Ready Q) : Ready (P+Q) := by
  rw [← sub_neg_eq_add]; exact h.sub g.neg
lemma Ready.finite (t : Finset ι) (u : ι → Brushes α) (h : ∀ i ∈ t, Ready (u i)) : Ready (∑ i ∈ t, u i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Ready.zero
  | @insert i t he ih => rw [Finset.sum_insert he]; exact (h i (by simp)).add (ih fun i hi => h _ (by simp [hi]))

/-- Rectangular conversion cost is a *per row type* maximum, payable
before period is known. -/
lemma ready_strip [Fintype α] [Fintype β] {R : Row α β} (H : ∀ i, Ready (R i)) (s : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ R.strip s M := by
  choose m hm h using fun i j => H i j s
  refine ⟨∑ i, ∑ j, m i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hm i j,fun i j => ?_⟩
  exact (h i j).mono le_rfl ((Finset.single_le_sum (fun a _ => hm i a) (Finset.mem_univ j)).trans (Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => hm a b)) (Finset.mem_univ i)))

-- Read along an arbitrary fine slot; anchored at coarse x.
def spot (g : Ratio c f) (P : Line g.count) (x : Site c) (a : Body 1 f) :=
  sift (P (splitCo g (TypeFace 1) a).2) c x (splitCo g (TypeFace 1) a).1
variable {g : Ratio c f} {p q : Line g.count} (x : Site c) (a : Body 1 f)

@[simp] lemma spot_zero : spot g 0 x a = 0 := by simp [spot,sift]
lemma spot_add (hp : Ready p) (hq : Ready q) : spot g (p+q) x a = spot g p x a + spot g q x a := by
  unfold spot sift
  rw [← (summable_sift (hp.leans _) _ _).tsum_add (summable_sift (hq.leans _) _ _)]
  refine tsum_congr fun z => ?_
  split <;> simp
lemma spot_prod (r : ℝ) : spot g (r • p) x a = r*spot g p x a := by
  unfold spot sift; rw [← tsum_mul_left]; refine tsum_congr fun z => ?_; split <;> simp
lemma spot_neg : spot g (-p) x a = -spot g p x a := by rw [← neg_one_smul ℝ p,spot_prod]; ring
lemma spot_sub (hp : Ready p) (hq : Ready q) : spot g (p-q) x a = spot g p x a - spot g q x a := by
  rw [sub_eq_add_neg,spot_add x a hp hq.neg,spot_neg]; rfl
lemma spot_sum (t : Finset ι) (u : ι → Line g.count) (h : ∀ i, Ready (u i)) : spot g (∑ i ∈ t, u i) x a = ∑ i ∈ t, spot g (u i) x a := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t he ih => rw [Finset.sum_insert he,Finset.sum_insert he,spot_add x a (h i) (Ready.finite t u fun i _ => h i),ih]

/-- Generate the charge at a *fine offset* and a direction
(orientation sign applied by caller AFTER relocation). -/
def mark (L : Side) (e : Edge Cover) : Line L := fun j z =>
  if z=carry (0:Site L) e.1 then
    if j=(arrives (0:Site L) e.1,coord e.2) then 1 else 0
  else 0

lemma ready_mark (e : Edge Cover) : Ready (mark L e) := by
  intro j s
  let F z := Real.exp (s*size z)*‖mark L e j z‖
  let k := carry (0:Site L) e.1
  have H z (hz : z ≠ k) : F z = 0 := by
    change z ≠ carry (0:Site L) e.1 at hz
    simp [mark,F,hz]
  have h z : 0 ≤ F z := by unfold F; positivity
  exact ⟨F k,h k,h,summable_of_ne_finset_zero (s:={k}) fun i hi => H i (by simpa using hi), (tsum_eq_single k H).le⟩

lemma spot_mark (e : Edge Cover) : spot g (mark g.count e) x a = ((Pi.single a (1:ℝ)):form 1 f) (g.embed x+wrap f e.1,coord e.2) := by
  let k := carry (0:Site g.count) e.1
  let j := (arrives (0:Site g.count) e.1,coord e.2)
  let y : Body 1 f := (g.embed x+wrap f e.1,coord e.2)
  let E := splitCo g (TypeFace 1)
  have he : E y=(x+wrap c k,j) := by
    simp only [E,y,j,k,split_co,moves_parent,moves_residue,g.embed_parent,g.residue_embed]
  change sift (mark g.count e (E a).2) c x (E a).1 = ((Pi.single a (1:ℝ)):form 1 f) y
  rw [Pi.single_apply,sift,tsum_eq_single k]
  · by_cases h : y=a
    · simp only [← h,he]; unfold mark; simp [k,j]
    rw [if_neg h]; split
    · unfold mark
      rw [if_pos rfl, if_neg]; intro ha
      apply h; exact E.injective (he.trans (Prod.ext ‹(E a).1 = _›.symm ha.symm))
    rfl
  intro z hz
  unfold mark; split
  · rfl
  rfl

def path (L : Side) (z : Cover) : Walk → Line L
  | [] => 0
  | b :: v => (if b.neg then -mark L (b.used z) else mark L (b.used z)) + path L (z+b.vec) v

lemma path_ready (z : Cover) (w : Walk) : Ready (path L z w) := by
  induction w generalizing z with
  | nil => exact Ready.zero
  | cons b w ih =>
    rw [path]; split
    · exact (ready_mark _).neg.add (ih _)
    exact (ready_mark _).add (ih _)

lemma spot_path (z : Cover) (w : Walk) : spot g (path g.count z w) x a =
    integralLink (wrap f z+g.embed x) w (Pi.single a 1) := by
  induction w generalizing z with
  | nil => exact spot_zero ..
  | cons b w ih =>
    have hx : Ready (if b.neg then -mark g.count (b.used z) else mark g.count (b.used z)) := by
      split
      · exact (ready_mark _).neg
      exact ready_mark _
    rw [path, spot_add x a hx (path_ready (z+b.vec) w), ih]
    have ht : (wrap f (z+b.vec)+g.embed x)=(wrap f z+g.embed x+b.vec) := by rw [map_add,wrap_vec]; abel
    rw [ht]
    rcases b with ⟨d,h|h⟩
    · rw [if_neg (by simp), spot_mark]
      simp only [Step.used,Bool.false_eq_true,↓reduceIte]; rw [add_comm (g.embed x)]; rfl
    rw [if_pos rfl, spot_neg, spot_mark]
    simp only [Step.used,↓reduceIte,map_sub,wrap_step]
    rw [show g.embed x+(wrap f z-step d)=wrap f z+g.embed x-step d by abel]; rfl
end Draw

open Draw


-- Same averaging order and frame centering as probe.
def traffic (P : Patch) (i : P.Points) : Line P.L :=
  -((Fintype.card P.Points:ℝ)⁻¹ • ∑ j : P.Points,
    (Fintype.card Lattice.Order:ℝ)⁻¹ • ∑ t : Lattice.Order, path P.L i.val (route i.val j.val t))
lemma traffic_ready (P : Patch) (i : P.Points) : Ready (traffic P i) := by
  apply Ready.neg; apply Ready.prod; apply Ready.finite
  intro j _; apply Ready.prod; apply Ready.finite; intro t _; exact path_ready _ _
lemma traffic_spot (S : StepData c f) (i : S.patch.Points) (x : Site c) (a : Body 1 f) :
    spot S.ratio (traffic S.patch i) x a = tau S x i (Pi.single a 1) := by
  have hg (j : S.patch.Points) : Ready (∑ t : Lattice.Order, path S.patch.L i.val (route i.val j.val t)) :=
    Ready.finite _ _ fun t _ => path_ready _ _
  -- provide h explicitly for sums
  unfold tau traffic; erw [spot_neg, spot_prod, spot_sum x a _ _ fun j => (hg j).prod _]
  simp only [LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply, smul_eq_mul]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [spot_prod,spot_sum x a _ _ fun _ => path_ready _ _]; congr 1
  exact Finset.sum_congr rfl fun t _ => spot_path x a _ _

def rootRow (P : Patch) : Row (TypeFace 0) (Co P.L (TypeFace 1)) :=
  fun _ => traffic P P.center - ∑ b, P.weight b • traffic P b
def connectorRow (P : Patch) : Row (TypeFace 1) (Co P.L (TypeFace 1)) :=
  fun i => ∑ b, P.weight b • path P.L b.val (List.replicate P.L.val (posDir (axisEquiv.symm i)))

lemma ready_rootRow (P : Patch) (s : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ (rootRow P).strip s M :=
  ready_strip (fun _ => (traffic_ready _ _).sub (Ready.finite _ _ fun j _ => (traffic_ready P j).prod (P.weight j))) s
lemma ready_connectorRow (P : Patch) (s : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ (connectorRow P).strip s M :=
  ready_strip (fun _ => Ready.finite _ _ fun j _ => (path_ready _ _).prod (P.weight j)) s

lemma block_root (S : StepData c f) :
    fixRoot S = ((rootRow S.patch).acts c).submatrix id (splitCo S.ratio (TypeFace 1)) := by
  ext x a
  have hh (x a) : ((fixRoot S)*ᵥ Pi.single a (1:ℝ)) x = fixRoot S x a := by simp
  rw [← hh,fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,Matrix.submatrix_apply]
  rw [adjusted,LinearMap.sub_apply,LinearMap.sum_apply]
  change _ = spot S.ratio (rootRow S.patch x.2) x.1 a
  erw [rootRow,spot_sub x.1 a (traffic_ready _ _) (Ready.finite _ _ fun j _ => (traffic_ready S.patch j).prod _),
      spot_sum x.1 a _ _ fun j => (traffic_ready S.patch j).prod _, traffic_spot]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  erw [spot_prod,traffic_spot]; rfl

lemma block_mean (S : StepData c f) :
    mean S = ((connectorRow S.patch).acts c).submatrix id (splitCo S.ratio (TypeFace 1)) := by
  ext x a
  have hh : (mean S *ᵥ Pi.single a (1:ℝ)) x = mean S x a := by simp
  rw [← hh,mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply]
  change _ = spot S.ratio (connectorRow S.patch x.2) x.1 a
  erw [connectorRow, spot_sum x.1 a _ _ fun b => Ready.prod _ (path_ready _ _)]
  simp_rw [LinearMap.smul_apply,spot_prod,spot_path]; rfl

lemma cobound_ready (r : ℕ) (s : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ (cobound r).strip s B := by
  apply ready_strip
  intro i j s
  let F (z : Cover) := Real.exp (s*size z)*‖cobound r i j z‖
  have hy z (hz : z ∉ support) : F z = 0 := by simp [F,certified _ _ _ _ hz]
  have ht z : 0 ≤ F z := by unfold F; positivity
  exact ⟨∑ z ∈ support, F z, Finset.sum_nonneg fun i _ => ht i, ht,
    summable_of_ne_finset_zero hy, (tsum_eq_sum hy).le⟩

def plusRows (P Q : Row α β) : Row α β := minusRows P (scaleRows (-1) Q)
lemma strip_plus {P Q : Row α β} {A B s : ℝ} (hp : P.strip s A) (hq : Q.strip s B) :
    (plusRows P Q).strip s (A+B) := by simpa [plusRows] using strip_minus hp (strip_scale hq (-1))
lemma acts_plus {P Q : Row α β} {A B s : ℝ} (hp : P.strip s A) (hq : Q.strip s B) (hs : 0 ≤ s) (n : Side) :
    (plusRows P Q).acts n = P.acts n + Q.acts n := by rw [plusRows,acts_minus hs hp (strip_scale hq _), acts_scale]; simp

/-- Probe as a universal row IN coarse OUT fine when following row → column.
Action is fine to coarse, as required. -/
def probeRow (P : Patch) := plusRows (connectorRow P) (composeRows (cobound 0) (rootRow P))
lemma probe_ready (P : Patch) (s : ℝ) (hs : 0 ≤ s) : ∃ K : ℝ, 0 ≤ K ∧ (probeRow P).strip s K := by
  obtain ⟨a,ha,h₁⟩ := ready_connectorRow P s; obtain ⟨b,hb,h₂⟩ := ready_rootRow P s
  obtain ⟨c,hc,h₃⟩ := cobound_ready 0 s
  exact ⟨_, by positivity, strip_plus h₁ (strip_compose hs h₃ h₂)⟩

lemma block_probe (S : StepData c f) : probe S =
    ((probeRow S.patch).acts c).submatrix id (splitCo S.ratio (TypeFace 1)) := by
  obtain ⟨a,-,h₁⟩ := ready_connectorRow S.patch 0; obtain ⟨b,-,h₂⟩ := ready_rootRow S.patch 0
  obtain ⟨m,-,h₃⟩ := cobound_ready 0 0
  rw [probe,block_mean,block_root,probeRow,acts_plus h₁ (strip_compose le_rfl h₃ h₂) le_rfl,
    acts_compose le_rfl h₃ h₂]; rfl
end YM.FreeResolvent
