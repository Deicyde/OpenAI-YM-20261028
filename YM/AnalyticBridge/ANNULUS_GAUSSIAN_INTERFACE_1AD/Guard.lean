import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Push.SECTOR_MEASURE.Profile
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay

/-!
# Retained profiles (, items 2, 3, 4 )

Use actual Allocation source: take Chi.profiles when factoring
into genuinely local prerequisites. Likelihood occupations are probabilities
(branch criteria and one shared k), not density estimates on a counting
volume. Don't assume that every tag had positive mass; the nonzero local
product itself licenses the prerequisite. We include **all** frame and bond
factors in these larger halo slabs, exact when multiplying back together,
thus don't need the more delicate rule setting fallback weights to their
uniform values outside core (in particular won't do that off-plateau).
See dedicated tag estimates later.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric   Exterior Bloch
open  YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset
variable {c f n : Side} {G : Gauge} {S : StepData c f}

section arithmetic
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def profile (q : Chi) (s : Finset ι) (v : ι → ℝ) (d : ℝ) (i : ι) :=
  if i∈s then 1-q.innerShare d (v i) else q.innerShare d (v i)
lemma profile_range (q : Chi) (s : Finset ι) (v : ι → ℝ) (d : ℝ) (i : ι) :
    profile q s v d i∈Set.Icc (0:ℝ) 1 := by
  have h : q.innerShare d (v i) ∈ Set.Icc (0:ℝ) 1 := q.range _
  unfold profile; split
  · exact ⟨sub_nonneg.mpr h.2,sub_le_self _ h.1⟩
  exact h

lemma profile_charged (q : Chi) (s : Finset ι) (v : ι→ℝ) {d : ℝ} (hd : 0<d) (i : ι)
    (h : profile q s v d i ≠ 0) (he : 0≤v i) : (i∈s → d < v i) ∧ (i∉s → v i < 2*d) := by
  constructor
  · intro ht; exact q.exterior_gt (v i) d he hd (by simpa [profile,ht] using h)
  intro ht; exact q.chosen_lt (v i) d hd (by simpa [profile,ht] using h)
end arithmetic

/-- Store fine/noise partition profiles and tags at *actual locations*
(minimum over all incident endpoints for a plaquette or bond). -/
def nearFace (S : StepData c f) (X : Support c) : Finset (Cell f) := univ.filter fun p => ¬ Disjoint (startPos S p) X

def nearNoise (X : Support c) : Finset (Bond c) := univ.filter fun i : Bond c => ¬ Disjoint (pinPos i) X

def tokenF (A : Stores S) (q : Chi) (x : ℝ) (U : Config G f) :=
  profile q A.costs (toll U) (fiery G x S.patch.L / 4)
def tokenB (A : Stores S) (q : Chi) (x w : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) :=
  profile q A.aisles (wire (S.prediction U k) V) (w*fiery G x S.patch.L)

def frame (k : S.Choices) (U : Config G f) (i : Site c) :=
  S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i)
def bond (k : S.Choices) (U : Config G f) (i : Bond c) :=
  S.patch.predictorMass S.kernel (S.connector U k.1 i) (k.2 i)
def flag (x : ℝ) (A : Stores S) (V : Config G c) (i : Site c) : ℝ :=
  if (i∈A.flags ↔ i∈RG.flags (temp x) V) then 1 else 0

lemma frame_zero (k : S.Choices) (U : Config G f) (i : Site c) :
    0 ≤ frame k U i := by unfold frame Patch.frameMass; split
                          · positivity
                          split <;> positivity
lemma bond_zero (k : S.Choices) (U : Config G f) (i : Bond c) : 0≤ bond k U i := by
  unfold bond Patch.predictorMass; split
  · positivity
  exact S.patch.weight_nonneg _
lemma frame_price (k : S.Choices) (U : Config G f) (h : S.patch.Branches S.kernel G) (i : Site c) :
    frame k U i ≤ 1 := by
  rw [← S.patch.frameMass_sum h (expandAt (S.ratio.embed i) U)]
  apply single_le_sum (s:=Finset.univ) _ (mem_univ (k.1 i))
  exact fun u _ => frame_zero (show S.Choices from ((fun _=>u), k.2)) U i
lemma bond_price (k : S.Choices) (U : Config G f) (i : Bond c) : bond k U i ≤ 1 := by
  rw [← S.patch.predictorMass_sum (C:=S.kernel) (S.connector U k.1 i)]
  exact single_le_sum (s:=Finset.univ) (fun u _ => bond_zero (show S.Choices from (k.1,fun _=>u)) U i) (mem_univ _)

lemma flag_range (x : ℝ) (A : Stores S) (V : Config G c) (i : Site c) : flag x A V i ∈ Set.Icc (0:ℝ) 1 := by
  unfold flag; split <;> norm_num
lemma prod_ne (X : Type*) [DecidableEq X] {F : X → ℝ} {s : Finset X} (h : (∏ i ∈ s,F i) ≠ 0) {i : X} (he : i∈s) : F i≠0 := fun hF => h (Finset.prod_eq_zero he hF)



def profilesHere (x w : ℝ) (q : Chi) (A : Stores S) (U : Config G f) (V : Config G c) (k : S.Choices)
    (N : Support c) (E : Finset (Cell f)) (Y : Finset (Bond c)) :=
  (∏ p∈E, tokenF A q x U p)*(∏ i∈Y, tokenB A q x w U V k i)*(∏ i∈N,flag x A V i)
def prayersHere (k : S.Choices) (U : Config G f) (N : Support c) (M : Finset (Bond c)) :=
  (∏ i∈N,frame k U i)*(∏ i∈M,bond k U i)

def receipts (q : Chi) (A : Stores S) (x w : ℝ) (N : Support c) (E : Finset (Cell f))
    (M : Finset (Bond c)) (U : Config G f) (V : Config G c) (k : S.Choices) :=
  profilesHere x w q A U V k N E M * prayersHere k U N M



lemma unit_product {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hb : b∈Set.Icc (0:ℝ) 1) : a*b∈Set.Icc (0:ℝ) 1 :=
  ⟨mul_nonneg ha.1 hb.1,(mul_le_mul ha.2 hb.2 hb.1 (zero_le_one)).trans (by norm_num)⟩
lemma unit_alphabet (X : Type*) {s : Finset X} (f : X→ℝ) (he : ∀ i ∈ s,f i∈Set.Icc (0:ℝ) 1) :
    (∏ i∈s,f i)∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨Finset.prod_nonneg (fun i hi => (he i hi).1),?_⟩
  calc
    _ ≤ ∏ _i∈s,(1:ℝ) := Finset.prod_le_prod (fun i hi => (he i hi).1) (fun i hi => (he i hi).2)
    _ = _ := by simp

lemma prayers_unit (k : S.Choices) (U : Config G f) (N : Support c) (M : Finset (Bond c))
    (h : S.patch.Branches S.kernel G) : prayersHere k U N M∈Set.Icc (0:ℝ) 1 := by
  unfold prayersHere
  exact unit_product (unit_alphabet _ _ fun i _ => ⟨frame_zero ..,frame_price k U h i⟩)
    (unit_alphabet _ _ (fun i _ => ⟨bond_zero ..,bond_price ..⟩))
lemma profiles_unit (x w : ℝ) (q : Chi) (A : Stores S) (U : Config G f) (V : Config G c) (k : S.Choices)
    (N : Support c) (E : Finset (Cell f)) (M : Finset (Bond c)) : profilesHere x w q A U V k N E M∈Set.Icc (0:ℝ) 1 := by
  unfold profilesHere
  exact unit_product (unit_product (unit_alphabet _ _ (fun i _ => profile_range q A.costs _ _ i))
    (unit_alphabet _ _ (fun i _ => profile_range q A.aisles _ _ i))) (unit_alphabet _ _ (fun i _ => flag_range ..))
lemma receipts_unit (q : Chi) (A : Stores S) (x w : ℝ) (V : Config G c)
    (N : Support c) (E : Finset (Cell f)) (M : Finset (Bond c)) (U : Config G f) (k : S.Choices)
    (h : S.patch.Branches S.kernel G) : receipts q A x w N E M U V k∈Set.Icc (0:ℝ) 1 := by
  exact unit_product (profiles_unit ..) (prayers_unit _ _ _ _ h)

end YM.AnalyticBridge.Annulus1AD
