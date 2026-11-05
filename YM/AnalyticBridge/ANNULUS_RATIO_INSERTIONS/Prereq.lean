import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Push.SECTOR_MEASURE.Profile
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Clean


/-!
# Actual compulsory prerequisites through the packet region

Deploy the literal `Chi.profiles` allocation. Keep all comparisons
of these typed seed and flag sites through the halo of interest, frame
mass factors (and connector masses also here) through same halo including
defaults further out than H1; H1 shortcut would need another (analytic-branch)
argument, we retain the factors rather than take that shortcut. Exact split
leaves profiles and actual masses elsewhere. Do not need positively selected
predictor tag data *eligibility* in regions where noise likelihood not used
but keep them anyway; these are the same t choices throughout.

The incoming flag-coverage condition is also kept on the addresses below;
use with the same K list before/after restoring defaults. The K support
and actual fine nondefault incidence may force extra joining; not
attempting that enumeration. This is staying conditional on the K-list,
and deliberately NOT pulling part of a K address off to pay/prove it
using only the data of this packet. See `K...` adapter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Dress
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
   
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure  
open SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Per-address factors, avoiding any claim of disjoint profiles. -/
def address {ι : Type*} [DecidableEq ι] (q : Chi) (s : Finset ι) (r : ι → ℝ) (t : ℝ) (i : ι) :=
  if i∈s then 1-q.innerShare t (r i) else q.innerShare t (r i)

lemma full {ι : Type*} [Fintype ι] [DecidableEq ι] (q : Chi) (s : Finset ι) (r : ι → ℝ) (t : ℝ) :
    (∏ i, address q s r t i) = q.share s r t := by
  unfold address
  rw [Finset.prod_ite]; unfold Chi.share
  have ht {p : Finset ι} : (Finset.univ.filter fun i => i∈p) = p := by ext; simp
  rw [ht]
  have hx : (Finset.univ.filter fun i => i∉s)=sᶜ := by ext; simp
  rw [hx]

lemma tiny {ι : Type*} [DecidableEq ι] (q : Chi) (s : Finset ι) (r : ι → ℝ) (t : ℝ) (i : ι) :
    address q s r t i ∈ Set.Icc 0 1 := by
  have hi : q.innerShare t (r i) ∈ Set.Icc (0:ℝ) 1 := q.range _
  unfold address; split
  · rcases hi with ⟨h,t⟩; constructor <;> linarith
  exact hi

lemma live {ι : Type*} [DecidableEq ι] (q : Chi) (s : Finset ι) (r : ι → ℝ) (t : ℝ) (i : ι)
    (ht : 0 < t) (he : 0 ≤ r i) (hh : address q s r t i ≠0) :
    (i∈s → t < r i) ∧ (i∉s → r i <2*t) := by
  constructor
  · intro hi
    rw [address,if_pos hi] at hh; exact q.exterior_gt _ _ he ht hh
  intro hi
  rw [address,if_neg hi] at hh; exact q.chosen_lt _ _ ht hh

lemma address_meas {ι X : Type*} [DecidableEq ι] [MeasurableSpace X] (q : Chi) (s : Finset ι)
    (r : X → ι → ℝ) (t : ℝ) (i : ι) (he : Measurable (fun x => r x i)) : Measurable (fun x => address q s (r x) t i) := by
  have hm : Measurable (fun x => q.innerShare t (r x i)) := q.smooth.continuous.measurable.comp ((he.div_const t).pow_const 2)
  unfold address; split
  · exact measurable_const.sub hm
  exact hm

/-- Tag densities at actual U with actual shared t. -/
def rooted (U : Config G f) (k : S.Choices) (x : Site c) :=
  S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) (k.1 x)

def forecast (U : Config G f) (k : S.Choices) (b : Bond c) :=
  S.patch.predictorMass S.kernel (S.connector U k.1 b) (k.2 b)

lemma tag_range (U : Config G f) (k : S.Choices) (h : S.patch.Branches S.kernel G) :
    (∀ i, rooted U k i ∈ Set.Icc (0:ℝ) 1) ∧ ∀ b, forecast U k b ∈ Set.Icc (0:ℝ) 1 := by
  have he (Y : CoverConfig G) (i : S.patch.FrameTag) : 0 ≤ S.patch.frameMass S.kernel Y i := by
    unfold Patch.frameMass; split; next _ => positivity
    split <;> positivity
  have hb (Y : S.patch.Connector G) (i : S.patch.Points) : 0 ≤ S.patch.predictorMass S.kernel Y i := by
    unfold Patch.predictorMass; split; next _ => positivity
    exact Patch.weight_nonneg _ _
  constructor
  · intro i
    unfold rooted
    refine ⟨he _ _,?_⟩
    rw [← S.patch.frameMass_sum h (expandAt (S.ratio.embed i) U)]
    exact Finset.single_le_sum (fun a _ => he (expandAt (S.ratio.embed i) U) a) (Finset.mem_univ (k.1 i))
  intro b
  unfold forecast
  refine ⟨hb _ _,?_⟩
  rw [← S.patch.predictorMass_sum (C:=S.kernel) (S.connector U k.1 b)]
  exact Finset.single_le_sum (fun a _ => hb (S.connector U k.1 b) a) (Finset.mem_univ (k.2 b))

lemma tag_meas (k : S.Choices) (h : S.patch.Branches S.kernel G) :
    (∀ i,Measurable (fun U : Config G f => rooted U k i)) ∧
      ∀ b, Measurable (fun U : Config G f => forecast U k b) := by
  constructor
  · intro i
    unfold rooted; apply (S.patch.frameMass_meas _).comp
    have ht : Continuous (fun U : Config G f => expandAt (S.ratio.embed i) U) := by unfold expandAt; fun_prop
    exact ht.measurable
  intro b
  exact (S.patch.predictorMass_meas _).comp (S.connector_meas h k.1 b)

/-- Keep output predicate as individual checks (in testing and any subsequent estimates).
Final use inside `Allocation.bill.profiles` implements all these. -/
def signal (A : Stores S) (t : ℝ) (V : Config G c) (i : Site c) : ℝ :=
  if (i ∈ A.flags ↔ i ∈ RG.flags t V) then 1 else 0



lemma signal_one {A : Stores S} {t : ℝ} {V : Config G c} {i : Site c} (h : signal A t V i ≠0) :
    i∈A.flags ↔ i∈RG.flags t V := by
  unfold signal at h; split at h; assumption; exact (h rfl).elim

variable (O A : Stores S) (x W : ℝ) (V : Config G c) (k : S.Choices) (U : Config G f) (q : Chi)

/-- Core/extended compulsory decisions e.g. out to H300 (D≤200);
anchor test **incident** on every coarse noise bond and every physical
fine plaquette. Keep same tag denominators and tag alphabet as StepData
(uniform-reference conversion is separate). -/
def qFaces (R : ℕ) : Finset (Cell f) := Finset.univ.filter fun i => ¬Disjoint (O.dome R) (startPos S i)
def qBonds (R : ℕ) : Finset (Bond c) := Finset.univ.filter fun i => ¬Disjoint (O.dome R) (pinPos i)

def localSite (i : Site c) := signal A (temp x) V i * rooted U k i
def localNoise (i : Bond c) := address q A.aisles (wire (S.prediction U k) V) (W*fiery G x S.patch.L) i * forecast U k i
def localPlaque : Cell f → ℝ := address q A.costs (toll U) (fiery G x S.patch.L / 4)

def multi (p : Support c) (b : Finset (Bond c)) (h : Finset (Cell f)) : ℝ :=
  ((∏ i∈p, localSite A x V k U i) * ∏ i∈b, localNoise A x W V k U q i) *
    ∏ i∈h, localPlaque A x U q i

def insist (R : ℕ) := multi A x W V k U q (O.dome R) (qBonds O R) (qFaces O R)





private lemma rate_mul {a b : ℝ} (h : a∈Set.Icc 0 1) (ht : b∈Set.Icc 0 1) : a*b∈Set.Icc 0 1 :=
  ⟨mul_nonneg h.1 ht.1,(mul_le_mul h.2 ht.2 ht.1 zero_le_one).trans (by norm_num)⟩
private lemma rate_join {α : Type*} (a : Finset α) (b : α→ℝ) (h : ∀ i,b i∈Set.Icc 0 1) : (∏ i∈a,b i)∈Set.Icc 0 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (h i).1), (Finset.prod_le_prod (fun i (_:i∈a) => (h i).1) (fun i _ => (h i).2)).trans (by simp)⟩

lemma multi_range (h : S.patch.Branches S.kernel G) (P : Support c) (B : Finset (Bond c)) (E : Finset (Cell f)) :
    multi A x W V k U q P B E ∈ Set.Icc (0:ℝ) 1 := by
  have hv := tag_range U k h
  refine rate_mul (rate_mul (rate_join _ _ (fun i => rate_mul (show signal A _ V i ∈ Set.Icc _ _ from by
    unfold signal; split <;> simp) (hv.1 i))) (rate_join _ _ (fun i => rate_mul (tiny ..) (hv.2 i)))) (rate_join E _ (fun i => tiny ..))

/-- Keep the shared profile through the D+5 halo. On its nonzero set
have all of the oriented sector prerequisites (use `turn_wide` at that
same k). No assumption on fields realizing other defaults. -/
lemma insists {D R : ℕ} (hR : (D+5)*radiusB x ≤ R)
    (hW : 0<W) (hf : 0 < fiery G x S.patch.L) (h : S.patch.Branches S.kernel G)
    (he : insist O A x W V k U q R ≠ 0) : Wide O A D x W U k V := by
  unfold insist multi at he; have ht := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul he)
  have hh := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul he))
  have hi := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul (left_ne_zero_of_mul he))
  have hx : O.dome ((D+5)*radiusB x) ⊆ O.dome R := Corona.halo_mono hR (fun _ h => h)
  constructor
  · intro i hy
    have hm : i∈qFaces O R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hu => hy (hu.mono_left hx)⟩
    obtain ⟨h1,h2⟩ := live q A.costs _ _ i (div_pos hf (by norm_num)) (G.chord_nonneg (faceValue U i)) (ht i hm)
    exact ⟨fun he => (h1 he).le,fun he => by linarith [h2 he]⟩
  · intro i hy
    have hm : i∈qBonds O R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hu => hy (hu.mono_left hx)⟩
    have hs := left_ne_zero_of_mul (hh i hm)
    obtain ⟨h1,h2⟩ := live q A.aisles _ _ i (mul_pos hW hf) (show 0 ≤ wire (S.prediction U k) V i from G.chord_nonneg _) hs
    exact ⟨fun hv => (h1 hv).le,fun hv => by rw [mul_assoc]; exact (h2 hv).le⟩
  · intro i hy
    exact signal_one (left_ne_zero_of_mul (hi i (hx hy)))
  intro i hy; exact (tag_range U k h).1 i |>.1.lt_of_ne' (right_ne_zero_of_mul (hi i (hx hy)))

/-- Only promise Borel at fixed V,k. -/
lemma multi_meas (h : S.patch.Branches S.kernel G) (P : Support c) (B : Finset (Bond c)) (E : Finset (Cell f)) :
    Measurable (fun U : Config G f => multi A x W V k U q P B E) := by
  have hv := tag_meas k h
  have hI i : Measurable (fun U : Config G f => localSite A x V k U i) := measurable_const.mul (hv.1 i)
  have hP i : Measurable (fun U : Config G f => toll U i) := by unfold toll faceValue; fun_prop
  have hQ i : Measurable (fun U : Config G f => wire (S.prediction U k) V i) := by
    unfold wire; have he := (measurable_pi_apply i).comp (S.prediction_meas h k)
    exact G.continuous_chord.measurable.comp (measurable_const.mul he.inv)
  have hJ i : Measurable (fun U : Config G f => localPlaque A x U q i) := address_meas _ _ _ _ i (hP i)
  have hK i : Measurable (fun U : Config G f => localNoise A x W V k U q i) :=
    (address_meas q A.aisles (fun U : Config G f => wire (S.prediction U k) V) _ i (hQ i)).mul (hv.2 i)
  exact ((Finset.measurable_fun_prod _ fun i _ => hI i).mul (Finset.measurable_fun_prod _ fun i _=> hK i)).mul
    (Finset.measurable_fun_prod _ fun i _ => hJ i)

end YM.AnalyticBridge.AnnulusRatioInsertions.Dress
