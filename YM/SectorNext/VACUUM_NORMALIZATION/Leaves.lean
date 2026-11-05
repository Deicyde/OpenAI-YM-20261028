import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Pi.Interval
import Mathlib.Data.ZMod.ValMinAbs
import YM.Space.Index




/-!
# Finite-region incidence algebra for support-separated scalar terms

(`glue` is union convolution, NOT the disjoint-union product. In
particular for the log we do NOT forget repeated/overlapping hits.)
No assumption cover cost is subadditive on arbitrary unions.
Deals also with absolute majorants & the convergent log series when
all addressed terms touch a pin. Coordinates defined on the full Native
torus so support statements can include all visits, intersections and
negative queries. Unrelated to RG ChartRatio.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SectorNext.Vacuum.ReLog
open Finset Function
open scoped BigOperators Classical Topology
variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev Leaf (J : Type*) := Finset J
abbrev Grid (J : Type*) := Leaf J → ℝ

/-- Scalar entry counted against its entire support. -/
def grain (Q : Leaf J) (a : ℝ) : Grid J := fun T => if Q=T then a else 0

def glue (f g : Grid J) (T : Leaf J) := ∑ P,∑ Q,if P ∪ Q=T then f P*g Q else 0

def shed (f : Grid J) (s : Leaf J) := ∑ i ∈ s.powerset,f i

def crop (w f : Grid J) := ∑ i,w i*|f i|

def Pinned (P : Leaf J) (f : Grid J) := ∀ T, f T ≠ 0 → P ⊆ T

/-- Costs, connected-union inequality only. -/
structure Rate (w : Grid J) : Prop where
  pos (P : Leaf J) : 1 ≤ w P
  joined (P Q : Leaf J) : (P ∩ Q).Nonempty → w (P∪Q) ≤ w P*w Q

lemma shed_io (f : Grid J) (s : Leaf J) : shed f s = ∑ i : Leaf J,if i⊆s then f i else 0 := by
  rw [← Finset.sum_filter]
  have h : Finset.univ.filter (fun i : Leaf J => i ⊆ s) = s.powerset := by ext; simp
  rw [h]; rfl

lemma shed_grain (P s : Leaf J) (x : ℝ) : shed (grain P x) s = if P ⊆ s then x else 0 := by
  unfold shed grain
  by_cases h : P⊆s <;> simp [h]

lemma crop_grain (w : Grid J) (P : Leaf J) (x : ℝ) : crop w (grain P x) = w P*|x| := by
  unfold crop grain
  simp [abs_ite,mul_ite]

private lemma shed_filter (P Q s : Leaf J) (x : ℝ) :
    (∑ i∈s.powerset, if P ∪ Q=i then x else 0) = if P ⊆ s ∧ Q ⊆ s then x else 0 := by simp [union_subset_iff]
lemma shed_glue (f g : Grid J) (s : Leaf J) : shed (glue f g) s = shed f s*shed g s := by
  unfold shed glue
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=s.powerset) (t:=Finset.univ),shed_filter]
  rw [show ∑ i∈s.powerset, f i = _ from shed_io f s, show ∑ i∈s.powerset, g i = _ from shed_io g s,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases he : i⊆s <;> by_cases hh : j⊆s <;> simp [he,hh]

lemma shed_fin {ι : Type*} (I : Finset ι) (f : ι → Grid J) (s : Leaf J) :
    shed (fun t => ∑ i∈I,f i t) s = ∑ i∈I,shed (f i) s := sum_comm
lemma shed_add (f g : Grid J) (s : Leaf J) : shed (fun i => f i+g i) s = shed f s+shed g s := by unfold shed; exact Finset.sum_add_distrib
lemma shed_inj : Injective (shed (J:=J)) := by
  intro f g h; funext i
  induction i using Finset.strongInduction with
  | H i ih =>
    have he := congr_fun h i
    unfold shed at he
    rw [←insert_erase (s:= i.powerset) (a:=i) (by simp),Finset.sum_insert (Finset.notMem_erase _ _), Finset.sum_insert (Finset.notMem_erase _ _)] at he
    have hf := Finset.sum_congr (s₁:=i.powerset.erase i) (s₂:=i.powerset.erase i) rfl (fun j hj =>
      ih j (by obtain ⟨hh,hy⟩ := mem_erase.mp hj; exact Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hy,hh⟩))
    rwa [hf,add_left_inj] at he

lemma crop_nonneg {w : Grid J} (h : Rate w) (f : Grid J) : 0≤crop w f := sum_nonneg fun i _ => mul_nonneg (zero_le_one.trans (h.pos i)) (abs_nonneg _)
lemma crop_point {w : Grid J} (h : Rate w) (f : Grid J) (i : Leaf J) : |f i| ≤ crop w f :=
  (le_mul_of_one_le_left (abs_nonneg _) (h.pos i)).trans <| Finset.single_le_sum (fun j _ => mul_nonneg (zero_le_one.trans (h.pos j)) (abs_nonneg (f j))) (mem_univ i)
lemma crop_shed {w : Grid J} (h : Rate w) (f : Grid J) (S : Leaf J) : |shed f S| ≤ crop w f := by
  rw [shed_io]; apply (abs_sum_le_sum_abs ..).trans
  refine sum_le_sum fun i _ => ?_
  split
  · exact le_mul_of_one_le_left (abs_nonneg _) (h.pos i)
  rw [abs_zero]; exact mul_nonneg (zero_le_one.trans (h.pos _)) (abs_nonneg _)
lemma crop_fin {ι : Type*} {w : Grid J} (h : Rate w) (I : Finset ι) (f : ι → Grid J) :
    crop w (fun t => ∑ i∈I,f i t) ≤ ∑ i∈I,crop w (f i) := by
  unfold crop; rw [Finset.sum_comm]; refine sum_le_sum fun i _ => ?_; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (zero_le_one.trans (h.pos _))
lemma crop_add {w : Grid J} (h : Rate w) (f g : Grid J) : crop w (fun i => f i+g i) ≤ crop w f+crop w g := by
  unfold crop; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _ => ?_
  rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le ..) (zero_le_one.trans (h.pos i))

lemma grain_pin (P : Leaf J) (x : ℝ) : Pinned P (grain P x) := by intro i hi; unfold grain at hi; split at hi; subst i; rfl; contradiction
lemma pin_glue {P : Leaf J} {f g : Grid J} (h : Pinned P f) : Pinned P (glue f g) := by
  intro T ht
  contrapose! ht
  unfold glue
  refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
  split; swap; rfl
  have he : i⊆T := ‹i ∪ _ = T› ▸ subset_union_left
  rw [show f i=0 from by
    by_contra e; exact ht ((h i e).trans he),zero_mul]

/-- Sum estimate only under touching supports (charged on the true
connected cover, not the imagined sum of two covers that could be
arbitrarily far from one another). -/
lemma crop_glue {w f g : Grid J} (h : Rate w)
    (ht : ∀ i j, f i≠0 → g j≠0 → (i ∩ j).Nonempty) : crop w (glue f g) ≤ crop w f * crop w g := by
  unfold crop glue
  calc
    _ ≤ ∑ t : Leaf J,∑ i : Leaf J,∑ j : Leaf J, if i ∪ j=t then w t*(|f i| *|g j|) else (0:ℝ) := by
      refine sum_le_sum fun t _ => ?_
      have he (i j : Leaf J) : (if i ∪ j=t then w t*(|f i| *|g j|) else 0) = w t*|if i∪j=t then f i*g j else 0| := by
        by_cases hh : i∪j=t <;> simp [hh,abs_mul]
      simp_rw [he,← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (h.pos _))
      exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs ..)
    _ = ∑ i, ∑ j, w (i∪j)*(|f i| *|g j|) := by
      rw [Finset.sum_comm]; refine sum_congr rfl fun i _ => ?_; rw [Finset.sum_comm]; simp
    _ ≤ _ := by
      rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]; refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      by_cases hx : f i=0; simp [hx]
      by_cases hy : g j=0; simp [hy]
      exact (mul_le_mul_of_nonneg_right (h.joined i j (ht i j hx hy)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)

lemma glue_mono_abs {u v U V : Grid J} (h : ∀ i,|u i| ≤ U i) (he : ∀ i,|v i| ≤ V i) (i : Leaf J) :
    |glue u v i| ≤ glue U V i := by
  apply (abs_sum_le_sum_abs ..).trans; refine sum_le_sum fun j _ => ?_
  apply (abs_sum_le_sum_abs ..).trans; refine sum_le_sum fun k _ => ?_
  split
  · rw [abs_mul]; exact mul_le_mul (h j) (he k) (abs_nonneg _) ((abs_nonneg _).trans (h _))
  simp

/-- Product recursion for -log(1 - f), starts with f (n+1 factors). -/
def ribbon (f : Grid J) : ℕ → Grid J
  | 0 => f
  | n+1 => glue (ribbon f n) f
lemma pinned_ribbon {P : Leaf J} {f : Grid J} (h : Pinned P f) (n : ℕ) : Pinned P (ribbon f n) := by
  induction n with | zero => exact h | succ n ih => exact pin_glue ih
lemma shed_ribbon (f : Grid J) (n : ℕ) (s : Leaf J) : shed (ribbon f n) s = shed f s^(n+1) := by
  induction n with | zero => simp [ribbon] | succ n ih => rw [ribbon,shed_glue, ih,pow_succ _ (n+1)]
lemma crop_ribbon {w : Grid J} (h : Rate w) {P : Leaf J} (ht : P.Nonempty) (f : Grid J) (hh : Pinned P f) (n : ℕ) :
    crop w (ribbon f n) ≤ (crop w f)^(n+1) := by
  induction n with
  | zero => simp [ribbon]
  | succ n ih =>
    apply (crop_glue h ?_).trans (mul_le_mul_of_nonneg_right ih (crop_nonneg h f) |>.trans_eq (pow_succ ..).symm)
    intro i j hi hj; obtain ⟨x,hx⟩ := ht
    exact ⟨x,mem_inter.mpr ⟨pinned_ribbon hh n i hi hx,hh j hj hx⟩⟩

def lamp (f : Grid J) (i : Leaf J) := ∑' n : ℕ, ribbon f n i / (n+1:ℝ)
lemma lamp_dom {w f : Grid J} (h : Rate w) {P : Leaf J} (ht : P.Nonempty) (hh : Pinned P f)
    (hw : crop w f < 1) (i : Leaf J) : Summable fun n : ℕ => ribbon f n i/(n+1:ℝ) := by
  let q := crop w f
  have hq : 0 ≤ q := crop_nonneg h f
  refine Summable.of_norm_bounded ((Real.hasSum_pow_div_log_of_abs_lt_one (x:=q) (by rwa [abs_of_nonneg hq])).summable) ?_
  intro n; rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : (0:ℝ)<n+1)]
  exact div_le_div_of_nonneg_right ((crop_point h _ i).trans (crop_ribbon h ht f hh _)) (by positivity)
lemma lamp_shed {w f : Grid J} (h : Rate w) {P : Leaf J} (ht : P.Nonempty) (hh : Pinned P f)
    (hw : crop w f < 1) (s : Leaf J) : shed (lamp f) s = -Real.log (1-shed f s) := by
  unfold shed lamp
  rw [← Summable.tsum_finsetSum (fun i _ => lamp_dom h ht hh hw i)]
  simp_rw [← Finset.sum_div]
  change (∑' n : ℕ, shed (ribbon f n) s/_) = -Real.log (1-shed f s)
  simp_rw [shed_ribbon]
  exact (Real.hasSum_pow_div_log_of_abs_lt_one ((crop_shed h f s).trans_lt hw)).tsum_eq

lemma lamp_cropped {w f : Grid J} (h : Rate w) {P : Leaf J} (ht : P.Nonempty) (hh : Pinned P f) (hw : crop w f < 1) :
    crop w (lamp f) ≤ -Real.log (1-crop w f) := by
  let q := crop w f; have hq : 0 ≤ q := crop_nonneg h f
  have hf := Real.hasSum_pow_div_log_of_abs_lt_one (x:=q) (by rwa [abs_of_nonneg hq])
  unfold crop lamp
  calc
    _ ≤ ∑ i : Leaf J,w i * ∑' n : ℕ, ‖ribbon f n i / (n+1:ℝ)‖ :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (lamp_dom h ht hh hw i).norm) (zero_le_one.trans (h.pos i))
    _ = ∑' n : ℕ,crop w (ribbon f n)/(n+1:ℝ) := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun i _ => (lamp_dom h ht hh hw i).norm.mul_left _)]
      apply tsum_congr; intro i; unfold crop; rw [Finset.sum_div]; congr 1; funext j
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : (0:ℝ)< i+1),mul_div_assoc]
    _ ≤ _ := by
      simp only [q] at hf
      change _ ≤ -Real.log (1-crop w f)
      rw [← hf.tsum_eq]
      have hh₁ (n : ℕ) := div_le_div_of_nonneg_right (crop_ribbon h ht f hh n) (by positivity : (0:ℝ)≤n+1)
      exact (hf.summable.of_nonneg_of_le (fun n : ℕ => div_nonneg (crop_nonneg h _) (by positivity)) hh₁).tsum_le_tsum hh₁ hf.summable
lemma lamp_mono {w f F : Grid J} (h : Rate w) {P : Leaf J} (ht : P.Nonempty)
    (h₁ : Pinned P f) (h₂ : Pinned P F) (hh : ∀ i, |f i| ≤ F i) (hw : crop w F < 1) (i : Leaf J) :
    |lamp f i| ≤ lamp F i := by
  have he j := (abs_nonneg _).trans (hh j)
  have hz : crop w f < 1 := lt_of_le_of_lt (b:=crop w F) (sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left ((hh i).trans (abs_of_nonneg (he i)).symm.le) (zero_le_one.trans (h.pos i))) hw
  refine le_trans (norm_tsum_le_tsum_norm (lamp_dom h ht h₁ hz i).norm) ?_
  apply (lamp_dom h ht h₁ hz i).norm.tsum_le_tsum _ (lamp_dom h ht h₂ hw i)
  intro b; rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : (0:ℝ)<b+1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  induction b generalizing i with
  | zero => exact hh _
  | succ b ih => exact glue_mono_abs ih hh _

end YM.SectorNext.Vacuum.ReLog
