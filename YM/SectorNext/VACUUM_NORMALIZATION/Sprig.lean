import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import YM.SectorNext.VACUUM_NORMALIZATION.Leaves


/-!
# Restriction-local pieces and exponential payment at a pin

Using ordered products for deletion, *not* assuming the graph
exponential formula. Starting from one grain Q (guaranteed even
when a weight vanishes), glue any number of supports T meeting Q.
Dependency stencil grows, but pays only for connected unions. Uses
arbitrary explicit order on the physical indices, consistently.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SectorNext.Vacuum.ReLog
open Finset Function
open scoped BigOperators Classical Topology
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Mobius inversion on a finite region, with the convenient restriction law. -/
def pieces (f : Grid J) (i : Leaf J) : ℝ := f i - ∑ s : {s // s∈i.powerset.erase i}, pieces f s.val
termination_by i.card
decreasing_by
  have h := s.property
  obtain ⟨h',hh⟩ := Finset.mem_erase.mp h
  exact Finset.card_lt_card (show s.val ⊂ i from Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hh,h'⟩)

lemma unfold_pieces (f : Grid J) (i : Leaf J) : pieces f i = f i - ∑ s∈i.powerset.erase i,pieces f s := by
  rw [pieces,sum_subtype (p:=fun s => s∈i.powerset.erase i) _ (fun i => Iff.rfl)]
lemma enact (f : Grid J) (i : Leaf J) : shed (pieces f) i = f i := by
  unfold shed
  rw [←insert_erase (s:=i.powerset) (a:=i) (by simp),Finset.sum_insert (notMem_erase _ _),unfold_pieces]; ring
lemma allocation (f : Grid J) : pieces (shed f)=f := shed_inj (funext (enact (shed f)))
lemma pieces_by {f g : Grid J} {i : Leaf J} (h : ∀ v : Leaf J,v ⊆ i → f v=g v) : pieces f i=pieces g i := by
  induction i using Finset.strongInduction with
  | H i ih =>
    rw [unfold_pieces, unfold_pieces, h i (by rfl)]
    congr 1
    apply sum_congr rfl; intro j he
    obtain ⟨ht,hk⟩ := mem_erase.mp he
    exact ih j (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hk, ht⟩) fun s hs => h s (hs.trans (mem_powerset.mp hk))
lemma from_shed {f g : Grid J} {i : Leaf J} (h : ∀ v : Leaf J,v ⊆ i → shed f v=g v) : f i=pieces g i := by
  have ht := pieces_by h; rw [allocation] at ht; exact ht
lemma shed_changes (f : Grid J) (x : J) :
    (fun A => f A - f (A.erase x)) = shed (fun i => if x∈i then pieces f i else 0) := by
  funext A
  have he : f (A.erase x) = ∑ i∈A.powerset, if x∈i then 0 else pieces f i := by
    simp_rw [show ∀ i : Leaf J,(if x∈i then (0:ℝ) else pieces f i)= if x∉i then pieces f i else 0 from fun i=> by by_cases h : x∈i <;> simp [h]]
    rw [← Finset.sum_filter]
    rw [←enact f, shed]
    congr 1
    ext s
    simp only [mem_filter,mem_powerset]
    exact subset_erase
  rw [he,←enact f A,shed,←Finset.sum_sub_distrib,shed]
  apply sum_congr rfl; intro s _; split <;> simp
lemma changes (f : Grid J) (x : J) (i : Leaf J) :
    pieces (fun A => f A-f (A.erase x)) i= if x∈i then pieces f i else 0 := by rw [shed_changes,allocation]

-- Multiply by the idempotent exponential of a single coordinate.
def sell (f : Grid J) (g : Grid J) (T : Leaf J) : Grid J :=
    fun i => f i + glue f (grain T (Real.exp (g T)-1)) i
lemma shed_sell (f g : Grid J) (T A : Leaf J) : shed (sell f g T) A =
    shed f A * (if T ⊆ A then Real.exp (g T) else 1) := by
  unfold sell; rw [shed_add,shed_glue,shed_grain]
  split <;> ring
lemma pinned_sell (P : Leaf J) (f g : Grid J) (T : Leaf J) (h : Pinned P f) :
    Pinned P (sell f g T) := by
  intro i hi; contrapose! hi; unfold sell
  rw [show f i=0 from by by_contra e; exact hi (h i e), show glue _ _ i = 0 from by
    by_contra e; exact hi (pin_glue h i e),add_zero]

-- weighted budget increment. w≥1 permits the activity exponent times w *inside* an exponential
private lemma exp_stairs {a : ℝ} (_ : 0 ≤ a) {y : ℝ} (hy : 1 ≤ y) :
    1 + y * (Real.exp a-1) ≤ Real.exp (y*a) := by
  have he : 0<y := zero_lt_one.trans_le hy
  -- exp a = exp (0*(1-1/y)+y*a/y); convex!
  have hx : 1/y ≤ 1 := (div_le_one he).mpr hy
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (y*a)) (show 0 ≤ 1-1/y by linarith) (show 0 ≤ 1/y by positivity) (by ring)
  rw [smul_eq_mul,smul_eq_mul,mul_zero,zero_add,show 1/y*(y*a)=a by field_simp,
    smul_eq_mul,smul_eq_mul,Real.exp_zero,mul_one] at h
  field_simp at h; linarith only [h]
lemma sell_price {w f g : Grid J} (h : Rate w) {P : Leaf J} (hp : Pinned P f) (T : Leaf J)
    (he : (T∩P).Nonempty) (hg : 0 ≤ g T) : crop w (sell f g T) ≤ crop w f * Real.exp (w T*g T) := by
  unfold sell
  apply (crop_add h f _).trans
  have hx : crop w (glue f (grain T (Real.exp (g T)-1))) ≤ crop w f*crop w (grain T (Real.exp (g T)-1)) := by
    apply crop_glue h; intro i j hi hj
    obtain ⟨x,hx⟩ := he; exact ⟨x,mem_inter.mpr ⟨hp i hi (mem_inter.mp hx).2,grain_pin T _ j hj (mem_inter.mp hx).1⟩⟩
  rw [crop_grain,abs_of_nonneg (by linarith only [Real.one_le_exp hg])] at hx
  have hv := mul_le_mul_of_nonneg_left (exp_stairs hg (h.pos T)) (crop_nonneg h f)
  rw [mul_add,mul_one] at hv; linarith only [hv,hx]

private lemma diff_exp (a c : ℝ) (h : |a| ≤ c) : |Real.exp a-1| ≤ Real.exp c - 1 := by
  have hh := Real.exp_le_exp.mpr (show a ≤ c from le_of_abs_le h)
  have hv := Real.exp_le_exp.mpr (show -a ≤ c from neg_le.mp (neg_le_of_abs_le h))
  have hx : 2*(1:ℝ) ≤ Real.exp (-a) + Real.exp a := by
    linarith only [Real.add_one_le_exp a,Real.add_one_le_exp (-a)]
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma sell_compare (f g F G : Grid J) (T : Leaf J) (hf : ∀ i,|f i| ≤ F i) (hg : |g T| ≤ G T) (i : Leaf J) :
    |sell f g T i| ≤ sell F G T i := by
  apply (abs_add_le ..).trans (add_le_add (hf _) _)
  apply glue_mono_abs hf _; intro P
  unfold grain; split
  · exact diff_exp _ _ hg
  simp

/-- Finite W-window recursive contribution. Bottom item with support P. -/
def grow (I : List (Leaf J)) (P : Leaf J) (x : ℝ) (g : Grid J) : Grid J :=
    match I with
    | [] => grain P x
    | T::b => sell (grow b P x g) g T
lemma pinned_grow (I : List (Leaf J)) (P : Leaf J) (x : ℝ) (g : Grid J) : Pinned P (grow I P x g) := by
  induction I with | nil => exact grain_pin _ _ | cons a b ih => exact pinned_sell _ _ _ _ ih
lemma shed_grow (I : List (Leaf J)) (P : Leaf J) (x : ℝ) (g : Grid J) (A : Leaf J) : shed (grow I P x g) A =
    if P ⊆ A then x * Real.exp ((I.map fun T => if T⊆A then g T else 0).sum) else 0 := by
  induction I with
  | nil => simp [grow,shed_grain]
  | cons a b ih => rw [grow,shed_sell,ih,List.map_cons,List.sum_cons,Real.exp_add]; split <;> split <;> simp [mul_comm,mul_left_comm]
lemma grown_price {w : Grid J} (h : Rate w) {P : Leaf J} (x : ℝ) (g : Grid J) (I : List (Leaf J))
    (he : ∀ T∈I,(T∩P).Nonempty) (hh : ∀ T∈I,0 ≤ g T) :
    crop w (grow I P x g) ≤ w P*|x| * Real.exp ((I.map (fun i => w i*g i)).sum) := by
  induction I with
  | nil => simp [grow,crop_grain]
  | cons a b ih =>
    rw [grow,List.map_cons,List.sum_cons,add_comm,Real.exp_add]
    refine (sell_price h (pinned_grow b P x g) a (he a (.head _)) (hh a (.head _))).trans ((mul_le_mul_of_nonneg_right (ih (fun t ht => he t (.tail _ ht))
      (fun t ht => hh t (.tail _ ht))) (Real.exp_pos _).le).trans_eq (mul_assoc ..))
lemma grown_compare (P : Leaf J) (x y : ℝ) (h : |x| ≤ y) (g G : Grid J) (I : List (Leaf J))
    (hg : ∀ i∈I,|g i| ≤ G i) (i : Leaf J) : |grow I P x g i| ≤ grow I P y G i := by
  induction I generalizing i with
  | nil => unfold grow grain; split; exact h; simp
  | cons a b ih => exact sell_compare _ _ _ _ _ (fun j => ih (fun i hi => hg i (.tail _ hi)) j) (hg a (.head _)) _

/-- Deterministic ordering of the already present finite support pieces. -/
def sprig (I : Finset (Leaf J)) := grow I.toList
lemma sprig_shed (I : Finset (Leaf J)) (P : Leaf J) (x : ℝ) (g : Grid J) (A : Leaf J) :
    shed (sprig I P x g) A = if P ⊆ A then x * Real.exp (∑ T∈I, if T⊆A then g T else 0) else 0 := by
  simp [sprig,shed_grow]
lemma pinned_sprig (I : Finset (Leaf J)) (P : Leaf J) (x : ℝ) (g : Grid J) : Pinned P (sprig I P x g) := pinned_grow I.toList _ _ _
lemma sprig_cost {w : Grid J} (h : Rate w) {P : Leaf J} (x : ℝ) (g : Grid J) (I : Finset (Leaf J))
    (he : ∀ T∈I,(T∩P).Nonempty) (hh : ∀ T∈I,0 ≤ g T) :
    crop w (sprig I P x g) ≤ w P*|x| * Real.exp (∑ i∈I,w i*g i) := by
  simpa [sprig,Finset.sum_toList] using grown_price h x g I.toList (fun T ht => he T (by simpa using ht)) (fun T ht => hh T (by simpa using ht))
lemma sprig_compare {P : Leaf J} (x y : ℝ) (h : |x| ≤ y) (g G : Grid J) (I : Finset (Leaf J))
    (hg : ∀ i∈I,|g i| ≤ G i) (i : Leaf J) : |sprig I P x g i| ≤ sprig I P y G i :=
  grown_compare P x y h g G I.toList (fun i hi => hg i (by simpa using hi)) i

end YM.SectorNext.Vacuum.ReLog
