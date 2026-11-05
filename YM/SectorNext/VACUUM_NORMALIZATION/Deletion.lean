import YM.SectorNext.VACUUM_NORMALIZATION.Sprig

/-!
# Region deletion re-log and absolute budget

Dobrushin/GK-style site induction rather than graph trees. Here we
lift the deletion argument to *support arrays* (union of touched native
sites). Coefficients are restriction-local (Mobius) pieces of -log Xi,
NOT individual tuple coefficients of Flogg. Even for variable bounded
activities we pay an absolute hit bound on the support pieces **before**
summing them (one common majorant from -fugacity gas). Exclusion of
supports in the forced gas will thus cost local OMITTED pieces only.
Sign: use `Deletion u Xi` where the activity of support i is **-u i**.
Empty polymers not used. Real expansion at actual parameters incl
negative activities; neither positivity of individual activities nor an
implicit choice of complex log of the full partition.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SectorNext.Vacuum.ReLog
open Function Finset
open scoped BigOperators Classical Topology
variable {J : Type*} [Fintype J] [DecidableEq J]

local notation "expo" => Real.exp
local notation "logr" => Real.log

/-- Deletion interface for Xi. Supplied below for actual unforced
disjoint selection. Does NOT assume nonvanishing. -/
structure Deletion (u Z : Grid J) : Prop where
  bottom : Z ∅ = 1
  hole (B : Leaf J) (x : J) : x∈B →
    Z B = Z (B.erase x) - ∑ P ∈ B.powerset.filter (fun P => x∈P), u P*Z (B\P)

/-- Pinned threshold. Inflation in card here, paid via native cover below.
The RHS includes equality, still gives a strict log radius at 1; no
multiplicative spare radius included by default. -/
structure Receipt (w U : Grid J) (a : ℝ) : Prop where
  budget : Rate w
  zero (i : Leaf J) : 0 ≤ U i
  pos : 0 ≤ a
  hits (x : J) : ∑ i ∈ (univ : Finset (Leaf J)).filter (fun i => x∈i), w i*U i*expo (a*i.card) ≤ 1-expo (-a)

/-- Negative-log bulk labels at the given V (V suppressed). -/
def locker (Z : Grid J) := pieces fun A => -logr (Z A)

def neighbors (B : Leaf J) (x : J) (P : Leaf J) := (B.erase x).powerset.filter fun T => (T ∩ P).Nonempty

def owners (B : Leaf J) (x : J) := B.powerset.filter fun P => x∈P

def signal (u Z : Grid J) (B : Leaf J) (x : J) := fun i => ∑ P∈owners B x, sprig (neighbors B x P) P (u P) (locker Z) i
lemma signal_pinned (u Z : Grid J) (B : Leaf J) (x : J) : Pinned {x} (signal u Z B x) := by
  intro i hi; contrapose! hi; unfold signal; apply sum_eq_zero
  intro P he; have hx := (mem_filter.mp he).2
  by_contra ht; exact hi (fun j hj => (mem_singleton.mp hj).symm ▸ pinned_sprig (neighbors B x P) P (u P) (locker Z) i ht hx)

lemma neighbor_parts (f : Grid J) {A B P : Leaf J} {x : J} (h : A ⊆ B.erase x) :
    f A-f (A\P) = ∑ i ∈ neighbors B x P, if i⊆A then pieces f i else 0 := by
  rw [← enact f A,← enact f (A\P),shed,shed, ← Finset.sum_filter]
  let I := (neighbors B x P).filter fun i => i⊆A
  have hh : I=A.powerset.filter (fun i => (i∩P).Nonempty) := by
    ext i; simp only [I,neighbors,mem_filter,mem_powerset]; exact
      ⟨fun h => ⟨h.2,h.1.2⟩,fun ht => ⟨⟨ht.1.trans h,ht.2⟩,ht.1⟩⟩
  change _ = ∑ i∈I,_
  rw [hh]
  have hk : A.powerset.filter (fun i => ¬(i∩P).Nonempty) = (A\P).powerset := by
    ext i; simp only [mem_filter,mem_powerset,Finset.Nonempty,mem_inter]
    constructor
    · rintro ⟨h1,h2⟩ j hj; exact mem_sdiff.mpr ⟨h1 hj,fun e => h2 ⟨j,hj,e⟩⟩
    intro h1; refine ⟨h1.trans sdiff_subset,?_⟩; rintro ⟨j,hj,h2⟩; exact (mem_sdiff.mp (h1 hj)).2 h2
  have hz := Finset.sum_filter_add_sum_filter_not A.powerset (fun i => (i∩P).Nonempty) (pieces f)
  rw [hk] at hz; linarith only [hz]

lemma matures {u Z : Grid J} (h : Deletion u Z) {B : Leaf J} {x : J} (_ : x∈B)
    (he : ∀ A, A ⊆ B.erase x → 0<Z A) (A : Leaf J) (ht : A⊆B) :
    Z A = Z (A.erase x)*(1 - shed (signal u Z B x) A) := by
  unfold signal; rw [shed_fin]; simp_rw [sprig_shed]; rw [mul_sub, mul_one,Finset.mul_sum]
  by_cases ha : x∈A; swap
  · rw [erase_eq_of_notMem ha, sum_eq_zero,sub_zero]
    intro i hi
    rw [if_neg (show ¬ i⊆A from fun H => ha (H (mem_filter.mp hi).2)),mul_zero]
  rw [h.hole A x ha]; apply congr_arg
  change ∑ i∈owners A x,u i*Z _ = _
  rw [show owners A x = (owners B x).filter (fun i => i⊆A) by ext i; simp only [owners,mem_filter,mem_powerset]; exact
    ⟨fun h => ⟨⟨h.1.trans ht,h.2⟩,h.1⟩,fun h => ⟨h.2,h.1.2⟩⟩,Finset.sum_filter]
  apply sum_congr rfl; intro P hp
  split <;> rename_i hy
  · have hh := erase_subset_erase x ht
    have hg := (mem_filter.mp hp).2
    have hl : A \ P ⊆ A.erase x := subset_erase.mpr ⟨sdiff_subset,fun H => (mem_sdiff.mp H).2 hg⟩
    have hk := neighbor_parts (fun A => -logr (Z A)) (B:=B) (P:=P) hh
    have hv : A.erase x \ P = A \ P := by
      ext i; constructor
      · intro h; obtain ⟨h1,h2⟩ := mem_sdiff.mp h; exact mem_sdiff.mpr ⟨mem_of_mem_erase h1,h2⟩
      intro h; obtain ⟨h1,h2⟩ := mem_sdiff.mp h
      exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun e => h2 (e.symm ▸ hg),h1⟩,h2⟩
    rw [hv] at hk
    have hw : (∑ i∈neighbors B x P, if i⊆A then locker Z i else 0) =
        ∑ i∈neighbors B x P, if i⊆A.erase x then locker Z i else 0 := by
      apply sum_congr rfl; intro i hi
      have he := mem_powerset.mp (mem_filter.mp hi).1
      have h0 : i⊆A.erase x ↔ i⊆A := ⟨fun h => h.trans (erase_subset ..),fun h => subset_erase.mpr ⟨h, fun hh => notMem_erase x B (he hh)⟩⟩
      simp [h0]
    rw [hw,locker,←hk,sub_neg_eq_add,Real.exp_add,Real.exp_neg,Real.exp_log (he _ hh),Real.exp_log (he _ (hl.trans hh))]; field_simp [(he _ hh).ne']
  simp

/-- Terms meeting P (not x) can be paid per y∈P. -/
private lemma fan {w Y : Grid J} {a : ℝ} {B : Leaf J} {x : J} {P : Leaf J} (hA : 0 ≤ a) (hP : P ⊆ B)
    (h : Rate w) (hY : ∀ i⊆B.erase x,0 ≤ Y i)
    (ht : ∀ y∈ B.erase x, ∑ i ∈ owners (B.erase x) y, w i * Y i ≤ a) :
    ∑ i∈neighbors B x P,w i*Y i ≤ a * P.card := by
  have hz := Finset.sum_le_sum (s:=neighbors B x P) (g:=fun i => ∑ y∈P,if y∈i then w i*Y i else 0)
    (f:=fun i=>w i*Y i) (fun i hi => by
      obtain ⟨hh,hh'⟩ := mem_filter.mp hi; obtain ⟨y,hk⟩ := hh'
      exact (if_pos (mem_inter.mp hk).1).symm.le.trans (Finset.single_le_sum (f:=fun y=>if y∈i then w i*Y i else 0) (fun j _ => by
        split; exact mul_nonneg (zero_le_one.trans (h.pos _)) (hY _ (mem_powerset.mp hh)); rfl) (mem_inter.mp hk).2))
  apply hz.trans; rw [sum_comm]
  have ha : ∀ y∈P,(∑ i∈neighbors B x P,if y∈i then w i*Y i else 0) ≤ a := by
    intro y hy; by_cases he : y=x
    · subst y
      -- need nonneg a (may not come from hits on empty B-x)
      simp only [←Finset.sum_filter]
      have h0 : ((neighbors B x P).filter fun i => x∈i) = ∅ := eq_empty_iff_forall_notMem.mpr fun i hi => by
        obtain ⟨hv,hy⟩ := mem_filter.mp hi
        exact notMem_erase x B (mem_powerset.mp (mem_filter.mp hv).1 hy)
      rw [h0,sum_empty]; exact hA
    refine le_trans ?_ (ht y (mem_erase.mpr ⟨he,hP hy⟩))
    rw [← Finset.sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hi).1).1,(mem_filter.mp hi).2⟩
    intro i hi _; exact mul_nonneg (zero_le_one.trans (h.pos _)) (hY _ (mem_powerset.mp (mem_filter.mp hi).1))
  exact (sum_le_sum ha).trans (le_of_eq (by simp [mul_comm]))

/-- Compare arbitrary signed activities to negative fugacity gas. -/
private lemma signal_pay {U z Z L w : Grid J} {a : ℝ} (h : Receipt w U a) (hu : ∀ i,|z i| ≤ U i)
    {B : Leaf J} {x : J} (_ : x∈B)
    (he : ∀ i⊆B.erase x, |locker L i| ≤ locker Z i) (hN : ∀ y∈ B.erase x,
      ∑ i∈owners (B.erase x) y,w i*locker Z i ≤ a) :
    (∀ i, |signal z L B x i| ≤ signal U Z B x i) ∧ crop w (signal U Z B x) ≤ 1-expo (-a) := by
  have hi (P : Leaf J) (t : Leaf J) (ht : t∈neighbors B x P) := he t (mem_powerset.mp (mem_filter.mp ht).1)
  refine ⟨fun i => (abs_sum_le_sum_abs ..).trans (sum_le_sum fun P hP => sprig_compare (z P) (U P) (hu _) _ _ (neighbors B x P) (hi P) i),?_⟩
  apply (crop_fin h.budget _ _).trans
  apply le_trans (b:=∑ i∈owners B x,w i*U i*expo (a*i.card)) _
    (le_trans (b:=∑ i ∈ (univ : Finset (Leaf J)).filter (fun i => x∈i), _) ?_ (h.hits x))
  swap
  · apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
    intro i _ _; have := h.zero i; have hh := h.budget.pos i; positivity
  refine sum_le_sum fun i hP => ?_
  have hh v hv := (abs_nonneg (locker L v)).trans (he v hv)
  refine (sprig_cost h.budget _ _ _ (fun t ht => (mem_filter.mp ht).2) (fun t ht => (abs_nonneg _).trans (hi i t ht))).trans ?_
  rw [abs_of_nonneg (h.zero _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (fan h.pos (mem_powerset.mp (mem_filter.mp hP).1) h.budget hh hN)) (mul_nonneg (zero_le_one.trans (h.budget.pos _)) (h.zero _))


private lemma locker_one {u Z w : Grid J} (h : Deletion u Z) {B : Leaf J} {x : J} (hx : x∈B)
    (he : ∀ A, A ⊆ B.erase x → 0<Z A) (hw : Rate w) (ht : crop w (signal u Z B x) < 1) :
    0 < Z B ∧ (∀ A⊆B,(if x∈A then locker Z A else 0) = lamp (signal u Z B x) A) := by
  let M := signal u Z B x
  have hg (i : Leaf J) : 0<1-shed M i := sub_pos.mpr ((le_abs_self _).trans_lt ((crop_shed hw M i).trans_lt ht))
  have hZ (A : Leaf J) (hA : A⊆B) : 0<Z A := by
    rw [matures h hx he A hA]; exact mul_pos (he _ (erase_subset_erase x hA)) (hg A)
  refine ⟨hZ B (by rfl),fun A hA => ?_⟩
  refine ((changes (fun A => -logr (Z A)) x A).symm).trans (Eq.symm (from_shed ?_))
  intro C hc
  rw [lamp_shed hw (singleton_nonempty _) (signal_pinned _ _ _ _) ht,matures h hx he C (hc.trans hA), Real.log_mul (he _ (erase_subset_erase x (hc.trans hA))).ne' (hg C).ne']
  ring

private lemma coupon_log (a r : ℝ) (_ : 0 ≤ a) (h : r ≤ 1-expo (-a)) : -logr (1-r) ≤ a := by
  have ht := Real.log_le_log (Real.exp_pos (-a)) (by linarith only [h] : Real.exp (-a) ≤ 1-r)
  rw [Real.log_exp] at ht; linarith only [ht]

/-- Main support-array induction. Z from *negative* envelope activities,
Y from the given signed activities written likewise with a minus. The
very pieces of Z certify the absolute prices on Y (hence no `volume`- or
`alphabet-cardinality`- cost even passing to bounds for families in V).
Interior boundary case x-last is where the log lemma with intersecting
union weights is essential. -/
theorem leash {U z Z Y w : Grid J} {a : ℝ} (hh : Receipt w U a) (hu : ∀ i,|z i| ≤ U i)
    (hZ : Deletion U Z) (hy : Deletion z Y) (B : Leaf J) :
    0<Z B ∧ 0<Y B ∧ |locker Y B| ≤ locker Z B ∧
      ∀ x∈B, ∑ i∈owners B x,w i * locker Z i ≤ a := by
  induction B using Finset.strongInduction with | H B ih
  by_cases hB : B.Nonempty; swap
  · rw [not_nonempty_iff_eq_empty.mp hB,hZ.bottom,hy.bottom,locker,locker, unfold_pieces, unfold_pieces]
    simp [hZ.bottom,hy.bottom]
  have hf (x : J) (hx : x∈B) :
      (0<Z B ∧ ∀ i⊆B,(if x∈i then locker Z i else 0)=lamp (signal U Z B x) i) ∧ 0<Y B ∧
        |locker Y B| ≤ locker Z B ∧ crop w (lamp (signal U Z B x)) ≤ a := by
    have he {i : Leaf J} (hi : i⊆B.erase x) := ih i (Finset.ssubset_iff_subset_ne.mpr ⟨hi.trans (erase_subset ..),by
      intro he; subst i; exact notMem_erase x B (hi hx)⟩)
    obtain ⟨h1,h2⟩ := signal_pay hh hu hx (fun i hi => (he hi).2.2.1) ((ih _ (erase_ssubset hx)).2.2.2)
    let m := signal z Y B x; let M := signal U Z B x
    have ht : crop w M < 1 := h2.trans_lt (by linarith only [Real.exp_pos (-a)])
    have hl : crop w m < 1 := lt_of_le_of_lt (b:=crop w M) (sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left ((h1 i).trans (le_abs_self _)) (zero_le_one.trans (hh.budget.pos i))) ht
    let hQ := locker_one hZ hx (fun i hi => (he hi).1) hh.budget ht
    obtain ⟨hp,hw⟩ := locker_one hy hx (fun i hi => (he hi).2.1) hh.budget hl
    have Hm : Pinned {x} m := signal_pinned _ _ _ _; have HM : Pinned {x} M := signal_pinned _ _ _ _
    refine ⟨hQ,hp,?_,(lamp_cropped hh.budget (singleton_nonempty _) HM ht).trans (coupon_log _ _ hh.pos h2)⟩
    have h3 := hQ.2 B (by rfl); have h4 := hw B (by rfl); rw [if_pos hx] at h3 h4; rw [h3,h4]; exact lamp_mono hh.budget (singleton_nonempty _) Hm HM h1 ht _
  obtain ⟨i,hi⟩ := hB
  refine ⟨(hf i hi).1.1,(hf i hi).2.1,(hf i hi).2.2.1,fun x hx => ?_⟩
  apply le_trans _ (hf x hx).2.2.2
  unfold owners crop
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (s:=B.powerset.filter fun i => x∈i) (subset_univ _) fun i _ _ => mul_nonneg (zero_le_one.trans (hh.budget.pos _)) (abs_nonneg _))
  refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans (hh.budget.pos j))
  obtain ⟨hk,hb⟩ := mem_filter.mp hj
  have h := (hf x hx).1.2 j (mem_powerset.mp hk); rw [if_pos hb] at h; rw [h]
  exact le_abs_self _

/-- Assembled, no crop restrictions left; includes whole hit budget
on absolute labels, supports with winding, and zero flags outside.
-/
structure Applied (w Y : Grid J) (a : ℝ) (r : Grid J) : Prop where
  pos (B : Leaf J) : 0 < Y B
  log_form (B : Leaf J) : Y B = expo (- shed (locker Y) B)
  negLog (i : Leaf J) : |locker Y i| ≤ r i
  hits (x : J) : ∑ i∈(univ : Finset (Leaf J)).filter (fun i => x∈i), w i*r i ≤ a

def ceiling (Z : Grid J) := locker Z

theorem swept {U Z w : Grid J} {a : ℝ} (hh : Receipt w U a) (hZ : Deletion U Z)
    {z Y : Grid J} (hu : ∀ i,|z i| ≤ U i) (hy : Deletion z Y) : Applied w Y a (ceiling Z) := by
  have h := leash hh hu hZ hy
  refine ⟨fun i => (h i).2.1,fun i => ?_,fun i => (h i).2.2.1,fun x => ?_⟩
  · unfold locker; rw [enact,neg_neg,Real.exp_log (h i).2.1]
  have ht := (h univ).2.2.2 x (mem_univ _)
  unfold owners at ht
  convert ht using 2
  · ext i; simp
  rfl

end YM.SectorNext.Vacuum.ReLog
