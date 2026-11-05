import YM.Push.ABSOLUTE_SUMS.Forest
import YM.Push.ABSOLUTE_SUMS.Ursell

/-!
Occurrence indexing by Option (Fin m) for convenience, equivalently
number `1+m` of vertices, using exponent weight on ACTUAL union. We
also export the *stronger bound* with PRODUCT of the support weights,
so the summability of marks/cost-polynomials can be tested before
regrouping them. Uses a concrete conflict relation R (usually `blocked X`),
which may even be a subset of overlaps in the test. Thus X here can also
be a handle for a larger B-coverage estimate. Need R symmetric and
including same-address conflicts for the hard-core logarithm meaning;
just `pay` works also for tighter edge filters.

No positivity of the gas, analytic branches or exponential/logarithm
*identity* assumed here. Proves the absolute bounds ON that second
graph series, not a step producing the actual unforced/forced weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Ursell
open Trees Graph RG Lattice Relation Finset
open scoped BigOperators Classical Topology
variable {ι : Type*} (R : ι → ι → Prop) {n : Side}
variable (X : ι → Support n) (B : ℕ)

-- No arity zero term in the cluster/log series
abbrev Tuple (ι : Type*) (m : ℕ) := Option (Fin m) → ι
abbrev Clusters (ι : Type*) := Σ m, Tuple ι m

def unionOf {m : ℕ} (z : Tuple ι m) := univ.biUnion (X ∘ z)
def charge (w : ι → ℝ) (a : ℝ) (i : ι) := w i * Trees.currency B a (X i)

def clusters (w : ι → ℝ) {m : ℕ} (z : Tuple ι m) : ℝ :=
    |coefficient R z| * (∏ i, w (z i)) / (m+1).factorial

/-- Root at an arbitrary tuple position pays possibly different weights u,
using the normalization for ROOT-hit counts (n−1)!. -/
def atVertex (w u : ι → ℝ) {m : ℕ} (j : Option (Fin m)) (z : Tuple ι m) : ℝ :=
    |coefficient R z| * (∏ i, if i=j then u (z i) else w (z i)) / m.factorial

lemma clusters_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {m : ℕ} (z : Tuple ι m) :
    0 ≤ clusters R w z := div_nonneg (mul_nonneg (abs_nonneg _) (prod_nonneg fun i _ => hw _))
      (by positivity)

lemma atVertex_pos {w u : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) {m : ℕ}
    (j : Option (Fin m)) (z : Tuple ι m) : 0 ≤ atVertex R w u j z :=
  div_nonneg (mul_nonneg (abs_nonneg _) (prod_nonneg fun i _ => by
    split
    · exact hu _
    · exact hw _))
      (by positivity)

lemma charge_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ) (i : ι) :
    0 ≤ charge X B w a i := mul_nonneg (hw _) (Real.exp_pos _).le

/-- Only comparison from ACTUAL incompatibilities to estimated overlaps!
Doesn't impose extra incompatibilities on the gas. -/
def Tests := ∀ i j : ι, R i j → Ac.meets X j (X i)

lemma literal_test (hn : ∀ i, (X i).Nonempty) : Tests (blocked X) X := by
  rintro i j (hi|hi)
  · subst j; obtain ⟨x,hx⟩ := hn i; exact ⟨_,hx,hx⟩
  exact hi

abbrev indexRoot {m : ℕ} (z : Tuple ι m) (p : Fin m → Option (Fin m)) : RootAt ι m :=
    (z none,p,z ∘ some)

lemma spanned (h : Tests R X) {m : ℕ} {z : Tuple ι m} {p : Fin m → Option (Fin m)}
    (hp : Graph.sprouts (pot R z) p) : Trees.Sprouts X (X (z none)) p (z ∘ some) := by
  constructor
  · exact hp.1
  intro i
  have he := h _ _ (allow R z (hp.2 i))
  cases hk : p i <;> rw [hk] at he <;> exact he

private lemma test_none (ht : Tests R X) (m : ℕ) (z : Tuple ι m) (w u : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) (a : ℝ) :
    atVertex R (charge X B w a) (charge X B u a) none z ≤
      ∑ p : Fin m → Option (Fin m), rootW X B w u a ⟨m,indexRoot z p⟩ := by
  let W := charge X B w a; let U := charge X B u a
  have hg := Graph.pay (pot R z)
  let P (p : Fin m → Option (Fin m)) : Prop := Graph.sprouts (pot R z) p
  let o := ∏ i : Option (Fin m), if i=none then U (z i) else W (z i)
  have he : o=U (z none)*∏ i : Fin m, W (z (some i)) := by simp [o,Fintype.prod_option]
  have hb : 0 ≤ o := he ▸ mul_nonneg (charge_pos X B hu ..) (prod_nonneg fun i _ => charge_pos X B hw ..)
  change |coefficient R z| * o/m.factorial ≤ _
  calc
    _ ≤ (∑ p, if P p then (1:ℝ) else 0)*o/m.factorial := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hg hb) (by positivity)
    _ ≤ _ := by
      rw [sum_mul,sum_div]; apply sum_le_sum; intro i _; split
      next h =>
        unfold rootW forestW; dsimp only; rw [forestWeight,if_pos (spanned R X ht h),Fintype.card_fin,
          he,one_mul,mul_div_assoc]; exact le_rfl
      next h => simpa only [zero_mul,zero_div] using rootW_nonneg X B hw hu a ⟨m,indexRoot z i⟩

private lemma indexRoot_inj {m : ℕ} : Function.Injective
    (fun p : Tuple ι m × (Fin m → Option (Fin m)) => indexRoot p.1 p.2) := by
  rintro ⟨z,p⟩ ⟨w,q⟩ h
  have hp : p=q := congr_arg (fun x => x.2.1) h
  suffices he : z=w by rw [he,hp]
  funext i; cases i with
  | none => exact congr_arg (fun x => x.1) h
  | some j => exact congr_arg (fun x : RootAt ι m => x.2.2 j) h

private lemma budget_none (ht : Tests R X) {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (charge X B u (a+δ)) b)
    (m : ℕ) : SumBudget (fun z : Tuple ι m => atVertex R (charge X B w a) (charge X B u a) none z)
      (b*q^m) := by
  have hw := h.2.2.2.2.1
  have hh := budget_pull _ (@indexRoot_inj ι m) (root_at X B hu h he m)
  let f := fun p : Tuple ι m × (Fin m → Option (Fin m)) => rootW X B w u a ⟨m,indexRoot p.1 p.2⟩
  refine budget_of_sum (fun z => atVertex_pos R (charge_pos X B hw a) (charge_pos X B hu a) none z)
    fun s => ?_
  calc
    _ ≤ ∑ z∈s, ∑ p, f (z,p) := sum_le_sum fun z _ => test_none R X B ht m z w u hw hu a
    _ = ∑ i∈s ×ˢ univ, f i := by rw [sum_product]
    _ ≤ _ := budget_sum hh _

lemma budget_root (ht : Tests R X) {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (charge X B u (a+δ)) b)
    (m : ℕ) (i : Option (Fin m)) :
    SumBudget (fun z : Tuple ι m => atVertex R (charge X B w a) (charge X B u a) i z) (b*q^m) := by
  let e := Equiv.swap i none
  let W := charge X B w a; let U := charge X B u a
  have he' : Function.Injective (fun z : Tuple ι m => z ∘ e) := fun z p h => by
    funext i; obtain ⟨i,rfl⟩ := e.surjective i; exact congr_fun h i
  have eq (z : Tuple ι m) : atVertex R W U i z = atVertex R W U none (z ∘ e) := by
    unfold atVertex
    rw [relabel R e z]; congr 2
    symm; apply Fintype.prod_equiv e; intro j
    by_cases h : j=none
    · rw [h]; simp [e]
    have he : e j ≠ i := by rw [← show e none=i by simp [e]]; exact e.injective.ne h
    simp only [h,he,↓reduceIte,Function.comp_apply]
  simp_rw [show ∀ z : Tuple ι m, atVertex R (charge X B w a) (charge X B u a) i z = _ from eq]
  exact budget_pull _ he' (budget_none R X B ht hu h he m)

/-- The designated weight u is an ordinary vertex cost, charged with the
same support exponential as the others. -/
def marked (Q : ι → Prop) (w : ι → ℝ) (i : ι) := if Q i then w i else 0

-- Parenthesized conditional uses classical checks in a uniform grammar.
lemma marked_pos (Q : ι → Prop) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : ∀ i, 0 ≤ marked Q w i := by
  intro i; unfold marked; split <;> first | exact hw i | exact le_rfl

theorem cluster_at (ht : Tests R X) {w : ι → ℝ} {a γ δ q b : ℝ} (Q : ι → Prop)
    (h : Ready X B w a γ δ q) (he : SumBudget (charge X B (marked Q w) (a+δ)) b) (m : ℕ) :
    SumBudget (fun z : Tuple ι m => if ∃ i, Q (z i) then clusters R (charge X B w a) z else 0)
      (b*q^m) := by
  let V := Option (Fin m)
  let W := charge X B w a; let u := marked Q w; let U := charge X B u a
  have hw := h.2.2.2.2.1; have hw' := charge_pos X B hw a
  have hu := marked_pos Q hw; have hu' := charge_pos X B hu a
  let n : ℝ := (m:ℝ)+1
  have hn : 0 < n := by unfold n; positivity
  have hb := budget_scale (show 0 ≤ n⁻¹ by positivity) (budget_over univ
    (fun (i : Option (Fin m)) z => atVertex R W U i z) (fun _ => b*q^m)
    (fun i _ => budget_root R X B ht hu h he m i))
  have hc : SumBudget (fun z : Tuple ι m => n⁻¹ * ∑ i : Option (Fin m), atVertex R W U i z)
      (b*q^m) := budget_loosen hb (by unfold n; simp; apply le_of_eq; field_simp)
  -- once z hits, one possible root i suffices; after sum use all of them.
  refine budget_mono hc (fun i => ?_) fun i => ?_
  · split
    next h => exact clusters_nonneg R hw' i
    next h => exact le_rfl
  split
  next h =>
    obtain ⟨j,hj⟩ := h
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (fun a _ =>
      atVertex_pos R hw' hu' a i) (mem_univ j)) (by positivity))
    have he : U (i j)=W (i j) := by simp only [U,W,u,charge,marked,if_pos hj]
    unfold atVertex clusters
    rw [prod_congr rfl (show ∀ a ∈ (univ:Finset V),
      (if a=j then U (i a) else W (i a)) = W (i a) from fun a _ => by
          split
          · subst a; exact he
          · rfl),
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    unfold W n
    apply le_of_eq; ring_nf; field_simp; ring
  next h => exact hc.1 i

theorem cluster_tail (ht : Tests R X) {w : ι → ℝ} {a γ δ q b : ℝ} (Q : ι → Prop)
    (h : Ready X B w a γ δ q) (he : SumBudget (charge X B (marked Q w) (a+δ)) b) (m : ℕ) :
    SumBudget (fun z : Clusters ι => if m ≤ z.1 then (if ∃ i, Q (z.2 i) then
      clusters R (charge X B w a) z.2 else 0) else 0) (b*q^m*(1-q)⁻¹) := by
  -- work around potential distinct `Classical.decEq` instances
  apply sigma_tail (fun z : Clusters ι => if ∃ i, Q (z.2 i) then clusters R (charge X B w a) z.2 else 0)
    (fun k => cluster_at R X B ht Q h he k) (budget_nonneg he) (ready_pos X B h).le
    h.2.2.2.1 m

lemma connected_pay (ht : Tests R X) {m : ℕ} (z : Tuple ι m) {a : ℝ} (ha : 0 ≤ a)
    (he : coefficient R z ≠ 0) : currency B a (unionOf X z) ≤
      ∏ i : Option (Fin m), currency B a (X (z i)) := by
  let T := pot R z
  have hg : (connectedGroups T).Nonempty := by
    by_contra hh; rw [not_nonempty_iff_eq_empty] at hh
    exact he (by change ∑ i∈connectedGroups T, alternating i=0; rw [hh,sum_empty])
  obtain ⟨s,hs⟩ := hg
  obtain ⟨hk,hs⟩ := belongs.mp hs
  obtain ⟨p,d,hp⟩ := Breadth.build (Graph.link s) (fun _ => 0) (hs none)
  have hh : Graph.sprouts T p := ⟨Breadth.growth_ranked hp.toGrowth,
    fun i => ⟨(hp.edges i).1,hk (hp.edges i).2⟩⟩
  have hx := overall_paid X B ha (spanned R X ht hh)
  rw [Fintype.prod_option]
  have he : unionOf X z = overall X (X (z none)) (z ∘ some) := by
    unfold unionOf overall
    congr 1; funext i; cases i <;> rfl
  rw [he]; exact hx

lemma pay_cover (ht : Tests R X) {w : ι → ℝ} (hw : ∀ i, 0≤w i) {a : ℝ} (ha : 0≤a)
    {m : ℕ} (z : Tuple ι m) : clusters R w z * currency B a (unionOf X z) ≤
      clusters R (charge X B w a) z := by
  by_cases hh : coefficient R z = 0
  · simp [clusters,hh]
  unfold charge clusters
  rw [Finset.prod_mul_distrib,div_mul_eq_mul_div,mul_assoc];
  gcongr
  · exact prod_nonneg fun i _ => hw _
  exact connected_pay R X B ht z ha hh

theorem log_hit_tail (ht : Tests R X) {w : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B w a γ δ q)
    (ha : 0 ≤ a) (m : ℕ) (x : Site n) :
    SumBudget (fun z : Clusters ι => if m ≤ z.1 ∧ x∈unionOf X z.2 then
      clusters R w z.2 * currency B a (unionOf X z.2) else 0) (γ*q^m*(1-q)⁻¹) := by
  let Q := fun i => x∈X i
  have he : SumBudget (charge X B (marked Q w) (a+δ)) γ := by
    convert test_hit X B h x using 1; ext i; simp [charge,hit,marked,Q]
  have hc := cluster_tail R X B ht Q h he m
  have hw := h.2.2.2.2.1
  refine budget_mono hc (fun i => ?_) fun i => ?_
  · split
    next he => exact mul_nonneg (clusters_nonneg R hw _) (Real.exp_pos _).le
    next he => exact le_rfl
  split
  next he =>
    have hh : ∃ j, Q (i.2 j) := by
      obtain ⟨j,hj,hx⟩ := mem_biUnion.mp he.2
      exact ⟨j,hx⟩
    rw [if_pos he.1,if_pos hh]; exact pay_cover R X B ht hw ha i.2
  next he => exact hc.1 i
end YM.Push.AbsoluteSums.Ursell
