import YM.Corona.Halo
import YM.SectorNext.VACUUM_NORMALIZATION.Gas


/-!
# At first gas: native torus locality & actual masks

At the scalar level (zero V derivatives). Issue common coefficients
on full supports T: suppression by any flag in T, visit/dependency
locality BEFORE mask (hence actual Held locality through inspected T),
Borel and gauge invariance. Preserve support addresses even on zeros.
No identity/Hessian subtraction at this layer (don't assert output E
receipt). Works regardless of interior expression for the integrated
atoms (no dependence claimed on an analytic operation that constructs
them, or on acquiring new labels after an expansion).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.ReLog
open Lattice Lattice.Corona RG Wilson Finset Filter
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {ι : Type*} {G : Gauge} {n : Side}
  (X : ι → Support n)

def native (M : ℕ) (A : ℝ) (i : Leaf (Site n)) := Real.exp (A*coverNumber M i)
lemma native_rate (M : ℕ) {A : ℝ} (h : 0≤A) : Rate (native (n:=n) M A) := by
  refine ⟨fun i => Real.one_le_exp (mul_nonneg h (by positivity)),fun P Q he => ?_⟩
  unfold native; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
  rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ h
  obtain ⟨x,hx⟩ := he
  -- instance DecidableEq at site n
  exact_mod_cast meets_sum (mem_inter.mp hx).1 (mem_inter.mp hx).2 M

def roof (M : ℕ) : ℝ := (((M+M+1:ℕ):ℝ)^4)
lemma native_support (M : ℕ) (i : Support n) (a : ℝ) (h : 0≤a) (hh : a*roof M ≤ 1) : a*(i.card : ℝ) ≤ coverNumber M i := by
  have he : (i.card:ℝ) ≤ coverNumber M i * roof M := by unfold roof; exact_mod_cast pays i M
  apply (mul_le_mul_of_nonneg_left he h).trans
  rw [mul_left_comm]; exact mul_le_of_le_one_right (Nat.cast_nonneg _) hh

/-- Concrete hit reserve (A+1 formulation; can generalize). Native
connected (M+M+1)^4, not spending radius-lattice-site powers pre-block.
Same incoming, often finite δ from a calendar after post-L. -/
structure Fund (M : ℕ) (A a δ : ℝ) (v : ι → ℝ) : Prop where
  pos : 0≤a
  nonnegative : 0≤A
  wires : a*roof M ≤ 1
  small : δ ≤ 1-Real.exp (-a)
  cost (i : ι) : 0≤v i
  visit (x : Site n) : SumBudget (fun i => if x∈X i then native M (A+1) (X i)*v i else 0) δ

lemma permits (M : ℕ) {A a δ : ℝ} {v : ι → ℝ} (h : Fund X M A a δ v) : Sufficient X (native M A) v a δ := by
  have ht := native_rate (n:=n) M h.nonnegative
  refine ⟨ht,h.cost,h.pos,h.small,fun x => ?_⟩
  let q := fun i : ι => if x∈X i then native M A (X i)*v i*Real.exp (a*(X i).card) else 0
  let r := fun i : ι => if x∈X i then native M (A+1) (X i)*v i else 0
  have hh : SumBudget r δ := h.visit x
  have hq (i) : 0≤q i := by unfold q; split; have := h.cost i; unfold native; positivity; rfl
  have hl (i) : q i ≤ r i := by
    unfold q r; split
    · unfold native; rw [mul_right_comm,← Real.exp_add]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [native_support M (X i) a h.pos h.wires])) (h.cost i)
    rfl
  have hw := hh.2.1.of_nonneg_of_le hq hl
  have ht : SumBudget q δ := ⟨hq,hw,(hw.tsum_le_tsum hl hh.2.1).trans hh.2.2⟩
  convert ht using 3



/-- The labels before masks; emitted unforced numerical component and
complete site support (not the internal path address used to produce that
number). -/
structure Tags (b : BudgetPoint) (E : ι → Config G n → ℝ) (v : ι → ℝ) : Prop where
  full i : (X i).Nonempty
  probes i : LocalOn (X i) (E i)
  gi i : GaugeInvariant (E i)
  bors i : Measurable (E i)
  on i U : Healthy b.threshold (X i) U → |E i U| ≤ v i

/-- Output labels BEFORE mask. This is computed by testing only addresses
whose support lies in i; even though `tsum` appears to test all in its
definition, addresses ineligible by support here are ineligible on every
configuration. Retain address i and its full dependencies even if this
value is zero. Outside the good domain these are just representatives
(junk allowable, Borel and gauge invariant); tests at & just *inside*
the good domain should use the actual smooth extensions if calling E
costs (not here). -/
def raw (E : ι → Config G n → ℝ) (i : Support n) (V : Config G n) := locker (fumes X (fun j => E j V)) i
def herald (b : BudgetPoint) (E : ι → Config G n → ℝ) (V : Config G n) := fun j => masked b.threshold (X j) (E j) V
def locked (b : BudgetPoint) (E : ι → Config G n → ℝ) (i : Support n) := masked b.threshold i (raw X E i)

private theorem local_dependencies {u v : ι → ℝ} (P : Leaf (Site n)) (h : ∀ i,X i⊆P → u i=v i) :
    locker (fumes X u) P = locker (fumes X v) P := by
  apply pieces_by fun t ht => ?_
  apply congr_arg (fun j : ℝ => -Real.log j); apply tsum_congr; intro j
  unfold note; split <;> rename_i he
  · exact Finset.prod_congr rfl fun i hi => h i ((((accepts ..).mp he).2.1 i hi).trans ht)
  rfl

lemma retest (E : ι → Config G n → ℝ) (h : ∀ i,LocalOn (X i) (E i)) (i : Leaf (Site n)) : LocalOn i (raw X E i) := by
  intro V W hk
  apply local_dependencies; intro j hj; exact h j V W (agrees_mono hk (show X j ⊆ i from hj))
lemma retest_gi (E : ι → Config G n → ℝ) (h : ∀ i,GaugeInvariant (E i)) (i : Support n) : GaugeInvariant (raw X E i) := by
  intro t V; apply local_dependencies; intro j _; rw [h j]
lemma retest_meas [Countable ι] (E : ι → Config G n → ℝ) (h : ∀ i,Measurable (E i)) (i : Support n) : Measurable (raw X E i) := by
  induction i using Finset.strongInduction with | H i ih
  let Y := fun V : Config G n => fumes X (fun j => E j V) i
  have h0 : Measurable Y := by
    unfold Y fumes; apply Measurable.tsum; intro s; unfold note; split
    · apply Finset.measurable_fun_prod; intro a _; exact h a
    exact measurable_const
  have he : raw X E i = fun V => - Real.log (Y V) - ∑ j∈i.powerset.erase i, raw X E j V := by
    funext; exact unfold_pieces ..
  rw [he]; apply h0.log.neg.sub; apply Finset.measurable_fun_sum; intro j hj
  exact ih j (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_erase.mp hj).2,(mem_erase.mp hj).1⟩)

/-- L_i of masked data is zero if even *one* site in i failed a hard
indicator. No property of the log function at zero invoked. -/
lemma retain_mask (b : BudgetPoint) (E : ι → Config G n → ℝ) (V : Config G n) (i : Support n) :
    locker (fumes X (herald X b E V)) i = locked X b E i V := by
  by_cases h : Healthy b.threshold i V
  · rw [locked, masked_eq _ _ _ _ h]
    refine local_dependencies X _ (fun j hj => ?_)
    unfold herald; rw [masked_eq _ _ _ _ (Disjoint.mono_left hj h)]
  rw [locked, masked_ne _ _ _ _ h]
  simp only [Healthy,Finset.disjoint_left] at h; push Not at h; obtain ⟨x,h1,h2⟩ := h
  let u := herald X b E V
  let f := fun A => -Real.log (fumes X u A)
  change pieces f i=0
  rw [←(if_pos h1 : (if x∈i then pieces f i else (0:ℝ)) = pieces f i),← changes]
  have hh (A : Support n) : f A=f (A.erase x) := by
    unfold f; congr 2; apply tsum_congr; intro Q
    by_cases ht : allowed X (A.erase x) Q
    · have hk := (accepts ..).mp ht
      have hp : allowed X A Q := (accepts ..).mpr ⟨hk.1,fun j hj => (hk.2.1 j hj).trans (erase_subset ..),hk.2.2⟩
      simp [note,ht,hp]
    by_cases hk : allowed X A Q; swap; simp [note,hk,ht]
    rw [note,if_pos hk,note,if_neg ht]; have hp := (accepts ..).mp hk
    have hr : ∃ j∈Q,x∈ X j := by
      by_contra! hy; exact ht ((accepts ..).mpr ⟨hp.1,fun j hj => subset_erase.mpr ⟨hp.2.1 j hj,hy j hj⟩,hp.2.2⟩)
    obtain ⟨j,hj,he⟩ := hr
    apply Finset.prod_eq_zero hj
    exact masked_ne _ _ _ _ (fun ht => Finset.disjoint_left.mp ht he h2)
  rw [show (fun A => f A-f (A.erase x)) = shed (fun _=>0) from funext fun A => by rw [hh A,sub_self]; simp [shed],allocation]


private lemma herald_cost {b : BudgetPoint} {E : ι → Config G n → ℝ} {v : ι→ℝ}
    (t : Tags X b E v) (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v) (V : Config G n) (j : ι) : |herald X b E V j| ≤ v j := by
  by_cases hi : Healthy b.threshold (X j) V
  · unfold herald; rw [masked_eq _ _ _ _ hi]; exact t.on _ _ hi
  unfold herald; rw [masked_ne _ _ _ _ hi,abs_zero]; exact h.cost _

/-- Absolute support prices, emitted with a **common envelope for all V**.
Usable even though there was no global small l¹ hypothesis across the
whole torus. Also when the first integrated unforced gas has any set of
sites disabled by already selected forced supports. `pieces ∅ = 0` so
keep as padding (anchor required on every actual Rep reg label). -/
theorem intake {b : BudgetPoint} {E : ι → Config G n → ℝ} {v : ι → ℝ} (t : Tags X b E v)
    (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v) :
    let g := ceiling (fumes X (-v))
    let Z := fun V => fumes X (herald X b E V)
    (∀ V : Config G n,locked X b E ∅ V=0) ∧
      (∀ V i,|locked X b E i V| ≤ g i) ∧
      (∀ x,∑ i∈(univ:Finset (Support n)).filter (fun i=>x∈i),native M A i*g i ≤ a) ∧
      ∀ V (Q : Leaf (Site n)), 0 < Z V Q ∧ Z V Q = Real.exp (-∑ i∈Q.powerset, locked X b E i V) ∧
        let l := ∑ i∈(univ:Finset (Support n)).filter (fun i => ¬ Disjoint i Q), locked X b E i V
        Z V (univ\Q) = Z V univ * Real.exp l ∧ |l| ≤ Q.card*a := by
  intro g Z
  -- Keep the very same Labels and V for every occurrence and calculation.
  have hr := permits X M h
  have H (V) := catalog t.full hr (herald X b E V) (herald_cost X t M h V)
  refine ⟨fun V => ?_,fun V i => ?_,fun x => ?_,fun V Q=> ?_⟩
  · rw [← retain_mask]; unfold locker
    rw [unfold_pieces,(shelf X t.full (herald X b E V)
      (Summable.of_norm_bounded (supplied_sum t.full hr) (herald_cost X t M h V))).bottom]; simp
  · rw [←retain_mask]; exact (H V).negLog i
  · exact (H (1:Config G n)).hits x
  have ht (i : Support n) := retain_mask X b E V i
  have hm := omitted t.full hr (herald X b E V) (herald_cost X t M h V) Q
  have hh := (H V).log_form Q; unfold shed at hh; simp only [ht] at hh
  refine ⟨(H V).pos Q,hh,?_⟩
  intro l; unfold Z l
  have heS : (univ:Finset (Support n)).filter (fun i => ¬ Disjoint i Q) = univ.filter (fun i => (i ∩ Q).Nonempty) := by ext i; simp [Finset.disjoint_left,Finset.Nonempty]
  rw [heS]; simp_rw [← ht]; exact hm

/-- Upper bound on log contributions that one is about to move to the
scalar (site units). Works through activated threshold guards, no
counting of N-tag copies. -/
theorem extensive {b : BudgetPoint} {E : ι → Config G n → ℝ} {v : ι → ℝ} (t : Tags X b E v)
    (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v) (V : Config G n) :
    ∑ i : Leaf (Site n), |locked X b E i V| ≤ Fintype.card (Site n)*a := by
  let u (i) := |locked X b E i V|; let g := ceiling (fumes X (-v))
  obtain ⟨h1,h2,h3,-⟩ := intake X t M h
  have he i : u i ≤ native M A i*g i := (h2 V i).trans (le_mul_of_one_le_left ((abs_nonneg _).trans (h2 V i)) (native_rate M h.nonnegative |>.pos _))
  have ht (x : Site n) : (∑ i,if x∈i then u i else (0:ℝ)) ≤ a := by
    rw [← sum_filter]
    exact (sum_le_sum (fun i _=>he i)).trans (h3 x)
  calc
    _ ≤ ∑ i,∑ x : Site n,if x∈i then u i else 0 := by
      refine sum_le_sum fun i _ => ?_
      by_cases hh : i=(∅:Leaf (Site n)); subst i; simp [h1]
      obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hh
      have hf := single_le_sum (f:=fun x : Site n=>if x∈i then u i else 0) (fun i _=>by split; exact abs_nonneg _; rfl) (mem_univ x)
      simpa [hx] using hf
    _ ≤ _ := by rw [sum_comm]; apply (sum_le_sum fun i _=>ht i).trans; simp

/-- Indicator compensation for these very coefficient labels, e.g. when
moving the constants to the external scalar at flat V. Correction terms
are activated only by *actual* output flags. These still need attaching to
old forced species before claiming the output Representation bounds. -/
def adjust (b : BudgetPoint) (E : ι → Config G n → ℝ) (i : Support n) (V : Config G n) :=
    if Healthy b.threshold i V then 0 else raw X E i 1

def devalue (b : BudgetPoint) (E : ι → Config G n → ℝ) (i : Support n) :=
    masked b.threshold i (fun V => raw X E i V-raw X E i 1)


theorem adjustment (b : BudgetPoint) (E : ι → Config G n → ℝ) (i : Support n) (V : Config G n) :
    -locked X b E i V = -raw X E i 1 - devalue X b E i V + adjust X b E i V := by
  unfold adjust devalue locked; split
  · rw [masked_eq _ _ _ _ ‹_›,masked_eq _ _ _ _ ‹_›]; ring
  rw [masked_ne _ _ _ _ ‹_›,masked_ne _ _ _ _ ‹_›]; ring



end YM.SectorNext.Vacuum.ReLog
