import YM.Ac.Tree
import YM.Corona.Fit
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.Regular
import YM.Next.FOUNDATIONS.SU2


/-!
# Full product and reanchoring bounds on the actual regular jets 

One total output left-derivative order, not that order spent separately on
moving every factor. Allows coincident/overlapping or repeated factors, and
complex coefficients. Use on the common GOOD set including equality; nothing
is claimed about derivatives of the indicator. Prices below are for the
nonfactorial sup-norm version. Helper chart argument uses the actual local
log/exp analysis as for Next.FOUNDATIONS.Regular.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.Germs
open Function Filter Wilson RG Lattice MeasureTheory Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {ι : Type*} {n : Side} {G : Gauge} (s : Finset ι)

private lemma near {f : Config G n → ℂ} {U : Config G n} {k : ℕ}
    (h : ContDiffAt ℝ (↑k) (f ∘ increment U) 0) (A : Directions G n) :
    ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ (↑k) (f ∘ increment (increment U (t • A))) 0 := by
  let H (p : ℝ × Directions G n) e := G.lieExp (p.2 e) * G.lieExp (p.1 • A e)
  have ht (e) : Tendsto (H · e) (𝓝 0) (𝓝 1) := by
    rw [← show H 0 e=1 by simp [H]]; exact (show Continuous (H · e) by unfold H; fun_prop).tendsto _
  have he (e) : ContDiff ℝ ω (fun q => G.mat (H q e)) := by
    apply (G.exp_jet.comp ?_).mul (G.exp_jet.comp ?_) <;> fun_prop
  let J (p : ℝ × Directions G n) : Directions G n := fun e => G.plog (G.mat (H p e))
  have hg : ContDiffAt ℝ ω J 0 := contDiffAt_pi.mpr fun i =>
    ContDiffAt.comp (g:=G.plog) (f:=fun q => G.mat (H q i)) _ (by simp [H,G.plog_diff]) (he i).contDiffAt
  have hJ : J 0=0 := by ext; simp [J,H]
  have h' : ContDiffAt ℝ (↑k) (fun p : ℝ × Directions G n => f (increment (increment U (p.1 • A)) p.2)) 0 := by
    apply ((hJ.symm ▸ h : ContDiffAt _ (↑k:WithTop ℕ∞) _ (J 0)).comp 0 (hg.of_le le_top)).congr_of_eventuallyEq
    filter_upwards [Filter.eventually_all.mpr (fun i => (ht i).eventually G.plog_right)] with p hp
    apply congr_arg f; ext1 e
    change G.lieExp _ * (G.lieExp _ * U e) = G.lieExp (J p e) * U e
    rw [← mul_assoc,show G.lieExp (J p e)=_ from hp e]; rfl
  have h0 : Tendsto (fun x : ℝ => (x,(0:Directions G n))) (𝓝 0) (𝓝 0) := continuous_id.continuousAt.prodMk continuousAt_const
  filter_upwards [h0.eventually (h'.eventually (by simp))] with x hx
  exact hx.comp 0 (f:=fun v => (x,v)) (contDiffAt_const.prodMk contDiffAt_id)

section Assignment
variable {E : Type*}

def push (a : E) (j : ι) (q : ι → List E) := Function.update q j (a :: q j)

private lemma push_has (a : E) (i : ι) (hi : i∈s) {L : E → Prop} {l : ℕ} (v : ι → List E)
    (hv : ∀ i∈s,∀ a∈v i,L a) (hz : ∑ i∈s, (v i).length = l) (ha : L a) :
    (∀ j∈s,∀ b∈push a i v j,L b) ∧ ∑ j∈s,(push a i v j).length=l+1 := by
  constructor
  · intro j hj b hb; unfold push at hb
    by_cases h : j=i
    · subst j; rw [update_self,List.mem_cons] at hb; rcases hb with rfl|hb; exact ha; exact hv i hi b hb
    rw [update_of_ne h] at hb; exact hv j hj b hb
  rw [← sum_erase_add _ _ hi] at hz ⊢
  have he j (hj : j∈s.erase i) : push a i v j = v j := Function.update_of_ne (ne_of_mem_erase hj) ..
  rw [sum_congr rfl fun j hj => congr_arg List.length (he j hj),push,update_self,List.length_cons,← hz]; omega

/-- Sum over assignments of directions in a list to ordered sublists at the
factors, in original order on each factor. No permutation law on left jets. -/
def assign : List E → ((ι → List E) → ℂ) → ℂ
  | [], H => H fun _ => []
  | a::l,H => assign l (fun q => ∑ j∈s, H (push a j q))

private lemma assign_has (l : List E) (A : (ι→List E) → ℝ → ℂ) (A' : (ι→List E) → ℂ)
    (h : ∀ q, (∀ j∈s,(q j).length ≤ l.length) → HasDerivAt (A q) (A' q) 0) : HasDerivAt
    (fun t => assign s l (fun q => A q t)) (assign s l A') 0 := by
  induction l generalizing A A' with
  | nil => exact h _ fun _ _ => le_rfl
  | cons a l ih =>
    refine ih _ _ (fun q hq => HasDerivAt.fun_sum fun i _ => h _ (fun j hj => ?_))
    dsimp only [push]; by_cases he : j=i
    · subst j; simpa only [update_self, List.length_cons, Nat.add_le_add_iff_right] using hq _ hj
    rw [update_of_ne he]; simpa only [List.length_cons] using (hq _ hj).trans (Nat.le_succ _)

private lemma assign_push (a : E) (l : List E) (H : (ι→List E) → ℂ) : assign s (a::l) H =
    assign s l (fun q => ∑ i∈s, H (push a i q)) := rfl

lemma assignment_norm {L : E → Prop} (l : List E) (F : (ι → List E) → ℂ) (c : ℝ) (hl : ∀ i∈l,L i)
    (hf : ∀ q, (∀ i∈s, ∀ v ∈ q i,L v) → (∑ i∈s, (q i).length)=l.length → ‖F q‖ ≤ c) :
    ‖assign s l F‖ ≤ (s.card:ℝ)^l.length * c := by
  induction l generalizing F c with
  | nil => simpa [assign] using hf (fun _ => []) (by simp) (by simp)
  | cons a l ih =>
    simp only [assign,List.length_cons,pow_succ,mul_assoc]; apply ih _ _ (fun i hi => hl i (List.mem_cons_of_mem _ hi))
    intro q hq hz; have hp i (hi : i∈s) := push_has s a i hi q hq hz (hl a List.mem_cons_self)
    refine (norm_sum_le ..).trans ?_
    simpa using sum_le_sum (fun i hi => hf _ (hp i hi).1 (hp i hi).2)
end Assignment

variable {P : BudgetPoint} {X : Support n} {U : Config G n}

lemma leibniz (f : ι→Config G n → ℂ) {k : ℕ} (h : ∀ i∈s,ContDiffAt ℝ (↑k) (f i ∘ increment U) 0)
    (l : List (Directions G n)) (hl : l.length ≤ k) :
    leftDerivs (fun u => ∏ i∈s, f i u) l U = assign s l (fun q => ∏ i∈s,leftDerivs (f i) (q i) U) := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih =>
    have he : l.length < k := hl
    let F (q : ι → List (Directions G n)) (t : ℝ) := ∏ i∈s, leftDerivs (f i) (q i) (increment U (t • a))
    let F' (q : ι → List (Directions G n)) := ∑ i∈s, ∏ j∈s, leftDerivs (f j) (push a i q j) U
    rw [leftDerivs,assign_push]; apply HasDerivAt.deriv
    refine (assign_has s l F F' (fun q hq => ?_)).congr_of_eventuallyEq ?_
    · have H := HasDerivAt.fun_finsetProd fun i hi => Next.Foundations.left_has a ((hq i hi).trans_lt he) (h i hi)
      simp only [zero_smul,show increment U 0=U by ext1 i; simp [increment]] at H
      convert H using 1
      any_goals rfl
      apply sum_congr rfl; intro i hi
      rw [← prod_erase_mul _ _ hi]
      dsimp only [push]; rw [update_self,smul_eq_mul]; congr 1
      exact prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    · filter_upwards [eventually_all_finset _ |>.mpr fun i hi => near (h i hi) a] with t ht using ih ht he.le

lemma smoothProd {Y : ι→Support n} {F : ι → Config G n → ℂ}
    (h : ∀ i∈s, P.Regular (Y i) (F i)) : P.Regular (s.biUnion Y) (fun U => ∏ i∈s, F i U) := by
  have he (U : Config G n) (hu : Healthy P.threshold (s.biUnion Y) U) : ContDiffAt ℝ (↑P.order)
      ((fun U => ∏ i∈s,F i U) ∘ increment U) 0 := by
    refine contDiffAt_prod (fun i hi => (h i hi).smooth U (Finset.disjoint_of_subset_left ?_ hu))
    exact subset_biUnion_of_mem Y hi
  refine ⟨fun U V hV => prod_congr rfl fun i hi => (h i hi).sites U V (agrees_mono hV fun _ hx =>
    mem_biUnion.mpr ⟨i,hi,hx⟩), Finset.measurable_fun_prod _ (fun i hi => (h i hi).borel),
    fun t U => prod_congr rfl fun i hi => (h i hi).symmetry ..,he,fun U hu a l hl => Next.Foundations.left_has a hl (he U hu)⟩

/-- Only a COMMON dilation is needed. True totalized derivatives, even when
called at places where they return junk. -/
lemma dilation (f : Config G n → ℂ) (l : List (Directions G n)) (c : ℝ) :
    leftDerivs f (l.map (c • ·)) U = c^l.length • leftDerivs f l U := by
  induction l generalizing U with
  | nil => simp [leftDerivs]
  | cons a l ih =>
    simp_rw [List.map_cons,leftDerivs, ih,smul_smul,mul_comm _ c]
    rw [deriv_fun_const_smul_field,show deriv (fun t => leftDerivs f l (increment U ((c*t) • a))) 0 = _ from
      deriv_comp_mul_left c (fun t => leftDerivs f l (increment U (t • a))) 0,mul_zero,smul_smul,List.length_cons,pow_succ]

lemma relocate_dir {o y : Site n} {b : ℝ} {a : Directions G n} (hb : (1+(separation o y:ℝ)) ≤ b)
    (h : P.dirBound y a) : P.dirBound o (b⁻¹^P.power • a) := by
  have hB : 0 < b := lt_of_lt_of_le (by positivity) hb
  intro e; rw [Pi.smul_apply, norm_smul,Real.norm_of_nonneg (by positivity), inv_pow]
  apply (mul_le_mul_of_nonneg_left (h e) (by positivity)).trans
  have h' : (separation e.1 y:ℝ) ≤ separation e.1 o + (separation o y : ℝ) := by exact_mod_cast separation_triangle e.1 o y
  rw [inv_mul_eq_div,div_le_iff₀ (by positivity), mul_assoc,← mul_pow]; have := P.threshold_pos; gcongr
  nlinarith [show (0:ℝ) ≤ separation e.1 o by positivity]

lemma relocated_bound {o y : Site n} {b c : ℝ} {f : Config G n → ℂ}
    (h : (1+(separation o y:ℝ)) ≤ b) (hf : P.supBounds o X f c) (hu : Healthy P.threshold X U)
    (l : List (Directions G n)) (hl : l.length ≤ P.order) (hr : ∀ a∈l,P.dirBound y a) :
    ‖leftDerivs f l U‖ ≤ (b^P.power)^l.length*c := by
  have hB : 0 < b := lt_of_lt_of_le (by positivity) h
  have hg := hf.2 U hu (l.map ((b⁻¹^P.power:ℝ) • ·)) (by simpa) fun a ha => (by obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha; exact relocate_dir h (hr _ hv))
  rw [dilation,norm_smul,Real.norm_of_nonneg (by positivity),inv_pow,inv_pow,inv_mul_eq_div,div_le_iff₀ (by positivity),mul_comm c] at hg
  exact hg

variable {Y : ι → Support n} {F : ι → Config G n → ℂ} {o : ι → Site n} {c : ι → ℝ}

/-- Ordered multi-factor version of (reamx), nonfactorial convention. One `y`
common for the OUTPUT, may be used for every marker root. Full direction
weights moved from each `o i` to y. Each loss is paid per slot, not per slot
per occurrence. `b` is any bound for 1+distance. -/
lemma multibound (y : Site n) {b : ℝ} 
    (h : ∀ i∈s, P.Regular (Y i) (F i)) (he : ∀ i∈s,P.supBounds (o i) (Y i) (F i) (c i))
    (hr : ∀ i∈s, (1+(separation (o i) y:ℝ)) ≤ b) (hu : Healthy P.threshold (s.biUnion Y) U)
    (l : List (Directions G n)) (hl : l.length ≤ P.order) (hd : ∀ a∈l,P.dirBound y a) :
    ‖leftDerivs (fun U => ∏ i∈s,F i U) l U‖ ≤ ((s.card:ℝ)*b^P.power)^l.length*∏ i∈s,c i := by
  have hx i (hi : i∈s) := Finset.disjoint_of_subset_left (subset_biUnion_of_mem Y hi) hu
  rw [leibniz s F (fun i hi => (h i hi).smooth U (hx i hi)) l hl,mul_pow,mul_assoc]
  apply assignment_norm s l _ _ hd; intro q hq hh; rw [norm_prod,←hh, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  apply prod_le_prod (fun i _ => norm_nonneg _); intro i hi
  have H := (single_le_sum (fun j (_ : j∈s) => Nat.zero_le (q j).length) hi).trans_eq hh
  exact relocated_bound (hr i hi) (he i hi) (hx i hi) (q i) (H.trans hl) (hq i hi)

/-- The repeated-variable cost as sum of the ACTUAL connected-cover costs
. Element type permits any number of repeated fields and multiple
addresses meeting a root. -/
def occurrences (M : ℕ) (Y : ι → Support n) := ∑ i∈s,coverNumber M (Y i)

def pay (P : BudgetPoint) := ((4*P.B+2:ℝ)^P.power)^P.order

theorem reanchored (y : Site n) (h : ∀ i∈s, P.Regular (Y i) (F i)) (he : ∀ i∈s, P.supBounds (o i) (Y i) (F i) (c i))
    (hS : Ac.Spark Y s) (ho : ∀ i∈s,o i∈Y i) (hy : y∈s.biUnion Y) :
    P.supBounds y (s.biUnion Y) (fun U => ∏ i∈s,F i U)
      (pay P * (1+(occurrences s P.B Y : ℝ))^((P.power+1)*P.order)*∏ i∈s,c i) := by
  let w := occurrences s P.B Y
  let b := (4*(P.B:ℝ)+2)*(1+w)
  have hf := prod_nonneg (fun i hi => (he i hi).1)
  have hb i (hi : i∈s) : 1+(separation (o i) y : ℝ) ≤ b := by
    have h : (separation (o i) y:ℝ) ≤ w*(4*P.B+2)+(2*(P.B:ℝ)) := by
      exact_mod_cast (Corona.extent _ P.B (mem_biUnion.mpr ⟨i,hi,ho i hi⟩) hy).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Ac.cover Y P.B hS)) _)
    unfold b; linarith
  have h1 : 1 ≤ b := by
    unfold b; have hw : (0:ℝ)≤w := by positivity
    have hB : (0:ℝ) ≤ P.B := by positivity
    nlinarith
  have hw : 1 ≤ (s.card :ℝ) := by exact_mod_cast (card_pos.mpr hS.1)
  have hx : (s.card:ℝ) ≤ (1+w:ℝ) := by
    have hc i (hi : i∈s) : 1 ≤ coverNumber P.B (Y i) := by
      have := card_pos.mpr (show (Y i).Nonempty from ⟨_,ho i hi⟩)
      have he := Corona.pays (Y i) P.B
      by_contra! h; rw [Nat.lt_one_iff.mp h,zero_mul] at he; omega
    exact le_trans (b:=(w:ℝ)) (by unfold w; exact_mod_cast (show s.card ≤ w by simpa [w,occurrences] using sum_le_sum hc)) (le_add_of_nonneg_left zero_le_one)
  refine ⟨by unfold pay; positivity, fun U hU l hl hd => ?_⟩
  refine (multibound s y h he hb hU l hl hd).trans (mul_le_mul_of_nonneg_right ?_ hf)
  rw [show pay P*(1+(occurrences s P.B Y:ℝ))^((P.power+1)*P.order)=((1+w)*b^P.power)^P.order by
    unfold b pay; change _*(1+(w:ℝ))^_=_; rw [pow_mul,pow_succ]; simp only [mul_pow]; ring]
  apply le_trans (b:=((1+(w:ℝ))*b^P.power)^l.length) _ (pow_le_pow_right₀ (by nlinarith [one_le_pow₀ (n:=P.power) h1]) hl)
  gcongr



end YM.Extra.Multi.Germs
