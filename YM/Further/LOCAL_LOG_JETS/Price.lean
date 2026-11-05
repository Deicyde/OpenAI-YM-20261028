import YM.Extra.MULTISOURCE_BOUNDS.Germs
import YM.Further.LOCAL_LOG_JETS.Windows
import YM.Push.ABSOLUTE_SUMS.FiniteLog
import YM.Push.ABSOLUTE_SUMS.Reserves
import YM.Push.LOCAL_SPLITTING.Products





set_option warningAsError false

/-!
# Ordered support prices for the actual log occurrence arrays

At the complete union support BEFORE hard mask. Keep numbered
occurrences, including repeated addresses. Apply the reanchoring
polynomial once PER CLUSTER, not once per factor (cf. Buy it with a support-reserve, in `overlap_price`;
this asks only the trees.Ready hit criterion on the input **atoms**. The same prices include the tails in arity and sum with no volume in
the hit. Winding supports ok ($B$ at this scale). Use separately
from actually obtaining primitive per-atom jets/costs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.LogJets
open Filter Function Finset Lattice Wilson RG Next.Foundations Push.Local Push.AbsoluteSums
open Trees Ursell
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {ι : Type*} {G : Gauge} {n : Side}
variable (X : ι → Support n)

/-- Retains even the occurrences with zero coefficient. -/
abbrev foot (z : Clusters ι) := unionOf X z.2

lemma covered (z : Clusters ι) (i) : X (z.2 i) ⊆ foot X z :=
  subset_biUnion_of_mem (X ∘ z.2) (mem_univ i)
lemma footprint_full (z : Clusters ι) (h : ∀ i, (X i).Nonempty) : (foot X z).Nonempty :=
  (h (z.2 none)).mono (covered X z _)

/-- The NEGATIVE-log price uses these actual signed contributions. -/
def part (E : ι → Config G n → ℝ) (z : Clusters ι) (V : Config G n) :=
  -Gas.term (blocked X) (fun i => E i V) z

def scalarWeight (z : Clusters ι) := -(coefficient (blocked X) z.2 / (z.1+1).factorial)

lemma cost_eq (E : ι → Config G n → ℝ) (z : Clusters ι) : part X E z = fun V =>
    scalarWeight X z * ∏ i,E (z.2 i) V := by funext V; unfold scalarWeight part Gas.term; ring

def coversFee (P : BudgetPoint) (z : Clusters ι) :=
    ∑ i : Option (Fin z.1), (coverNumber P.B (X (z.2 i)):ℝ)

def orderFee (P : BudgetPoint) := (P.power+1)*P.order

def premium (P : BudgetPoint) (z : Clusters ι) :=
    Extra.Multi.Germs.pay P * (1+coversFee X P z)^orderFee P

def fee (P : BudgetPoint) (v : ι → ℝ) (z : Clusters ι) := premium X P z * clusters (blocked X) v z.2

lemma covers_pos (P : BudgetPoint) (z : Clusters ι) : 0 ≤ coversFee X P z :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _
lemma premium_pos (P : BudgetPoint) (z : Clusters ι) : 0 ≤ premium X P z := by
  have := covers_pos X P z; unfold premium Extra.Multi.Germs.pay; positivity
lemma fee_pos (P : BudgetPoint) (v : ι → ℝ) (hv : ∀ i,0 ≤ v i) (z : Clusters ι) :
    0 ≤ fee X P v z := mul_nonneg (premium_pos X ..) (clusters_nonneg _ hv _)

lemma quota (P : BudgetPoint) (v : ι → ℝ) (z : Clusters ι) : fee X P v z =
    |scalarWeight X z| * (premium X P z * ∏ i,v (z.2 i)) := by
  unfold fee clusters scalarWeight
  rw [abs_neg,abs_div,abs_of_nonneg (show 0≤ (((z.1+1).factorial:ℕ):ℝ) by positivity)]; ring

private lemma chart_product (s : Finset ι) (f : ι → Config G n → ℝ) {U : Config G n} {k : ℕ}
    (h : ∀ i∈s, Chart k (f i) U) : Chart k (fun V => ∏ i∈s,f i V) U := contDiffAt_prod h

/-- Point version, also useful on extension windows which do not assert
Regular on every point of the whole configuration space. -/
theorem product_here (s : Finset ι) (f : ι → Config G n → ℝ) (c : ι → ℝ) (D : Directions G n → Prop)
    {U : Config G n} {k : ℕ} (h : ∀ i∈s, Chart k (f i) U)
    (hh : ∀ i∈s, ∀ l : List (Directions G n), l.length ≤ k → (∀ a∈l,D a) → ‖leftDerivs (f i) l U‖ ≤ c i)
    (l : List (Directions G n)) (hl : l.length ≤ k) (hd : ∀ a∈l,D a) :
    ‖leftDerivs (fun V => ∏ i∈s,f i V) l U‖ ≤ (s.card:ℝ)^l.length * ∏ i∈s,c i := by
  let g := Complex.ofRealCLM
  let F i := g ∘ f i
  have he (q : Config G n → ℝ) (hq : Chart k q U) (L : List (Directions G n))
      (hk : L.length ≤ k) : ‖leftDerivs (g ∘ q) L U‖ = ‖leftDerivs q L U‖ := by
    rw [left_linear g L hq hk]; exact Complex.norm_real _
  have hf (i) (hi : i ∈ s) : Chart k (F i) U := g.contDiff.contDiffAt.comp _ (h i hi)
  have hy := left_prod_bound s F (a:=c) hf (fun i hi L hk hz => (he (f i) (h i hi) L hk).trans_le (hh i hi L hk hz)) l hl hd
  have hz : g ∘ (fun V => ∏ i∈s,f i V) = ∏ i∈s,F i := by
    funext U; rw [Finset.prod_apply]; exact Complex.ofReal_prod ..
  rw [←he _ (chart_product _ _ h) l hl,hz]; exact hy

section Occurrence
variable {P : BudgetPoint} {W : Windows P G n} {o : ι → Site n} {E : ι → Config G n → ℝ} {v : ι → ℝ}
variable {X}

lemma occurrence_germ (h : AtomJets W X o E v) (z : Clusters ι) : W.Germ (foot X z) (part X E z) := by
  rw [cost_eq]
  apply Windows.Germ.scale
  refine ⟨fun U V hu => ?_, Finset.measurable_fun_prod _ (fun i _ => (h.germ _).borel),fun k U => ?_,fun U hu => ?_⟩
  · exact prod_congr rfl fun i _ => (h.germ _).probes _ _ (agrees_mono hu (show X (z.2 i) ⊆ foot X z from covered X z i))
  · exact prod_congr rfl fun i _ => (h.germ _).symm k U
  exact chart_product _ _ (fun i _ => (h.germ _).smooth _ (W.less (covered X z i) hu))

private lemma covers_union (z : Clusters ι) (h : ∀ i, (X i).Nonempty)
    (hz : coefficient (blocked X) z.2 ≠ 0) : (coverNumber P.B (foot X z):ℝ) ≤ coversFee X P z := by
  have he := connected_pay _ X P.B (literal_test X h) z.2 (show (0:ℝ) ≤ 1 from zero_le_one) hz
  simpa only [currency,one_mul,←Real.exp_sum,Real.exp_le_exp,foot,coversFee] using he

private lemma covers_arity (z : Clusters ι) (h : ∀ i, (X i).Nonempty) :
    (((univ : Finset (Option (Fin z.1))).card):ℝ) ≤ coversFee X P z := by
  have hr (i) : (1:ℝ) ≤ coverNumber P.B (X i) := by
    have hv := Corona.pays (X i) P.B
    have hp := card_pos.mpr (h i)
    have hx : coverNumber P.B (X i) ≠ 0 := by rintro hh; rw [hh,zero_mul] at hv; omega
    exact_mod_cast (show 1 ≤ coverNumber P.B (X i) from Nat.pos_of_ne_zero hx)
  simpa [coversFee] using Finset.sum_le_sum (s:=(univ:Finset (Option (Fin z.1)))) fun i _ => hr (z.2 i)

set_option maxHeartbeats 600000 in
private lemma product_cap (h : AtomJets W X o E v) (z : Clusters ι) (x : Site n) (hx : x∈foot X z)
    (hz : coefficient (blocked X) z.2 ≠ 0) (U : Config G n) (hu : U ∈ W.openAt (foot X z))
    (l : List (Directions G n)) (hl : l.length ≤ P.order) (he : ∀ a∈l,P.dirBound x a) :
    ‖leftDerivs (fun V => ∏ i,E (z.2 i) V) l U‖ ≤ premium X P z * ∏ i,v (z.2 i) := by
  let s : Finset (Option (Fin z.1)) := univ
  let b := ((4:ℝ)*P.B+2)*(1+coversFee X P z)
  let r := b^P.power
  have h1 : 1 ≤ 1+coversFee X P z := le_add_of_nonneg_right (covers_pos X P z)
  have hB : 1≤b := one_le_mul_of_one_le_of_one_le
    (show (1:ℝ) ≤ (4:ℝ)*P.B+2 by have := Nat.cast_nonneg (α:=ℝ) P.B; linarith) h1
  have hr : 1 ≤ r := one_le_pow₀ hB
  have hR : 0 < r := zero_lt_one.trans_le hr
  let f i := E (z.2 i)
  have ha i : U ∈ W.openAt (X (z.2 i)) := W.less (covered X z i) hu
  have hf (i) (_ : i∈s) : Chart P.order (f i) U := (h.germ _).smooth U (ha i)
  have distance (i : Option (Fin z.1)) : (1:ℝ) + separation (o (z.2 i)) x ≤ b := by
    have d : (separation (o (z.2 i)) x:ℝ) ≤ coverNumber P.B (foot X z)*((4:ℝ)*P.B+2)+2*(P.B:ℝ) := by
      exact_mod_cast Corona.extent _ P.B (covered X z i (h.anchor (z.2 i))) hx
    have d' := mul_le_mul_of_nonneg_right (covers_union z h.full hz (P:=P)) (by positivity : (0:ℝ) ≤ (4:ℝ)*P.B+2)
    unfold b; nlinarith only [d,d',Nat.cast_nonneg (α:=ℝ) P.B]
  let p := l.map fun a => r⁻¹ • a
  let D (a : Directions G n) := ∀ i : Option (Fin z.1), P.dirBound (o (z.2 i)) a
  have hk : ∀ a∈p,D a := by
    intro a ha i
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    simpa only [r,inv_pow] using Extra.Multi.Germs.relocate_dir (distance i) (he j hj)
  have hm : 0 ≤ ∏ i,v (z.2 i) := prod_nonneg fun i _ => (h.owns _).1
  have ht := product_here s f (fun i => v (z.2 i)) D hf
    (fun i _ l hl hd => (h.owns _).2 _ (ha i) _ hl (fun a hv => hd a hv i)) p (by simpa [p]) hk
  let q := fun V => ∏ i,E (z.2 i) V
  change ‖leftDerivs q p U‖ ≤ (s.card:ℝ)^p.length * ∏ i,v (z.2 i) at ht
  change ‖leftDerivs q l U‖ ≤ _
  unfold p at ht; rw [left_homogeneous l (chart_product s _ hf) hl, norm_smul,
    Real.norm_of_nonneg (by positivity), inv_pow,List.length_map] at ht
  rw [inv_mul_eq_div,div_le_iff₀ (by positivity)] at ht
  apply ht.trans
  rw [mul_right_comm,← mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ hm
  have hb : (s.card:ℝ)*r ≤ (1+coversFee X P z)*r := mul_le_mul_of_nonneg_right
    ((covers_arity z h.full).trans (le_add_of_nonneg_left zero_le_one)) hR.le
  refine (pow_le_pow_left₀ (by positivity) hb l.length).trans ((pow_le_pow_right₀
    (one_le_mul_of_one_le_of_one_le h1 hr) hl).trans_eq ?_)
  unfold r b premium orderFee Extra.Multi.Germs.pay
  simp only [pow_mul,pow_add,mul_pow]; ring

/-- Pointwise price for all placements in the support: . -/
theorem overlap_cap (h : AtomJets W X o E v) (z : Clusters ι) (x : Site n) (hx : x∈foot X z) :
    W.Cap x (foot X z) (part X E z) (fee X P v z) := by
  refine ⟨fee_pos X _ _ (fun i => (h.owns i).1) _,fun U hu l hl he => ?_⟩
  rw [cost_eq,left_constant_mul]
  change ‖_ * _‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs (scalarWeight X z), quota]
  by_cases hZ : coefficient (blocked X) z.2 = 0
  · simp [scalarWeight,hZ]
  exact mul_le_mul_of_nonneg_left (product_cap h z x hx hZ U hu l hl he) (abs_nonneg _)
end Occurrence


section Budget
variable {P : BudgetPoint} {v : ι → ℝ} {ε γ δ q : ℝ}

def chargeRate (P : BudgetPoint) (ε γ q : ℝ) (m : ℕ) :=
    Extra.Multi.Germs.pay P * (Reserves.polyPrice ε (orderFee P) * Reserves.treeYield γ q m)

/-- Uniform derivative hit tail, for all W-windows using these v. Input
requires two extra ε reserves besides the δ for trees. No change of
norm in the tail. Even an ALL-arity price on the complete supports;
root Ω sum itself without hit-filter can still cost entire volume. -/
theorem overlap_tail (hX : ∀ i,(X i).Nonempty) (he : 0 < ε)
    (h : Ready X P.B v (P.supportExponent + 2*ε) γ δ q) (x : Site n) (m : ℕ) :
    SumBudget (fun z : Clusters ι => if m ≤ z.1 ∧ x∈foot X z then
      P.mass (foot X z) (fee X P v z) else 0) (chargeRate P ε γ q m) := by
  have ht := h.2.2.2.2.1
  let z₀ (_ : ι) := (0:ℝ)
  have hh : Ready X P.B (Reserves.tariff v z₀ z₀ ε) (P.supportExponent+2*ε) γ δ q := by
    rw [show Reserves.tariff v z₀ z₀ ε=v by ext; simp [Reserves.tariff,z₀]]; exact h
  have hp := Reserves.cluster_prices X P.B v z₀ z₀ (blocked X) (literal_test X hX) ht (fun _=>le_rfl)
    he P.exponent_pos.le hh m (orderFee P) x (fun _=>True) (T:=0) (U:=0) (fun i _ _ _ _=> by
      unfold z₀ Reserves.clusterPrice Reserves.weight; simp; positivity)
  have hf := budget_scale (show 0 ≤ Extra.Multi.Germs.pay P by unfold Extra.Multi.Germs.pay; positivity) hp
  unfold chargeRate; convert hf using 1
  · ext i
    by_cases hy : m ≤ i.1 <;> by_cases hx : x∈foot X i
    all_goals
      simp [Reserves.occurrence, show Ursell.unionOf X i.2=foot X i from rfl, hx, hy, fee,
        premium,coversFee,BudgetPoint.mass,Reserves.clusterPrice,Reserves.weight,currency,z₀,mul_comm,mul_left_comm,mul_assoc]
  · simp [Reserves.extract]

theorem overlap_price (hX : ∀ i,(X i).Nonempty) (he : 0 < ε)
    (h : Ready X P.B v (P.supportExponent + 2*ε) γ δ q) :
    Ac.Hit (foot X) P.B (fee X P v) P.supportExponent (chargeRate P ε γ q 0) := by
  intro x
  simpa only [Nat.zero_le,true_and,BudgetPoint.mass,mul_comm (Real.exp _)] using overlap_tail X hX he h x 0

/-- All priced labels (including arbitrary padding/duplicates) with
nonempty footprints in finite volume. Use with `Ac.Hit`. -/
lemma volume_sum (hX : ∀ i, (X i).Nonempty) (ht : ∀ i,0≤v i) (h : Ac.Hit X P.B v P.supportExponent γ) :
    Summable v := by
  let f (x : Site n) i := if x∈ X i then v i * Real.exp (P.supportExponent*(coverNumber P.B (X i))) else 0
  have he x : SumBudget (f x) γ := h x
  have hw i : v i ≤ ∑ x : Site n,f x i := by
    obtain ⟨x,hx⟩ := hX i
    have hh : v i ≤ f x i := by
      unfold f; rw [if_pos hx, mul_comm]; exact P.loMass (X i) _ (ht _)
    exact hh.trans (single_le_sum (f:=fun x => f x i) (fun x _=>(he x).1 _) (mem_univ x))
  exact (summable_sum (fun x _ => (he x).2.1)).of_nonneg_of_le ht hw

lemma fee_sum (hX : ∀ i,(X i).Nonempty) (he : 0 < ε)
    (h : Ready X P.B v (P.supportExponent + 2*ε) γ δ q) : Summable (fee X P v) :=
  volume_sum _ (fun z => footprint_full X z hX) (fee_pos X P v h.2.2.2.2.1) (overlap_price X hX he h (P:=P))
end Budget
end YM.Further.LogJets
