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
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Bid.Drops
import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.Initialize
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B04

set_option warningAsError false

/-!
# Sharpen the indispensable one-source forced merger

For local canonical extraction from raw bulk outputs. Pack version,
compatible with the calibrated histories & Born machine. Here even
need an actual Mint on the *incoming* vacuum at any additional exponent
used on OUTPUT. Note E may use even more. Assumes μ purchase, however
even at fixed stage B, it needn't pay any factor exp(card Support),
as in the general Multi sharing statement for sources with small
stencils. Critical when the raw bulk inputs may be at growing/unbounded
cover sizes/winding and we apply THROUGHOUT the stages without giving up
exponent in the paired trajectory itself. `invoice` accomplishes this by
charging through one compulsory Pack absorption with simultaneous small
site-hit budget, then spending two units of reserve. Don't assume a
factor on its tariff at every input AND already consumed in a mix.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Primary
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Finset
open Multi.Couples
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge} (P : Rep G n)

lemma rough (Y : Support n) (D : Config G n→ℂ) (U : Config G n) (h : Weight P.p Y D) {δ κ : ℝ}
    (hP : P.activities.Valid P.p δ κ) :
    tangent P (0,ballast Y P D) U=(P.eval U:ℂ)*D U := by
  let C : Vessel G n := ⟨Y,0,D⟩
  have hs : masked P.p.threshold Y D=0 := by
    funext x; by_cases he : Healthy P.p.threshold Y x
    · rw [masked_eq _ _ _ _ he]; change D x=0
      by_contra ht
      obtain ⟨v,hv,hf⟩ := h.needs x ht; exact disjoint_left.mp he hv hf
    rw [masked_ne _ _ _ _ he]; rfl
  have ht : C.tail P=D := by ext1 x; simp only [C,Vessel.tail,Vessel.cheek,Vessel.full,hs,Pi.zero_apply]; ring
  have he := Multi.birth_tangent P C hP (ht ▸ h) U
  change tangent P (C.cheek P,ballast Y P (C.tail P)) U=(P.eval U:ℂ)*(0+D U) at he
  rwa [ht,zero_add,show C.cheek P=0 from funext fun x => by simp [Vessel.cheek,C,hs]] at he

lemma credible (Y : Support n) (D : Config G n→ℂ) (h : Weight P.p Y D) {δ κ : ℝ} (hp : P.activities.Valid P.p δ κ)
    (i : Pack n) : Legible P.p i (ballast Y P D i) ∧ (ballast Y P D i≠0 → Y ⊆ i.zone) := by
  have he := Multi.Couples.single_payload (fun _ : Unit => Y) P (fun _ => D) i ()
  have hf : Multi.Couples.payload (fun _ : Unit => Y) P (fun _ => D) {()} i=ballast Y P D i := funext he
  refine ⟨hf ▸ (Multi.Couples.pay_legible (Y:=fun _ : Unit => Y) P _ {()} i hp.forced fun _ => h),?_⟩
  intro hi x hx; by_contra he'; apply hi
  funext U
  unfold ballast
  split
  · rw [sum_eq_zero (fun j hj => ?_),mul_zero]; rfl
    obtain ⟨_,_,_,hg,_⟩ := (mem_filter.mp hj).2
    exact False.elim (he' (hg ▸ Finset.mem_union_left _ hx))
  rfl

private def relevant (Y : Support n) (S : Finset (Pack n)) : Prop := S.Nonempty ∧ (S:Set (Pack n)).PairwiseDisjoint Pack.zone ∧
      ∀ j∈S,¬ Disjoint Y j.zone
private def pooled (Y : Support n) (p : Pack n) (S : Finset (Pack n)) :=
    Y∪S.biUnion Pack.zone=p.zone ∧ S.biUnion Pack.flagsAt=p.flagsAt
private noncomputable def portfolio (Y : Support n) (p : Pack n) : Finset (Finset (Pack n)) :=
    univ.filter fun S => relevant Y S ∧ pooled Y p S

private lemma pooled_unique (Y : Support n) (j : Finset (Pack n)) {p q : Pack n} (h : pooled Y p j)
    (he : pooled Y q j) : p=q := Subtype.ext (Prod.ext (h.1.symm.trans he.1) (h.2.symm.trans he.2))

private def territories (Y : Support n) : Finset (Pack n) := Y.biUnion (fun i => univ.filter (fun p : Pack n => i∈p.zone))

private def pBound (f : Pack n→ℝ) (Y : Support n) (c : ℝ) (p : Pack n) := c*∑ S∈portfolio Y p, ∏ i∈S, f i

private lemma zones (Y : Support n) (p : Pack n) (S : Finset (Pack n)) (h : S∈portfolio Y p) : S ⊆ territories Y := by
  intro i hi
  have ht := (mem_filter.mp h).2.1.2.2 i hi
  obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp ht
  refine Finset.mem_biUnion.mpr ⟨x,hx, Finset.mem_filter.mpr ?_⟩; exact ⟨mem_univ _,hy⟩

private lemma pBudget (f : Pack n → ℝ) (Y : Support n) (D : Config G n → ℂ) (hf : ∀ i,0 ≤ f i ∧ ∀ U,‖incumbent P U i‖≤f i)
    (q : ℝ) (hq : 0≤q) (hc : ∀ U, ‖D U‖ ≤ q) (i) : 0 ≤ pBound f Y q i ∧ ∀ U, ‖ballast Y P D i U‖ ≤ pBound f Y q i := by
  have hp : 0 ≤ pBound f Y q i := mul_nonneg hq (sum_nonneg fun j _ => prod_nonneg fun i _ => (hf i).1)
  refine ⟨hp,fun U => ?_⟩
  unfold ballast; split
  · rw [norm_mul]; refine mul_le_mul (hc _) ((norm_sum_le ..).trans ?_) (norm_nonneg _) hq
    refine le_trans (sum_le_sum (g:=fun j => ∏ i∈j,f i) fun j _ => ?_) ?_
    · rw [norm_prod]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (hf i).2 _)
    apply le_of_eq; apply Finset.sum_congr _ (fun _ _ => rfl); ext S; simp only [portfolio,pooled,relevant,
      and_assoc,mem_filter]
  rw [norm_zero]; exact hp

private lemma combined (Y : Support n) (S : Finset (Pack n))
    (h : ∀ j∈S, ¬ Disjoint Y j.zone) (B) : coverNumber B (Y∪S.biUnion Pack.zone)≤coverNumber B Y+∑ i∈S, coverNumber B i.zone := by
  induction S using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    specialize ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨x,hx,hv⟩ := Finset.not_disjoint_iff.mp (h i (mem_insert_self ..))
    let X := (Y ∪ Finset.biUnion s Pack.zone)
    have he : x∈ X := Finset.mem_union_left _ hx
    rw [biUnion_insert,show Y∪ (i.zone ∪ _)=i.zone∪ X by unfold X; rw [Finset.union_left_comm],sum_insert hi]
    change coverNumber B X ≤ _ at ih
    exact (Corona.meets_sum hv he B).trans (by omega)

/-- Sharp in |Y| μ. No assumption of smallness on Y. Use with μ small
relative to the volume PER regulator ball to subsequently price the exponent.
-/
lemma inventory (Y : Support n) (F : Config G n→ℂ) {μ c r : ℝ} (h : Mint P r μ) (hr : 0 ≤ r)
    (hc : 0 ≤ c) (hf : ∀ U, ‖F U‖≤c) :
    ∃ f : Pack n→ℝ, (∑ i,burn P.p r i.zone*f i) ≤ burn P.p r Y * c * (Real.exp ((Y.card:ℝ)*μ)-1) ∧
      ∀ i, 0 ≤ f i ∧ ∀ U, ‖ballast Y P F i U‖ ≤ f i := by
  obtain ⟨f,hf',hg⟩ := h
  let g i := burn P.p r (Pack.zone i)*f i
  let V := (territories Y).powerset.erase ∅
  let s := burn P.p r Y
  have hZ : 0 ≤ s := (burn_pos ..).le
  have hh i : 0 ≤ g i := mul_nonneg (burn_pos ..).le (hf' _).1
  have he : ∑ i∈ territories Y, g i ≤ (Y.card:ℝ)*μ := by
    rw [show (Y.card:ℝ)*μ = ∑ _∈ Y, μ from Eq.symm (by simp)]
    let T i j := if i∈Pack.zone j then g j else 0
    calc
      ∑ i∈territories Y, g i ≤ ∑ i∈territories Y,∑ x∈Y,T x i := sum_le_sum fun i hi => by
        obtain ⟨x,hx,h⟩ := mem_biUnion.mp hi
        refine (show g i ≤ T x i from ?_).trans (Finset.single_le_sum (f:=fun x => T x i) (fun i _ => ?_) hx)
        · exact (if_pos (Finset.mem_filter.mp h).2).symm.le
        unfold T; split; exact hh _; exact le_rfl
      _ ≤ ∑ i,∑ x∈Y,T x i := sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sum_nonneg (fun j _ => by
        unfold T; split; exact hh _; exact le_rfl))
      _ ≤ _ := by
        rw [sum_comm]; refine Finset.sum_le_sum fun x _ => ?_
        rw [← Finset.sum_filter]; exact hg x -- le μ
  have hT : (∑ S∈ V,∏ i∈S, g i) ≤ Real.exp (Y.card*μ)-1 := by
    apply le_sub_iff_add_le.mpr
    rw [show (1:ℝ)=∏ i∈∅,g i from rfl,Finset.sum_erase_add _ _ (by simp),← prod_one_add]
    exact ((prod_le_prod (fun i _ => add_nonneg zero_le_one (hh i)) (fun i _ => (add_comm ..).le.trans (Real.add_one_le_exp (g i))))).trans
      (by rw [←Real.exp_sum]; exact Real.exp_monotone he)
  have hI :
      (∑ i : Pack n, ∑ S∈portfolio Y i, ∏ i∈S,g i) ≤ ∑ S∈V,∏ i∈S,g i := by
    let q p S := if S∈portfolio Y p then ∏ i∈S,g i else 0
    calc
      _ = ∑ i : Pack n,∑ S∈ V,q i S := by
        apply Finset.sum_congr rfl; intro i _
        unfold q; rw [← Finset.sum_filter]; apply Finset.sum_congr ?_ fun j _ => rfl
        ext j; rw [mem_filter]; exact ⟨fun h => ⟨mem_erase.mpr ⟨(Finset.mem_filter.mp h).2.1.1.ne_empty,
          mem_powerset.mpr (zones Y i j h)⟩,h⟩,And.right⟩
      _ ≤ _ := by
        rw [sum_comm]; apply sum_le_sum; intro j hj
        by_cases he : ∃ i : Pack n, j∈portfolio Y i
        · obtain ⟨i,hi⟩ := he
          rw [Finset.sum_eq_single i, show q i j= ∏ i∈j,g i from if_pos hi]
          · intro p _ hh; exact if_neg fun h => hh (pooled_unique Y _ (Finset.mem_filter.mp h).2.2 (Finset.mem_filter.mp hi).2.2)
          simp
        push Not at he; rw [Finset.sum_eq_zero (fun i _ => if_neg (he i))]; exact prod_nonneg fun i _ => hh _
  refine ⟨pBound f Y c,le_trans ?_ (mul_le_mul_of_nonneg_left (hI.trans hT) (mul_nonneg hZ hc)),pBudget P f Y _ hf' c hc hf⟩
  rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro p _; unfold pBound
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]; apply sum_le_sum; intro j hj
  have ht := (mem_filter.mp hj).2.2.1
  change Y ∪ _=p.zone at ht
  have hx := combined Y j ((mem_filter.mp hj).2.1.2.2) P.p.B
  rw [ht] at hx
  have hW : burn P.p r p.zone ≤ s*∏ i∈j,burn P.p r i.zone := by
    unfold s burn; rw [← Real.exp_sum,← Real.exp_add,← Finset.mul_sum, ← mul_add]
    apply Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ (add_nonneg P.p.exponent_pos.le hr))
    exact_mod_cast hx
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW hc) (prod_nonneg fun i _ => (hf' i).1)).trans_eq
  unfold g; rw [prod_mul_distrib]; ring

/-- Maximum sites per cover ball (handles wraps). Require late clock for
its absorption. Its uses still depend on buying Mint at corresponding output
exponent.
-/
def cells (P : BudgetPoint) : ℝ := ( (P.B+P.B+1)^4 : ℕ)
lemma cash {Y : Support n} : (Y.card:ℝ) ≤ coverNumber P.p.B Y*cells P.p := by
  unfold cells; exact_mod_cast Corona.pays Y P.p.B

lemma cashBill (Y : Support n) {μ κ c r : ℝ} (hm : 0 ≤ μ) (hc : 0≤c) (hκ : μ ≤ κ) (hA : cells P.p * μ ≤ 1) :
    burn P.p r Y * c * (Real.exp ((Y.card:ℝ)*μ)-1) ≤ κ*(cells P.p * (burn P.p (r+2) Y*c)) := by
  let x : ℝ := Y.card; let d : ℝ := coverNumber P.p.B Y; let y := cells P.p
  have hd : 0 ≤ d := by positivity
  have he : 0≤x := by positivity
  have hy : 0≤y := by unfold y cells; positivity
  have hx : x≤ d*y := cash P
  have hl : x*μ ≤ d := calc
    _ ≤ d*y*μ := mul_le_mul_of_nonneg_right hx hm
    _ = d*(y*μ) := mul_assoc ..
    _ ≤ d := mul_le_of_le_one_right hd hA
  have hh : Real.exp (x*μ)-1 ≤ x*μ*Real.exp (x*μ) := by
    have hw := Real.add_one_le_exp (-(x*μ))
    rw [Real.exp_neg,← one_div, le_div_iff₀ (Real.exp_pos _)] at hw
    linarith
  have hB : burn P.p (r+2) Y= (burn P.p r Y)*(Real.exp d)*(Real.exp d) := by
    unfold burn; rw [← Real.exp_add,← Real.exp_add]; unfold d; ring_nf
  let g := burn P.p r Y*c; have hg : 0≤g := mul_nonneg (burn_pos ..).le hc
  have hF i := (Real.exp_pos i).le
  calc
    _ ≤ g * (d*y*κ*Real.exp d) := mul_le_mul_of_nonneg_left (le_trans hh (mul_le_mul (mul_le_mul hx hκ hm (mul_nonneg hd hy)) (Real.exp_monotone hl) (hF _) (mul_nonneg (mul_nonneg hd hy) (hm.trans hκ)))) hg
    _ ≤ g * (Real.exp d*y*κ*Real.exp d) := by
      apply mul_le_mul_of_nonneg_left _ hg
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hy) (hm.trans hκ)) (hF _)
      linarith only [Real.add_one_le_exp d]
    _ = _ := by rw [hB]; dsimp only [g,y]; ring

theorem invoice (Y : Support n) (F : Config G n→ℂ) (hF : Weight P.p Y F) {μ κ c r σ w : ℝ} (hV : P.activities.Valid P.p σ w)
    (hκ : μ ≤ κ) (hm : cells P.p * μ ≤ 1) (hr : 0 ≤ r) (hM : Mint P r μ)
    (hc : 0 ≤ c) (hf : ∀ U, ‖F U‖ ≤ c) :
    ∃ f : Pack n→ℝ, (∑ i,burn P.p r i.zone*f i) ≤ κ*(cells P.p*(burn P.p (r+2) Y*c)) ∧
      ∀ i, Legible P.p i (ballast Y P F i) ∧ (ballast Y P F i ≠ 0 → Y ⊆ i.zone) ∧ 0 ≤ f i ∧
        ∀ U, ‖ballast Y P F i U‖ ≤ f i := by
  obtain ⟨f,hQ,h⟩ := inventory P Y F hM hr hc hf
  obtain ⟨g,hg,he⟩ := hM
  have ht : 0 ≤ μ := le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (burn_pos ..).le (hg i).1) (he 0)
  exact ⟨f,hQ.trans (cashBill P Y ht hc hκ hm),fun i => ⟨(credible P Y F hF hV i).1,(credible P Y F hF hV i).2, h _⟩⟩
end YM.AnalyticNext.GridStop.Primary
