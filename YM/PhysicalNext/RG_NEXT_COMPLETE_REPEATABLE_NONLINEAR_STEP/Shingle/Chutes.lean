import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Sunroom
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Alto
/-!
 # Jets budget of graft. sharpened kernels varied before prices of mergers.
 Adapt authentic source interval, scalar phase treat Angle separately. No annulus assumption.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shingle
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {B : BudgetPoint} {X : Listing G c} {z w : ℕ} {e p d a δ Y : ℝ} {x:ℝ} {s:Set ℝ}
section curves
variable {V : ℝ→ Collection.Source G c}
-- Prop bool variation. independent across Tape
lemma curtain (h:Compared X B V s) (f:ℕ→Prop) {u:ℝ→ Collection.Source G c}
    (he:∀ x∈s, (u x).hardRead=(V x).hardRead) (ht:∀ x∈s,∀ i,(u x).logRead i= if f i then (V x).logRead i else 0):Compared X B u s:= by
  constructor
  · intro x hx; have hm:= h.values x hx
    constructor
    · intro i ε hε; filter_upwards [self_mem_nhdsWithin,hm.1 i ε hε] with y hy hv
      change variesRegular _ (X.reg i) ((u x).logRead i) ((u y).logRead i) _; rw [ht _ hx,ht _ hy]; split; exact hv
      exact ⟨hε.le,fun _ _ _ _ _=> by simp [hε.le]⟩
    intro i ε hε; filter_upwards [self_mem_nhdsWithin,hm.2 i ε hε] with y hy hv U
    change ‖(u x).hardRead i U-(u y).hardRead i U‖≤_; rw [he _ hx,he _ hy]; exact hv U
  intro x hx y hy
  obtain ⟨r,f',k,hr,hk,hq,hp,hE⟩:= h.series x hx y hy
  have h (x:ℝ) (hx:x∈s) (he' : Majorizes B f' k (X.read (V x))): Majorizes B f' k (X.read (u x)):= by
    constructor
    · intro i; change B.supBounds ((X.reg i).site) (X.reg i).support ((u x).logRead i) (f' i); rw [ht _ hx]; split; exact he'.smooth i
      exact VerifiedReset.sup_le (CouplingShape.sup_const 0) (by rw [abs_zero]; exact (he'.smooth i).1)
    intro i; refine ⟨he'.hard i|>.1,?_⟩; intro U; change ‖(u x).hardRead i U‖ ≤ k i; rw [he _ hx]; exact (he'.hard _).2 _
  exact ⟨r, f',k,hr,hk,hq,h x hx hp, (hE.and ((hy.comp hr).eventually self_mem_nhdsWithin)).mono fun i hx=> h _ hx.2 hx.1⟩
end curves
variable (z w)
section major
variable {y : ℕ→ℝ} {V:ℝ→ Collection.Source G c} {g t: ℝ → Trio.Offer G c}
   {p k : ℕ→ℝ}
    (hp : ∀ x∈s,∀ i,B.Regular (neighbors z i) (g x i))
    (ht:∀ x∈s,∀ i,B.supBounds i (neighbors z i) (g x i) a)
    (hc:∀ x∈s,∀ i U,‖t x i U‖ ≤ d)
local notation "Z" => (Marlin.lodge X z w)
local notation "D" => (fun x=> Marlin.bison (V x) (g x) (t x))
include hp ht hc
lemma gatheredCrew (he : x∈s) (hy : ∀ᶠ i in atTop,y i∈s) (hP: Summable p) (hk: Summable k)
   (h : Majorizes B p k (X.read (V x))) (hh : ∀ᶠ i in atTop, Majorizes B p k (X.read (V (y i)))) :
    ∃ e b:ℕ→ℝ,Summable e ∧ Summable b ∧ Majorizes B e b (Ovens.Pipes.fused (hak Z) B (D x)) ∧
      ∀ᶠ i in atTop, Majorizes B e b (Ovens.Pipes.fused (hak Z) B (D (y i))) := by
  let u:= Rim c*d
  let w' := Marlin.tract c d
  let e:=Sum.elim p (fun _ : Door c=> Rim c* (turnFee B *a)); let g':ℕ→ℝ:=e ∘ leanU c
  have hD := (norm_nonneg _).trans (hc x he 0 1); have hu : 0≤u:= mul_nonneg (rim_nn _) hD
  let F:=Real.exp u; let b:=w' ∘ leanU c
  have hv i:b i=0 ∨ b i=u:= by change w' (leanU c i)=0∨w' (leanU c i)=u; cases leanU c i; exact Or.inl rfl; exact Or.inr rfl
  have hb : Summable b:= (leanU c).summable_iff.mpr (Summable.sum w' (show Summable (fun i:ℕ=>w' (.inl i)) from summable_zero) Summable.of_finite)
  let D' := Sum.elim k (fun i=> F * b i)
  have hF : Summable D':= Summable.sum D' hk (hb.mul_left F)
  let R (i:ℕ):= ∏ j∈ (hak Z i).val,D' j
  have hR : Summable R:= (summable_finsetProd_of_summable_norm hF.norm).comp_injective (f:=fun i:Finset Ovens.Label=>∏ j∈i,D' j) (i:=(Subtype.val ∘ (hak Z))) (Subtype.val_injective.comp (hak Z).injective) -- check binder
  have ht' i:0≤D' i:= by
    cases i
    · exact (h.hard _).1
    next i=> rcases hv i with hv|hv; all_goals change 0 ≤ F * b i; rw [hv]; first | simp | exact mul_nonneg (Real.exp_nonneg _) hu
  have hm (x:ℝ) (h:x∈s) (hE:Majorizes B p k (X.read (V x))): Majorizes B g' R (Ovens.Pipes.fused (hak Z) B (D x)) := by
    let A:= g x; let E:= t x
    have hi i V':‖(D x).logarithm i V'‖ ≤ b i:= Marlin.softly _ _ _ (hc x h) _ _ _
    constructor
    · intro i
      let y:= leanU c i; change B.supBounds ((Sum.elim X.reg _ y:RegularAddress c).site) (Sum.elim X.reg (sea z) y|>.support) (Sum.elim (V x).logRead (choir A) y) (e y); cases y with
      | inl i=> exact hE.smooth i
      | inr i=>
        have he := CouplingShape.sup_scale (Rim c) (Song.transSup i.1 (hp _ h i.2) (ht x h i.2)); rw [abs_of_nonneg (rim_nn _)] at he; exact he
    intro i; have hx : 0≤ R i:= prod_nonneg (fun j _=> ht' j)
    refine ⟨hx,fun U=>?_⟩
    change ‖(solid (hak (Marlin.lodge X z w)) B (D x) i U)‖ ≤ _; unfold Ovens.Pipes.solid; split
    next hX=>
      rw [norm_prod]; refine prod_le_prod (fun i _=>norm_nonneg _) fun j _=>?_ ; cases j
      · exact (hE.hard _).2 U
      next j hj=>
        let a:= (D x).logarithm j U; have ha: ‖a‖≤ b j:= hi j U; have hx: ‖a‖≤ u:=ha.trans (by rcases hv j with h|h; exact h.trans_le hu; exact h.le)
        change ‖Real.exp a-1‖ ≤ F*b j; apply le_trans _ (mul_le_mul_of_nonneg_left ha (Real.exp_nonneg u)); rw [Real.norm_eq_abs,Real.norm_eq_abs]; by_cases h:0≤a
        · have hv:= Real.add_one_le_exp (-a)
          rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp h)), abs_of_nonneg h]; apply le_trans _ (mul_le_mul_of_nonneg_right (Real.exp_monotone (b:=u) ((le_abs_self _).trans hx)) h)
          have hh:=mul_le_mul_of_nonneg_left hv (Real.exp_nonneg a); rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh; linarith only [hh]
        have hv:=le_of_not_ge h; rw [abs_of_nonpos hv, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hv))]; apply le_trans _ (le_mul_of_one_le_left (by linarith only [hv] : 0 ≤ -a) (Real.one_le_exp hu)); linarith only [Real.add_one_le_exp a]
    rw [norm_zero]; exact hx
  exact ⟨g',R, (leanU c).summable_iff.mpr (Summable.sum e hP Summable.of_finite),hR,hm x he h, (hh.and hy).mono fun i hh=> hm _ hh.2 hh.1⟩
end major
end YM.PhysicalNext.Repeat.Shingle
