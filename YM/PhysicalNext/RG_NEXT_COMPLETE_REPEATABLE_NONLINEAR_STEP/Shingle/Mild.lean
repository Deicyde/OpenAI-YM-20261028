import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Loft
/-!
 # Whole-sector Lens: convergence. even translated direction. Use finite supports AFTER anchor redistribution. 
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
open Refrain    Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {B : BudgetPoint} {X Z: Support c} {z w : ℕ} {e p d a δ Y : ℝ} {x:ℝ} {s:Set ℝ} {ι:Type} {f g:ℝ→ Config G c→ℝ}
-- Gauge/convergence along valid interval. Sum budget in limit.
structure Mild (B:BudgetPoint) (X:Support c) (f:ℝ→ Config G c→ℝ) (s:Set ℝ) : Prop where
  smooth i : i∈s→B.Regular X (f i)
  budget (x : ℝ) : x∈s→∀ i:Site c,∀ ε> (0:ℝ),∀ᶠ y in 𝓝[s] x,B.supBounds i X (f x-f y) ε
namespace Mild
variable (hp: Mild B X f s) (h: Mild B X g s)
lemma tagged (h : ∀ i∈s,B.Regular X (f i)) (i:RegularAddress c) (ht:X=i.support) (hv: ∀ x∈s,∀ ε>0,∀ᶠ y in 𝓝[s] x,variesRegular B i (f x) (f y) ε) : Mild B X f s:= by
  refine ⟨h,fun x hx k ε he=>?_⟩; subst X; obtain ⟨V,hV,H⟩:= Meadow.supHeight (G:=G) (n:=c) B; have hh:= zero_lt_one.trans_le hV
  filter_upwards [self_mem_nhdsWithin, hv x hx _ (div_pos he hh)] with y hy hX
  have hp:=H i.site k _ _ (VerifiedReset.reg_sub (h x hx) (h y hy)) _ ((VerifiedReset.sup_varies (d:=i) (h _ hx) (h _ hy)).1 hX)
  exact VerifiedReset.sup_le hp (le_of_eq (by field_simp))
include hp
lemma stillA : Mild B X (fun i=>Boulevard.stillA (f i)) s:= by
  refine ⟨fun i hi=> VerifiedReset.reg_sub (hp.smooth _ hi) (CouplingShape.reg_const _),fun x hx i ε ht=>?_⟩
  filter_upwards [self_mem_nhdsWithin,hp.budget x hx i (ε/2) (half_pos ht)] with y hy hz
  let P (_ : Config G c):= f x 1-f y 1; have he: B.supBounds i X P (ε/2) := by
    have hv := hz.2 1 (flat_ok ..) [] (Nat.zero_le _) (by simp)
    exact VerifiedReset.sup_le (CouplingShape.sup_const _) hv
  rw [show Boulevard.stillA (f x)-Boulevard.stillA (f y)= (f x-f y)-P from (by ext u; change f x u-f x 1-(f y u-f y 1)=_-(f x 1-f y 1); dsimp only [Pi.sub_apply]; ring)]
  exact VerifiedReset.sup_le (CouplingShape.sup_sub (VerifiedReset.reg_sub (hp.smooth _ hx) (hp.smooth _ hy)) (CouplingShape.reg_const _) hz he) (le_of_eq (add_halves _))
lemma mono (he : X ⊆ Z): Mild B Z f s:= ⟨fun x hx=> CouplingShape.reg_extend (hp.smooth x hx) he, fun x hx i ε h=> (hp.budget x hx i ε h).mono fun _ h=> VerifiedReset.sup_larger h he⟩
lemma scale (a:ℝ): Mild B X (fun x=>a • f x) s:= by
  refine ⟨fun x hx=> CouplingShape.reg_scale _ (hp.smooth _ hx),fun x hx i ε h=> ?_⟩
  by_cases hA:a=0; · subst a; simp only [zero_smul,sub_zero]; filter_upwards with y; exact VerifiedReset.sup_le (CouplingShape.sup_const 0) (by rw [abs_zero]; exact h.le) -- edit
  have ha:0 < |a|:= abs_pos.mpr hA
  filter_upwards [hp.budget _ hx i (ε / |a|) (div_pos h ha)] with y hy; rw [← smul_sub]; exact VerifiedReset.sup_le (CouplingShape.sup_scale a hy) (le_of_eq (by field_simp))
lemma clipped (x) (hx:x∈s): Varies (fun i=> masked B.threshold X (f i)) x s:= by
  intro ε he; filter_upwards [hp.budget _ hx 0 ε he] with y hv i
  have h : masked B.threshold X (f x) i-masked B.threshold X (f y) i = masked B.threshold X (f x-f y) i:= by by_cases ht:Healthy B.threshold X i <;> simp [masked_eq,masked_ne, ht]
  rw [h]; exact CouplingShape.mask_cost hv i
lemma travels (x) (hx:x∈s) (V:Config G c) (h : Healthy B.threshold X V): Varies (fun i (_ : Config G c)=> f i V) x s:= by
  intro ε he; filter_upwards [hp.clipped x hx ε he] with y hv i
  have hg:=hv V; rwa [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h] at hg
lemma aboard {y : Set ℝ} {g: ℝ→ Config G c→ℝ} (b:ℝ→ℝ) (hb : ContinuousOn b y) (he:Set.MapsTo b y s) (h :∀ i∈y, g i=f (b i)): Mild B X g y:= by
  refine ⟨fun i hi=> (h i hi).symm ▸ hp.smooth _ (he hi),fun x hx i ε hε=>?_⟩
  have ht := hb x hx |>.tendsto_nhdsWithin (he); filter_upwards [self_mem_nhdsWithin,ht.eventually (hp.budget _ (he hx) i ε hε)] with k hk hg; rw [h x hx,h k hk]; exact hg
include h
lemma add : Mild B X (f+g) s:= by
  refine ⟨fun i hi=> ?_,fun x hx i ε he=>?_⟩
  · have hh:= VerifiedReset.reg_sub (hp.smooth i hi) (CouplingShape.reg_scale (-1) (h.smooth i hi)); rw [neg_one_smul, sub_neg_eq_add] at hh; exact hh
  filter_upwards [self_mem_nhdsWithin,hp.budget x hx i _ (half_pos he),h.budget x hx i _ (half_pos he)] with y hy hE hF
  have hh := CouplingShape.sup_sub (VerifiedReset.reg_sub (hp.smooth _ hx) (hp.smooth _ hy)) (CouplingShape.reg_scale (-1) (VerifiedReset.reg_sub (h.smooth _ hx) (h.smooth _ hy))) hE (CouplingShape.sup_scale (-1) hF)
  rw [abs_neg, abs_one,one_mul, neg_one_smul,sub_neg_eq_add, add_halves, show f x-f y+(g x - g y)=(f+g) x-(f+g) y from (by simp; abel)] at hh; exact hh
omit h hp
lemma total (F:Finset ι) {g:ι→ℝ→ Config G c→ℝ} (h:∀ i∈ F,Mild B X (g i) s): Mild B X (fun x=>∑ i∈F,g i x) s:= by
  have he:(fun x=>∑ i∈F,g i x)= ∑ i∈ F, g i:=funext fun i=>(Finset.sum_apply ..).symm
  rw [he]; clear he; induction F using Finset.induction_on with
  | empty=> rw [sum_empty]; refine ⟨fun _ _=>CouplingShape.reg_const _,fun _ _ i ε he=>?_⟩; filter_upwards with y; change B.supBounds i X (0-0:Config G c→ℝ) ε; rw [sub_zero]; exact VerifiedReset.sup_le (CouplingShape.sup_const 0) (by rw [abs_zero]; exact he.le)
  | @insert i F hi ih=> rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma weighted {A:Type*} {f:ι→ℝ→A→ℝ} (t:Finset ι) (h : ∀ i∈t, Varies (f i) x s): Varies (fun x k=> ∑ i∈t,f i x k) x s:= by
  induction t using Finset.induction_on with
  | empty=> simp_rw [sum_empty]; exact Varies.fixed _
  | @insert i t he ih=> simp_rw [sum_insert he]; exact (h i (mem_insert_self ..)).add (ih fun j hj=> h j (mem_insert_of_mem hj))
end Mild
end YM.PhysicalNext.Repeat.Shingle
