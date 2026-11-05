import YM.RG08.Arc.Tow

/-! # After pointwise Wick along path: exchange evaluated finite polynomials,
      NOT any smooth perturbative tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial YM.PertExtension.Chart YM.PertExtension.GaussianScore
open Function Finset Analysis Stationary
open scoped BigOperators Topology Real ContDiff Classical
variable {E X Y : Type*}

section spr
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
-- Grass E lives Type; specialize
end spr
section G
variable {E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ→ E→ℝ}
inductive Meadow : (ℝ→ E→ℝ)→Prop where
 | seeds {f : E→ℝ} {g : ℝ→ℝ} : Grass f → ContDiffAt ℝ ∞ g 0 → Meadow (fun t=> g t • f)
 | more {f g : ℝ→ E→ℝ} : Meadow f → Meadow g → Meadow (f+g)
lemma Meadow.work (p : ℝ→ℝ) (h : ContDiffAt ℝ ∞ p 0) : Meadow (fun t:ℝ=> fun _:E=>p t) := by
  rw [show (fun t (x:E)=>p t)=(fun t : ℝ=>p t • fun _:E=>(1:ℝ)) from funext fun t=>funext fun x=>by simp]
  exact Meadow.seeds (Grass.const 1) h
lemma Meadow.single {f : E→ℝ} (h : Grass f) : Meadow (fun _=>f) := by simpa using! Meadow.seeds h (contDiffAt_const (c:= (1:ℝ)))
lemma Meadow.sets (h : Meadow f) (t : ℝ) : Grass (f t) := by induction h with| seeds h _=> exact h.scale _| more _ _ hp hv=> exact hp.sum hv
lemma Meadow.arc (h : Meadow f) (x : E) : ContDiffAt ℝ ∞ (fun t : ℝ=> f t x) 0 := by induction h with| seeds _ h=> exact h.mul contDiffAt_const| more _ _ hp hv=> exact hp.add hv
lemma Meadow.times (h : Meadow f) (hp : Meadow g) : Meadow (f*g) := by
  induction h with
  | @seeds f g h he=>
    induction hp with
    | @seeds F H hF hG => exact (show ((fun t=>g t • f)*(fun t=>H t • F))=(fun t:ℝ=> (g*H) t • (f*F)) by funext t x; simp; ring) ▸ Meadow.seeds (h.times hF) (he.mul hG) -- cast direction?
    | more _ _ hx hy=> rw [mul_add]; exact hx.more hy
  | more _ _ hx hy=> rw [add_mul]; exact hx.more hy
lemma Meadow.sum {ι : Type*} {f : ι→ℝ→E→ℝ} {s : Finset ι} (h : ∀ i∈s,Meadow (f i)) : Meadow (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=> rw [Finset.sum_empty]; exact Meadow.single (Grass.const 0)
  | insert i s hi ih=>rw [Finset.sum_insert hi]; exact (h _ (mem_insert_self ..)).more (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma Meadow.prod {ι : Type*}{f : ι→ℝ→E→ℝ}{s : Finset ι} (h : ∀ i∈s, Meadow (f i)) : Meadow (∏ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=> rw [Finset.prod_empty]; exact Meadow.single (Grass.const 1)
  | insert i s hi ih=>rw [Finset.prod_insert hi]; exact (h _ (mem_insert_self ..)).times (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma Meadow.sums {ι : Type*}{F : ι→ℝ→E→ℝ}{s : Finset ι} (h : ∀ i∈s, Meadow (F i)) : Meadow (fun t x=>∑ i∈s, F i t x) := by
  rw [show (fun t x=> ∑ i∈s,F i t x)=∑ i∈s,F i from funext fun t=>funext fun x=> by simp [Finset.sum_apply]]; exact Meadow.sum h
variable [Fintype X]
lemma meadowCompose {F : Psalm X} (h : Grass F) {f : ℝ→ E→ X→ℝ} (he : ∀ i, Meadow (fun t x=> f t x i)) : Meadow (fun t x=> F (f t x)) := by
  induction h with
  | @base k p hp =>
    obtain ⟨A,hv,rfl⟩:=hp
    let Y (u : Fin k→X) := (∏ i, (fun t:ℝ=>fun x : E=> f t x (u i))) * (fun _ : ℝ=>fun _ : E=> A (fun i=> Pi.single (u i) 1))
    rw [show (fun (t:ℝ) (x:E)=> Tensor.diagonal A (f t x))= ∑ i,Y i from funext fun t=>funext fun x=> by
      have hv := expand_coord A.toMultilinearMap (fun _=> f t x); rw [recording_apply] at hv; unfold Y; simp only [Finset.sum_apply,Pi.mul_apply,Finset.prod_apply]; exact hv.symm]
    exact Meadow.sum (fun i _=> (Meadow.prod fun j _=> he _).times (Meadow.single (Grass.const _)))
  | sum _ _ hp hx=> exact hp.more hx
variable {M : Matrix X X ℝ} (h : M.PosDef) (μ : Measure (X→ℝ)) [μ.HasTemperateGrowth]
lemma normSun [NeZero μ] : 0 < ∫ x,(crownM h).kern x ∂μ := by
  have hi := (crownM h).integrable_entry (A:=1) μ (PertExtension.Series.Zone.Invoice.const (1:ℝ)) continuous_const
  rw [one_mul] at hi; exact integral_exp_pos hi
lemma meadowTour {F : ℝ→ Psalm X} (hs : Meadow F) : Aspiration (fun t=> (crownM h).average μ (F t))
      (fun j=> (crownM h).average μ (fun x=> ink (fun t=> F t x) j)) ∧ ∀ i,Grass (fun x=> ink (fun t=> F t x) i) := by
  let P:=crownM h
  induction hs with
  | @seeds f g hp hT=>
    have ht i : (fun x=> ink (fun t=> (g t • f) x) i)=(ink g i) • f := funext fun x=> by rw [show (fun t=> (g t • f) x)= (f x) • g from funext fun t=>mul_comm (g t) _, ink_c _ hT]; exact mul_comm ..
    dsimp only
    simp_rw [sun_stem,ht,sun_stem]
    refine ⟨?_,fun i=> hp.scale _⟩
    let D:=P.average μ f
    convert aspireCoin (ink_aspire hT) D using 1
    · funext t; exact mul_comm ..
    funext t; exact mul_comm ..
  | @more f g hp hq hF hG=>
    have hu i : (fun x=> ink (fun t=> (f+g) t x) i)=(fun x=>ink (fun t=> f t x) i)+(fun x=>ink (fun t=> g t x) i) := funext fun x=> congr_fun (ink_add (hp.arc x) (hq.arc x)) _
    simp_rw [hu,sun_add h μ (hF.2 _) (hG.2 _), Pi.add_apply,sun_add h μ (hp.sets _) (hq.sets _)] -- erase lambda risks
    exact ⟨hF.1.add hG.1,fun i=> (hF.2 i).sum (hG.2 i)⟩
-- gaussian kernel INCLUDED
lemma ink_cross {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    {f K : U→ℝ} (h' : PertExtension.Series.Radial.Stationary f) (hp : ContDiffAt ℝ ∞ K 0) (x : U) :
    Aspiration (fun t=>PertExtension.Series.Radial.projection K f t x) (fun i=>normTerm K f i x) := by
  intro n; let A:= PertExtension.Series.Radial.zone (E:=U); obtain ⟨δ,C,k,hδ,hC,hb⟩:=((integrand hp h' (show (0:ℝ)<1 from by positivity)).fits n).cost
  have ht : 0<A.w x := lt_of_lt_of_le zero_lt_one (A.high _)
  refine ⟨C*A.w x^k*shade 1 x*‖kernel f x‖,by unfold shade; positivity,?_⟩
  filter_upwards [eventually_small (show 0<δ/(A.w x) by positivity)] with t hv
  let z:=kernel f x
  have he (t) : peval (fun i=>normTerm K f i x) n t = PertExtension.Series.Zone.eval (integrandSeries f K) n t x*z := by unfold peval PertExtension.Series.Zone.eval; rw [Finset.sum_mul]; apply sum_congr rfl; intro i hi; unfold normTerm; exact (mul_assoc ..).symm -- sign adjust
  have hd := hb x t hv.1 ((le_div_iff₀ ht).mp hv.2.le)
  change ‖insertion f K t x*z- peval _ n t‖ ≤ _
  rw [he,← sub_mul,norm_mul]; exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans_eq (by unfold z A; ring)
end G
end YM.RG08.Reflect
