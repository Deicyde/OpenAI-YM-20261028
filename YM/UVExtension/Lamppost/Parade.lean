import YM.UVExtension.Lamppost.Husk

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Complex Filter Metric Function Topology MeasureTheory Set
open scoped BigOperators ContDiff Classical NNReal ENNReal
variable {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace Husk
omit [CompleteSpace E]
lemma records [MeasurableSpace A] (μ: Measure A) : Husk (fun f:A→E=> AEStronglyMeasurable f μ) := by
  refine ⟨aestronglyMeasurable_zero,fun _ _ h g=> AEStronglyMeasurable.add h g,fun t x h=> AEStronglyMeasurable.const_smul h t,?_⟩; intro F f hp he
  obtain ⟨n,hn⟩:= eventually_atTop.mp hp
  have ht: Tendsto (fun i:ℕ=> i+n) atTop atTop:= StrictMono.tendsto_atTop (show StrictMono (fun i:ℕ=> i+n) from fun i j hij=> Nat.add_lt_add_right hij _)
  exact aestronglyMeasurable_of_tendsto_ae atTop (μ:=μ) (g:=f) (f:=fun i=>F (i+n)) (fun i=> hn (i+n) (by omega)) (Eventually.of_forall fun a=> (he a).comp ht)
lemma strong [MeasurableSpace A] : Husk (fun f:A→E=> StronglyMeasurable f):= by
  refine ⟨stronglyMeasurable_zero,fun _ _ h g=> StronglyMeasurable.add h g,fun t x h=>StronglyMeasurable.const_smul h _,?_⟩; intro F f hp he
  obtain ⟨n,hn⟩:= eventually_atTop.mp hp
  have ht:Tendsto (fun i:ℕ=> i+n) atTop atTop:= StrictMono.tendsto_atTop (show StrictMono (fun i:ℕ=> i+n) from fun i j hij=> Nat.add_lt_add_right hij _)
  exact stronglyMeasurable_of_tendsto atTop (f:=fun i => F (i+n)) (g:=f) (fun i=> hn (i+n) (by omega)) (tendsto_pi_nhds.mpr fun a=> (he a).comp ht)
lemma audit (a b:A):Husk (fun f:A→E=> f a=f b):=
    ⟨rfl,fun _ _ hf hg=> congr_arg₂ (·+·) hf hg,fun t _ h=> congr_arg (t • ·) h, fun {_ _} hp he=> tendsto_nhds_unique ((he a).congr' hp) (he b)⟩
end Husk
section
variable {ι : Type*} [Fintype ι] {V : ι → Set ℂ} {s : ℝ} {B : (ι→ℝ) → Prop}
abbrev Plot (ι : Type*) := ι→ℂ
def hoist (Z : ι→ℝ):Plot ι:=fun i=> Z i
def Courtyard (V : ι→Set ℂ) : Set (Plot ι):= Set.pi univ V
omit [Fintype ι] in
lemma within {f : Plot ι} : f∈ Courtyard V ↔ ∀ i,f i∈V i := by simp [Courtyard]
omit [Fintype ι] in
lemma opened (h : ∀ i,IsOpen (V i)) (p : Finset ι) : IsOpen {z:Plot ι| ∀ i∈p,z i∈ V i} := by simp only [setOf_forall]; exact isOpen_biInter_finset (fun i _=> (h i).preimage (continuous_apply i))
lemma court_open (h:∀ i,IsOpen (V i)):IsOpen (Courtyard V):= by convert opened h Finset.univ using 1; ext x; rw [within]; simp
-- true hol on curves of parameters; avoids using analytic At in many complex dimensions
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
def Bumps (S:Set X) (F:X→E) := ∀ (T : Set ℂ) (f:ℂ→X), IsOpen T→MapsTo f T S → DifferentiableOn ℂ f T → DifferentiableOn ℂ (fun z=>F (f z)) T
omit [CompleteSpace E]
lemma bumps (S:Set X) (F:X→E) (h:DifferentiableOn ℂ F S):Bumps S F:= fun _ _ _ hm ht=> h.comp ht hm
lemma bends_add {S:Set X} {F f:X→E} (h:Bumps S F) (p:Bumps S f):Bumps S (fun x=>F x+f x):= fun Z v hz hv ht=> (h Z v hz hv ht).add (p Z v hz hv ht)
lemma bends_smul {S:Set X} {F:X→E} {f:X→ℂ} (h:Bumps S F) (p:Bumps S f):Bumps S (fun x=> f x • F x):=fun Z v hz hv ht=> (p Z v hz hv ht).smul (h Z v hz hv ht)
lemma bend_finset {S:Set X} {ι:Type*} (s:Finset ι) (f:ι→ X→ E) (h:∀ i∈s,Bumps S (f i)) : Bumps S (fun x=>∑ i∈s,f i x):= fun _ _ hz hv ht=> DifferentiableOn.fun_sum fun i hi=> h i hi _ _ hz hv ht
end
section
variable {ι : Type*} [Fintype ι] {V : ι → Set ℂ}

lemma regatta {c : ι→ℝ} (C : ι→Set ℝ) (hw : ∀ i,C i∈𝓝 (c i)) (hh : ∀ i t,t∈C i→ (t:ℂ)∈V i) (hp : ∀ i,IsOpen (V i)) (ht :∀ i,IsPreconnected (V i))
    (F : Plot ι → A→ E) {P : (A→E)→ Prop} (h : Husk P) (hF : ∀ y:A,Bumps (Courtyard V) (fun z=> F z y))
    (he : ∀ f:ι→ℝ, (∀ i,f i∈C i) → P (F (hoist f))) : ∀ x∈ Courtyard V,P (F x) := by
  suffices he : ∀ s:Finset ι,∀ x∈Courtyard V,(∀ i∉s,∃ t:ℝ,t∈C i∧ x i=t)→ P (F x) from fun x hx=> he Finset.univ x hx (by simp)
  intro s; induction s using Finset.induction_on with
  | empty =>
    intro x hx hg; simp only [Finset.notMem_empty,not_false_eq_true, forall_true_left] at hg
    choose c hc hh using hg; rw [show x=hoist c from funext hh]; exact he c hc
  | insert a s ha ih =>
    intro x hx hg
    let X z:= F (Function.update x a z)
    suffices hv:P (X (x a)) by simpa only [X,Function.update_eq_self] using hv
    have hh' : MapsTo (Function.update x a) (V a) (Courtyard V):=by intro z hz; refine within.mpr fun i=>?_ ; by_cases he : i=a; simpa [he] using hz; simpa [he] using within.mp hx i
    refine h.invades (hp a) (ht a) (fun i=> hF i (V a) _ (hp a) hh' (show DifferentiableOn ℂ (Function.update x a) (V a) from (by
      apply Differentiable.differentiableOn; intro z; refine differentiableAt_pi.mpr fun j=>?_; by_cases h:j=a <;> (simp [h]))))
      (hh a (c a) (mem_of_mem_nhds (hw a))) ?_ (within.mp hx _)
    have hz : ∀ᶠ t:ℝ in 𝓝 0,c a+t∈C a:= by
      have ht:= Continuous.tendsto (continuous_const_add (c a)) 0; rw [show c a+0=c a from add_zero ..] at ht; exact ht.eventually (hw a)
    filter_upwards [hz] with t hv; rw [← Complex.ofReal_add]
    refine ih _ (hh' (hh _ _ hv)) (fun i hi=>?_); by_cases hc:i=a
    · subst i; exact ⟨_,hv,Function.update_self ..⟩
    rw [Function.update_of_ne hc]; exact hg i (by simp [hc,hi])

lemma matched {c:ι→ℝ} (C:ι→ Set ℝ) (hw:∀ i,C i∈𝓝 (c i)) (hh:∀ i t,t∈C i→ (t:ℂ)∈V i) (hp : ∀ i,IsOpen (V i)) (ht:∀ i,IsPreconnected (V i))
    {F G: Plot ι → E} (h : Bumps (Courtyard V) F) (g:Bumps (Courtyard V) G) (he : ∀ f:ι→ℝ,(∀ i,f i∈C i)→ F (hoist f)=G (hoist f)) : EqOn F G (Courtyard V) := by
  let Z p (i:Bool):E:= if i=true then F p else G p
  intro x hx; refine regatta C hw hh hp ht Z (Husk.audit true false) ?_ ?_ x hx
  · intro i; cases i; exact g; exact h
  exact he
end
end YM.UVExtension.Lamppost
