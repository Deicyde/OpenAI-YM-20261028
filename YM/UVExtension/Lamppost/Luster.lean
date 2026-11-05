import YM.UVExtension.Lamppost.Spice

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Set Filter Function Topology
open scoped BigOperators ContDiff Classical
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Analytic on appointed concrete real finite-dimensional probes. No infinite-order
    smoothness in angular directions is required and this tests on the unmasked germ. -/
structure Luster (s : Set A) (x : E) (j : ℕ) (f : A → E → ℂ) : Prop where
  stage (z : A) (hz:z∈s) : ContDiffAt ℝ (↑j) (f z) x
  order (i) (hi:i≤j) (v:Fin i → E) : DifferentiableOn ℂ (fun z=> iteratedFDeriv ℝ i (f z) x v) s

variable {s : Set A} {x : E} {j k : ℕ} {f g : A → E→ℂ}
namespace Luster
lemma shorter (h : Luster s x j f) (hp : k≤j) : Luster s x k f :=
    ⟨fun z hz=> (h.stage z hz).of_le (by exact_mod_cast hp),fun i hi=> h.order i (hi.trans hp)⟩

lemma values (h : Luster s x j f) : DifferentiableOn ℂ (fun z=> f z x) s := by simpa using! h.order 0 (Nat.zero_le _) (fun _=>0)

lemma plus (h : Luster s x j f) (p:Luster s x j g) : Luster s x j (fun z y=> f z y+g z y) := by
  refine ⟨fun z hz=> (h.stage z hz).add (p.stage z hz),fun i hi v=> DifferentiableOn.congr ((h.order i hi v).add (p.order i hi v)) ?_⟩
  intro z hz; dsimp only [Pi.add_apply]; change iteratedFDeriv ℝ i (f z+g z) x v= _
  rw [iteratedFDeriv_add_apply ((h.shorter hi).stage z hz) ((p.shorter hi).stage z hz)]; rfl
lemma resting {f : E→ℂ} (h : ContDiffAt ℝ (↑j) f x) : Luster s x j (fun _=>f) := ⟨fun _ _=>h,fun _ _ _=> differentiableOn_const _⟩
lemma summit {t : A→ℂ} (h : DifferentiableOn ℂ t s) : Luster s x j (fun z _=>t z) := by
  refine ⟨fun _ _=>contDiffAt_const,?_⟩; rintro (_|i) hi v
  · simpa
  have he : (fun z=> iteratedFDeriv ℝ (i+1) (fun _ : E=> t z) x v)=(fun _=>0) := funext fun z=> by rw [iteratedFDeriv_succ_const]; rfl
  rw [he]; exact differentiableOn_const _
lemma mask (h : Luster s x j f) (q : ∀ z∈s, g z=ᶠ[𝓝 x] f z) : Luster s x j g :=
    ⟨fun z hz=> (h.stage z hz).congr_of_eventuallyEq (q z hz),fun i hi v=> (h.order i hi v).congr (fun z hz=>congr_arg (fun w:E [×i]→L[ℝ] ℂ=>w v) (((q z hz).iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds))⟩

lemma stage_succ (v : E) (h : Luster s x (j+1) f) (z) (hz:z∈s) : ContDiffAt ℝ (↑j) (fun y=> fderiv ℝ (f z) y v) x :=
    ((h.stage z hz).fderiv_right (by simp : (j:WithTop ℕ∞)+1 ≤ ↑(j+1 : ℕ))).clm_apply contDiffAt_const
lemma fade {f : E→ℂ} (h : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (v : E) (V: Fin j → E) :
    iteratedFDeriv ℝ j (fun y=> fderiv ℝ f y v) x V=iteratedFDeriv ℝ (j+1) f x (Fin.snoc V v) := by
  let L:= ContinuousLinearMap.apply ℝ ℂ v
  change iteratedFDeriv ℝ j (L ∘ fderiv ℝ f) x V=_
  rw [L.iteratedFDeriv_comp_left (h.fderiv_right (by simp : (j:WithTop ℕ∞)+1 ≤ ↑(j+1 : ℕ))) le_rfl,
    iteratedFDeriv_succ_apply_right]; simp; rfl
lemma derby (h : Luster s x (j+1) f) (v : E) : Luster s x j (fun z y=> fderiv ℝ (f z) y v) :=
    ⟨stage_succ v h,fun i hi V=> (h.order (i+1) (by omega) (Fin.snoc V v)).congr (fun z hz=> fade ((h.shorter (show i+1≤j+1 from (by omega))).stage z hz) v V)⟩
lemma growth (h : ∀ z∈s,ContDiffAt ℝ (↑(j+1:ℕ)) (f z) x) (he : DifferentiableOn ℂ (fun z=> f z x) s)
    (hp : ∀ v:E,Luster s x j (fun z y=> fderiv ℝ (f z) y v)) : Luster s x (j+1) f := by
  refine ⟨h,?_⟩; rintro (_|i) hi v
  · simpa
  apply DifferentiableOn.congr ((hp (v (Fin.last _))).order i (by omega) (Fin.init v)); intro z hz
  rw [fade ((h z hz).of_le (by exact_mod_cast hi))]; simp

lemma adjacent {f:E→ℂ} (h : ContDiffAt ℝ (↑(j+1:ℕ)) f x) : ∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y := by
  filter_upwards [h.eventually (by simp)] with y hy; exact hy.differentiableAt (by simp)
lemma times (h : Luster s x j f) (p : Luster s x j g) : Luster s x j (fun z y=> f z y*g z y) := by
  induction j generalizing f g with
  | zero => refine ⟨fun z hz=> (h.stage z hz).mul (p.stage z hz),?_⟩; rintro (_|i) hi v; simpa using! h.values.fun_mul p.values; omega
  | succ j ih =>
    refine growth (fun z hz=> (h.stage z hz).mul (p.stage z hz)) (h.values.mul p.values) (fun v=> ?_)
    apply (((ih (h.shorter (show j≤j+1 from (by omega))) (p.derby v))).plus (ih (p.shorter (show j≤j+1 from (by omega))) (h.derby v))).mask
    intro z hz; filter_upwards [adjacent (h.stage z hz),adjacent (p.stage z hz)] with y hy hw; rw [fderiv_fun_mul hy hw]; rfl
lemma powered (h : Luster s x j f) : Luster s x j (fun z y=> Complex.exp (f z y)) := by
  induction j with
  | zero => refine ⟨fun z hz=> (h.stage z hz).cexp,?_⟩; rintro (_|i) hi v; simpa using h.values.cexp; omega
  | succ j ih =>
    refine growth (fun z hz=> (h.stage z hz).cexp) h.values.cexp (fun v=> ?_)
    apply ((ih (h.shorter (by omega))).times (h.derby v)).mask; intro z hz; filter_upwards [adjacent (h.stage z hz)] with y hy
    rw [hy.hasFDerivAt.cexp.fderiv]; rfl
lemma poll {ι:Type*} (u : Finset ι) (w : ι→ A → E → ℂ) (hp : ∀ i∈u,Luster s x j (w i)) : Luster s x j (fun z y=>∏ i∈u,w i z y) := by
  induction u using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using! (resting (s:=s) (contDiffAt_const (x:=x) (n:=↑j) (c:=(1:ℂ))))
  | insert a u hi hU => simp_rw [Finset.prod_insert hi]; exact (hp a (Finset.mem_insert_self ..)).times (hU fun i hi=> hp i (Finset.mem_insert_of_mem hi))
lemma pluses {ι:Type*} (u : Finset ι) (w : ι→ A → E → ℂ) (hp : ∀ i∈u,Luster s x j (w i)) : Luster s x j (fun z y=>∑ i∈u,w i z y) := by
  induction u using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! (resting (s:=s) (contDiffAt_const (x:=x) (n:=↑j) (c:=(0:ℂ))))
  | insert a u hi hU => simp_rw [Finset.sum_insert hi]; exact (hp a (Finset.mem_insert_self ..)).plus (hU fun i hi=> hp i (Finset.mem_insert_of_mem hi))
end Luster
end YM.UVExtension.Lamppost
