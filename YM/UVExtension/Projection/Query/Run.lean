import YM.UVExtension.Projection.Query.Test

/-! Use finite-dimensional tests. Uniform DEGREE for a span, not dimension! -/
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.UVExtension.Projection
open Filter Function Finset ContinuousLinearMap MenuView Module
open scoped Topology BigOperators ContDiff Classical
variable {I X Y E : Type} (P : MenuView I)
  [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup E] [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ E] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]
lemma elevate (v : X →ₗ[ℝ] Y) (h : Injective v) {p : I→ X} {d}
    (he : P.sees d fun i=> v (p i)) : P.sees d p:= by
  obtain ⟨L,hL⟩:= LinearMap.exists_leftInverse_of_injective v (LinearMap.ker_eq_bot.mpr h)
  have hh : (fun i=> L (v (p i)))=p:= funext fun i=> DFunLike.congr_fun hL (p i)
  exact hh ▸ acts he L
lemma panel {α : Type} [Fintype α] (p : I → α → X) {d} (h : ∀ i,P.sees d fun j=> p j i) : P.sees d p:= by
  have hh: p=fun j=> ∑ i : α,(LinearMap.single ℝ (fun _=>X) i) (p j i):=by funext i j; simp [Finset.sum_apply,Pi.single_apply]
  rw [hh]; refine aggregated univ _ fun i _=> (acts (h i) _)
lemma laminate (l : I→ X→L[ℝ] Y) {d} (h : ∀ x : X,P.sees d fun i=> l i x) : P.sees d l:= by
  let e:= Module.finBasis ℝ X
  let K := LinearMap.pi (fun i => (ContinuousLinearMap.apply ℝ Y (e i)).toLinearMap)
  refine elevate P K (fun x y H=> coe_injective ?_) (panel P _ (fun i=> h _))
  exact Module.Basis.ext e (fun i => (show x _=y _ from congr_fun H i))
lemma put_linear (l : I→ X →L[ℝ] Y) (x : I→ X) {a b} (h : P.sees a l) (he : P.sees b x): P.sees (b+a) fun i=> l i (x i):= by
  let e:= Module.finBasis ℝ X
  have hh i : l i (x i) = ∑ j,e.repr (x i) j • l i (e j):=by simp only [← map_smul, ← map_sum, Basis.sum_repr]
  simp_rw [hh]; exact aggregated univ _ fun i _=> scales (he (e.coord i)) (acts h (ContinuousLinearMap.apply ℝ Y (e i)).toLinearMap)
lemma pane_mat {α β: Type} [Fintype α] [Fintype β] (p : I → Matrix α β X) {d}(h: ∀ i j,P.sees d (fun n=> p n i j)):P.sees d p:=by
  exact (panel P _ (fun i=> panel P _ (h i)))

variable {P} {f g : I → X → Y} {G : I→ Y→E} {x : I→ X} {d k b : ℕ}
structure Run (P : MenuView I) (d k : ℕ) (f : I→ X→ Y) (x : I→X): Prop where
    born i : ContDiffAt ℝ ω (f i) (x i)
    tests (i : ℕ): i≤k → ∀ p,P.sees d fun t=> iteratedFDeriv ℝ i (f t) (x t) p

namespace Run
theorem more (h : Run P d k f x) (hp : d≤b){t}(he : t≤ k) : Run P b t f x:= ⟨h.born, fun i hi p=> sees_up (h.tests i (hi.trans he) p) hp⟩
theorem fix (f:X→Y)(x:X)(k d)(h:ContDiffAt ℝ ω f x): Run P d k (fun _=> f) (fun _=> x):= ⟨fun _=> h,fun _ _ _=>steady P _ _⟩
theorem germ (h:Run P d k f x) (hc:∀ i,g i =ᶠ[𝓝 (x i)] f i): Run P d k g x:=
    ⟨fun i=> (h.born i).congr_of_eventuallyEq (hc _), fun i hi p=> (by have hp n:= ((hc n).iteratedFDeriv ℝ i).eq_of_nhds; simp_rw [hp]; exact h.tests i hi p)⟩
theorem sum (h : Run P d k f x) (he : Run P d k g x) : Run P d k (fun i=> f i+g i) x:= by
  refine ⟨fun i=> (h.born i).add (he.born _),fun i hi p=>?_⟩
  have hh p: iteratedFDeriv ℝ i (f p + g p) (x p)=_:= iteratedFDeriv_add_apply ((h.born p).of_le le_top) ((he.born p).of_le le_top)
  simp_rw [hh]; exact joins (h.tests i hi p) (he.tests i hi p)
theorem party (h : Run P d k f x){g : I→ X→E}(he : Run P d k g x) : Run P d k (fun i a=> (f i a,g i a)) x:= by
  refine ⟨fun i=> (h.born i).prodMk (he.born _),fun i hi p=>?_⟩
  simp_rw [iteratedFDeriv_prodMk (h.born _) (he.born _) le_top]; exact sees_both (h.tests i hi p) (he.tests i hi p)
theorem cash (h : Run P d k f x) (L : Y→L[ℝ] E) : Run P d k (fun i=> L ∘ f i) x:= by
  refine ⟨fun i=> L.contDiff.contDiffAt.comp _ (h.born _),fun i hi p=>?_⟩
  simp_rw [L.iteratedFDeriv_comp_left (h.born _) le_top]; exact acts (h.tests i hi p) L.toLinearMap

def flight (c : OrderedFinpartition k) (g : Y→ E)(f : X→ Y)(x : X)(v : Fin k→ X):= iteratedFDeriv ℝ c.length g (f x) (fun i=> iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i))
lemma soar (c : OrderedFinpartition k) (v : Fin k→ X) (hg : ∀ w,P.sees b fun i=> iteratedFDeriv ℝ c.length (G i) (f i (x i)) w) (h : ∀ j, ∀ w,P.sees d fun i=> iteratedFDeriv ℝ (c.partSize j) (f i) (x i) w): P.sees (k*d+b) fun i=> flight c (G i) (f i) (x i) v:= by
  apply sees_up (multi c.length _ _ (fun _=> d) hg (fun i=> h i _)); simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul]; gcongr; exact c.length_le
lemma path {f : X→Y} {x : X} {g:Y→E} (h : ContDiffAt ℝ ω f x) (he:ContDiffAt ℝ ω g (f x)) (v : Fin k→ X): iteratedFDeriv ℝ k (g∘f) x v=∑ c,flight c g f x v:= by
  rw [iteratedFDeriv_comp he h le_top]; simp_rw [FormalMultilinearSeries.taylorComp,_root_.sum_apply]; rfl
theorem comp (h : Run P d k f x) (he : Run P b k G (fun i=> f i (x i))) : Run P (k*d+b) k (fun i=> G i ∘ f i) x:= by
  refine ⟨fun i=> (he.born i).comp _ (h.born i),fun i hi v=>?_⟩; simp_rw [path (h.born _) (he.born _)]
  exact aggregated _ _ fun j _=> sees_up (soar j v (he.tests _ (j.length_le.trans hi)) (fun l=> h.tests _ ((j.partSize_le l).trans hi))) (by gcongr)
set_option linter.unusedSectionVars false in
lemma diff (h : Run P d (k+1) f x): Run P d k (fun i=> fderiv ℝ (f i)) x:=by
  refine ⟨fun i=> (h.born i).fderiv_right (m:=ω) (by simp),fun i hi v=>?_⟩
  apply laminate P _ (fun w=>?_); have ht:= h.tests (i+1) (by omega) (Fin.snoc v w); simp only [iteratedFDeriv_succ_apply_right,Fin.snoc_last,Fin.init_snoc] at ht; exact ht
end Run
end YM.UVExtension.Projection
