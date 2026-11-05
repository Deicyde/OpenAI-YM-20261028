import YM.UVExtension.Lamppost.Tone
import YM.UVExtension.Lamppost.Blossom

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open ConnectedActivityE6 Blaze Lamppost Finset Function Filter Set
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {Z D : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {T:Opening D Z}
    {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j:ℕ} {t:E} {ρ : ℝ} {a b : Z→ℝ}
-- One probe patch. May be different lifts for every probe, all analytic continuations agree by T.agrees.
structure Twist (T:Opening D Z) (t:E) (j:ℕ) (f:D→E→ℝ) (g:Z→ E→ℂ) : Prop where
    smooth d : ContDiffAt ℝ (↑j) (f d) t
    wrap d : Foil t j (g (T.call d)) (fun i=> ((f d i:ℝ):ℂ))
    past (s:Set ℂ) (p:ℂ→Z) : IsOpen s → MapsTo p s T.span → DifferentiableOn ℂ p s → Luster s t j (g ∘ p)
namespace Twist
variable {f f' : D→ E→ℝ} {g g' : Z → E → ℂ}
lemma smoothC (h : Twist T t j f g) (d:D): ContDiffAt ℝ (↑j) (fun i=> Complex.ofReal (f d i)) t:= Complex.ofRealCLM.contDiff.contDiffAt.comp t (h.smooth d)
lemma sideBy (h:Twist T t j f g) (c:Twist T t j f' g') : Twist T t j (fun z i=>f z i+f' z i) (fun z i=> g z i+g' z i) :=by
  refine ⟨fun d=> (h.smooth d).add (c.smooth d),fun d=>?_,fun s p hs hh hd=>?_⟩
  · simpa only [Complex.ofReal_add] using! (h.wrap d).plus (c.wrap d) (h.smoothC d) (c.smoothC d)
  exact (h.past s p hs hh hd).plus (c.past s p hs hh hd)
lemma plus (c : ℝ) : Twist T t j (fun _ _ => c) (fun _ _=>↑c):= ⟨fun _=> contDiffAt_const,fun _=>⟨contDiffAt_const,fun _ _=> rfl⟩,fun _ _ _ _ _=> Luster.resting contDiffAt_const⟩
lemma times (h:Twist T t j f g) (c:Twist T t j f' g') : Twist T t j (fun z i=>f z i*f' z i) (fun z i=> g z i*g' z i):=by
  refine ⟨fun d=> (h.smooth d).mul (c.smooth d),fun d=>?_,fun s p hs hh hd=>?_⟩
  · simpa only [Complex.ofReal_mul] using! (h.wrap d).times (c.wrap d) (h.smoothC d) (c.smoothC d)
  exact (h.past s p hs hh hd).times (c.past s p hs hh hd)

variable {ι : Type*} (s:Finset ι) (F:ι → D→ E→ℝ) (G:ι→ Z→ E→ℂ)
lemma crew (h:∀ i∈s,Twist T t j (F i) (G i)): Twist T t j (fun d x=>∑ i∈s,F i d x) (fun z x=>∑ i∈s,G i z x):=by
  induction s using Finset.induction_on with
  | empty => simpa using! plus (T:=T) (j:=j) (t:=t) 0
  | insert i s hi hh => simp_rw [Finset.sum_insert hi]; exact (h _ (mem_insert_self ..)).sideBy (hh fun i hi=> h i (mem_insert_of_mem hi))
lemma clues (h:∀ i∈s,Twist T t j (F i) (G i)): Twist T t j (fun d x=>∏ i∈s,F i d x) (fun z x=>∏ i∈s,G i z x):=by
  induction s using Finset.induction_on with
  | empty => simpa using! plus (T:=T) (j:=j) (t:=t) 1
  | insert i s hi hh => simp_rw [Finset.prod_insert hi]; exact (h _ (mem_insert_self ..)).times (hh fun i hi=> h i (mem_insert_of_mem hi))
lemma read (h:Twist T t j f g) (p:ℕ) (hp:p≤j)(v:Fin p→ E)(d:D): iteratedFDeriv ℝ p (g (T.call d)) t v= ↑(iteratedFDeriv ℝ p (f d) t v):= by
  rw [(h.wrap d).congr p hp, show (fun x=> ((f d x:ℝ):ℂ))= Complex.ofRealCLM ∘ f d from rfl,
    ContinuousLinearMap.iteratedFDeriv_comp_left _ (h.smooth d) (by exact_mod_cast hp)]; rfl

variable [FiniteDimensional ℝ E]
theorem bloomset (h:∀ d, ContDiffAt ℝ (↑j) (f d) t) (b:Z→ℝ) (p:(i:ℕ)→(Fin i→ E) → Z→ℂ) (hv:∀ d i, i≤j→∀ v,p i v (T.call d)=↑(iteratedFDeriv ℝ i (f d) t v))
    (hg:∀ i ≤ j,∀ v,Bumps T.span (p i v)) (hm:∀ z∈T.span,0≤b z) (hf:∀ z∈T.span,∀ i≤j,∀ v,‖p i v z‖≤ b z*∏ k, ‖v k‖):
    ∃ g, Twist T t j f g∧∀ z∈T.span,Brush j (b z) 1 (g z) t := by
  obtain ⟨g,hg',ht,hF,hG⟩:= forge T (F:=fun a=> Complex.ofRealCLM ∘ f a) p (fun a=> Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h a)) hg (fun a i hi v=> by rw [hv a i hi v]; rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ (h a) (by exact_mod_cast hi)]; rfl)
  refine ⟨g,⟨h,ht,hF⟩,fun z hz=>⟨hg' _,zero_le_one,fun i hi=>?_⟩⟩
  · rw [one_pow,mul_one]; apply ContinuousMultilinearMap.opNorm_le_bound (hm z hz)
    intro v; rw [← hG z hz i hi v]; exact hf z hz i hi v
end Twist
end YM.UVExtension.Concert
