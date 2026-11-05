import YM.UVExtension.Limits

/-! Split two subsequential sequences. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension
open Filter Function
open scoped Topology
variable {X : Type*} (f g:ℕ→ X)

def concat (i:ℕ):X:= if i%2=0 then f (i/2) else g (i/2)

def eStep :ℕ→ℕ := (·*2)
def oStep :ℕ→ℕ := fun i=> i*2+1
@[simp] theorem concat_castE (i:ℕ) : concat f g (eStep i)= f i:=by simp [concat,eStep]
@[simp] theorem concat_castO (i:ℕ): concat f g (oStep i)=g i:=by simp [concat,oStep]; congr 1; omega
lemma split_all {p : ℕ→ Prop}(h : ∀ i,p (eStep i))(hr:∀ i,p (oStep i)):∀ i,p i:=by
  intro i; by_cases hh: i%2=0
  · convert h (i/2) using 1; unfold eStep; congr 1; omega
  convert hr (i/2) using 1; unfold oStep; congr 1; omega
lemma split_ev {p : ℕ→ Prop}(h : ∀ᶠ i in atTop,p (eStep i))(hr:∀ᶠ i in atTop,p (oStep i)):∀ᶠ i in atTop,p i:=by
  obtain ⟨a,h⟩:= eventually_atTop.1 h; obtain ⟨b,hb⟩:= eventually_atTop.1 hr
  exact (eventually_ge_atTop (2*a+2*b+2)).mono (split_all (p:=fun i=>2*a+2*b+2≤ i→p i) (fun i hi=> h i (by unfold eStep at hi; omega)) (fun i hi=> hb i (by unfold oStep at hi; omega)))
lemma split_go [TopologicalSpace X]{F:ℕ→ X}{y:X}(h : Tendsto (F∘eStep) atTop (𝓝 y))(he:Tendsto (F∘oStep) atTop (𝓝 y)): Tendsto F atTop (𝓝 y):= tendsto_def.mpr fun i hi=> split_ev (p:=fun i'=> F i'∈i) (h.eventually hi) (he.eventually hi)
lemma upE:Tendsto eStep atTop atTop:= StrictMono.tendsto_atTop (fun i j hi=> (show eStep i < eStep j by unfold eStep; omega))
lemma upO:Tendsto oStep atTop atTop:= StrictMono.tendsto_atTop (fun i j hi=> (show oStep i < oStep j by unfold oStep; omega))
end YM.UVExtension
