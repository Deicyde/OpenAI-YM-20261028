import YM.Push.LOOP_COEFFICIENT.Pullback

/-!
# Testing a leading Taylor term along a complex line
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Metric Set Matrix Complex
open scoped Topology ContDiff BigOperators
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {f g : ℂ → E} {x y : E} {n m : ℕ}

/-- f(t)=t^n(x+O(t)), with a regular quotient near zero. -/
def Lead (n : ℕ) (f : ℂ → E) (x : E) : Prop := ∃ g : ℂ → E, ContDiffAt ℂ ω g 0 ∧ g 0=x ∧ ∀ᶠ t in 𝓝 (0:ℂ), f t = t^n • g t

lemma Lead.congr {g : ℂ → E} (h : Lead n f x) (he : f =ᶠ[𝓝 0] g) : Lead n g x := by obtain ⟨t,ht,hx,H⟩ := h; exact ⟨t,ht,hx,he.symm.trans H⟩
lemma lead_zero (h : ContDiffAt ℂ ω f 0) : Lead 0 f (f 0) := ⟨f,h,rfl,by simp⟩
lemma Lead.zero : Lead n (fun _ : ℂ => (0:E)) 0 := ⟨fun _ => 0,contDiffAt_const,rfl, by simp⟩

lemma Lead.add (h : Lead n f x) (h' : Lead n g y) : Lead n (fun t => f t + g t) (x+y) := by obtain ⟨a,ha,rfl,H⟩ := h; obtain ⟨b,hb,rfl,H'⟩ := h'; exact ⟨fun t => a t+b t,ha.add hb,rfl, (H.and H').mono fun _ ⟨h1,h2⟩ => by dsimp only; rw [h1,h2,smul_add]⟩

lemma Lead.map (L : E →L[ℂ] F) (h : Lead n f x) : Lead n (fun t => L (f t)) (L x) := by obtain ⟨a,ha,rfl,H⟩ := h; exact ⟨L ∘ a,L.contDiff.contDiffAt.comp 0 ha,rfl,H.mono fun _ he => by simp [he]⟩

lemma Lead.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E} {x : ι → E} (h : ∀ i∈s, Lead n (f i) (x i)) : Lead n (fun t => ∑ i∈s,f i t) (∑ i∈s,x i) := by
  classical induction s using Finset.induction with
    | empty => simp; exact Lead.zero
    | insert i s hi ih => simp [hi]; apply Lead.add (h i (by simp)); exact ih (fun j hj => h j (by simp [hj]))
lemma Lead.lower (h : Lead n f x) (he : m < n) : Lead m f 0 := by
  obtain ⟨g,hg,hx,H⟩ := h; exact ⟨fun t => t^(n-m) • g t,(contDiffAt_id.pow _).smul hg,by simp [Nat.sub_ne_zero_of_lt he],H.mono fun t ht => by rw [ht,smul_smul,← pow_add, Nat.add_sub_cancel' he.le]⟩
variable {R : Type} [NormedRing R] [NormedAlgebra ℂ R]
lemma Lead.mul {f g : ℂ → R} {x y} (hf : Lead n f x) (hg : Lead m g y) : Lead (n+m) (fun t => f t * g t) (x*y) := by
  obtain ⟨u,hu,rfl,H⟩ := hf; obtain ⟨v,hv,rfl,H'⟩ := hg; exact ⟨fun t => u t * v t,hu.mul hv,rfl,(H.and H').mono fun t ⟨ht, ht'⟩ => by dsimp only; rw [ht,ht',pow_add,mul_smul, smul_mul_assoc, mul_smul_comm]⟩








end YM.Push.Loops.Paths
