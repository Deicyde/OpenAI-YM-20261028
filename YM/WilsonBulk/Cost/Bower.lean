import YM.WilsonBulk.Grid.Age

/-!
# Post-age account for strict events, monotone-polynomial caps

Only assessed after receiving a proper L-demand. `Tariff` means a single
formula nonnegative on all nonnegative prices (also `pow`s), using REAL
powers for later scheduling but here N. May choose parameters order finite.
Monotonicity recorded to translate to uniform tails under `delay` price
conditions. Not an interchange of formal/positivity domains.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Topology BigOperators Classical

variable {p q : ℝ→ℝ}
def Tariff (p : ℝ→ℝ) :=
 (∀ x,0≤x → 0 ≤ p x) ∧ (∀ x y,0≤x→ x≤y→ p x≤p y) ∧ (∃ (d:ℕ) (c:ℝ), 0≤c ∧ ∀ x, 1≤x→ p x ≤ c*x^d)
namespace Tariff
lemma one : Tariff fun x:ℝ => x := ⟨fun x h=>h, fun x y h hx=>hx,1,1,zero_le_one,fun x h=> by simp⟩
lemma const (v : ℝ) (h : 0≤v) : Tariff fun _=>v := ⟨fun _ _=>h,fun x y h hx=>le_rfl,0,v,h,fun x _=>by simp⟩
lemma add (h : Tariff p) (hh : Tariff q) : Tariff fun x=>p x+q x := by
  refine ⟨fun x hx=>add_nonneg (h.1 x hx) (hh.1 x hx),fun x y hx hy=>add_le_add (h.2.1 x y hx hy) (hh.2.1 x y hx hy),?_⟩
  obtain ⟨d,c,hc,he⟩:=h.2.2; obtain ⟨f,k,hk,hf⟩:= hh.2.2
  refine ⟨d+f,c+k,add_nonneg hc hk,fun x hx=>?_⟩
  rw [add_mul]; exact add_le_add ((he _ hx).trans (by gcongr; omega)) ((hf _ hx).trans (by gcongr; omega))
lemma prod (h : Tariff p) (hh : Tariff q) : Tariff fun x=>p x*q x := by
  refine ⟨fun x hx=>mul_nonneg (h.1 x hx) (hh.1 x hx),fun x y hx hy=>mul_le_mul (h.2.1 x y hx hy) (hh.2.1 x y hx hy) (hh.1 x hx) (h.1 y (hx.trans hy)),?_⟩
  obtain ⟨d,c,hc,he⟩:=h.2.2; obtain ⟨f,k,hk,hf⟩:= hh.2.2
  refine ⟨d+f,c*k,mul_nonneg hc hk,fun x hx=>?_⟩
  have hv := zero_le_one.trans hx; rw [pow_add,mul_mul_mul_comm]; exact mul_le_mul (he _ hx) (hf _ hx) (hh.1 x hv) (by positivity)
lemma gather {ι : Type*} (s : Finset ι) {p : ι→ℝ→ℝ} (h : ∀ i∈s,Tariff (p i)) : Tariff fun x=>∑ i∈s,p i x := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact const _ le_rfl
  | insert i s h' ih=> simp only [Finset.sum_insert h']; exact (h i (Finset.mem_insert_self ..)).add (ih (fun a ha=> h a (Finset.mem_insert_of_mem ha)))
lemma powers (h : Tariff p) (d : ℕ) : Tariff fun x=> (p x)^d := by
  induction d with
  | zero => simp only [pow_zero]; exact const _ zero_le_one
  | succ i ih => simp only [pow_succ]; exact ih.prod h
lemma composed (h : Tariff p) (hh : Tariff q) : Tariff fun x=>p (q x) := by
  refine ⟨fun x hx=>h.1 _ (hh.1 _ hx), fun x y hx hy=>h.2.1 _ _ (hh.1 _ hx) (hh.2.1 x y hx hy),?_⟩
  obtain ⟨d,c,hc,he⟩:=h.2.2
  obtain ⟨f,k,hk,hf⟩:= ((const c hc).prod ((hh.add (const 1 zero_le_one)).powers d)).2.2
  refine ⟨f,k,hk,fun x hx=>?_⟩
  have hr := hh.1 x (zero_le_one.trans hx)
  exact (h.2.1 _ _ hr (show q x ≤ q x+1 by linarith)).trans ((he _ (by linarith)).trans (hf x hx))
end Tariff
end YM.WilsonBulk
