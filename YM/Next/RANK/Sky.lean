import YM.Next.RANK.Anima

/-!
# Remainder from known plaquettes in a lifted stencil

When hub data all zero, any value in stencil comes entirely from next order
differences, with extent cost polynomial in (Cover) radius. Uniform estimate
from actual origins, not using jet identifications off stencil. Useful also for
taking one difference estimate at this end of a kernel while allowing further
discrete comparisons on the other end.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open Lattice Wilson CellsInt Maxwell Labels Tensor Configuration Function Finset
open scoped Classical Topology BigOperators

variable {G : Gauge} {r q j d : ℕ}

def street (z : Cover) := ∑ i,(z i).natAbs
lemma empty_road : street 0=0 := by simp [street]
lemma once_road (x : Cover) {i : Axis} (h : 0 < x i) : street (x-step i)+1=street x := by
  unfold street
  rw [← add_sum_erase (univ : Finset Axis) (fun b : Axis => ((x-step i : Cover) b).natAbs) (mem_univ i),← add_sum_erase _ (fun b => (x b).natAbs) (mem_univ i)]
  simp only [Pi.sub_apply,step_apply,↓reduceIte]
  have hx : ∑ b∈univ.erase i,(x b - (if b=i then (1:ℤ) else 0)).natAbs = ∑ b∈univ.erase i,(x b).natAbs := by
    apply sum_congr rfl; intro b hb; have ht : b ≠ i := by simpa using hb
    simp [ht]
  rw [hx]; omega
lemma mirror_road (x : Cover) : street (-x)=street x := by simp [street]

lemma strolling (z : Cover) : z=0 ∨ ∃ p : Cover, street p+1=street z ∧ ∃ i, z=p+step i ∨ p=z+step i := by
  by_cases h : z=0; · exact Or.inl h
  right; obtain ⟨i,hi⟩ := Function.ne_iff.mp h; change z i ≠ 0 at hi
  rcases lt_or_gt_of_ne hi with h|h
  · refine ⟨z+step i,?_,i,Or.inr rfl⟩
    rw [← mirror_road z, ← mirror_road (z+_), neg_add, ← sub_eq_add_neg]; exact once_road _ (by exact neg_pos.mpr h)
  exact ⟨z-step i, once_road z h, i, Or.inl (sub_add_cancel ..).symm⟩

lemma absent {L : Degree G} (h : L.degree=d-1) (p : Horizon G) : gesture L (cloud d p)=0 := by
  unfold cloud; rw [map_sum]; apply sum_eq_zero; intro i _; rw [map_smul]
  have hi := i.property; dsimp only [generation] at hi
  rw [show gesture L (tester i.val)=0 from gesture_over L (show i.val.1 < L.degree by omega) (axes G i.val.1 i.val.2),smul_zero]

lemma retreat (f : Horizon G) (h : focus (d:=d) 0 f=0) (B : ℝ) (hb : 0≤B) (r : ℕ)
    (H : ∀ L : Degree G, L.degree=d-1 → street L.point ≤ r → ‖gesture L f‖ ≤ B) (i : Address G) (hp : street i.1 ≤ r) :
    ‖f i‖ ≤ r^(d-1)*B := by
  -- `(r:ℝ)^...`; avoid 0^0 via mathlib one.
  obtain ⟨x,a,c⟩ := i
  let u:= d-1; let R:= (r:ℝ)
  let v (z : Cover):= f (z,a,c)
  have hl (j : ℕ) (hj : j ≤ u) (t : Fin j → Axis) (x : Cover) (hx : street x ≤ r) : ‖jumps j t v x‖ ≤ R^(u-j)*B := by
    induction hj using Nat.decreasingInduction generalizing x with
    | self => rw [Nat.sub_self,pow_zero,one_mul]; exact H ⟨a,c,x,u,t⟩ rfl hx
    | of_succ k hk IH =>
      let P:= R^(u-(k+1))*B
      have hP : 0≤P := mul_nonneg (by unfold R; positivity) hb
      let X := jumps k t v
      have ht (i : Axis) (p : Cover) (hf : street p ≤ r) : ‖stepValue X i p‖ ≤ P := by
        dsimp only [X]; rw [← hopped,← steps]; exact IH _ p hf
      have h₁ : X 0=0 := by
        let L : Degree G := ⟨a,c,0,k,t⟩
        have he : k+2 ≤ d := by dsimp only [u] at hk; omega
        exact congr_fun h (⟨L,rfl,Nat.zero_le _,he⟩ : Hub G d 0)
      have hh (w : ℕ) (p : Cover) (hp : street p=w) (hr : w≤r) : ‖X p‖ ≤ w*P := by
        induction w generalizing p with
        | zero =>
          obtain hg|⟨_,hh,_⟩ := strolling p
          · rw [hg,h₁]; simp
          omega
        | succ w HW =>
          obtain hg|⟨q,hq,i,H⟩ := strolling p
          · rw [hg,h₁]; simp only [norm_zero]; positivity
          have hy : street q=w := by omega
          have he := HW q hy (by omega)
          have hb : ‖X p-X q‖ ≤ P := by
            rcases H with H|H
            · rw [H]; exact ht i q (by omega)
            rw [norm_sub_rev, H]; exact ht i p (hp.trans_le hr)
          calc
            _ ≤ ‖X p-X q‖+‖X q‖ := le_trans (le_of_eq (congr_arg norm (sub_add_cancel ..).symm)) (norm_add_le ..)
            _ ≤ _ := by push_cast; linarith only [hb,he]
      calc
        _ ≤ _ := hh (street x) x rfl hx
        _ ≤ R*P := mul_le_mul_of_nonneg_right (by unfold R; exact_mod_cast hx) hP
        _ ≤ _ := by unfold P; rw [show u-k=u-(k+1)+1 by omega,pow_succ]; exact le_of_eq (by ring)
  have hv := hl 0 (Nat.zero_le _) Fin.elim0 x hp; rw [Nat.sub_zero] at hv; exact hv

lemma remains (f : Horizon G) (h : shutter f) (B : ℝ) (hb : 0≤B) (r : ℕ)
    (H : ∀ L : Degree G, L.degree=d-1 → street L.point ≤ r → ‖gesture L f‖ ≤ B) (i : Address G) (hp : street i.1 ≤ r) :
    ‖(f-cloud d f) i‖ ≤ r^(d-1)*B := by
  refine retreat _ (by rw [map_sub, visible d f h,sub_self]) B hb r (fun l hl ht => ?_) i hp
  rw [map_sub,absent hl f,sub_zero]; exact H l hl ht
end YM.Next.Rank.Beamer
