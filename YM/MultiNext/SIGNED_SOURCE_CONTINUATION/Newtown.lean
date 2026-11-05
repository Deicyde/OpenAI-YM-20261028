import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newt

set_option warningAsError false

/-!
# Total-degree Newton errors in costs BEFORE L

Full E-order remainders incl negative offsets. Cubes via L1 for
convenience; use also near/far with periodic output. `drift`: caller
posts multiplied-by-path-power discipline on the ACTUAL cover output,
with `r` e.g. inverse block and `b` the requested row spatial power.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Newt
open Function Filter Finset Lattice Wilson RG Labels Laurent
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Cover → E} {r C M : ℝ}
private lemma predecessor {x : Cover} (h : x≠0) : ∃ (i : Axis) (y : Cover),
    size x=size y+1 ∧ (x=y+step i ∨ x=y-step i) := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠0 := by by_contra! he; exact h (funext he)
  rcases lt_or_gt_of_ne hi with H|H
  · refine ⟨i,x+step i,?_,Or.inr (by abel)⟩
    unfold size; simp only [Pi.add_apply,step_apply]
    rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ (fun j => (x j + if j=i then 1 else 0).natAbs) (mem_univ i)]
    rw [sum_congr rfl (show ∀ j∈Finset.univ.erase i,(x j+(if j=i then 1 else 0)).natAbs=(x j).natAbs from fun j hj => by rw [if_neg (mem_erase.mp hj).1,add_zero]), if_pos rfl]
    omega
  refine ⟨i,x-step i,?_,Or.inl (by abel)⟩
  unfold size; simp only [Pi.sub_apply,step_apply]
  rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ (fun j => (x j - if j=i then 1 else 0).natAbs) (mem_univ i)]
  rw [sum_congr rfl (show ∀ j∈Finset.univ.erase i,(x j-(if j=i then 1 else 0)).natAbs=(x j).natAbs from fun j hj => by rw [if_neg (mem_erase.mp hj).1,sub_zero]), if_pos rfl]
  omega

omit [NormedSpace ℝ E] in
lemma pointwise (n : ℕ) (h : p 0=0) (he : 0 ≤ M) (hh : ∀ i : Axis,∀ x : Cover, (size x:ℝ) ≤ C →
    ‖jump p i x‖ ≤ M*(1+(size x:ℝ))^n) (x : Cover) (hx : (size x:ℝ) ≤ C) :
    ‖p x‖ ≤ M*(1+(size x:ℝ))^(n+1) := by
  suffices ∀ k : ℕ,∀ x,size x=k → (size x:ℝ) ≤ C → ‖p x‖ ≤ M*(1+(size x:ℝ))^(n+1) by exact this _ _ rfl hx
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hk hi
    by_cases hx:x=0
    · subst x; rw [h,norm_zero]; positivity
    obtain ⟨i,y,ht,hP⟩:= predecessor hx
    have hl : (size y:ℝ)+1=size x := by exact_mod_cast ht.symm
    have hy : 0 ≤ (size y:ℝ) := by positivity
    have hC : (size y:ℝ) ≤ C := by linarith
    have hb := ih (size y) (hk ▸ (show size y < size x by omega)) y rfl hC
    let d := 1+(size x:ℝ)
    have hd : 0 ≤ d := by unfold d; positivity
    have hA : ‖p x-p y‖ ≤ M*d^n := by
      rcases hP with H|H
      · have he' : p x-p y=jump p i y := H ▸ rfl
        rw [he']; apply (hh i y hC).trans
        unfold d; gcongr; omega
      rw [norm_sub_rev]
      have he' : p y-p x=jump p i x := congr_arg (fun v => p v-p x) (show y=x+Lattice.step i by rw [H]; abel)
      rw [he']; exact hh i x hi
    apply le_trans (b:=‖p x-p y‖+‖p y‖)
    · simpa using norm_add_le (p x-p y) (p y)
    apply (add_le_add hA hb).trans
    have hf : M*(1+(size y:ℝ))^n ≤ M*d^n := by unfold d; gcongr; omega
    have hl' : (1+(size y:ℝ))+1=d := by unfold d; linarith
    change _ ≤ M*d^_
    rw [pow_succ,pow_succ]
    have H0 := mul_le_mul_of_nonneg_right hf (show (0:ℝ) ≤ 1+(size y:ℝ) by positivity)
    calc
      _ ≤ M*d^n+M*(d^n * (1+(size y:ℝ))) := by nlinarith only [H0]
      _ = M*(d^n*d) := by rw [←hl']; ring

-- first in list differentiated first
def iterate (p : Cover→E) : List Axis → Cover→E
| [] => p
| i::l => iterate (jump p i) l

lemma localized (d : ℕ) (hM : 0 ≤ M) (R : ℝ) (h : ∀ l : List Axis, l.length = d → ∀ x,(size x:ℝ) ≤ R → ‖iterate p l x‖ ≤ M)
    (x : Cover) (he : (size x:ℝ) ≤ R) : ‖tail d p x‖ ≤ M*(1+(size x:ℝ))^d := by
  induction d generalizing x p with
  | zero => simpa only [tail, Newt.take, Finset.range_zero, Finset.sum_empty,sub_zero,pow_zero,mul_one] using (show ‖p x‖ ≤ M from h [] rfl x he)
  | succ i ih =>
    refine pointwise i (Newt.top ..) hM (C:=R) (fun j v hv => ?_) x he
    rw [currency]; apply ih (p:=jump p j) ?_ v hv
    intro l hl; exact h (j::l) (by simp [hl])

open Pattern
lemma coord_size (x : Cover) (i : Axis) : ‖xyz x i‖ ≤ (size x:ℝ) := by
  change ‖((x i:ℤ):ℝ)‖ ≤ _
  rw [← norm_natAbs, Real.norm_natCast]
  exact_mod_cast single_le_sum (s:=Finset.univ) (f:=fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)

/-- The Newton coefficients have explicit growth, L1 position allowed
 integer xy recentered on cover. -/
lemma component (n : ℕ) (p : Cover → E) (hM : 0 ≤ M)
    (he : ∀ l : List Axis,l.length=n → ‖iterate p l 0‖ ≤ M) (x : Cover) :
    ‖piece n p (xyz x)‖ ≤ ((4*((n:ℝ)+1))^n)*(1+(size x:ℝ))^n*M := by
  suffices ∀ (y : E4) (d : ℝ),0 ≤ d → (∀ i,‖y i‖ ≤ d) →
      ‖piece n p y‖ ≤ ((4*((n:ℝ)+1))^n)*(1+d)^n*M by exact this _ _ (by positivity) (coord_size x)
  -- easier induction proof with (d+n+1)^n
  have h (i : ℕ) (p : Cover→E) (h : ∀ l : List Axis, l.length=i → ‖iterate p l 0‖ ≤ M) :
      ∀ (y : E4) (d : ℝ),0 ≤ d → (∀ i, ‖y i‖ ≤ d) → ‖piece i p y‖ ≤ 4^i*(d+i)^i*M := by
    induction i generalizing p with
    | zero => simpa only [piece,pow_zero,mul_one,one_mul] using fun (_ : E4) (_ : ℝ) _ _ => (show ‖p 0‖ ≤ M from h [] rfl)
    | succ i ih =>
      intro y d hd H
      let a := ((i:ℝ)+1)
      let u := d+a
      have ha : 1 ≤ a := by unfold a; linarith only [Nat.cast_nonneg (α:=ℝ) i]
      have hv : 0 ≤ u := add_nonneg hd (zero_le_one.trans ha)
      rw [piece,norm_smul]
      have hw j : ‖y j • piece i (jump p j) (y-basis j)‖ ≤ u*(4^i*u^i*M) := by
        have hx : ∀ k,‖(y-basis j : E4) k‖ ≤ d+1 := fun k => by
          simp only [PiLp.sub_apply]; apply (norm_sub_le ..).trans
          refine add_le_add (H k) ?_
          simp [basis]; split_ifs <;> simp
        have hp := ih (jump p j) (fun l hl => h (j::l) (by simp [hl])) _ (d+1) (by positivity) hx
        rw [show d+1+i=u by unfold u a; ring] at hp
        rw [norm_smul]; exact mul_le_mul ((H j).trans (le_add_of_nonneg_right (zero_le_one.trans ha))) hp (norm_nonneg _) hv
      rw [Real.norm_of_nonneg (inv_pos.mpr (zero_lt_one.trans_le ha)).le]; push_cast
      change a⁻¹* ‖∑ _,_‖ ≤ 4^_ * u^_*_
      refine mul_le_mul (inv_le_one_of_one_le₀ ha) ((norm_sum_le ..).trans ((sum_le_sum (fun j _ => hw j)).trans ?_)) (norm_nonneg _) (by norm_num) |>.trans (le_of_eq (one_mul _))
      rw [sum_const,card_univ,nsmul_eq_mul,show Fintype.card Axis=4 by rfl]
      norm_num; ring_nf; rfl
  intro y d hd hh
  apply (h n p he y d hd hh).trans
  rw [← mul_pow,← mul_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) hM
  have hh : (0:ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith only [hd,hh,mul_nonneg hh hd]
end YM.MultiNext.SignedSource.Newt
