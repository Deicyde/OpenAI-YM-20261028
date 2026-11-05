import YM.Next.STATIONARY.Infrastructure.Jets
import YM.Planned.PRIMARY_INTEGRAL_295.Cases
import YM.Progress.STATIONARY_SCENES.Green

/-!
# Rooted jet volumes in finite box. Counting. The power sits alongside exponential
    and sustains decrements even if widths eventually shrink. Use same counting size for
    momentum conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Stationary Filter Function Matrix Lattice Precision
open scoped Topology BigOperators ContDiff Classical
open YM.Planned.PrimaryIntegral295.Cases (finest)

def shelter (α : ℝ) (t : ℕ) (r : ℝ) := (1+r)^t * Real.exp (α*r)
lemma shelter_pos (α : ℝ) (t : ℕ) {r : ℝ} (h : 0 ≤ r): 0 < shelter α t r := by unfold shelter; positivity
lemma shelter_top {α β : ℝ} {t u : ℕ} {r R : ℝ} (ha : 0 ≤ α) (hb : α ≤ β) (hr : 0 ≤ r) (hR : r ≤ R) (hp : t ≤ u) : shelter α t r ≤ shelter β u R := by
  have hx := ha.trans hb; have h : 1 ≤ 1+r := by linarith
  unfold shelter
  exact mul_le_mul ((pow_le_pow_right₀ h hp).trans (pow_le_pow_left₀ (by linarith only[h]) (by linarith only[hR]) u)) (Real.exp_le_exp.mpr (mul_le_mul hb hR hr hx)) (Real.exp_pos _).le (pow_nonneg (by linarith only[h,hR]) _)
lemma shelter_triangle (α p : ℝ) (t : ℕ) {r s : ℝ} (hx : 0≤ p) (hr : 0≤ r)(hs:0≤s) : shelter α t (p+r+s) ≤ shelter α t p * shelter α t r * shelter α t s:=by
  have h X Y (hX:0 ≤ X)(hY:0 ≤ Y): shelter α t (X+Y) ≤ shelter α t X * shelter α t Y:=by
    unfold shelter; rw [mul_add α,Real.exp_add]; refine le_trans ?_ (le_of_eq (a:=((1+X)^t*(1+Y)^t)*(Real.exp (α*X)*Real.exp (α*Y))) (by ring))
    rw [← mul_pow]; gcongr; nlinarith only [mul_nonneg hX hY]
  exact (h (p+r) s (add_nonneg hx hr) hs).trans (mul_le_mul_of_nonneg_right (h p r hx hr) (shelter_pos _ _ hs).le)
lemma shelter_add (α : ℝ) (t : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) : shelter α t (r+s) ≤ shelter α t r*shelter α t s := by simpa [shelter] using shelter_triangle α 0 t le_rfl hr hs

variable {I J W : Type} [Fintype I] [Fintype J] [Fintype W] {m : ℕ}
open Finset

def limitN (B : I→ ℕ) (x : W → I) := Finset.univ.sup fun i => B (x i)

omit [Fintype I] in
lemma limitN_ge (B:I→ℕ) (x:W→ I)(i:W) : B (x i) ≤ limitN B x:= Finset.le_sup (s:=univ) (f:=fun i=> B (x i)) (Finset.mem_univ i)
omit [Fintype I] in
lemma limitN_le (B:I→ℕ) (x:W→ I){n:ℕ} : limitN B x ≤ n ↔∀ i,B (x i)≤n:=by simp [limitN]
omit [Fintype I] in
lemma limitN_mem (B:I→ℕ)(x:W→I) (h : Nonempty W) : ∃ i:W, limitN B x=B (x i):=by
  letI : Nonempty W := h
  obtain ⟨i,_,hx⟩:= Finset.exists_mem_eq_sup (univ:Finset W) univ_nonempty (B ∘ x); exact ⟨i,hx⟩

def spot (α : ℝ)(t : ℕ)(r : ℝ)(b : ℕ):=shelter α t (max 0 ((b:ℝ)-r))
lemma spot_pos (α t r b): 0< spot α t r b := shelter_pos α t (le_max_left ..)
lemma spot_one {α : ℝ}(h : 0 ≤ α) (t r b) : 1 ≤ spot α t r b := by
  have he := shelter_top (t:=t) (u:=t) (r:=0) h le_rfl le_rfl (le_max_left 0 ((b:ℝ)-r)) le_rfl; simpa [spot,shelter] using he
lemma spot_mono (α t r) (h : 0≤α) : Monotone (spot α t r) := fun _ _ H=> shelter_top h le_rfl (le_max_left ..) (max_le_max_left _ (sub_le_sub_right (Nat.cast_le.mpr H) _)) le_rfl
lemma spot_tiny (t u : ℕ)(r b){α β : ℝ}(ha:0 ≤ α)(h : α ≤ β) (hu:t ≤ u): spot α t r b ≤ spot β u r b:= shelter_top ha h (le_max_left ..) le_rfl hu
lemma spot_anti (α t b)(h : 0 ≤ α)(r s : ℝ)(hp : r ≤ s): spot α t s b ≤ spot α t r b:=shelter_top h le_rfl (le_max_left ..) (max_le_max_left _ (sub_le_sub_left hp _)) le_rfl
lemma spot_build {α r : ℝ}(t b)(h : 0≤α) (hr : 0≤r) : spot α t 0 b ≤ shelter α t r*spot α t r b:=by
  apply (le_trans ?_ (shelter_add _ _ hr (s:=max 0 ((b:ℝ)-r)) (le_max_left ..)))
  unfold spot; apply shelter_top h le_rfl (le_max_left ..) _ le_rfl
  simp; linarith only [le_max_right (0:ℝ) ((b:ℝ)-r)]

variable [DecidableEq W] {X : Type*}[NormedAddCommGroup X]
def cost (A : I→ ℕ) (α : ℝ)(t : ℕ)(r : ℝ)(q : (W → I) → X) := ∑ x: W → I, spot α t r (limitN A x) * ‖q x‖
lemma cost_nn (A α t r) (q : (W→ I) → X) : 0 ≤ cost A α t r q := sum_nonneg (s:=univ) fun _ _ => mul_nonneg (spot_pos ..).le (norm_nonneg _)
lemma cost_add (A α t r)(q w : (W→ I) → X) : cost A α t r (q+w) ≤ cost A α t r q+cost A α t r w:=by
  unfold cost; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _=>?_ ; rw [Pi.add_apply,←mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (spot_pos ..).le
lemma cost_sum {T:Type}[Fintype T] (A α t r) (F:T→(W→ I)→ X): cost A α t r (fun v=>∑ i,F i v)≤∑ i,cost A α t r (F i):= by
 unfold cost; rw [Finset.sum_comm]; refine sum_le_sum fun i _ => ?_; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (spot_pos ..).le
lemma cost_anti (q : (W→ I)→X)(A:I→ℕ)(α t r s)(h:0 ≤ α)(ht:r ≤ s): cost A α t s q ≤ cost A α t r q:= by
 apply sum_le_sum;intro i _; exact mul_le_mul_of_nonneg_right (spot_anti _ _ _ h _ _ ht) (norm_nonneg _)
lemma cost_tiny (q:(W→I)→ X)(A:I→ℕ)(α β t u r)(ha:0≤α)(h: α ≤ β)(hp:t ≤ u): cost A α t r q ≤ cost A β u r q:= sum_le_sum fun _ _=> mul_le_mul_of_nonneg_right (spot_tiny _ _ _ _ ha h hp) (norm_nonneg _)
lemma cost_build (q:(W→I)→ X)(A α t r)(h:0 ≤ α)(hp:0 ≤ r): cost A α t 0 q ≤ shelter α t r*cost A α t r q:= by
 unfold cost; rw [Finset.mul_sum]; refine sum_le_sum fun i _=> ?_; rw [← mul_assoc];apply mul_le_mul_of_nonneg_right (spot_build _ _ h hp) (norm_nonneg _)

omit [Fintype I] [Fintype W] in
lemma splitN (A:I→ℕ)(α t r)(c:OrderedFinpartition m)(x:Fin m→I)(h:0≤α)(he:0≤r): spot α t r (limitN A x) ≤ ∏ i : Fin c.length, spot α t r (limitN A (x ∘ c.emb i)) := by
 classical
 rcases isEmpty_or_nonempty (Fin m) with h₀|h₀
 · rw [show limitN A x=0 by simp [limitN],show spot α t r 0=1 by simp [spot,shelter,he]]; exact one_le_prod fun _ _=> spot_one h ..
 obtain ⟨i,hi⟩:= limitN_mem A x h₀
 obtain ⟨b,H⟩:= c.equivSigma.surjective i
 rcases b with ⟨v,l⟩; subst i
 rw [hi]; refine (spot_mono _ _ _ h (a:=_) (limitN_ge A (x ∘ c.emb v) l)).trans ?_
 let f i:= spot α t r (limitN A (x ∘ c.emb i)); change f v≤∏ i,f i; rw [← mul_prod_erase (s:=univ) _ (Finset.mem_univ v)]; exact le_mul_of_one_le_right (spot_pos ..).le (one_le_prod fun _ _=>spot_one h ..)

end YM.Trace.Perfect
