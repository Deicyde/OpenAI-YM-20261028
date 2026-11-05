import YM.Next.STATIONARY.Spectral.Slabs
import YM.Work.A05.Window
import YM.Work.B09.Shell

set_option autoImplicit false
/-!
# Weights on local derivative tests

Use probabilities on all reading locations (a multiset allowed via weight),
not probability on the big mesh. `Hearing t=ℓ∞,ℓ²,ℓ¹` for t=0,1,2
rough legs. Real derivatives on arrays, then finite complexification.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {α β γ : Type} [Fintype α] [Fintype β] {X Y Z : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] {C D H : ℝ} {n m : ℕ}

structure Audience (α : Type) [Fintype α] where
  weight : α → ℝ
  wage i : 0 ≤ weight i
  enough : ∑ i, weight i=1

variable (A : Audience α)
def Audience.weightedSum (f : α → ℝ) := ∑ i,A.weight i*f i
@[simp] lemma Audience.staying (a : ℝ) : A.weightedSum (fun _ => a)=a := by rw [weightedSum, ← sum_mul, A.enough,one_mul]
lemma Audience.column {p q : α → ℝ} (h : p ≤ q) : A.weightedSum p ≤ A.weightedSum q := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h _) (A.wage i)
lemma Audience.grow (p : α → ℝ) (a : ℝ) : A.weightedSum (fun i => a*p i)= a*A.weightedSum p := by unfold weightedSum; rw [Finset.mul_sum]; exact sum_congr rfl fun _ _ => by ring
lemma Audience.peak (f : α → ℝ) : 0 ≤ A.weightedSum (fun i => f i^2) := (A.staying 0) ▸ A.column (p:=fun _ => 0) (q:=fun i => f i^2) (fun i => sq_nonneg _)
lemma Audience.compare (f g : α → ℝ) : A.weightedSum (fun i => f i*g i) ≤ Real.sqrt (A.weightedSum (fun i => f i ^ 2)) * Real.sqrt (A.weightedSum (fun i => g i ^2)) := by
  have ht := Real.sum_mul_le_sqrt_mul_sqrt univ (fun i => Real.sqrt (A.weight i)*f i) (fun i => Real.sqrt (A.weight i)*g i)
  have he i : A.weight i*(f i*g i)=Real.sqrt (A.weight i)*f i*(Real.sqrt (A.weight i)*g i) := by
    rw [show Real.sqrt _ * _ * _ = Real.sqrt (A.weight i)^2*(f i*g i) by ring,Real.sq_sqrt (A.wage _)]
  unfold weightedSum; simp_rw [he]; simpa only [mul_pow,Real.sq_sqrt (A.wage _)] using ht
lemma Audience.couple {f g : α→ℝ} (h : A.weightedSum (fun i => f i^2)≤ C^2) (he : A.weightedSum (fun i => g i^2)≤D^2) (hp : 0≤C) (hq : 0≤D) : A.weightedSum (fun i => f i*g i)≤C*D :=
    (A.compare f g).trans (mul_le_mul ((Real.sqrt_le_left hp).mpr h) ((Real.sqrt_le_left hq).mpr he) (Real.sqrt_nonneg _) hp)

structure Hearing (A : Audience α) (t : ℕ) (f : α→X) (c : ℝ) : Prop where
  cap : 0 ≤ c
  all : t=0 → ∀ i, ‖f i‖ ≤ c
  ample : t=1 → A.weightedSum (fun i => ‖f i‖^2) ≤ c^2
  enough : t=2 → A.weightedSum (fun i => ‖f i‖) ≤ c

variable {A} {f g : α →X} {u : α → Y} {v : α→Z}
namespace Hearing
lemma more (h : Hearing A n f C) (he : C ≤ H) : Hearing A n f H := ⟨h.cap.trans he, fun p i => (h.all p i).trans he,
   fun p => (h.ample p).trans (pow_le_pow_left₀ h.cap he _), fun p => (h.enough p).trans he⟩
lemma softer (h : Hearing A n f C) (p : ∀ i, ‖u i‖≤‖f i‖) : Hearing A n u C := ⟨h.cap,fun hp i => (p _).trans (h.all hp i),fun hp => le_trans (A.column (p:=fun i => ‖u i‖^2) (fun i => pow_le_pow_left₀ (norm_nonneg _) (p _) _)) (h.ample hp),fun hp => le_trans (A.column (p:=fun i => ‖u i‖) (q:=fun i => ‖f i‖) p) (h.enough hp)⟩
lemma sup (hc : 0≤C) (hf : ∀ i, ‖f i‖ ≤ C) : Hearing A n f C := by
  refine ⟨hc,fun _ => hf, fun hp => ?_, fun hp => ?_⟩
  · exact (A.column (p:=fun i => ‖f i‖^2) (q:=fun _ => C^2) (fun i => pow_le_pow_left₀ (norm_nonneg _) (hf i) _)).trans_eq (A.staying _)
  exact (A.column (p:=fun i => ‖f i‖) (q:=fun _ => C) hf).trans_eq (A.staying _)
lemma rasp (h : Hearing A n f C) (he : n ≤ 2) : A.weightedSum (fun i => ‖f i‖) ≤ C := by
  interval_cases n
  · exact Hearing.enough (Hearing.sup h.cap (A:=A) (h.all rfl)) (Eq.refl 2)
  · have ht := A.couple (f:=fun i => ‖f i‖) (g:=fun _ => (1:ℝ)) (D:=1) (h.ample rfl) (by rw [A.staying]) h.cap (by norm_num)
    simpa using ht
  exact h.enough rfl

lemma added {g : α→ Z} (p : ∀ i, ‖u i‖ ≤ ‖f i‖+‖g i‖) (h : Hearing A n f C) (q : Hearing A n g D) : Hearing A n u (C+D) := by
  refine ⟨add_nonneg h.cap q.cap,fun hp i => (p i).trans (add_le_add (h.all hp i) (q.all hp i)),fun hp => ?_,fun hp => ?_⟩
  · apply (A.column (p:=fun i => ‖u i‖^2) (fun i => pow_le_pow_left₀ (norm_nonneg _) (p i) 2)).trans
    have hk := A.couple (f:=fun i => ‖f i‖) (g:=fun i => ‖g i‖) (h.ample hp) (q.ample hp) h.cap q.cap
    have he : A.weightedSum (fun i => (‖f i‖ + ‖g i‖)^2) = A.weightedSum (fun i => ‖f i‖^2) + A.weightedSum (fun i => ‖g i‖^2)+2*A.weightedSum (fun i => ‖f i‖*‖g i‖) := by
      unfold Audience.weightedSum; rw [mul_sum,← sum_add_distrib,← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
    rw [he]; nlinarith only [hk,h.ample hp, q.ample hp]
  apply (A.column (p:=fun i => ‖u i‖) (q:=fun i => ‖f i‖+‖g i‖) p).trans
  simpa only [Audience.weightedSum,_root_.mul_add,sum_add_distrib] using add_le_add (h.enough hp) (q.enough hp)
lemma appended (h : Hearing A n f C) (q : Hearing A n g D) : Hearing A n (fun i => f i+g i) (C+D) := added (fun i => norm_add_le ..) h q
lemma deleted (h : Hearing A n f C) (q : Hearing A n g D) : Hearing A n (fun i => f i-g i) (C+D) := added (fun i => norm_sub_le ..) h q
lemma grows (h : Hearing A n f C) (a : ℝ) (hh : 0 ≤ a) (he : ∀ i, ‖u i‖ ≤ a*‖f i‖) : Hearing A n u (a*C) := by
  refine ⟨mul_nonneg hh h.cap, fun hp i => (he _).trans (mul_le_mul_of_nonneg_left (h.all hp i) hh),fun hp => ?_, fun hp => ?_⟩
  · apply (A.column (p:=fun i => ‖u i‖^2) (fun i => pow_le_pow_left₀ (norm_nonneg _) (he i) 2)).trans
    simp_rw [mul_pow]; exact (A.grow _ (a^2)) ▸ mul_le_mul_of_nonneg_left (h.ample hp) (sq_nonneg a)
  exact (A.column (p:=fun i => ‖u i‖) (q:=fun i => a*‖f i‖) he).trans (by rw [A.grow]; exact mul_le_mul_of_nonneg_left (h.enough hp) hh)
lemma multiplied (p : ∀ i, ‖v i‖ ≤ ‖f i‖*‖u i‖) (h : Hearing A n f C) (q : Hearing A m u D) : Hearing A (n+m) v (C*D) := by
  by_cases hc : n=0
  · subst n; rw [zero_add]
    exact q.grows C h.cap (fun i => (p _).trans (mul_le_mul_of_nonneg_right (h.all rfl i) (norm_nonneg _)))
  by_cases hd : m=0
  · subst m; rw [add_zero,mul_comm]; exact h.grows D q.cap (fun i => (p _).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (q.all rfl i) (norm_nonneg _)))
  refine ⟨mul_nonneg h.cap q.cap, by omega, by omega, fun he => ?_⟩
  exact (A.column (p:=fun i => ‖v i‖) (q:=fun i => ‖f i‖*‖u i‖) p).trans (A.couple (f:=fun i => ‖f i‖) (g:=fun i => ‖u i‖) (h.ample (by omega)) (q.ample (by omega)) h.cap q.cap)
lemma join (s : Finset γ) {f : γ → α→X} {k : γ→ℝ} (h : ∀ i∈s,Hearing A n (f i) (k i)) : Hearing A n (fun i => ∑ j∈s, f j i) (∑ i∈s,k i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using! (sup (f:=fun _ => (0:X)) (n:=n) (A:=A) le_rfl (by simp))
  | insert a s hp ih => simpa [hp] using (h a (by simp)).appended (ih fun j hj => h j (by simp [hj]))
end Hearing
end YM.Stationary
end

/-!
# Probability operations with relative Hearings. A Taylor coefficient is
always tested at its exact mesh. Cropping costs include exact cardinal ratio.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {α β γ : Type} [Fintype α] [Fintype β] {X Y : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] {C D H : ℝ} {n m : ℕ}

namespace Audience
variable (A : Audience α) (B : Audience β)

def balcony (α : Type) [Fintype α] [Nonempty α] : Audience α where
  weight _ := (Fintype.card α:ℝ)⁻¹
  wage _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  enough := by
    have he : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
    simp [he.ne']

def circus : Audience (α × β) where
  weight x := A.weight x.1*B.weight x.2
  wage x := mul_nonneg (A.wage _) (B.wage _)
  enough := by simp_rw [Fintype.sum_prod_type,← Finset.mul_sum,B.enough, mul_one,A.enough]
lemma balcony_circus [Nonempty α] [Nonempty β] : circus (balcony α) (balcony β)=balcony _ := by
  unfold balcony circus; congr; ext; simp [mul_comm]
lemma fubini (p : α→β→ℝ) : (A.circus B).weightedSum (fun i => p i.1 i.2) = A.weightedSum (fun i => B.weightedSum (p i)) := by
  unfold Audience.weightedSum; rw [Fintype.sum_prod_type]; simp_rw [circus,mul_sum,mul_assoc]

variable [NormedSpace ℝ X]
def partakes (p : α→X) : X := ∑ i,A.weight i • p i
lemma norm_part (p : α→X) : ‖A.partakes p‖ ≤ A.weightedSum (fun i => ‖p i‖) := (norm_sum_le ..).trans_eq (sum_congr rfl (fun i _ => by rw [norm_smul,Real.norm_eq_abs, abs_of_nonneg (A.wage i)]))
lemma square_part (p : α→X) : ‖A.partakes p‖^2 ≤ A.weightedSum (fun i => ‖p i‖^2) := by
  have hp := A.compare (fun i => ‖p i‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,A.staying,Real.sqrt_one] at hp
  exact (pow_le_pow_left₀ (norm_nonneg _) ((A.norm_part p).trans hp) _).trans_eq (Real.sq_sqrt (A.peak _))
@[simp] lemma partakes_still (v : X) : A.partakes (fun _ => v)=v := by rw [partakes,← Finset.sum_smul,A.enough,one_smul]
lemma partakes_add (x y : α→X) : A.partakes (fun i => x i+y i)=A.partakes x + A.partakes y := by simp_rw [partakes,smul_add,sum_add_distrib]
end Audience
open Audience

namespace Hearing
variable {A : Audience α} {B : Audience β} {f : α→X} {g : β→X}
lemma carried (h : Hearing A n f C) (p : β→α) (hs : ∀ x : α→ℝ, B.weightedSum (x∘p)=A.weightedSum x) : Hearing B n (f∘p) C :=
    ⟨h.cap,fun hp _ => h.all hp _,fun hp => show B.weightedSum ((fun i => ‖f i‖^2)∘p) ≤ C^2 from (hs _).symm ▸ h.ample hp,
      fun hp => show B.weightedSum ((fun i => ‖f i‖)∘p) ≤ C from (hs _).symm ▸ h.enough hp⟩

lemma on_right (h : Hearing B n g C) : Hearing (A.circus B) n (fun i => g i.2) C := h.carried Prod.snd fun x => by
  rw [show x ∘ Prod.snd=(fun i : α × β => (fun _ v => x v) i.1 i.2) from rfl,(fubini A B (fun _ v => x v))]; simp
lemma thins {T : Audience α} (hc : 1 ≤ H) (h : Hearing A n f C) (hv : ∀ i,T.weight i ≤ H*A.weight i) : Hearing T n f (H*C) := by
  have hu p (hx : ∀ i,0 ≤ p i) : T.weightedSum p ≤ H*A.weightedSum p := by
    unfold Audience.weightedSum; rw [mul_sum]; refine sum_le_sum fun i _ => (mul_le_mul_of_nonneg_right (hv i) (hx i)).trans_eq (by rw [mul_assoc])
  have ht : 0≤H := by linarith
  refine ⟨mul_nonneg ht h.cap, fun p i => (h.all p i).trans (le_mul_of_one_le_left h.cap hc), fun p => ?_, fun p => (hu _ (fun _ => norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (h.enough p) ht)⟩
  exact (hu _ (fun i => sq_nonneg _)).trans ((mul_le_mul_of_nonneg_left (h.ample p) ht).trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)))
lemma crops {g : β→Y} (p : Finset β) (P : β → α) (hp : Set.InjOn P (↑p))
    (hc : 1 ≤ H) (he : ∀ i∈p,‖g i‖ ≤ ‖f (P i)‖ ∧ B.weight i ≤ H*A.weight (P i)) (hx : ∀ i∉p, g i=0) (h : Hearing A n f C) : Hearing B n g (H*C) := by
  classical
  have hu := le_mul_of_one_le_left h.cap hc
  have ht : 0≤H := by linarith
  have hv j (hj : j≠0) : B.weightedSum (fun i => ‖g i‖^j) ≤ H * A.weightedSum (fun i => ‖f i‖^j) := by
    unfold Audience.weightedSum
    rw [← Finset.sum_subset (subset_univ p) (f:=fun i => B.weight i*‖g i‖^j) (by intro i _ hp; simp [hx i hp,hj]), Finset.mul_sum]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ (p.image P)) fun i _ _ => ?_)
    · rw [sum_image (by exact hp)]
      exact sum_le_sum fun i hi => by rw [← mul_assoc]; exact mul_le_mul (he i hi).2 (pow_le_pow_left₀ (norm_nonneg _) (he i hi).1 _) (by positivity) (mul_nonneg ht (A.wage _))
    exact mul_nonneg ht (mul_nonneg (A.wage _) (by positivity))
  refine ⟨mul_nonneg ht h.cap,fun p' i => ?_,fun p => ?_,fun p => ?_⟩
  · by_cases HZ : i∈p
    · exact ((he i HZ).1.trans (h.all p' _)).trans hu
    rw [hx i HZ,norm_zero]; exact h.cap.trans hu
  · exact (hv 2 (by decide)).trans ((mul_le_mul_of_nonneg_left (h.ample p) ht).trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)))
  have hi := hv 1 (by decide); simp_rw [pow_one] at hi; exact hi.trans (mul_le_mul_of_nonneg_left (h.enough p) ht)
lemma howling [NormedSpace ℝ X] {p : α→β→X} (h : Hearing (A.circus B) n (fun i => p i.1 i.2) C) : Hearing A n (fun i => B.partakes (p i)) C := by
  refine ⟨h.cap, fun hp i => (B.norm_part (p i)).trans ((B.column (p:=fun v => ‖p i v‖) (q:=fun _ => C) fun v => h.all hp (i,v)).trans_eq (B.staying C)),fun hp => ?_,fun hp => ?_⟩
  · apply (A.column (p:=fun i => ‖B.partakes (p i)‖^2) (fun i => B.square_part (p i))).trans
    rw [show A.weightedSum (fun i => B.weightedSum (fun j => ‖p i j‖^2))=_ from (fubini A B (fun i j => ‖p i j‖^2)).symm]; exact h.ample hp
  apply (A.column (p:=fun i => ‖B.partakes (p i)‖) (fun i => B.norm_part (p i))).trans
  rw [show A.weightedSum (fun i => B.weightedSum (fun j => ‖p i j‖))=_ from (fubini A B (fun i j => ‖p i j‖)).symm]; exact h.enough hp
end Hearing
end YM.Stationary
end

/-!
# Price polarization of ensembles of frame jets. Smooth, first harsh,
second harsh costs by `Hearing`. An ensemble with >2 harsh slots is not
tested. Real arrays here, no contour restriction. `Gallop` uses only
positive derivatives, permitting uniform path costs linear in axis length.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ : Type} [Fintype α] [Fintype β] {X Y Z : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] {C D H : ℝ} {n m l : ℕ}

def Audible (f : α → X→Y) := ∀ i,ContDiffAt ℝ ω (f i) 0
-- Price of one coefficient. n=0 allowed. R tests positive/& waived.
variable {A : Audience α} {B : Audience β}

def Tested (P : Audience α) (R : X → ℕ→Prop) (f : α → X→Y) (n : ℕ) (C : ℝ) := ∀ (u : Fin n→X) (b : Fin n → ℕ), (∀ i,R (u i) (b i)) → (∑ i,b i)≤ 2 → Hearing P (∑ i,b i) (fun i => iteratedFDeriv ℝ n (f i) 0 u) C
structure Gallop (P : Audience α) (R : X → ℕ→Prop) (f : α → X→Y) (n : ℕ) (C : ℝ) : Prop where
  listen : Audible f
  stamp : 0≤C
  reaches m : 0<m → m ≤ n → Tested P R f m C

variable {R : X→ℕ→Prop} {f g : α→X→Y}
lemma Tested.raises (h : Tested A R f n C) (he : C≤D) : Tested A R f n D := fun u b hb hf => (h u b hb hf).more he
lemma Tested.zeros (hn : 0≤C) (c : α→Y) (h : 0<n) : Tested A R (fun i _ => c i) n C := by
  intro u b _ _; exact Hearing.sup hn (by simp [iteratedFDeriv_const_of_ne (Nat.ne_of_gt h),hn])
lemma Tested.plus (p : Audible f) (q : Audible g) (h : Tested A R f n C) (he : Tested A R g n D) : Tested A R (fun i x => f i x+g i x) n (C+D) := by
  intro u b hb ha
  change Hearing _ _ (fun i => iteratedFDeriv ℝ n (f i+g i) 0 u) _
  simp_rw [iteratedFDeriv_add_apply ((p _).of_le le_top) ((q _).of_le le_top),_root_.add_apply]
  exact (h u b hb ha).appended (he u b hb ha)
lemma Tested.minus (p : Audible f) (q : Audible g) (h : Tested A R f n C) (he : Tested A R g n D) : Tested A R (fun i x => f i x-g i x) n (C+D) := by
  intro u b hb ha
  change Hearing _ _ (fun i => iteratedFDeriv ℝ n (f i-g i) 0 u) _
  simp_rw [iteratedFDeriv_sub_apply ((p _).of_le le_top) ((q _).of_le le_top),_root_.sub_apply]
  exact (h u b hb ha).deleted (he u b hb ha)
lemma Tested.makes {g : α→X→Z} (p : Audible f) (q : Audible g) (h : Tested A R f n C) (he : Tested A R g n D) : Tested A R (fun i x => (f i x,g i x)) n (C+D) := by
  intro u b hb hp
  simp_rw [iteratedFDeriv_prodMk (p _) (q _) le_top]
  exact Hearing.added (fun i => by
    change max _ _≤_+_
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))) (h u b hb hp) (he u b hb hp)
lemma Tested.splitS (p : Audible f) (h : Tested A R f n C) (d : ℝ) : Tested A R (fun i x => d • f i x) n (‖d‖*C) := by
  intro u b hb hp
  simp_rw [iteratedFDeriv_const_smul_apply' ((p _).of_le le_top),_root_.smul_apply]
  exact (h u b hb hp).grows _ (norm_nonneg _) (by intro i; rw [norm_smul])

namespace Gallop
lemma blank (hf : Audible f) (hd : 0 ≤ C) : Gallop A R f 0 C := ⟨hf,hd, by omega⟩

lemma renew (h : Gallop A R f n C) (he : ∀ i,g i =ᶠ[𝓝 0] f i) : Gallop A R g n C := ⟨fun i => (h.listen i).congr_of_eventuallyEq (he _),h.stamp,fun k hp hx u b hb hy => by
    simp_rw [((he _).iteratedFDeriv ℝ k).eq_of_nhds]; exact h.reaches k hp hx u b hb hy⟩
lemma raises (h : Gallop A R f n C) (hn : m≤n) (hp : C ≤ H) : Gallop A R f m H := ⟨h.listen,h.stamp.trans hp,fun k hk hx => Tested.raises (h.reaches _ hk (hx.trans hn)) hp⟩
lemma goes (c : α → Y) (h : 0≤C) : Gallop A R (fun i _ => c i) n C := ⟨fun _ => contDiffAt_const,h,fun _ hp _ => Tested.zeros h c hp⟩
lemma lips (h : Gallop A R f n C) (p : β→α) (hs : ∀ x : α → ℝ,B.weightedSum (x ∘ p)=A.weightedSum x) : Gallop B R (fun i x => f (p i) x) n C := ⟨fun i => h.listen (p i),h.stamp,fun j hd hq u b hu hv => (h.reaches j hd hq u b hu hv).carried p hs⟩
lemma doubles (h : Gallop A R f n C) (he : Gallop A R g n D) : Gallop A R (fun i x => f i x+g i x) n (C+D) := ⟨fun i => (h.listen i).add (he.listen i),add_nonneg h.stamp he.stamp,fun k hp hx => Tested.plus h.listen he.listen (h.reaches k hp hx) (he.reaches k hp hx)⟩
lemma minuses (h : Gallop A R f n C) (he : Gallop A R g n D) : Gallop A R (fun i x => f i x-g i x) n (C+D) := ⟨fun i => (h.listen i).sub (he.listen i),add_nonneg h.stamp he.stamp,fun k hp hx => Tested.minus h.listen he.listen (h.reaches k hp hx) (he.reaches k hp hx)⟩
lemma sings {g : α → X→ Z} (h : Gallop A R f n C) (he : Gallop A R g n D) : Gallop A R (fun i x => (f i x,g i x)) n (C+D) :=
    ⟨fun i => (h.listen i).prodMk (he.listen i),add_nonneg h.stamp he.stamp,fun k hp hx => Tested.makes h.listen he.listen (h.reaches k hp hx) (he.reaches k hp hx) ⟩
lemma splitS (h : Gallop A R f n C) (d : ℝ) : Gallop A R (fun i x => d • f i x) n (‖d‖*C) := ⟨fun i => (h.listen i).const_smul _, mul_nonneg (norm_nonneg _) h.stamp,fun k hp hx => Tested.splitS h.listen (h.reaches k hp hx) d⟩
lemma leans (h : Gallop A R f n C) (c : Y) : Gallop A R (fun i x => f i x - c) n C := by simpa using h.minuses (goes (fun _ => c) le_rfl)
end Gallop
end YM.Stationary
end

/-!
# Hearing a composite. Derivative-count partition measures,
>1 and only one. No estimates of undifferentiated averages required.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ : Type} [Fintype α] [Fintype β] {X Y Z : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] {C D H : ℝ} {n m l : ℕ}
variable {A : Audience α} {B : Audience β} {R : X→ℕ→Prop} {f g : α→X→Y}

omit [NormedSpace ℝ Y] in
lemma chapter_heard (s : Finset γ) {v : γ→α→Y} {b : γ → ℕ} {k : γ → ℝ} (h : ∀ i ∈ s,Hearing A (b i) (v i) (k i)) : Hearing A (∑ i∈s,b i) (fun i => ∏ j∈s, ‖v j i‖) (∏ j∈s,k j) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [sum_empty,prod_empty]; apply Hearing.sup (by norm_num); simp
  | insert a s hp ih =>
    simp_rw [sum_insert hp,prod_insert hp]
    refine Hearing.multiplied ?_ (h a (by simp)) (ih fun i hi => h i (by simp [hi]))
    intro i; rw [norm_mul]; simp
lemma entices (s : Finset γ) {v : γ→α→Y} {b : γ→ℕ} {k : γ→ℝ} (h : ∀ i∈s,Hearing A (b i) (v i) (k i)) {u : α→Z} (hh : ∀ i,‖u i‖ ≤ C*∏ j∈s,‖v j i‖) (hk : 0≤C) : Hearing A (∑ i∈s,b i) u (C*∏ j∈s,k j) := by
  apply Hearing.grows (chapter_heard s h) C hk
  intro i; rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact hh i

lemma partition_cardinal (c : OrderedFinpartition n) : ∑ i,c.partSize i=n := by simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
lemma crowded (c : OrderedFinpartition n) (h : 1<c.length) (i) : c.partSize i<n := by
  letI : Nontrivial (Fin c.length) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using h)
  obtain ⟨j,hj⟩ := exists_ne i (α:=Fin c.length)
  have he : c.partSize j + c.partSize i ≤ ∑ j,c.partSize j := by
    have ht := sum_le_sum_of_subset_of_nonneg (f:=c.partSize) (subset_univ {j,i}) (by intros; omega)
    simpa [hj] using ht
  exact lt_of_lt_of_le (lt_add_of_pos_left _ (c.partSize_pos j)) (he.trans_eq (partition_cardinal c))

variable {T : Y→Z} {u₀ : Y}
def apollo (F : Y→Z) (z : Y) (C : ℝ) (n : ℕ) := ∑ c : OrderedFinpartition n, ‖iteratedFDeriv ℝ c.length F z‖*(∏ _ : Fin c.length, C)
lemma apollo_pos (F : Y→Z) (z : Y) (h : 0≤C) (n : ℕ) : 0≤apollo F z C n := by unfold apollo; positivity
lemma tested_compartment (h : ContDiffAt ℝ ω T u₀) (hp : Gallop A R f m C) (he : ∀ i,f i 0=u₀)
    (hc : 0 < n) (hr : ∀ c : OrderedFinpartition n, iteratedFDeriv ℝ c.length T u₀≠0 → ∀ i,c.partSize i≤m) : Tested A R (fun i => T∘f i) n (apollo T u₀ C n) := by
  intro u b hx hv
  have heq i : iteratedFDeriv ℝ n (T∘f i) 0 u = ∑ c : OrderedFinpartition n, iteratedFDeriv ℝ c.length T u₀ (fun j => iteratedFDeriv ℝ (c.partSize j) (f i) 0 (u ∘ c.emb j)) := by
    rw [iteratedFDeriv_comp (show ContDiffAt ℝ ω T (f i 0) by rw [he]; exact h) (hp.listen i) le_top,he]
    simp only [FormalMultilinearSeries.taylorComp,_root_.sum_apply]; rfl
  simp_rw [heq]; unfold apollo; apply Hearing.join; intro c _
  by_cases hi : iteratedFDeriv ℝ c.length T u₀=0
  · rw [hi]; apply Hearing.sup (by simp) (by simp)
  have hh j : ∑ k,b (c.emb j k) ≤ 2 := by
    have ht : _ := single_le_sum (s:=univ) (f:=fun j => ∑ k,b (c.emb j k)) (by intro _ _; exact Nat.zero_le _) (mem_univ j)
    exact ht.trans ((c.sum_sigma_eq_sum b) ▸ hv)
  rw [← show _ = (∑ i,b i) from c.sum_sigma_eq_sum b]
  refine entices univ (A:=A) (γ:=Fin c.length) (v:=fun j i => iteratedFDeriv ℝ (c.partSize j) (f i) 0 (u ∘ c.emb j)) (fun j _ => hp.reaches (c.partSize j) (c.partSize_pos j) (hr c hi j) (u ∘ c.emb j) (b ∘ c.emb j) (fun i => hx _) (hh j)) (fun i => (iteratedFDeriv ℝ c.length T u₀).le_opNorm _) (norm_nonneg _)
lemma tested_lite (h : ContDiffAt ℝ ω T u₀) (hp : Gallop A R f m C) (he : ∀ i,f i 0=u₀) (hx : fderiv ℝ T u₀=0) : Tested A R (fun i => T∘f i) (m+1) (apollo T u₀ C (m+1)) := by
  refine tested_compartment h hp he (by omega) ?_
  intro c hc i; apply Nat.le_of_lt_succ (crowded c ?_ i)
  have ht := c.length_pos (Nat.zero_lt_succ _)
  by_contra! H; have hh : c.length=1 := by omega
  apply hc; rw [hh]; ext1 v; rw [iteratedFDeriv_one_apply,hx]; rfl

def encore (F : Y→ Z) (z : Y) (C : ℝ) (m : ℕ) := ∑ i ∈ range (m+1), apollo F z C i
lemma Gallop.comp (h : Gallop A R f m C) (hp : ∀ i, f i 0=u₀) (he : ContDiffAt ℝ ω T u₀) : Gallop A R (fun i => T ∘ f i) m (encore T u₀ C m) := by
  refine ⟨fun i => (show ContDiffAt ℝ ω T (f i 0) by rw [hp]; exact he).comp _ (h.listen i),Finset.sum_nonneg fun i _ => apollo_pos _ _ h.stamp _,fun k hk hx => ?_⟩
  exact (tested_compartment he h hp hk (fun c _ i => (c.partSize_le i).trans hx)).raises (single_le_sum (s:=range (m+1)) (fun i _ => apollo_pos T u₀ h.stamp i) (mem_range.mpr (Nat.lt_succ_of_le hx)))
end YM.Stationary
end

/-!
# Limited product for contours; no powers of length leak per-step.
All matrices with true norms, real-analytic germ. Includes λ=1 edges.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α β : Type} [Fintype α] [Fintype β] {X M : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedRing M] [NormedAlgebra ℝ M] {C D H E F μ : ℝ} {n m : ℕ}
variable {A : Audience α} {B : Audience β} {R : X→ℕ→Prop} {f g : α→X→M}

def chomp (M : Type) [Mul M] (p : M × M) := p.1*p.2
lemma choke : fderiv ℝ (chomp M) 0=0 := by
  change fderiv ℝ ((Prod.fst : M × M → M)*Prod.snd) 0=_
  rw [fderiv_mul' differentiableAt_fst differentiableAt_snd]
  apply ContinuousLinearMap.ext; intro x; change (0:M)*_+_*0=_; rw [zero_mul,mul_zero]; simp
-- zero backgrounds.
lemma streak (h : Gallop A R f m C) (hs : Gallop A R g m (μ*D)) (hz : ∀ i,f i 0=0) (hu : ∀ i,g i 0=0) (hv : 0<μ) : Tested A R (fun i x => f i x*g i x) (m+1) (μ*apollo (chomp M) 0 (C+D) (m+1)) := by
  let F := fun i x => μ⁻¹ • g i x
  have hp : Gallop A R F m D := by simpa only [F,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv), inv_mul_cancel_left₀ hv.ne'] using hs.splitS μ⁻¹
  let Y := fun i x => (f i x,F i x)
  have hy : Gallop A R Y m (C+D) := h.sings hp
  have hY : ContDiffAt ℝ ω (chomp M) 0 := contDiffAt_fst.mul contDiffAt_snd
  have hk : ∀ i, Y i 0=0 := by simp [Y,F,hz,hu]
  have he : Tested A R (fun i => chomp M ∘ Y i) (m+1) (apollo (chomp M) 0 (C+D) (m+1)) := tested_lite hY hy hk choke
  have hx := Tested.splitS (f:=fun i => chomp M ∘ Y i) (fun i => (hk i ▸ hY : ContDiffAt ℝ ω (chomp M) (Y i 0)).comp _ (hy.listen i)) he μ
  simpa [Real.norm_eq_abs,hv,abs_of_pos,chomp,Y,F,smul_smul,hv.ne'] using hx
lemma forestep (h : Gallop A R f m C) (hs : Gallop A R g (m+1) (μ*D)) (hz : ∀ i,f i 0=1) (hu : ∀ i,g i 0=1) (he : Tested A R f (m+1) H) (hv : 0<μ) : Tested A R (fun i x => f i x*g i x) (m+1) (H+μ*D+μ*apollo (chomp M) 0 (C+D) (m+1)) := by
  let F := fun i x => f i x-1; let V := fun i x => g i x-1
  have hf : Gallop A R F m C := h.leans _
  have hx : Gallop A R V (m+1) (μ*D) := hs.leans _
  have hy := streak hf (hx.raises (Nat.le_succ _) le_rfl) (by simp [F,hz]) (by simp [V,hu]) hv
  have ht : Tested A R (fun i x => f i x+V i x+F i x*V i x) (m+1) _ := Tested.plus
    (fun i => (h.listen i).add (hx.listen i)) (fun i => (hf.listen i).mul (hx.listen i)) (Tested.plus h.listen hx.listen he (hx.reaches _ (Nat.zero_lt_succ _) le_rfl)) hy
  rw [show (fun i x => f i x*g i x)=(fun i x => f i x+V i x+F i x*V i x) by
    ext i x; unfold F V; noncomm_ring]; exact ht

-- path recurrence. choose BEFORE size.
def convoy (M : Type) [NormedRing M] [NormedAlgebra ℝ M] (C D : ℝ) : ℕ→ℝ
    | 0 => 0
    | n+1 => let p := convoy M C D n; p+C*(D+apollo (chomp M) 0 (p+D) (n+1))
lemma convoy_cap (p : 0≤C) (h : 0≤D) (n : ℕ) : 0 ≤ convoy M C D n := by
  induction n with
  | zero => simp [convoy]
  | succ n ih => rw [convoy]; exact add_nonneg ih (mul_nonneg p (add_nonneg h (apollo_pos _ _ (add_nonneg ih h) _)))

lemma convoyed (F : ℕ → α → X → M) (U : ℕ → α → X → M) (h : ∀ j<m,F (j+1)=fun i x => F j i x * U j i x)
    (he : ∀ j<m,∀ i,U j i 0=1) (hp : ∀ i,F 0 i=fun _ => 1) (hd : 0≤D) (hu : 0<μ) (ht : (m:ℝ)*μ ≤ C) (hx : ∀ j<m, Gallop A R (U j) n (μ*D)) : ∀ k≤m, Gallop A R (F k) n (convoy M C D n) := by
  have hc : 0≤C := le_trans (mul_nonneg (Nat.cast_nonneg _) hu.le) ht
  have hh k (hk : k≤m) : ∀ i,F k i 0=1 := by
    induction k with
    | zero => simp [hp]
    | succ k ih => simp only [h k (by omega),he k (by omega),ih (by omega),one_mul,implies_true]
  induction n with
  | zero =>
    intro k hk; apply Gallop.blank (_ : Audible (F k)) (convoy_cap hc hd _); intro i
    induction k with
    | zero => rw [hp]; exact contDiffAt_const
    | succ k ih => rw [h k (by omega)]; exact (ih (by omega)).mul ((hx k (by omega)).listen i)
  | succ n ih =>
    specialize ih (fun k hk => (hx k hk).raises (Nat.le_succ _) le_rfl)
    let p := convoy M C D n
    let z := apollo (chomp M) 0 (p+D) (n+1)
    have hp' : 0≤p := convoy_cap hc hd _
    have hz : 0≤z := apollo_pos _ _ (add_nonneg hp' hd) _
    have hs k (hk : k ≤ m) : Tested A R (F k) (n+1) ((k:ℝ)* μ*(D+z)) := by
      induction k with
      | zero => rw [show F 0 = _ from funext hp]; simp only [Nat.cast_zero,zero_mul]; exact Tested.zeros le_rfl _ (by omega)
      | succ k ih' =>
        rw [h k (by omega),Nat.cast_add_one,add_mul,one_mul,add_mul,mul_add μ D, ← add_assoc]
        exact forestep (ih k (by omega)) (hx k (by omega)) (hh k (by omega)) (he k (by omega)) (ih' (by omega)) hu
    intro k hk
    have hw := ih k hk
    refine ⟨hw.listen,convoy_cap hc hd _,fun j hp hx => ?_⟩
    by_cases he : j=n+1
    · subst j; apply (hs k hk).raises
      exact le_trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk : (k:ℝ) ≤ (m:ℝ)) hu.le).trans ht) (add_nonneg hd hz)) (le_add_of_nonneg_left hp')
    exact (hw.reaches j hp (by omega)).raises (le_add_of_nonneg_right (mul_nonneg hc (add_nonneg hd hz)))
end YM.Stationary
end

/-! # Hearing at multiple locations. Crops on probability measures. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α β γ : Type} [Fintype α] [Fintype β] {X Y Z : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] {C D H μ : ℝ} {n m : ℕ}
variable {A : Audience α} {B : Audience β} {R : X→ℕ→Prop} {f g : α→X→Y}

namespace Gallop
lemma each_side [Nonempty γ] [Fintype γ] {T : β → X→ Y} {V : γ→β} [Nonempty β] (h : Gallop (balcony β) R T n C)
    (P : β × β ≃ γ) (hv : ∀ p,V (P p)=p.1) : Gallop (balcony γ) R (T ∘ V) n C := by
  apply h.lips
  intro x
  have hx : (balcony γ).weightedSum (x ∘ V)=(balcony (β × β)).weightedSum (fun i => x i.1) := by
    unfold Audience.weightedSum; rw [← Equiv.sum_comp P]; simp_rw [Function.comp_apply,hv]; simp only [Audience.balcony,← Fintype.card_congr P]
  rw [hx, ← balcony_circus, Audience.fubini (p:=fun i _ => x i)]; simp

lemma cuts (h : Gallop A R f n C) (p : α→Prop) [DecidablePred p] (v : Y) : Gallop A R (fun i x => if p i then f i x else v) n C := by
  refine ⟨fun i => ?_,h.stamp,fun k hp hu a b he hh => (h.reaches k hp hu a b he hh).softer ?_⟩
  · split
    · exact h.listen i
    exact contDiffAt_const
  intro i
  split
  · exact le_rfl
  simp [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hp)]
lemma on_or (h : Gallop A R f n C) (q : Gallop A R g n D) (p : α→Prop) [DecidablePred p] : Gallop A R (fun i x => if p i then f i x else g i x) n (C+D) := by
  apply ((h.cuts p 0).doubles (q.cuts (fun i => ¬p i) 0)).renew
  intro i; exact Eventually.of_forall fun x => by by_cases H : p i <;> simp [H]
lemma moveFast {g : β→X→Y} {s : Finset β} (h : Gallop A R f n C) (hc : 1 ≤ H) (p : β→α) (he : Set.InjOn p (↑s)) (hp : ∀ i∈s,g i=f (p i) ∧ B.weight i ≤ H*A.weight (p i)) (hu : ∀ i∉s,∃ y, g i=fun _ => y) : Gallop B R g n (H*C) := by
  classical
  have hq : 0≤H := by linarith
  refine ⟨fun i => ?_,mul_nonneg hq h.stamp,fun k hk hx u b hb hi => Hearing.crops s p he hc ?_ ?_ (h.reaches k hk hx u b hb hi)⟩
  · by_cases he : i∈s
    · rw [(hp i he).1]; exact h.listen _
    obtain ⟨y,hy⟩ := hu i he; rw [hy]; exact contDiffAt_const
  · intro i h; change _ ≤ _ ∧ _; rw [(hp i h).1]; exact ⟨le_rfl,(hp i h).2⟩
  intro i hv
  obtain ⟨y,hy⟩ := hu i hv; rw [hy, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk)]; simp
lemma shares {v : α→β→X→Y} (h : Gallop (A.circus B) R (fun i => v i.1 i.2) n C) : Gallop A R (fun i x => B.partakes (fun j => v i j x)) n C := by
  refine ⟨fun i => ContDiffAt.sum (fun j _ => (h.listen (i,j)).const_smul _),h.stamp,fun k hp hu x b hx hh => ?_⟩
  have he i : iteratedFDeriv ℝ k (fun x => B.partakes (fun j => v i j x)) 0 x=B.partakes (fun j => iteratedFDeriv ℝ k (v i j) 0 x) := by
    unfold Audience.partakes; rw [iteratedFDeriv_fun_sum_apply (f:=fun j x => B.weight j • v i j x) (fun j _ => ((show ContDiffAt ℝ ω (v i j) _ from h.listen (i,j)).of_le le_top).const_smul _),_root_.sum_apply]
    refine sum_congr rfl fun j _ => ?_; rw [iteratedFDeriv_const_smul_apply' ((show ContDiffAt ℝ ω (v i j) 0 from h.listen (i,j)).of_le le_top)]; rfl
  simp_rw [he]; exact Hearing.howling (p:=fun i j => _) (h.reaches k hp hu x b hx hh)
lemma budget (h : Gallop A R f n C) {T : Audience α} (hc : 1 ≤ H) (hv : ∀ i,T.weight i ≤ H*A.weight i) : Gallop T R f n (H*C) :=
    ⟨h.listen,mul_nonneg (by linarith) h.stamp,fun k hp hu x b hb hh => (h.reaches k hp hu x b hb hh).thins hc hv⟩
lemma rightS {g : β→X→Y} (h : Gallop B R g n C) : Gallop (A.circus B) R (fun i => g i.2) n C := ⟨fun i => h.listen i.2,h.stamp,fun k hk hp u b hb hv => (h.reaches k hk hp u b hb hv).on_right⟩

lemma line (h : Gallop A R f n C) (p : Y →L[ℝ] Z) : Gallop A R (fun i => p ∘ f i) n (‖p‖*C) := by
  refine ⟨fun i => p.contDiff.contDiffAt.comp _ (h.listen i),mul_nonneg (norm_nonneg _) h.stamp,fun k hk hp u b hb hx => ?_⟩
  simp_rw [p.iteratedFDeriv_comp_left (h.listen _) le_top]; exact (h.reaches k hk hp u b hb hx).grows _ (norm_nonneg _) (fun i => p.le_opNorm _)
-- for actual star isometry
lemma notes_star (G : Gauge) {T : α→X→G.Mat} (h : Gallop A R T n C) : Gallop A R (fun i x => star (T i x)) n C := by
  let F : G.Mat →L[ℝ] G.Mat := ((starL ℝ : G.Mat ≃L[ℝ] G.Mat) : G.Mat→L[ℝ] G.Mat)
  refine ⟨(h.line F).listen,h.stamp,fun j hk hx u b hb hp => (h.reaches j hk hx u b hb hp).softer ?_⟩
  intro i; change ‖iteratedFDeriv ℝ j (F ∘ T i) 0 u‖ ≤ _;
  have hv : iteratedFDeriv ℝ j (F ∘ T i) 0 u=star (iteratedFDeriv ℝ j (T i) 0 u) := DFunLike.congr_fun (F.iteratedFDeriv_comp_left (h.listen i) le_top) u
  rw [hv, norm_star]
end Gallop
end YM.Stationary
end

/-!
# Contacts in a coordinate order. Coppice inside patch.
Locality in actual oriented edges AND turns. The straight leg progress
uses active/inactive test at each j; no fixed-coordinate column root loss.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α β : Type} [Fintype α] [Fintype β] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {n m k : ℕ}

abbrev TPair (P : Patch) := P.Points × P.Points
def panelSwap (v : TPair P) (s : List Axis) : P.Points := ⟨fun i => if i∈s then v.2.val i else v.1.val i,by
  have he := box_test.mp v.2.property; have hx := box_test.mp v.1.property
  apply box_test.mpr; constructor <;> intro i <;> split
  exacts [he.1 i,hx.1 i,he.2 i,hx.2 i]⟩
def swapPanel (s : List Axis) : TPair P≃TPair P where
  toFun x := (panelSwap x s,panelSwap x.swap s)
  invFun x := (panelSwap x s,panelSwap x.swap s)
  left_inv x := Prod.ext (Subtype.ext (funext (fun i => by by_cases h : i∈s <;> simp [panelSwap,h]))) (Subtype.ext (funext (fun i => by by_cases h : i∈s <;> simp [panelSwap,h])))
  right_inv x := Prod.ext (Subtype.ext (funext (fun i => by by_cases h : i∈s <;> simp [panelSwap,h]))) (Subtype.ext (funext (fun i => by by_cases h : i∈s <;> simp [panelSwap,h])))
lemma panelSwap_swap (s : List Axis) (p : TPair P) : panelSwap (swapPanel s p) s=p.1 := congr_arg Prod.fst (Equiv.symm_apply_apply (swapPanel s) p)
lemma stopPanel (p : TPair P) (s : List Axis) (h : s.Nodup) : stop p.1.val (axisRoute p.1.val p.2.val s)=(panelSwap p s).val := by
  rw [axisRoute_end p.1.val p.2.val p.1.val s h]; ext i; by_cases h : i∈s <;> simp [panelSwap,h]
def panelD (v : TPair P) (i : Axis) := v.2.val i - v.1.val i
lemma panel_limit (v : TPair P) (i : Axis) : (panelD v i).natAbs ≤ 2*P.radius := by
  obtain ⟨hh,ht⟩ := box_test.mp v.1.property; obtain ⟨hq,hx⟩ := box_test.mp v.2.property
  unfold panelD; have h₁ := hh i; have h₂ := ht i; have h₃ := hq i; have h₄ := hx i; omega
def orientedLeg (v : TPair P) (i : Axis) : Lattice.Step := ⟨i,decide (panelD v i<0)⟩
def panelPath (v : TPair P) (i : Axis) (k : ℕ) : Walk := List.replicate (min k (panelD v i).natAbs) (orientedLeg v i)
lemma panel_walk (U : CoverConfig G) (p : TPair P) (s : List Axis) (i : Axis) (hs : s.Nodup) :
    travel U p.1.val (axisRoute p.1.val p.2.val (s++[i])) = travel U p.1.val (axisRoute p.1.val p.2.val s) * travel U (panelSwap p s).val (panelPath p i (2*P.radius)) := by
  rw [show axisRoute _ _ _=axisRoute p.1.val p.2.val s++panelPath p i (2*P.radius) by
    unfold axisRoute panelPath; rw [List.flatMap_append,min_eq_right (panel_limit p i)]; simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]; rfl,
    travel_append,stopPanel p s hs]
lemma stop_prongs (x : Cover) (d : Lattice.Step) (i : ℕ) : stop x (List.replicate i d)=x+i • d.vec := by
  induction i generalizing x with
  | zero => simp [stop]
  | succ i ih => rw [List.replicate_succ,stop,ih,succ_nsmul]; abel
lemma panel_reach (U : CoverConfig G) (v : TPair P) (i : Axis) (x : Cover) (j : ℕ) :
    travel U x (panelPath v i (j+1))= travel U x (panelPath v i j)* if j<(panelD v i).natAbs then
      (orientedLeg v i).read U (x+j • (orientedLeg v i).vec) else 1 := by
  unfold panelPath; split
  next h =>
    rw [min_eq_left (Nat.succ_le_of_lt h),min_eq_left h.le,show List.replicate (j+1) (orientedLeg v i) = List.replicate j (orientedLeg v i) ++ [orientedLeg v i] by rw [List.replicate_add]; rfl,travel_append,stop_prongs]; simp [travel]
  next h => push Not at h; rw [min_eq_right h,min_eq_right (by omega),mul_one]
lemma panel_rim (v : TPair P) (s : List Axis) (i : Axis) (he : i ∉ s) {j : ℕ} (h : j≤(panelD v i).natAbs) : (panelSwap v s).val+j • (orientedLeg v i).vec ∈ P.sites := by
  let x := panelSwap v s; let y := v.2
  obtain ⟨hh,ht⟩ := box_test.mp x.property; obtain ⟨hy,hz⟩ := box_test.mp y.property
  have hd : panelD v i=y.val i-x.val i := by simp [panelD,x,panelSwap,he,y]
  have hp : -(P.radius:ℤ) ≤ x.val i+(j:ℤ)*(orientedLeg v i).vec i ∧ x.val i+(j:ℤ)*(orientedLeg v i).vec i ≤ P.radius := by
    specialize hh i; specialize ht i; specialize hy i; specialize hz i
    by_cases H : panelD v i<0
    · simp [orientedLeg,Step.vec,H]; omega
    simp [orientedLeg,Step.vec,H]; omega
  apply box_test.mpr; constructor <;> intro a
  · by_cases H : a=i
    · subst a; exact hp.1
    simpa [x,panelSwap,orientedLeg,Step.vec,apply_ite (fun z : Cover => z a), H,ite_apply] using hh a
  by_cases H : a=i
  · subst a; exact hp.2
  simpa [x,panelSwap,orientedLeg,Step.vec,apply_ite (fun z : Cover => z a), H,ite_apply] using ht a
lemma read_rim (v : TPair P) (s : List Axis) (i : Axis) (he : i∉s) {j : ℕ} (h : j<(panelD v i).natAbs) :
    ((orientedLeg v i).used ((panelSwap v s).val+j • (orientedLeg v i).vec)).1 ∈ P.sites := by
  by_cases H : panelD v i<0
  · have hx := panel_rim v s i he (Nat.succ_le_of_lt h)
    simpa [orientedLeg,H,Step.used,Step.vec,succ_nsmul,add_mul,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hx
  simpa only [orientedLeg,Step.used,H, decide_false, Bool.false_eq_true, ↓reduceIte] using panel_rim v s i he h.le
lemma panel_locus {U V : CoverConfig G} (h : ∀ i∈P.sites, ∀ j,U (i,j)=V (i,j)) (v : TPair P) (i : Axis) (s : List Axis) (he : i∉s) (j : ℕ) :
    travel U (panelSwap v s).val (panelPath v i j)=travel V (panelSwap v s).val (panelPath v i j) := by
  induction j with
  | zero => simp [panelPath,travel]
  | succ j ih =>
    rw [panel_reach,panel_reach,ih]; split; next hz => unfold Step.read; have hh := h _ (read_rim v s i he hz) (((orientedLeg v i).used ((panelSwap v s).val+j • (orientedLeg v i).vec)).2); rw [Prod.mk.eta] at hh; rw [hh]
    rfl
lemma perimeter (p : TPair P) (s : List Axis) (hs : s.Nodup) {U V : CoverConfig G} (h : ∀ i∈P.sites,∀ j,U (i,j)=V (i,j)) :
    travel U p.1.val (axisRoute p.1.val p.2.val s)=travel V p.1.val (axisRoute p.1.val p.2.val s) := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s i ih =>
    rw [List.nodup_append] at hs; rw [panel_walk _ _ _ _ hs.1,panel_walk _ _ _ _ hs.1, ih hs.1,panel_locus h p i s (fun H => hs.2.2 i H i (by simp) rfl)]
end YM.Stationary
end

/-!
# Choir of oriented patches. Every leg pays shared L-cardinality C scaling.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α β : Type} [Fintype α] [Fintype β] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {n m k : ℕ} {R : X→ℕ→Prop} {C μ : ℝ}

section prepare

def choirSquare (G : Gauge) (a b : ℝ) (u v : G.Mat) (n : ℕ) : ℝ := encore (chomp G.Mat) (u,v) (a+b) n
lemma square_sing {A : Audience α} {u v} {D} {f g : α→X→G.Mat} (h : Gallop A R f n C) (he : Gallop A R g n D) (hp : ∀ i,f i 0=u) (hx : ∀ i,g i 0=v) :
    Gallop A R (fun i x => f i x*g i x) n (choirSquare G C D u v n) := Gallop.comp (h.sings he) (fun i => Prod.ext (hp i) (hx i)) (u₀:=(u,v)) (T:=chomp _) (contDiffAt_fst.mul contDiffAt_snd)
end prepare

variable {U : X → CoverConfig G}
def Singer (P : Patch) (R : X→ℕ→Prop) (U : X→CoverConfig G) (n : ℕ) (C : ℝ) := ∀ i : Axis,Gallop (balcony P.Points) R (fun a x => G.mat (U x (a.val,i))) n (inch P.L*C)

lemma Singer.soprano (h : Singer P R U n C) (u : Cover) (i : Axis) :
    Gallop (balcony P.Points) R (fun a x => if a.val+u ∈ P.sites then G.mat (U x (a.val+u,i)) else 1) n (inch P.L*C) := by
  classical
  let W := univ.filter fun a : P.Points => a.val+u ∈ P.sites
  let q := fun a : P.Points => if h : a.val+u ∈ P.sites then (⟨a.val+u,h⟩ : P.Points) else P.center
  have he i (hi : i∈W) : (q i).val=i.val+u := by simp only [W,mem_filter] at hi; simp [q,hi.2]
  refine Eq.mp (show Gallop (balcony P.Points) R _ n (1*(inch P.L*C))=Gallop _ _ _ _ _ by rw [one_mul]) ((h i).moveFast (s:=W) le_rfl q ?_ ?_ ?_)
  · intro x hx y hy hh; exact Subtype.ext (add_right_cancel (b:=u) (by rw [← he x hx,← he y hy,hh]))
  · intro a ha
    refine ⟨?_,by simp [balcony]⟩
    funext k; simp only [W,mem_filter] at ha; rw [if_pos ha.2,he a (by simp only [W,mem_filter, ha.1,ha.2,and_self])]
  intro a ha; simp only [W,mem_filter,mem_univ,true_and] at ha; exact ⟨1,funext fun i => if_neg ha⟩

lemma singer_patch (h : Singer P R U n C) (i : Axis) (s : List Axis) (hp : i ∉ s) (j : ℕ) :
    Gallop (balcony (TPair P)) R (fun v x => if j < (panelD v i).natAbs then
      G.mat ((orientedLeg v i).read (U x) ((panelSwap v s).val+j • (orientedLeg v i).vec)) else 1) n (inch P.L*(C+C)) := by
  classical
  let F (w : Cover) := fun a : P.Points => fun x => if a.val+w∈P.sites then G.mat (U x (a.val+w,i)) else 1
  have hF w : Gallop (balcony P.Points) R (F w) n (inch P.L*C) := h.soprano w i
  let A := fun v : TPair P => panelSwap v s
  let p := F (j • step i) ∘ A; let y := F (-((j+1) • step i)) ∘ A
  let hz := swapPanel (P:=P) s
  have hq : Gallop (balcony (TPair P)) R y n (inch P.L*C) := Gallop.each_side (hF _) hz (fun x => panelSwap_swap s x)
  have ht : Gallop (balcony (TPair P)) R p n (inch P.L*C) := Gallop.each_side (hF _) hz (fun x => panelSwap_swap s x)
  rw [mul_add]; refine (Gallop.cuts ((Gallop.notes_star G hq).on_or ht (fun v => panelD v i<0)) (fun v => j<(panelD v i).natAbs) 1).renew ?_
  intro v; exact Eventually.of_forall fun x => by
    by_cases H : j<(panelD v i).natAbs
    · have he := read_rim v s i hp H
      simp only [H,↓reduceIte]
      by_cases K : panelD v i<0
      · simp [orientedLeg,K,Step.used,Step.vec] at he
        simp only [orientedLeg,K,decide_true,Step.read,Step.used,↓reduceIte,Step.vec,y,F,A,Function.comp_apply,G.mat_inv,H];
        simp only [smul_neg,sub_eq_add_neg]
        have hz : (panelSwap v s).val + - (j • step i) + -step i = (panelSwap v s).val + -((j+1) • step i) := by rw [succ_nsmul]; abel
        rw [hz,if_pos];
        simpa [sub_eq_add_neg,- Pi.smul_apply,add_mul,add_assoc,add_left_comm,add_comm] using he
      simpa only [orientedLeg,K,decide_false, Bool.false_eq_true, ↓reduceIte,Step.read,Step.used,Step.vec,H,p, Function.comp_apply,F,A] using! (show G.mat (U x ((panelSwap v s).val+j • step i,i)) = F (j • step i) (A v) x from (if_pos (by simpa only [orientedLeg,K,decide_false,Bool.false_eq_true, ↓reduceIte,Step.used,Step.vec,A] using he)).symm)
    simp only [H, ↓reduceIte]

lemma singer_leg (h : Singer P R U n C) (hu : U 0=1) (i : Axis) (s : List Axis) (hp : i ∉ s) :
    Gallop (balcony (TPair P)) R (fun v x => G.mat (travel (U x) (panelSwap v s).val (panelPath v i (2*P.radius)))) n
        (convoy G.Mat (2*((P.J:ℝ)+3)) (C+C) n) := by
  let F k := fun v : TPair P => fun x => G.mat (travel (U x) (panelSwap v s).val (panelPath v i k))
  let V k := fun v : TPair P => fun x => if k < (panelD v i).natAbs then G.mat ((orientedLeg v i).read (U x) ((panelSwap v s).val+k • (orientedLeg v i).vec)) else 1
  have hk j : F (j+1)=fun i x => F j i x * V j i x := by
    funext v x; unfold F V; rw [panel_reach,G.mat_mul]; split <;> simp
  have he j (i : TPair P) : V j i 0=1 := by
    unfold V; split; next h => rw [hu]; unfold Step.read; split <;> simp
    rfl
  have hy : 0 ≤ C := nonneg_of_mul_nonneg_right (h i).stamp (inch_pos _)
  have hw v : F 0 v=fun _ => 1 := by simp [F,panelPath,travel]
  have hx : ((↑(2*P.radius):ℝ))*inch P.L=2*((P.J:ℝ)+3) := by push_cast; simp only [Patch.radius,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]; ring_nf; unfold inch; field_simp; abel
  exact convoyed F V (m:=2*P.radius) (fun j _ => hk j) (fun j _ => he j) hw (add_nonneg hy hy) (inch_pos _) hx.le (fun j _ => singer_patch h i s hp j) _ le_rfl

def aria (G : Gauge) (J n : ℕ) (C : ℝ) : ℕ → ℝ
    | 0 => 0
    | k+1 => choirSquare G (aria G J n C k) (convoy G.Mat (2*((J:ℝ)+3)) (C+C) n) 1 1 n
lemma singer_axes (h : Singer P R U n C) (hu : U 0=1) (s : List Axis) (hp : s.Nodup) :
    Gallop (balcony (TPair P)) R (fun v x => G.mat (travel (U x) v.1.val (axisRoute v.1.val v.2.val s))) n (aria G P.J n C s.length) := by
  have ht (v k) : G.mat (travel (U 0) (v:Cover) k)=1 := by rw [hu,Pressure.one,G.mat_one]
  induction s using List.reverseRecOn with
  | nil => exact Gallop.goes (fun _ => G.mat 1) le_rfl
  | append_singleton s i ih =>
    rw [List.nodup_append] at hp; simp_rw [List.length_append,List.length_singleton,aria,panel_walk _ _ _ i hp.1,G.mat_mul]
    exact square_sing (ih hp.1) (singer_leg h hu i s (fun v => hp.2.2 i v i (by simp) rfl)) (fun _ => ht ..) (fun _ => ht ..)
end YM.Stationary
end
