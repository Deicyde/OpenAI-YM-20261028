import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Counting
import YM.Bid.Drops
import YM.Next.FREE_KERNELS.Strands
import YM.Shift.Osc
import YM.Work.B04
import YM.Work.F05.Measure


/-!
# Mixed currencies needed for the external fields

Weighted sup for all smooth legs, counting l² when a rough tangent inserted.
Can pay positive *and* reciprocal exponential weights; for unweighted slot use
`const _ 1`. NOT the matrix determinant norms.

Used throughout `Estimate` and `Local`. Intended use: `f i` is a mixed
derivative of order S.card, at one term/root i; P.amps are the amplitudes
of the arguments. Either charge in sup or in l² over the roots. The latter
only when S contains the marked index (the single rough direction). Store
the l² cost as P.cap times this bill; e.g. when fine roots, cap = L²,
so curled smooth legs going like L⁻² can enter the same estimates as a
curled rough argument of l² size order one. Under Leibniz only one factor
can have the mark, *that's* the point of the sets of indices. Use also in
`Collective` etc for patch arrays (then averages as specified there).
These marks are auxiliary to differentiating the deterministic stationary
action; not field/source/cluster observables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis
open scoped Topology ContDiff BigOperators

variable {X Y Z α ι : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] [Fintype α]

def rlen (x : α→ℝ) := ell2 x
lemma rmono {x y : α→ℝ} (he : ∀ i, |x i| ≤ |y i|) : rlen x ≤ rlen y := by
  apply (sq_le_sq₀ (ell_nonneg _) (ell_nonneg _)).mp; rw [square_length,square_length]
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (he i) 2
lemma rless {x y : α→ℝ} (h : ∀ i, 0 ≤ x i) (he : ∀ i, x i ≤ y i) : rlen x ≤ rlen y := rmono fun i => by
  rw [abs_of_nonneg (h i), abs_of_nonneg ((h i).trans (he i))]; exact he i
lemma rconstant {v : ℝ} (hv : 0 ≤ v) (x : α→ℝ) : rlen (fun i => v*x i)=v*rlen x := by
  conv_rhs => rw [← Real.norm_of_nonneg hv]
  exact ell_smul v x
lemma rtriangle {x y z : α→ℝ} (h : ∀ i, 0 ≤ z i) (ht : ∀ i, z i ≤ x i + y i) : rlen z ≤ rlen x+rlen y :=
    (rless h (y:=x+y) ht).trans (ell_tri ..)
lemma rlimit {κ : Type*} {l : Filter κ} {f : κ→α→ℝ} {g}
    (h : ∀ i, Tendsto (fun x => f x i) l (𝓝 (g i))) : Tendsto (rlen ∘ f) l (𝓝 (rlen g)) := by
  have he : Continuous (fun z : α→ℝ => WithLp.toLp 2 z) := (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous
  exact (he.norm.tendsto _).comp (tendsto_pi_nhds.mpr h)
lemma rperm (e : Equiv.Perm α) (f : α→ℝ) : rlen (f ∘ e) = rlen f :=
  (sq_eq_sq₀ (ell_nonneg _) (ell_nonneg _)).1 (by rw [square_length, square_length]; exact Equiv.sum_comp e (fun i => ‖f i‖^2))

/-- Permit at most one wide slot, but not compulsory. Every use carries amplifiers
from actual inputs. `λ` may grow or decrease. -/
structure Purse (ι α : Type*) where
  mark : Option ι
  cap : ℝ
  rooted : 0 ≤ cap
  amps : ι→ℝ
  budget : ∀ i, 0 ≤ amps i
  toll : ι→α→ℝ
  toll_pos : ∀ i k, 0 < toll i k

namespace Purse
variable (P : Purse ι α)

def tagged (S : Finset ι) : Prop := ∃ i∈S,P.mark=some i

def price (S : Finset ι) (x : α) := ∏ i∈S, P.toll i x
def target (S : Finset ι) := ∏ i∈S, P.amps i
omit [Fintype α] in
lemma price_pos (S : Finset ι) (x : α) : 0 < P.price S x := Finset.prod_pos fun _i _ => P.toll_pos ..
omit [Fintype α] in
lemma target_pos (S : Finset ι) : 0 ≤ P.target S := Finset.prod_nonneg fun i _ => P.budget i

/-- `C` per actual assignment. -/
def Pays (S : Finset ι) (f : α→X) (C : ℝ) := 0 ≤ C ∧
    (¬ P.tagged S → ∀ i, P.price S i * ‖f i‖ ≤ C * P.target S) ∧
    (P.tagged S → rlen (fun i => P.price S i*‖f i‖) ≤ P.cap*C* P.target S)
variable {P} {S T R : Finset ι} {f : α→X} {g : α→Y} {E C D : ℝ}
lemma Pays.mono (h : P.Pays S f C) (he : C ≤ D) : P.Pays S f D := ⟨h.1.trans he,fun ht i =>
    (h.2.1 ht i).trans (mul_le_mul_of_nonneg_right he (P.target_pos _)), fun ht => (h.2.2 ht).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he P.rooted) (P.target_pos _))⟩
lemma Pays.under (h : P.Pays S f C) (he : ∀ i, ‖g i‖ ≤ ‖f i‖) : P.Pays S g C := ⟨h.1,fun ht i =>
    (mul_le_mul_of_nonneg_left (he i) (P.price_pos _ _).le).trans (h.2.1 ht i), fun ht =>
    le_trans (rless (fun _i => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)) (fun i => mul_le_mul_of_nonneg_left (he i) (P.price_pos _ _).le)) (h.2.2 ht)⟩
lemma Pays.neg (h : P.Pays S f C) : P.Pays S (-f) C := h.under (fun i => by simp)
lemma Pays.repay (h : P.Pays S f C) (hp : 0 ≤ D) (he : ∀ i, ‖g i‖ ≤ D*‖f i‖) : P.Pays S g (D*C) := by
  have ha i : P.price S i*‖g i‖ ≤ D*(P.price S i*‖f i‖) := (mul_le_mul_of_nonneg_left (he i) (P.price_pos _ _).le).trans_eq (mul_left_comm ..)
  refine ⟨mul_nonneg hp h.1,fun ht i => (ha i).trans ((mul_le_mul_of_nonneg_left (h.2.1 ht i) hp).trans_eq (mul_assoc ..).symm),fun ht =>
    (rless (fun i => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)) ha).trans ?_⟩
  rw [show rlen _=D*rlen (fun i => P.price S i*‖f i‖) from rconstant hp _]
  exact (mul_le_mul_of_nonneg_left (h.2.2 ht) hp).trans_eq (by ring)
lemma Pays.relocate (e : Equiv.Perm α) (h : P.Pays S f C) (hd : 0 ≤ D)
    (he : ∀ i,P.price S i*‖g i‖ ≤ D*(P.price S (e i)*‖f (e i)‖)) : P.Pays S g (D*C) := by
  refine ⟨mul_nonneg hd h.1, fun ht i => (he i).trans ((mul_le_mul_of_nonneg_left (h.2.1 ht _) hd).trans_eq (mul_assoc ..).symm),
    fun ht => (rless (fun i => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)) he).trans ?_⟩
  let x (i : α) := P.price S i*‖f i‖
  change (rlen fun i => D * ((x ∘ e) i)) ≤ _
  rw [show rlen _=D*rlen (x ∘ e) from rconstant hd _,rperm]
  exact (mul_le_mul_of_nonneg_left (h.2.2 ht) hd).trans_eq (by ring)
lemma Pays.plus {v : α→X} (h : P.Pays S f C) (hp : P.Pays S v D) : P.Pays S (f+v) (C+D) := by
  have hh i : P.price S i*‖(f+v) i‖ ≤ P.price S i*‖f i‖+P.price S i*‖v i‖ := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (P.price_pos _ _).le
  refine ⟨add_nonneg h.1 hp.1,fun he i => (hh i).trans ((add_le_add (h.2.1 he i) (hp.2.1 he i)).trans_eq (add_mul ..).symm),fun he => ?_⟩
  exact (rtriangle (fun i => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)) hh).trans
    ((add_le_add (h.2.2 he) (hp.2.2 he)).trans_eq (by ring))
lemma Pays.zero (h : 0 ≤ C) : P.Pays S (0 : α→X) C := ⟨h,fun _ i => by simpa using mul_nonneg h (P.target_pos S),fun _ => by
  simpa [rlen,show (fun _ : α => (0:ℝ))=0 from rfl] using mul_nonneg (mul_nonneg P.rooted h) (P.target_pos S)⟩
lemma Pays.blank (h : 0 ≤ C) (he : ∀ i, ‖f i‖ ≤ C) : P.Pays ∅ f C := by
  refine ⟨h,fun _ i => ?_,fun ⟨_,hx,_⟩ => ?_⟩
  · simpa [price,target] using he i
  simp at hx
lemma Pays.gather {κ : Type*} {f : κ→α→X} (q : Finset κ) (E : κ→ℝ) (h : ∀ i∈ q, P.Pays S (f i) (E i)) : P.Pays S (∑ i∈q,f i) (∑ i∈q,E i) := by
  classical
  induction q using Finset.induction_on with
  | empty => simpa using (show P.Pays S (0:α→X) 0 from Pays.zero le_rfl)
  | @insert i q hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun i he => h _ (Finset.mem_insert_of_mem he))
lemma Pays.limits {κ : Type*} {l : Filter κ} [l.NeBot] {F : κ→α→X} {c : κ→ℝ} (h : ∀ i, P.Pays S (F i) (c i))
    (he : Tendsto c l (𝓝 C)) (hc : ∀ i, Tendsto (fun j => F j i) l (𝓝 (f i))) : P.Pays S f C := by
  have hv i : Tendsto (fun j => P.price S i * ‖F j i‖) l (𝓝 (P.price S i * ‖f i‖)) := (hc i).norm.const_mul _
  refine ⟨ge_of_tendsto he (Eventually.of_forall fun i => (h i).1),fun ht i =>
    le_of_tendsto_of_tendsto' (hv i) (he.mul_const _) (fun j => ((h j).2.1 ht i)),fun ht => ?_⟩
  exact le_of_tendsto_of_tendsto' (rlimit hv) ((he.const_mul P.cap).mul_const _) (fun j => (h j).2.2 ht)
lemma Pays.tsum {κ : Type*} {f : κ→α→X} {E : κ→ℝ} (h : ∀ i, P.Pays S (f i) (E i)) (he : Summable E)
    (ht : ∀ i : α, Summable (fun j : κ => f j i)) : P.Pays S (fun i => ∑' j, f j i) (∑' i,E i) := by
  apply Pays.limits (fun q : Finset κ => Pays.gather q E fun i _ => h i) he.hasSum
  intro i; simp_rw [Finset.sum_apply]; exact (ht i).hasSum

variable {z : α→Z} [DecidableEq ι]
lemma Pays.times (h : P.Pays S f C) (hp : P.Pays T g D) (ht : Disjoint S T) (hu : ∀ i, ‖z i‖ ≤ ‖f i‖*‖g i‖) : P.Pays (S∪T) z (C*D) := by
  have hh : P.target (S∪T)=P.target S * P.target T := Finset.prod_union ht
  let a i := P.price S i*‖f i‖; let b i := P.price T i*‖g i‖
  have ha i : P.price (S∪T) i*‖z i‖ ≤ a i*b i := by
    exact (mul_le_mul_of_nonneg_left (hu i) (P.price_pos _ _).le).trans_eq (by unfold a b price; rw [Finset.prod_union ht]; ring)
  have hr : P.tagged (S∪T) ↔ P.tagged S ∨ P.tagged T := by simp only [tagged, Finset.mem_union]; grind
  refine ⟨mul_nonneg h.1 hp.1,?_,?_⟩
  · intro e i; rw [hh];
    exact (ha i).trans ((mul_le_mul (h.2.1 (fun x => e (hr.mpr (Or.inl x))) i) (hp.2.1 (fun x => e (hr.mpr (Or.inr x))) i)
      (mul_nonneg (P.price_pos _ _).le (norm_nonneg _)) (mul_nonneg h.1 (P.target_pos _))).trans_eq (by ring))
  have hd (i : α) : 0 ≤ P.price (S∪T) i* ‖z i‖ := mul_nonneg (P.price_pos _ _).le (norm_nonneg _)
  have he : P.tagged S → ¬ P.tagged T := by
    rintro ⟨i,hi,he⟩ ⟨j,hj,hv⟩
    rw [Option.some.inj (he.symm.trans hv)] at hi; exact Finset.disjoint_left.mp ht hi hj
  intro H; rw [hh]
  rcases hr.mp H with H|H
  · have hx := (rless hd (fun i => (ha i).trans ((mul_le_mul_of_nonneg_left (hp.2.1 (he H) i)
      (mul_nonneg (P.price_pos _ _).le (norm_nonneg _))).trans_eq (mul_comm ..))))
    rw [show rlen _ = _ from rconstant (mul_nonneg hp.1 (P.target_pos T)) a] at hx
    exact hx.trans ((mul_le_mul_of_nonneg_left (h.2.2 H) (mul_nonneg hp.1 (P.target_pos _))).trans_eq (by ring))
  have hx := rless hd (fun i => (ha i).trans (mul_le_mul_of_nonneg_right (h.2.1 (fun x => he x H) i) (mul_nonneg (P.price_pos _ _).le (norm_nonneg _))))
  rw [show rlen _ = _ from rconstant (mul_nonneg h.1 (P.target_pos S)) b] at hx
  exact hx.trans ((mul_le_mul_of_nonneg_left (hp.2.2 H) (mul_nonneg h.1 (P.target_pos _))).trans_eq (by ring))

lemma Pays.prod (v : ι→α→ℝ) (E : ι→ℝ) (S : Finset ι) (h : ∀ i∈S, P.Pays {i} (v i) (E i)) : P.Pays S (fun x => ∏ i∈S,v i x) (∏ i∈S,E i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Pays.blank (by norm_num) fun _ => norm_one.le
  | insert i S hi ih =>
    simp_rw [Finset.prod_insert hi,Finset.insert_eq]; apply Pays.times (h i (by simp)) (ih (fun i he => h i (Finset.mem_insert_of_mem he))) (Finset.disjoint_singleton_left.mpr hi)
    intro i; exact norm_mul_le ..
end Purse
end YM.AnalyticNext.QuarticMatch.Estimate
