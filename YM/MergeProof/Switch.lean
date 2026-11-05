import Mathlib.Analysis.Normed.Group.Tannery
import YM.Marker.Console

/-!
# Switching sources

Real sector-sum lemmas in this workplace used at nilpotent weights, via
switching. For finite index set I, g∈ Array gives values of a polynomial
xᵢ²=t*xᵢ at every tuple of 0/t's. Arrays determine and are determined by these
values at t>0. To use multilinear history terms (t=0) we always check weighted
budgets independent of t and continuity. Value solves scalar tests at every
point, not dividing by a density. In particular root prices will carry a sum
over coefficient costs already before summing over lattice fields. Inspired
by Lotus/Curtail differentiating real series for one mark.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open Function Set Finset Filter
open scoped Topology BigOperators Classical
variable {ι U A : Type} [Fintype ι]

abbrev Score (ι : Type) := Finset ι → ℝ
abbrev Ways (ι : Type) := ℝ → Score ι

def value (x : ℝ) (g : Score ι) (r : Finset ι) := ∑ i∈r.powerset,x^i.card*g i

attribute [local instance] Classical.propDecidable

local notation "α" => 𝓝[>] (0:ℝ)
lemma approached : ∀ᶠ x in α, 0<x ∧ x ≤ 1 := inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ge_mem_nhds zero_lt_one))

omit [Fintype ι] in
lemma entire {x:ℝ} (hx : 0<x) : Injective (value (ι:=ι) x) := by
  intro g h he; funext p
  induction p using Finset.strongInductionOn with
  | _ p ih =>
    have h₁:=congr_fun he p; have h₂ : ∀ u∈ (p.powerset.erase p),g u=h u:= fun u hu=> ih u (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_of_mem_erase hu),ne_of_mem_erase hu⟩)
    unfold value at h₁
    have hz : p∈p.powerset:=mem_powerset.mpr (Finset.Subset.refl p)
    rw [← add_sum_erase _ _ hz,← add_sum_erase _ (fun i : Finset ι=>x^i.card*h i) hz] at h₁
    exact mul_left_cancel₀ (pow_pos hx _|>.ne') (add_right_cancel (show _ from h₁.trans (congr_arg (_+·) (sum_congr rfl fun i hi=>congr_arg (_*·) (h₂ i hi|>.symm)))))

def decode (f : Ways ι) (x : ℝ) := Function.invFun (value (ι:=ι) x) (f x)

def jet (f : Ways ι) (v: Finset ι) : ℝ:= limUnder α fun x=>decode f x v

structure Models (f : Ways ι) (g : Ways ι) : Prop where
  current (x:ℝ) (hx : x∈Set.Icc (0:ℝ) 1): value x (g x)= f x
  converge (v): Tendsto (fun x=>g x v) α (𝓝 (g 0 v))

def high (b : Score ι):=∑ i,b i

def Bounded (g : Ways ι)(b : Score ι):=∀ x∈Set.Icc (0:ℝ) 1,∀ i, ‖g x i‖ ≤ b i

def Paid (f : U → Ways ι) (c : ℝ) := ∃ b : Score ι,(∀ i, 0≤b i) ∧ high b≤ c ∧ ∀ u,∃ g : Ways ι, Models (f u) g ∧ Bounded g b

omit [Fintype ι] in
lemma Models.exact {f g : Ways ι}(H : Models f g): jet f=g 0:=funext fun i=> by
  unfold jet
  have he : (fun x=>g x i)=ᶠ[α] fun x=>decode f x i := approached.mono fun x hx=> by
    unfold decode; dsimp only; rw [← H.current x ⟨hx.1.le,hx.2⟩,leftInverse_invFun (entire hx.1)]
  exact ((H.converge i).congr' he).limUnder_eq

variable {f g : U→ Ways ι} {a b : ℝ}

lemma Paid.rocket (h : Paid f a):0≤a:=le_trans (sum_nonneg fun i _=>h.choose_spec.1 i) h.choose_spec.2.1
lemma Paid.weaken (h : Paid f a)(he:a≤b) : Paid f b:=
  ⟨_,h.choose_spec.1,h.choose_spec.2.1.trans he,h.choose_spec.2.2⟩



lemma box {x : ℝ}(hx:x∈ Icc (0:ℝ) 1) {b p : Score ι} (h:∀ i,‖p i‖ ≤ b i)(r:Finset ι) : ‖value x p r‖≤ high b:=by
  apply (norm_sum_le ..).trans
  refine le_trans (b:=∑ i∈r.powerset,b i) ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>(norm_nonneg _).trans (h i))
  apply sum_le_sum; intro i _; rw [norm_mul,norm_pow,Real.norm_of_nonneg hx.1]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hx.1 hx.2)).trans (h i)
lemma Paid.tasting (h : Paid f a)(u:U)(x : ℝ)(hx:x∈ Icc (0:ℝ) 1)(r : Finset ι) : ‖f u x r‖ ≤ a:=by
  obtain ⟨b,hH,hB,h⟩:=h; obtain ⟨g,h,hg⟩:= h u
  rw [← h.current x hx]; exact (box hx (hg x hx) r).trans hB

lemma value_subset (x : ℝ)(p : Score ι) (r : Finset ι) : value x p r=∑ i,if i⊆r then x^i.card*p i else 0:=by rw [← Finset.sum_filter]; unfold value; congr; ext; simp

omit [Fintype ι] in
lemma Models.add {f g f' g':Ways ι}(h:Models f f')(he:Models g g'): Models (f+g) (f'+g'):=by
  constructor
  · intro x hx; change value x (f' x+g' x)= f x+g x; rw [← h.current x hx,← he.current x hx]; ext i; simp only [value,Pi.add_apply,mul_add, Finset.sum_add_distrib]
  intro v; exact (h.converge v).add (he.converge v)
lemma Paid.add (h:Paid f a)(he:Paid g b) : Paid (f+g) (a+b):=by
  obtain ⟨A,hA,h,H⟩:=h; obtain ⟨B,hB,h',H'⟩:=he
  refine ⟨A+B,fun i=> add_nonneg (hA i) (hB i),?_,fun u=>?_⟩
  · unfold high; simp only [Pi.add_apply,sum_add_distrib]; exact add_le_add h h'
  obtain ⟨g,h,k⟩:= H u; obtain ⟨g',h',k'⟩:= H' u
  exact ⟨g+g',h.add h',fun x hx i =>(norm_add_le _ _).trans (add_le_add (k x hx i) (k' x hx i))⟩

-- literal unit / monomial placements

def click (i:Finset ι)(c : ℝ)(x : ℝ): Score ι:=fun v=> if i⊆v then x^i.card*c else 0
def bench (i:Finset ι)(c : ℝ): Score ι:=fun v=> if v=i then c else 0
omit [Fintype ι] in
lemma modelClick (i:Finset ι)(c : ℝ) : Models (click i c) (fun _=>bench i c) :=by
  refine ⟨fun x _=> funext fun v=> ?_,fun _=>tendsto_const_nhds⟩
  unfold value click bench; split
  next h=>
    rw [sum_eq_single i]; · simp
    · intro b _ h; simp [h]
    exact fun H=>False.elim (H (mem_powerset.mpr h))
  next h=> apply Finset.sum_eq_zero; intro j hj; rw [if_neg (show j≠i from fun he=>h (he ▸ mem_powerset.mp hj)),mul_zero]
lemma paidClick (i:Finset ι){p:U→ℝ}{b:ℝ}(h:0≤b)(he:∀ u, ‖p u‖ ≤ b) : Paid (fun u=>click i (p u)) b:= by
  refine ⟨bench i b,fun j=>?_,?_,fun u=>⟨_,modelClick i _,?_⟩⟩
  · unfold bench; split; exact h; rfl
  · simp only [high,bench,Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte]; rfl
  intro x hx j; unfold bench; dsimp only;  split; exact he u; rw [norm_zero]
lemma constant (p : U→ℝ)(h:0≤a)(hp:∀ u,‖p u‖≤a) : Paid (ι:=ι) (fun u _ _=>p u) a := by
  convert! paidClick (∅:Finset ι) h hp using 1; ext; simp [click]
lemma paidZero : Paid (0 : U→Ways ι) 0:= constant (p:=fun _=>0) le_rfl (fun _=>(norm_zero (E:=ℝ)).le) -- maybe
lemma Paid.sum (u : Finset A)(g:A→U→ Ways ι)(a:A→ℝ) (h:∀ i∈u,Paid (g i) (a i)): Paid (∑ i∈u,g i) (∑ i∈u,a i) := by
  induction u using Finset.induction with
  | empty => simp only [sum_empty]; exact paidZero
  | insert i u hi ih=> rw [sum_insert hi,sum_insert hi]; exact Paid.add (h _ (mem_insert_self ..)) (ih fun i h' => h i (mem_insert_of_mem h'))
end YM.Merge.Switch
