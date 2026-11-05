import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import YM.MultiNext.VACUUM_STABILITY.Gaussian.Laplace

/-!
# Local probe class for the recursion

Native real derivatives on Lie coordinates in the supplied covariance.
Require actual *ordered* derivatives only through the given order and
nonasymptotic bounds on all real coordinates. At an intermediate stage,
when only a projected-support chart is allowed, first supply a regular
formula on these arguments (possibly with a smooth profile attached, NOT
transport of any hard reads). We never replace the covariance here when
a support is extended. Constants and repetition are unexceptional in
these definitions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Filter Finset Function Set
open YM.Multi.Vacuum.Gauss
open scoped Topology BigOperators

variable {V I J : Type} [Fintype I] [Fintype J]
abbrev Probes (V I : Type) := V → Row I → ℂ
abbrev Rows (V I J : Type) := V → I → Row J

variable [DecidableEq I]
namespace Probe

def basis (a : I) : Row I := Pi.single a 1
lemma basis_expand (x : Row I) : x = ∑ a,x a • basis a := by funext i; simp [Finset.sum_apply,basis,Pi.single_apply]

def hit (f : Row I → ℂ) (a : I) (x : Row I) := fderiv ℝ f x (basis a)

lemma all_axes (f : Row I → ℂ) (x y : Row I) : fderiv ℝ f x y=∑ i, y i • hit f i x := by
  conv_lhs => rhs; rw [basis_expand y]
  rw [map_sum]; apply sum_congr rfl; intro i _
  rw [map_smul]; rfl

def jet (f : Row I → ℂ) : List I → Row I → ℂ
  | [] => f
  | a::l => hit (jet f l) a
omit [Fintype I] in
lemma jet_hit (f : Row I → ℂ) (a : I) (l : List I) : jet (hit f a) l=jet f (l++[a]) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [jet,List.cons_append]; rw [ih]

def Reads (U : Finset I) (f : Row I → ℂ) := ∀ {x y : Row I}, (∀ i∈U,x i=y i) → f x=f y

lemma Reads.hits {U : Finset I} {f : Row I → ℂ} (h : Reads U f) (hd : Differentiable ℝ f) (a : I) :
    Reads U (hit f a) := by
  intro x y he
  have hb : (fun t : ℝ => f (x+t • basis a))=fun t : ℝ => f (y+t • basis a) := by
    funext t; apply h; intro i hi; simp [he i hi]
  have ht (x : Row I) : HasDerivAt (fun t : ℝ => f (x+t • basis a)) (hit f a x) 0 :=
    (hd x).hasFDerivAt.hasLineDerivAt (basis a)
  exact (hb ▸ ht x : HasDerivAt (fun t : ℝ => f (y+t • basis a)) (hit f a x) 0).unique (ht y)

lemma Reads.outside {U : Finset I} {f : Row I → ℂ} (h : Reads U f) (hd : Differentiable ℝ f) (a : I)
    (ha : a ∉ U) : hit f a=0 := by
  funext x
  have he : (fun t : ℝ => f (x+t • basis a))=fun _ : ℝ => f x := by
    funext t; apply h; intro i hi
    have ht : i≠a := fun h => ha (h ▸ hi)
    simp [basis,ht]
  have ht (x : Row I) : HasDerivAt (fun t : ℝ => f (x+t • basis a)) (hit f a x) 0 :=
    (hd x).hasFDerivAt.hasLineDerivAt (basis a)
  exact (ht x).unique (he.symm ▸ hasDerivAt_const 0 _)

/-- Data for one numerical test. Support is separate (may enlarge for
physical sites/paths/histories even if the value only needs fewer coordinates).
`pay w` carries possible shared-coordinate weights for integration. -/
structure Costs (n : ℕ) (f : Row I → ℂ) (w : Row I) (H : ℕ → ℝ) : Prop where
  fees k : 0 ≤ H k
  charm (l : List I) (hl : l.length ≤ n) : Continuous (jet f l)
  fires (l : List I) (hl : l.length < n) : Differentiable ℝ (jet f l)
  price (l : List I) (hl : l.length ≤ n) (x : Row I) : ‖jet f l x‖ ≤ H l.length * Real.exp (pay w x)

lemma Costs.minus {n m : ℕ} {f : Row I → ℂ} {w H} (h : Costs n f w H) (hm : m ≤ n) :
    Costs m f w H := ⟨h.fees,fun l hl => h.charm l (hl.trans hm),fun l hl => h.fires l (hl.trans_le hm),
      fun l hl => h.price l (hl.trans hm)⟩

lemma Costs.slice {n : ℕ} {f : Row I → ℂ} {w H} (h : Costs (n+1) f w H) (a : I) :
    Costs n (hit f a) w (fun i => H (i+1)) := by
  refine ⟨fun k => h.fees (k+1),fun l hl => ?_,fun l hl => ?_,fun l hl => ?_⟩
  · rw [jet_hit]; exact h.charm _ (by simp [hl])
  · rw [jet_hit]; exact h.fires _ (by simp [hl])
  rw [jet_hit]
  simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using h.price (l++[a]) (by simp [hl])

section
variable [DecidableEq V]

/-- Mark a particular occurrence i for a particular counting derivative a.
Cost shift below pays just on this occurrence i (charging two hits in the
transfer of bounds used below). -/
def marked (v : Probes V I) (i : V) (a : I) := update v i (hit (v i) a)

def bill (H : V → ℕ → ℝ) (i : V) := update H i (fun k => H i (k+1))

structure Valid (s : Finset V) (n : ℕ) (v : Probes V I) (w : V → Row I) (H : V → ℕ → ℝ) : Prop where
  guard i (hi : i ∈ s) : Costs n (v i) (w i) (H i)
end
section valid
variable {v : Probes V I} {w : V → Row I} {H : V → ℕ → ℝ} {s : Finset V} {n m : ℕ}

lemma Valid.lower (h : Valid s n v w H) (hm : m ≤ n) : Valid s m v w H :=
    ⟨fun i hi => (h.guard i hi).minus hm⟩

lemma Valid.read (h : Valid s n v w H) (i : V) (hi : i∈s) : Continuous (v i) := (h.guard i hi).charm [] (by simp)
lemma Valid.look (h : Valid s n v w H) (hn : 0<n) (i : V) (hi : i∈s) : Differentiable ℝ (v i) :=
  (h.guard i hi).fires [] hn
lemma Valid.pay (h : Valid s n v w H) (i : V) (hi : i∈s) (x : Row I) : ‖v i x‖ ≤ H i 0*Real.exp (pay (w i) x) :=
  (h.guard i hi).price [] (by simp) x

variable [DecidableEq V]
lemma Valid.mark (h : Valid s (n+1) v w H) (i : V) (a : I) : Valid s n (marked v i a) w (bill H i) := by
  constructor; intro x hx
  by_cases he : x=i
  · subst x; rw [bill,marked,update_self,update_self]; exact (h.guard i hx).slice a
  simp only [marked,bill,update_of_ne he]; exact (h.guard x hx).minus n.le_succ

/-- distinct ends, hence only one derivative order needed per vertex.
May charge valence factorial later. -/
lemma Valid.double (h : Valid s (n+1) v w H) {i j : V} (he : i≠j) (a b : I) :
    Valid s n (marked (marked v i a) j b) w (bill (bill H i) j) := by
  constructor; intro x hx
  by_cases ht : x=j
  · subst x; simp only [marked,bill,update_self,update_of_ne he.symm]; exact (h.guard j hx).slice b
  simp only [marked,bill,update_of_ne ht]; exact (h.mark i a).guard x hx
end valid
end Probe
end YM.Primitives.GCC
