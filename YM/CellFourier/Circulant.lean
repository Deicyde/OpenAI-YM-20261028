import YM.CellFourier.Alias

/-!
# Momentum to translation matrices

Entrywise ℝ coefficient kernels. Readers need absolute size receipts.
Sign convolution `K(x,y)=F[y-x]`; for cross kernels call this on the
coarse sites with residues as extra types. All these equalities are for
true periodic arithmetic, no a.e. or `p≠0` division. Note block density
still needs actual transported rather than flat kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bloch
open Lattice Laurent Matrix Function Filter Set Complex
open scoped Topology BigOperators ComplexConjugate ContDiff Matrix.Norms.Frobenius
variable {L : Side} {α β γ : Type*}

/-- entry size budgets used both when one extra color and when cross
kernel residue type. `band` charged per fixed types (some costs can't be
summed over both types at pre-L orders). -/
abbrev Row (α β : Type*) := α → β → Cover → ℝ

namespace Row

def strip (R : Row α β) (η A : ℝ) : Prop := ∀ i j,Laurent.Width η A (R i j)
def safe (R : Row α β) : Prop := ∀ i j, Summable fun x => ‖R i j x‖
lemma rights {R : Row α β} (η A) (h : strip R η A) (he : 0 ≤ η) : safe R := fun i j => ((h i j).unweighted he).2.1

def read (R : Row α β) (p : Momentum) : Matrix α β ℂ :=
    of fun i j => Laurent.read (fun x => ((R i j x):ℂ)) p

def acts (R : Row α β) (n : Side) : Matrix (Site n × α) (Site n × β) ℝ := of fun i j =>
    ∑' x, if j.1 = i.1 + wrap n x then R i.2 j.2 x else 0

lemma constant_strip (R : Row α β) {η A : ℝ} (h : strip R η A) (x : α) (y : β) : Laurent.Width η A (fun i => (R x y i:ℂ)) := by
  simpa only [Laurent.Width,norm_real] using h x y

lemma conjugate (R : Row α β) (p : Momentum) : (read R (-star p)) = (read R p).map star := by
  ext i j
  simp only [read,Matrix.of_apply,Laurent.read,Matrix.map_apply,tsum_star]
  refine tsum_congr fun b => ?_
  have hk := mode_adjoint (star p) b
  rw [star_star,mode_opposite,← mode_inverse] at hk
  simp only [smul_eq_mul,star_mul, hk]; rw [Complex.star_def,conj_ofReal,mul_comm]

/-- No norm hypothesis because reading reciprocal modes termwise.
Still require receipts for arithmetic uses. -/
lemma periods (R : Row α β) (p : Momentum) (x : Cover) : read R (p+reciprocal x)=read R p := by
  ext i j; apply Laurent.periodic
end Row

/-- physical DFT assembly of circ matrix. -/
def approached (A : Matrix α β ℝ) : Matrix α β ℂ := A.map (↑)

/-- promote commutes with products and adjoints. -/
@[simp] lemma prom_mul [Fintype β] (A : Matrix α β ℝ) (B : Matrix β γ ℝ) : approached (A*B)=approached A*approached B := by ext i j; simp [approached, Matrix.mul_apply]

@[simp] lemma prom_adj (A : Matrix α β ℝ) : approached A.transpose = (approached A).conjTranspose := by ext i j; simp [approached]
lemma prom_inj : Injective (approached (α:=α) (β:=β)) := fun _ _ h ↦ by ext i j; exact ofReal_injective (congr_fun (congr_fun h i) j)

/-- domain residue types represented as all rows over p. -/
def rotations (L : Side) (α : Type*) [DecidableEq α] : Matrix (Site L × α) (Site L × α) ℂ :=
    of fun i j => if i.2=j.2 then cell j.1 i.1 else 0

def fiber [DecidableEq (Site L)] (P : Site L → Matrix α β ℂ) : Matrix (Site L × α) (Site L × β) ℂ :=
    of fun i j => if i.1=j.1 then P i.1 i.2 j.2 else 0

-- Don't use extra decidable eq instance on Site L in statements; default
lemma rotations_gram (L : Side) (α : Type*) [DecidableEq α] [Fintype α] :
    rotations L α * star (rotations L α)=(L.val:ℂ)^4 • 1 := by
  rw [show rotations L α = aliasBlock L α 0 from ?_]
  · simpa only [returned,star_zero,Matrix.star_eq_conjTranspose] using straighten' L α 0
  ext ⟨x,i⟩ ⟨y,j⟩
  simp only [rotations,aliasBlock, of_apply,alias_comp,smul_zero,mode_constant,one_mul]

lemma cancel_rotation (L : Side) [DecidableEq α] [Fintype α] (X Y : Matrix β (Site L × α) ℂ)
    (h : X*rotations L α=Y*rotations L α) : X=Y := by
  have e := congr_arg (·*star (rotations L α)) h
  simp only [Matrix.mul_assoc,rotations_gram, Matrix.mul_smul, Matrix.mul_one] at e
  exact smul_right_injective _ (pow_ne_zero _ (side_ne L)) e

lemma rot_fiber (L : Side) (P : Site L → Matrix α β ℂ) [DecidableEq α] [Fintype α] (x p : Site L) (i : α) (j : β) :
    (rotations L α*fiber P) (x,i) (p,j)=cell p x * P p i j := by
  rw [mul_apply,Fintype.sum_prod_type]
  simp [rotations,fiber, ite_mul,mul_ite]

lemma circulant (L : Side) (R : Row α β) [DecidableEq α] [DecidableEq β] [Fintype β] [Fintype α]
    (h : R.safe) : approached (R.acts L) * rotations L β=rotations L α*fiber (fun p => R.read (mon p)) := by
  ext ⟨x,i⟩ ⟨p,j⟩
  rw [rot_fiber,mul_apply,Fintype.sum_prod_type]
  simp only [Row.acts,Row.read, rotations, approached, Matrix.map_apply, Matrix.of_apply]
  simp_rw [mul_ite,mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,Laurent.read]
  have hs (y : Site L) : Summable fun a => (if y = x+wrap L a then R i j a else 0) := by
    have H := (h i j).of_norm.indicator {a | y=x+wrap L a}
    exact H.congr (fun z => by simp [indicator])
  have ht (y : Site L) : Summable fun a => ((if y = x+wrap L a then R i j a else 0 : ℝ) : ℂ)*cell p y := ((Complex.ofRealCLM.summable (hs y))).mul_right _
  simp_rw [ofReal_tsum,← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (f:=fun y a => ((if y = x+wrap L a then R i j a else 0 : ℝ) : ℂ)*cell p y),← tsum_mul_left]
  · refine tsum_congr fun a => ?_
    simp_rw [apply_ite ((↑):ℝ→ℂ),ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      cell_add,cell_wrap,smul_eq_mul]
    ring
  exact fun i _ => ht i
end YM.Bloch
