import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Progress

set_option warningAsError false

/-! # Repair any finite list or compatible presentation port

Uniform proof, paid by aggregate per tag, not the sum over all tags at
any single hook. Missing slots still not guaranteed. This port reuses
exact algebra and keeps the vacuum *in place*. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open RG Marker Wilson Lattice Multi Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {G : Gauge} {n : Side} (P : Rep G n) (X : V→Support n)

structure Attempt (G : Gauge) (n : Side) (V : Type) where
  tag : V
  pack : Pack n
  includeSite : Site n
  value : Config G n → ℂ
  price : ℝ

namespace Attempt
variable (A : Attempt G n V) {Y : Rep G n}

def eligible (δ κ μ : ℝ) := Costed P A.pack A.includeSite A.value δ κ μ A.price (X A.tag)

def effect (x : V) : Pulse G n := if x=A.tag then nullPay P A.pack A.includeSite A.value else 0
def asks (x : V) : ℝ := if x=A.tag then A.price else 0
variable {κ δ μ : ℝ}
omit [Fintype V] in
lemma nonneg (h : A.eligible P X δ κ μ) (i : V) : 0 ≤ A.asks i := by
  obtain ⟨a,ha,_,he⟩ := h.stowed
  unfold asks; split
  · apply le_trans ?_ he
    exact mul_nonneg (add_nonneg (by norm_num) h.vacuum) (div_nonneg (mul_nonneg (burn_pos ..).le ha) h.κpos.le)
  exact le_rfl
end Attempt

variable (A : Attempt G n V) (L : List (Attempt G n V)) (D : Hot R → Pulse G n)

def debt (i : V) : ℝ := (L.map (·.asks i)).sum
def acts (i : V) : Pulse G n := (L.map (·.effect P i)).sum

def changed : Hot R → Pulse G n :=
    L.foldr (fun a y => edited P a.tag y a.pack a.includeSite a.value) D

lemma changed_many : Multi.many P R (changed P L D)= many P R D := by
  induction L with
  | nil => rfl
  | cons a l h => exact (edited_many ..).trans h

omit [Fintype V] in
lemma edited_each (i : V) : edited P A.tag D A.pack A.includeSite A.value (Hot.one R i)=D (Hot.one R i)+A.effect P i := by
  unfold Attempt.effect; by_cases he : i=A.tag
  · subst i; rw [if_pos rfl,edited_at]
  rw [if_neg he, dormant P A.tag _ _ _ _ _ (show A.tag ∉ ({i}:Finset V) by simp [Ne.symm he]), add_zero]

omit [Fintype V] in
lemma changed_one (i : V) : changed P L D (Hot.one R i)=D (Hot.one R i)+acts P L i := by
  induction L with
  | nil => exact (add_zero _).symm
  | cons a l h =>
    rw [show changed P (a::l) D=edited P a.tag (changed P l D) a.pack a.includeSite a.value from rfl] -- need exact args
    rw [edited_each,h,add_assoc]
    exact congr_arg (_+·) (by simp [acts,add_comm])

variable {σ ρ χ ξ μ δ κ μ' : ℝ}
omit [Fintype V] in
theorem changed_credit (hc : ∀ i,(X i).Nonempty) (hv : P.Lawful σ ρ χ ξ μ) (ht : Mint P δ μ') (he : ∀ a∈L,Attempt.eligible P X a δ κ μ')
    (k : V → ℝ) (_hk : ∀ i,0<k i) (hD : ∀ i,Multi.Credit P.p δ κ (covers X i) (D i) (Poly.toll k i.val)) :
    ∀ i, Multi.Credit P.p δ κ (covers X i) (changed P L D i) (Poly.toll (k+debt L) i.val) := by
  induction L with
  | nil => intro i; rw [show k+debt [] = k by ext; simp [debt]]; exact hD _
  | cons x l hx =>
    have hl : ∀ a∈l,a.eligible P X δ κ μ' := fun _ h => he _ (List.mem_cons_of_mem _ h)
    have hh := hx hl
    let g := k+debt l
    rw [show changed P (x::l) D=edited P x.tag (changed P l D) x.pack x.includeSite x.value from rfl]
    rw [show k+debt (x::l)=advance x.tag g (w:=x.price) by ext j; by_cases h : j=x.tag <;> simp [g,advance,debt,h,Attempt.asks] ; ring]
    exact edit_prices P X x.tag (changed P l D) x.pack x.includeSite x.value g hh hc hv ht (he x (List.mem_cons_self ..))
end YM.AnalyticNext.GridStop.Alphabet
