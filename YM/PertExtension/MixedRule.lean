import YM.PertExtension.BarePrescription

/-!
# Bare orbifold top rule on products across different lexical horizons

The basis input at each mark uses its own engineering filtration normalization
and top symbol matrix inverse, before any formal position solve. Doesn't
prove UV convergence or the appropriate identification of these entries with
on-shell labels as the cutoff is removed. Fixed-regulator expansion includes
the ordinary (moment) expectation, the common whole denominator as in
preExpectation, and the same separated mark offsets throughout. We sum over
the finite native lattice (so profiles with fixed physical compact support
can be used on fine meshes).
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace YM.PertExtension.LatticePT
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory RG Labels Source
open scoped Topology ContDiff Classical BigOperators
open Chart Series Series.Tested Orb Orb.SlotEvaluation

variable {G : Gauge}

/-- One physical bare insertion choice of pure degree, prior to position
mixing. -/
structure Word (G : Gauge) where
  d : ℕ
  F : Labels.Frame G d
  S : SectionData F
  H : Hol G
  sound : S.Sound H
  chosen : Bid.pop S
  axis : F.Index
  weight : (F.grades axis).1=d

def Word.cost (w:Word G)(j:w.F.Index)(ε : ℝ) := ε^4/ε^w.d * topBasis w.S w.H w.sound w.chosen w.axis j

namespace Mixed
variable {I : Type*}[Fintype I] (w : I→Word G)

abbrev Task := (i:I)→(w i).F.Index
-- expansion of lexical Laurent columns before position-frame transformations
def number (t : Task w) := ∑ i, ((w i).F.grades (t i)).2
def product {n : Side}(s:Finset I)(t : Task w)(x:I→Site n)(ε : ℝ)(u : Config G n) := ∏ i∈s,(w i).cost (t i) ε * fieldAt (w i).S (t i) (x i) u

open Series.Radial
lemma product_good {n : Side}(t : Task w)(x : I → Site n) (ε) :
  let O := product w Finset.univ t x ε
  PreTest O ∧ RadialOrder (number w t) ((restrictedO O) ∘ expLinks G (Cotree n)) := by
  intro O
  let f (i:I):= fieldAt (w i).S (t i) (x i)
  let g :Dir G n→Config G n:=representative
  let ρ (i:I) := (w i).cost (t i) ε
  have H i := pre_field (w i).S (w i).sound (w i).chosen (t i) (x i)
  have hc : Continuous O := continuous_finsetProd _ (fun i _=> continuous_const.mul ((H i).1.continuous))
  have hd : ContDiffAt ℝ ∞ ((restrictedO O)∘ expLinks G (Cotree n)) 0:= by
    convert! contDiffAt_prod (t:=Finset.univ (α:=I)) (f:=fun i x=>ρ i*f i (g x)) (fun i _=>contDiffAt_const.mul ((H i).1.curved.germ))
  refine ⟨⟨?_,⟨hc.comp continuous_links,hd⟩,hc⟩,?_⟩
  · intro u hu v; unfold O product; exact Finset.prod_congr rfl fun i _=> congr_arg _ ((H i).1.gauge u hu v)
  intro A; have he:= bill_product Finset.univ (fun i:I=>((w i).F.grades (t i)).2) (fun i (r:ℝ)=>ρ i*f i (g (r • A))) <|
    fun j _=>by simpa only [Nat.zero_add] using! bill_mul (bill_const (ρ j)) ((H j).2 A)
  convert! he using 1;funext _; simp only [Finset.prod_apply]; rfl

lemma product_finite {n : Side}(t:Task w)(x : I→Site n)(ε)(h : Even n.val) :
  let O := product w Finset.univ t x ε
  Aspiration (fun r=> (r⁻¹)^number w t * preExpectation O r)
     (fun j=> diagonalWith (tray G) (restrictedO O) (number w t+j)) := by
   intro O; obtain ⟨hP,hd⟩:=product_good w t x ε
   exact (before_tree_formula h (traySpec G) hP).shift (diag_down (traySpec G) hP.curved hd h)

variable (q : ℕ+)(m : ℕ)
variable (Ψ : (I→E4)→ℝ)
def placements (o : Native q m) (x : I→Native q m) (t:Task w) := product w Finset.univ t (fun i=>x i+o) (epsilon q m)
def price (x : I→Native q m) := ((origins q m).card:ℝ)⁻¹ * Ψ (point q m ∘ x)
def realTop (r:ℝ) := ∑ x:I→Native q m,∑ o∈origins q m,∑ t:Task w,price q m Ψ x * ((r⁻¹)^number w t * preExpectation (placements w q m o x t) r)
def polynomialTop (j:ℕ):=∑ x:I→Native q m,∑ o∈origins q m,∑ t:Task w,price q m Ψ x * diagonalWith (tray G) (restrictedO (placements w q m o x t)) (number w t+j)
private lemma scale_price (φ : ℝ→ℝ)(a : ℕ→ℝ)(c : ℝ)(h : Aspiration φ a) :Aspiration (c • φ) (c • a) := by
  intro j;obtain ⟨A,hA,H⟩:=h j
  refine ⟨‖c‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  filter_upwards [H] with t ht
  have hp : (c • φ - peval (c • a) j) t=c*((φ-peval a j) t):=by dsimp [peval,Zone.eval,Pi.sub_apply];rw [mul_sub,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro;intro;ring
  rw [hp,norm_mul]; exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
theorem comparison : Aspiration (realTop w q m Ψ) (polynomialTop w q m Ψ):=by
  let A (x:I→Native q m)(o)(t:Task w):= fun r:ℝ=>price q m Ψ x * ((r⁻¹)^number w t * preExpectation (placements w q m o x t) r)
  let B (x:I→Native q m)(o)(t:Task w):= fun j=>price q m Ψ x * diagonalWith (tray G) (restrictedO (placements w q m o x t)) (number w t+j)
  have hh (x:I→Native q m)(o : Native q m)(t:Task w) : Aspiration (A x o t) (B x o t) := scale_price _ _ (price q m Ψ x) <| product_finite w t (fun i=>x i+o) (epsilon q m) (side_even q m)
  let α (x:I→Native q m):= ∑ o∈origins q m,∑ t:Task w,A x o t
  let β (x:I→Native q m):= ∑ o∈origins q m,∑ t:Task w,B x o t
  have h x o := Aspiration.sum Finset.univ _ _ fun (t:Task w) _=> hh x o t
  have h (x:I→Native q m) : Aspiration (α x) (β x) := Aspiration.sum _ _ _ fun (o:Native q m) _=> h x o
  rw [show realTop w q m Ψ=∑ x:I→Native q m,α x by funext r; simp [realTop,α,A],
      show polynomialTop w q m Ψ=∑ x:I→Native q m, β x by funext r; simp [polynomialTop,β,B]]
  exact Aspiration.sum Finset.univ _ _ fun (x:I→Native q m) _=> h x

end Mixed
end YM.PertExtension.LatticePT
