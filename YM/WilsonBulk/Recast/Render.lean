import YM.WilsonBulk.Recast.Shape

/-! # Rendering reset as `Record` and `Tape`; rank zero included when not issued.
Need dominance by `stencils` through finite contractions elsewhere. Here no equality of densities at nonformal g,
only Series of cells. Scalar omitted elsewhere. These reexpress formulas export to integrators. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Recall
open PowerSeries Filter Function Finset Matrix Sheet Equiv
open scoped Topology Classical BigOperators
variable {α β A B : Type} [CommRing A] [Algebra ℝ A] {e k n i j d : ℕ}
variable {g r p q : Word} {I J : Record α}
-- rank isolated semantics. Includes scalar.

def pencil (g r : Word) (e n i : ℕ) := coeff (e-i) (g^i*r^n)
lemma pencil_falls (h : Pall g) (f : Pall r) (hz : k≤e) (hp : k%2 ≠ e%2) : pencil g r e n k=0 := by -- e k binder
  apply ((h.sq_pow _).square_mul (f.sq_pow _)); omega
lemma pencil_hero (e n : ℕ) (h : constantCoeff g=1) (k : constantCoeff r=1) : pencil g r e n e=1 := by unfold pencil; simp only [tsub_self, coeff_zero_eq_constantCoeff,map_mul, map_pow, h,k,one_pow,mul_one]

def reorder (g r : Word) (I : Record α) : Record α:= fun e n=> ∑ i∈range (e+1),pencil g r e n i • I i n
lemma Document.at_first (h : Document I) (hx : Pall g) (he : Pall r) : Document (reorder g r I) := by
  refine ⟨fun i j hi=> sum_eq_zero (fun u hv=> by rw [h.cap u j (by rw [mem_range] at hv; omega),smul_zero]), fun i j=> Regular.summed fun k _=> (h.coherent k _).scaled _, fun i j hi=> sum_eq_zero (fun y hy=> ?_)⟩
  by_cases hh : y%2=j%2; · rw [pencil_falls hx he (by rw [mem_range] at hy; omega) (by omega),zero_smul]
  rw [h.parity y j hh,smul_zero]
lemma Cashless.shelter (h : Cashless I) : Cashless (reorder g r I) := fun i=> by simp only [reorder,h,smul_zero,sum_const_zero] -- letter sum h _
lemma anchor_literal (h : constantCoeff g=1) (hr : constantCoeff r=1) : reorder g r I 0=I 0:= funext fun i=> by simp [reorder,pencil_hero 0 i h hr]
open Pert.Bulk
lemma Pamphlet.authorized {V : Record (Market α)} (hv : Pamphlet V) : Pamphlet (reorder g r V) := fun e u=> Public.gather (range (e+1)) (fun i _=> (hv i u).scale _)
lemma stamp_coupon (V : α → Text β n) (g : Finset α) (h : ∀ v∈g,Public (V v)) (c : Lattice.Side) : coupon c n (∑ i∈g,V i)= ∑ i∈g,coupon c n (V i) := by
  induction g using Finset.induction with
  | empty=> simp
  | insert i g hi ih=>
    have hf (i) (hi:i∈g): Public (V i):=h i (mem_insert_of_mem hi)
    rw [sum_insert hi,sum_insert hi,coupon_plus c (h i (mem_insert_self ..)) (Public.gather g hf), ih hf]
lemma Pamphlet.issue_reorders {V : Record (Market α)} (hv : Pamphlet V) (c : Lattice.Side) : issue c (reorder g r V)=reorder g r (issue c V) := by
  funext i j; unfold issue reorder; rw [stamp_coupon _ _ (fun i _=> (hv i j).scale _)]; exact sum_congr rfl fun i _=> coupon_scale c (hv i _).style _
variable [Fintype α]
lemma shifted_power (V : Page α n) (i u) (g r : Word) (hi : i ≤ u) : coeff u (shade g r (X^i*C (script V)))= pencil g r u n i • script V := by
  rw [map_mul,map_pow, shadeX,mul_pow,script_shift]; rw [show X^i*color_clock α g^i*(color_clock α r^n*C (script V))=X^i*(color_clock α (g^i*r^n)*C (script V)) by rw [map_mul,map_pow,map_pow]; ring,priceX u i _ hi,coeff_mul_C,tonic_coeff,pencil,MvPolynomial.C_mul']
lemma reorder_tape (h : FrameBound I) (g r : Word) : volumeTape (reorder g r I)= shade g r (volumeTape I) := by
  ext1 n
  have hh i (hi:i∈range (n+1)) : coeff i (volumeTape I)=∑ k∈allowed n, script (I i k):= by rw [tape_power,capsule]; exact sum_subset (range_mono (by rw [mem_range] at hi; omega)) (fun j _ hp=> by simp only [h i j (by simp only [allowed,mem_range] at hp; omega),script_zero])
  rw [Steps.push (shade g r) (by rw [shadeX];simp) (before_end (n+1) (volumeTape I)) n (by omega),map_sum,map_sum,tape_power,capsule]
  unfold reorder; simp_rw [script_sum,script_scale]; rw [sum_comm]; refine sum_congr rfl fun i hi=>?_; rw [hh i hi]; simp only [map_sum, Finset.mul_sum]; exact sum_congr rfl fun j _=> (shifted_power (I i j) i n g r (by rw [mem_range] at hi; omega)).symm
omit [Fintype α] in
lemma reorder_steps (U V : Record α) (k : ℕ) (hf : Steps k p q) (hg : Steps k g r) (he : ∀ i<k,∀ n,U i n=V i n) : ∀ i<k,∀ n,reorder p g U i n=reorder q r V i n:= by
  intro i h n; exact sum_congr rfl fun j hj=> congr_arg₂ _ (show pencil p g i n j=pencil q r i n j from ((hf.powers j).mul (hg.powers n)) _ (by omega)) (he j (by rw [mem_range] at hj; omega) n)
end YM.WilsonBulk.Recall
