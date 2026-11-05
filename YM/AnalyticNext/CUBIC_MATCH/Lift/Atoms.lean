import YM.AnalyticNext.CUBIC_MATCH.Lift.Pair
import YM.AnalyticNext.CUBIC_MATCH.Terms.Slots
import YM.Progress.JOINT_CALENDAR.Rows



set_option warningAsError false

/-!
# Output cubic atoms at true path budget

Includes the physical path lengths, even on windings,
so these plug into the `.Bounds` width without any period cost. Signed
execution still as whole-channel averages. Cutoff masks not applied to these
comparisons (this module isn't paying for the activity representation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function RG Wilson Lattice Precision Exterior Tree Work.F02 Work.F03 Bid Matrix
open Progress.Joint Lift Laurent
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}

abbrev Tiles3 := TypeFace 2 × TypeFace 2 × TypeFace 2
abbrev Box3 := Tiles3 × Couple
def slate (a : TypeFace 2) (x : Cover) : Slot := script (plaqEquiv.symm a,x)

def pigment (x : Fin 3 → G.ColorIndex) (i : Fin 3) := EuclideanSpace.basisFun G.ColorIndex ℝ (x i)

abbrev Stored (G : Gauge) := Three (Shades G) 2 2 2
def deposit (A : Stored G) (z : Tiles3) (q : Couple) : Atom G 3 :=
  ⟨![slate z.1 q.1,slate z.2.1 q.2,slate z.2.2 0],fun i => A z.1 z.2.1 z.2.2 q (pigment i)⟩

def marks3 : ℕ ≃ Box3 := by
  haveI : Nonempty (TypeFace 2) := ⟨plaquette ⟨(0,1),by decide⟩⟩
  exact Classical.choice nonempty_equiv_of_countable

def plant3 (A : Stored G) (i : ℕ) := deposit A (marks3 i).1 (marks3 i).2

variable {η C : ℝ}

lemma deposit_length (A : Stored G) (i : Tiles3) (q : Couple) :
    (deposit A i q).length=length2 q+12 := by
  unfold deposit Atom.length
  simp only [Fin.sum_univ_succ,cons_val_zero,cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change (slate i.1 q.1).length+((slate i.2.1 q.2).length+(slate i.2.2 0).length)=_
  unfold slate; simp_rw [script_length]
  rw [show size (0:Cover)=0 by simp [size]]
  unfold length2; omega

lemma deposit_poly (A : Stored G) (z : Tiles3) (m : Couple) (x : Fin 3 → G.Color) :
    (deposit A z m).poly x=A z.1 z.2.1 z.2.2 m x := by
  let T := A z.1 z.2.1 z.2.2 m
  let B := EuclideanSpace.basisFun G.ColorIndex ℝ
  let f (i : Fin 3) (k : G.ColorIndex) := x i k • B k
  have ht i : ∑ k, f i k = x i := B.sum_repr _
  have he := T.map_sum f
  simp_rw [ht] at he
  refine Eq.trans (Finset.sum_congr rfl (fun b hb => ?_)) he.symm
  change T (pigment b) * (∏ i, x i (b i)) = T (fun i => x i (b i) • pigment b i)
  rw [T.map_smul_univ (fun i => x i (b i)) (pigment b), smul_eq_mul,mul_comm]
lemma plant3_valid {A : Stored G} (h : ∀ i j a p,A i j a p∈ Shades.invariant G) (i : ℕ) :
    (plant3 A i).Invariant := by
  intro u x; rw [plant3,deposit_poly,deposit_poly]; exact h _ _ _ _ u x

lemma color_price {x : Fin 3 → G.ColorIndex} (A : Shades G) :
    |A (pigment x)| ≤ ‖A‖ := by simpa [pigment] using A.le_opNorm (pigment x)

/-- width loss buys the COUNT on y and z. -/
def lamp (G : Gauge) (η : ℝ) := (Fintype.card (Fin 3 → G.ColorIndex):ℝ)*Real.exp ((η/2)*12)
lemma lamp_nonneg (G : Gauge) (η : ℝ) : 0 ≤ lamp G η := by unfold lamp; positivity

def bookFee (G : Gauge) (η : ℝ) := (Fintype.card Tiles3 : ℝ)*lamp G η*
    (∑' q : Couple, wanes (η/2) (length2 q))
lemma bookFee_nonneg (G : Gauge) (η : ℝ) : 0 ≤ bookFee G η :=
  mul_nonneg (mul_nonneg (by positivity) (lamp_nonneg ..)) (tsum_nonneg fun _ => (wanes_pos ..).le)

private lemma published {A : Stored G} (h : Pace η C A) (hp : 0<η) (hx : 0≤C) (z : Tiles3) :
    SumBudget (fun p => (deposit A z p).budget (η/2)) (lamp G η * C *
      ∑' p : Couple,wanes (η/2) (length2 p)) := by
  let g := lamp G η * C
  have hy := summable_two (half_pos hp)
  have hh : SumBudget (fun p : Couple => g*wanes (η/2) (length2 p)) (g*∑' p : Couple,wanes (η/2) (length2 p)) := by
    refine ⟨fun i => mul_nonneg (mul_nonneg (lamp_nonneg ..) hx) (wanes_pos ..).le, hy.mul_left g,?_⟩; rw [tsum_mul_left]
  refine Work.F08.budget_minor hh (fun _ => mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Real.exp_pos _).le) fun p => ?_
  unfold Atom.budget
  rw [deposit_length]
  have he : (deposit A z p).magnitude ≤ Fintype.card (Fin 3 → G.ColorIndex)*(C*wanes η (length2 p)) := by
    unfold Atom.magnitude
    exact (Finset.sum_le_sum (fun i _ => (color_price (x:=i) (A z.1 z.2.1 z.2.2 p)).trans (h _ _ _ _))).trans_eq (by simp)
  refine (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans_eq ?_
  have hk : wanes η (length2 p)*Real.exp (η/2*((length2 p+12:ℕ):ℝ)) =
      Real.exp (η/2*12)*wanes (η/2) (length2 p) := by
    unfold wanes; rw [← Real.exp_add, ← Real.exp_add]; push_cast; congr 1; ring
  rw [mul_assoc,mul_assoc,hk]; unfold g lamp; ring

lemma plant3_quote {A : Stored G} (h : Pace η C A) (hp : 0<η) (hx : 0≤C) :
    SumBudget (fun i => (plant3 A i).budget (η/2)) (bookFee G η*C) := by
  have he := published h hp hx
  let f (q : Box3) := (deposit A q.1 q.2).budget (η/2)
  have ht : ∀ i, 0 ≤ f i := fun i => (he i.1).1 i.2
  have hh : Summable f := (summable_prod_of_nonneg ht).mpr ⟨fun i => (he i).2.1,.of_finite⟩
  change SumBudget (fun i => f (marks3 i)) _
  refine ⟨fun i => ht _, marks3.summable_iff.mpr hh,?_⟩
  rw [Equiv.tsum_eq marks3, hh.tsum_prod,tsum_fintype]; refine (Finset.sum_le_sum fun i _ => (he i).2.2).trans_eq ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold bookFee; ring

section site
variable {n : Side}
lemma tile_read (A : Stored G) (t : Tiles3) (q : Couple) (x : Dir G n) (z : Site n) :
    let V := dColor G n 1 x
    (deposit A t q).poly (fun b => faceCurl (slotFace ((deposit A t q).leg b) z) x) =
      A t.1 t.2.1 t.2.2 q (![V (wrap n q.1+z,t.1),V (wrap n q.2+z,t.2.1),V (z,t.2.2)]) := by
  let V := dColor G n 1 x; intro
  have hx (i : TypeFace 2) p : faceCurl (slotFace (slate i p) z) x= V (wrap n p+z,i) := by
    unfold faceCurl V slotFace slate
    rw [script_offset]; change V (_,plaqEquiv (plaqEquiv.symm i))=V _
    rw [plaqEquiv.apply_symm_apply]
  rw [deposit_poly]
  refine congr_arg (A ..) (funext fun i => ?_)
  fin_cases i
  · exact hx _ _
  · exact hx _ _
  change faceCurl (slotFace (slate _ 0) _) _= V (z,t.2.2)
  rw [hx,map_zero,zero_add]

lemma plant3_third {A : Stored G} (h : Pace η C A) (hp : 0<η) (hx : 0≤C) (x : Dir G n) :
    term 3 (fun t : ℝ => uncut (plant3 A) (represent (t • x)))=pair3 (completely A) x x x := by
  rw [(preamble (half_pos hp) (plant3_quote h hp hx) x).1, ← against_three h hp, translation h hp]
  refine Finset.sum_congr rfl fun z _ => ?_
  let Q (b : Box3) := (deposit A b.1 b.2).poly (fun i => faceCurl (slotFace ((deposit A b.1 b.2).leg i) z) x)
  change ∑' i, Q (marks3 i)=_
  have ha := plant3_quote h hp hx
  have hb := atom_story (A:=plant3 A) (j:=3) (U:=fun t : ℝ => represent (t • x)) (half_pos hp) ha z (test_ray x)
  have he : Summable Q := marks3.summable_iff.mp <| hb.summable.congr (fun i => (slot_first ..).1)
  rw [Equiv.tsum_eq marks3, he.tsum_prod,tsum_fintype]
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    tsum_congr fun p => tile_read A (i,j,k) p x z
end site
end YM.CubicMatch
