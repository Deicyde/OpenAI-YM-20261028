import YM.AnalyticNext.QUARTIC_MATCH.Addresses
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Inside
import YM.AnalyticNext.QUARTIC_MATCH.Leading
import YM.Progress.JOINT_CALENDAR.Rows


/-!
# Curvature payment on canonical paths

Use only to FILL a new correction. Doesn't alter incoming row paths nor the
paths of any of the lower terms. Includes all orientations when reading the
full nonlinear action. Use any choice obeying this leg rule and ACTUAL cost, e.g.
`shortest`. Not choosing torus geodesics separately at each mesh.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Tensor Joint BoxChain
open Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

namespace Mail
variable {n c : ℕ} {G : Gauge}

/-- Native-unit cover paths. -/
structure Printed (n : ℕ) where
  travels (a : Address n) : Fin (n+1)→RG.Slot
  control : ℕ
  positive : 1≤control
  rule (a : Address n) (i) : cells a i=((travels a i).offset,(plaquette (travels a i).plaq).val)
  bound (a : Address n) : ∑ i, (travels a i).length ≤ control*(1+loads a.2)

private lemma estate {n : ℕ} (a : Address n) :
    ∑ i : Fin (n+1), (size (Mail.offset a i)+4)=loads a.2+4*(n+1) := by
  rw [Finset.sum_add_distrib]; congr 1
  · have he := net a
    simpa [loads,cells,Mail.offset] using he
  simp [mul_comm]

def shortest (n : ℕ) : Printed n where
  travels a i := Progress.Joint.script (plaqEquiv.symm (a.1 i),Mail.offset a i)
  control := 4*(n+1)
  positive := by omega
  rule a i := by
    rw [Progress.Joint.script_offset]
    exact Prod.ext rfl (congr_arg Subtype.val (plaqEquiv.apply_symm_apply (a.1 i)).symm)
  bound a := by
    simp_rw [Progress.Joint.script_length]
    change ∑ i, (size (offset a i)+4) ≤ _
    rw [estate]
    nlinarith

variable (P : Printed n)

-- address numbering. need n positive (≥1 offset slot, even though arity may be 2)
def index (n : ℕ) [NeZero n] : ℕ ≃ Address n := by
  letI : Nonempty (TypeFace 2) := ⟨plaquette ⟨(0,1),by decide⟩⟩
  exact Classical.choice nonempty_equiv_of_countable

def composition (F : rootArray G n) (x : Address n) : Atom G (n+1) where
  leg := P.travels x
  coeff v := (F (cells x)).val fun i => EuclideanSpace.basisFun G.ColorIndex ℝ (v i)

lemma compose_value (F : rootArray G n) (x : Address n) (V : Fin (n+1)→G.Color) :
    (composition P F x).poly V = (F (cells x)).val V := by
  let f := (F (cells x)).val; let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  have he i : V i = ∑ j : G.ColorIndex, V i j • b j := by
    have hh := b.toBasis.sum_equivFun (V i)
    apply Eq.trans hh.symm; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Module.Basis.equivFun_apply]; simp [b]
  have hx : V=fun i => ∑ j : G.ColorIndex,V i j • b j := funext he
  conv_rhs => rw [hx]
  rw [ContinuousMultilinearMap.map_sum_finset]
  simp_rw [ContinuousMultilinearMap.map_smul_univ]
  classical
  rw [Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun i _ => mul_comm ..



lemma measureUp (F : rootArray G n) (x : Address n) :
    (composition P F x).magnitude ≤ Fintype.card (Fin (n+1)→G.ColorIndex)*‖F (cells x)‖ := by
  let T := F (cells x)
  calc
    _ ≤ ∑ _ : Fin (n+1)→G.ColorIndex, ‖T‖ := Finset.sum_le_sum fun i _ => by
      have hh := T.val.le_opNorm (fun k => EuclideanSpace.basisFun G.ColorIndex ℝ (i k))
      simp_rw [OrthonormalBasis.norm_eq_one, Finset.prod_const_one,mul_one] at hh; exact hh
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

namespace Printed
variable (G)
def width (σ : ℝ) := shiftRate (Fin (n+1)) σ/(2*P.control)
def tariff (σ : ℝ) := Fintype.card (Fin (n+1)→G.ColorIndex) * Real.exp (P.width σ * P.control)
def reserve (σ : ℝ) : ℝ := P.tariff G σ * (Fintype.card (Fin (n+1)→ TypeFace 2) *
    (2*((1+P.width σ * P.control)/(P.width σ * P.control)))^(Fintype.card (Fin n × Axis)))

lemma expans {σ : ℝ} (h : 0<σ) : 0<P.width σ :=
    div_pos (positive_rate h (0:Fin (n+1))) (mul_pos (by norm_num) (by exact_mod_cast P.positive))
lemma tariff_nonneg (σ : ℝ) : 0 ≤ P.tariff G σ := by unfold tariff; positivity
lemma reserve_nonneg (σ : ℝ) (h : 0<σ) : 0 ≤ P.reserve G σ := by
  have hx := P.positive; have hc := P.expans h
  unfold reserve; refine mul_nonneg (P.tariff_nonneg G σ) ?_; positivity
end Printed

variable [NeZero n]
def letters (F : rootArray G n) (k : ℕ) := composition P F (index n k)

theorem sends {F : rootArray G n} {σ C} (h : Pricing F σ C) :
    SumBudget (fun i => (letters P F i).budget (P.width σ)) (P.reserve G σ*C) := by
  have hp := P.positive
  let p := P.width σ; let d : ℝ := P.control
  have he : 0<p := P.expans h.rate
  have hz : 0<d := by unfold d; exact_mod_cast hp
  let f (a : Address n) := Real.exp (-(p*d)*loads a.2)
  have ht a : (composition P F a).budget p ≤ (P.tariff G σ*C)*f a := by
    have hy := P.bound a
    have hh : (↑((composition P F a).length):ℝ)≤d*(1+loads a.2) := by unfold d; exact_mod_cast hy
    have hc := pricing_anchor h (0:Fin (n+1)) (cells a)
    rw [net] at hc
    have hx := measureUp P F a
    calc
      _ ≤ (Fintype.card (Fin (n+1)→G.ColorIndex)* (C*Real.exp (-shiftRate (Fin (n+1)) σ*loads a.2))) *
          Real.exp (p*(d*(1+loads a.2))) := by
            unfold Atom.budget
            apply mul_le_mul (hx.trans (mul_le_mul_of_nonneg_left hc (by positivity)))
              (Real.exp_monotone (mul_le_mul_of_nonneg_left hh he.le)) (Real.exp_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg h.cap (Real.exp_nonneg _)))
      _ = _ := by
        have hi : p*(2*d)=shiftRate (Fin (n+1)) σ := div_mul_cancel₀ _ (by positivity)
        unfold f Printed.tariff; change _ = ↑(Fintype.card _) * Real.exp (p*d) * C * _
        rw [← hi, mul_assoc (Fintype.card _:ℝ),mul_assoc C, ← Real.exp_add, mul_right_comm _ _ C,mul_assoc _ _ (Real.exp _), ← Real.exp_add]
        ring_nf
  let M := P.tariff G σ*C
  have hk (i : ℕ) := ht (index n i)
  have hs := supply (mul_pos he hz) n
  have hv : Summable f := hs.2.1
  have hi : Summable (fun i => M*f (index n i)) := (index n).summable_iff.mpr (hv.mul_left _)
  have hc (i : ℕ) : 0 ≤ (letters P F i).budget p := by unfold Atom.budget Atom.magnitude; positivity
  have ha := hi.of_nonneg_of_le hc hk
  refine ⟨hc,ha, (ha.tsum_le_tsum hk hi).trans ?_⟩
  rw [tsum_mul_left, Equiv.tsum_eq (index n)]
  apply (mul_le_mul_of_nonneg_left hs.2.2 (mul_nonneg (P.tariff_nonneg ..) h.cap)).trans_eq
  unfold Printed.reserve p d; ring

section
variable {c : Side}

omit [NeZero n] in
lemma solve_pay (A : ArrayC (Fin n) (Per c) (ColorPart G n)) (V : Fin n → Ink G c) (l : List (Fin n))
    (h : l.Nodup) :
    post (solve l A) V = post A (fun i => if i∈l then track (V i) else V i) := by
  induction l generalizing V with
  | nil => simp [solve_empty]
  | cons a l ih =>
    rw [List.nodup_cons] at h
    rw [solve_head,transfers, ih _ h.2]; congr 1; funext i
    by_cases ht : i=a <;> simp [ht,h.1]

variable (F : rootArray G n) {σ C}

omit [NeZero n] in
lemma contents (a : Address n) (V : Dir G c) (x : Site c) :
    let W := BoxChain.track (liftField 1 V)
    (F (cells a)).val (fun i => W (place x a i)) =
      (composition P F a).poly fun j => faceCurl (slotFace ((composition P F a).leg j) x) V := by
  intro W
  rw [compose_value]; congr 1; funext i
  let s := (P.travels a i)
  let b := slotFace s x
  have he : place x a i= BoxChain.shape 2 (b.1,plaquette b.2) := by
    change move _ (tor _ (cells a i))=_; rw [P.rule a i]; rfl
  unfold W; rw [he, track_shape, show liftField 1 V ∘ BoxChain.shape 1=V from funext fun i => lifted_shape _ _ _]; rfl

lemma charges_period {Z : Dom G (n+1) c} (B : Colorwise Z) (hb : entries Z B=scene c 0 (solve (List.finRange (n+1)) F))
    (hp : Pricing F σ C) (hr : ∀ i, Rank F i 2) (V : Dir G c) :
    Z (fun _ => V) = ∑ x : Site c, ∑' j, (letters P F j).poly fun i =>
      faceCurl (slotFace ((letters P F j).leg i) x) V := by
  let W := liftField 1 V
  have he : W ∘ BoxChain.shape 1=V := funext fun i => lifted_shape ..
  calc
    _ = post (entries Z B) (fun _ => W) := by rw [pays_inputs]; congr 1; exact funext fun i => he.symm
    _ = post (scene c 0 F) (fun _ => BoxChain.track W) := by
      rw [hb,descend_list _ _ hp, solve_pay _ _ _ (List.nodup_finRange _)]
      simp only [List.mem_finRange, ↓reduceIte]
    _ = _ := by
      rw [ink_delivery hp hr]; refine Finset.sum_congr rfl fun x _ => ?_
      simp_rw [show ∀ (j : Address n), (F (cells j)).val (fun i => BoxChain.track W (place x j i))=_ from fun j => contents P F j V x]
      exact (Equiv.tsum_eq (index n) _).symm

/-- Leading and zero lower jets of the ACTUAL correction, on one period. -/
theorem retained {Z : Dom G (n+1) c} (hv : Residual.Legal Z)
    (hb : entries Z hv.color = scene c 0 (solve (List.finRange (n+1)) F))
    (hp : Pricing F σ C) (hr : ∀ i, Rank F i 2) :
    let U := impact (c:=c) (letters P F)
    Tensor.coeff U (n+1) 0=Z ∧ ∀ i, i<n+1 → Tensor.coeff U i 0=0 := by
  intro U
  obtain ⟨hL,hU⟩ := impact_leading (c:=c) (P.expans hp.rate) (sends P hp)
  refine ⟨Tensor.ext_diag _ _ (Tensor.coeff_symm ((impact_cont (P.expans hp.rate) (sends P hp)).of_le le_top)) hv.polar ?_,hL⟩
  funext v
  have he s : (∑ x : Site c,∑' i, (letters P F i).poly fun j => faceCurl (slotFace ((letters P F i).leg j) x) (shifts s (0:Site c) v))=Tensor.diagonal Z v :=
    (charges_period P F hv.color hb hp hr _).symm.trans (hv.translated s 0 fun _ => v)
  unfold U; rw [hU]; simp only [he]; unfold Patch.average; simp
end
end Mail
end YM.AnalyticNext.QuarticMatch
