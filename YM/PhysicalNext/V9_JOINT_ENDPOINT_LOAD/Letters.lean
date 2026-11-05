import YM.Further.GAUSSIAN_SCALAR_LEDGER.Correction
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Paths

/-! # Charges for actual `(-S)^j A` under all ordered V directions

Not a free Haar-branch or occurrence-read identity; uses the TRUE matrices
throughout. `expands` explains the physical multiplicity/address convention
inside the Z-dependent part of the density (one ratio index per position
chain, use with the first optional SUBSET expansion). Higher Taylor bills
in `block_ticket` on those exact same individual addresses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Matrix Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian
open Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism
open Push.SectorMeasure Wisps Schur
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} {c f : Side} {S : StepData c f} {T : Tube G S}
    {A : Stores S} {F : Forest S.ratio} {H : Patch} {x r s g : ℝ} {l : S.Choices}
    {V : Config G c} {v : Charges} {k : ℕ} {bp : BudgetPoint} {q : Chi}

def stretch {x : ℝ} (o : Site c) (P : ℕ) : (n : ℕ) → Active A x F → (Fin n → Active A x F) → ℝ
  | 0,i,_ => grade P o (site i)
  | n+1,i,h => grade P o (site i) + stretch o P n (h 0) (Fin.tail h)
lemma stretch_pos (o : Site c) (P n : ℕ) (i : Active A x F) (h : Fin n → Active A x F) : 0<stretch o P n i h := by
  induction n generalizing i with
  | zero => exact grade_pos ..
  | succ n ih => exact add_pos (grade_pos ..) (ih ..)

def nominal (v : Charges) (A : Stores S) (F : Forest S.ratio) (x : ℝ) : Wall (Active A x F) :=
  Matrix.of fun i j => v.ordinary (site i) (site j)
lemma nominal_pos (v : Charges) (i j : Active A x F) : 0 < nominal v A F x i j :=
  mul_pos (zero_lt_one.trans_le v.paid) (rate_pos ..)

def labelPrice (v : Charges) (A : Stores S) (F : Forest S.ratio) (x : ℝ) :=
  Trail.tread (v.levy x • nominal v A F x) (nominal v A F x)
lemma labelPrice_pos (v : Charges) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (n i h j) :
    0<labelPrice v A F x n i h j :=
  tread_pos (fun i j => mul_pos (v.levy_pos x) (nominal_pos v i j)) (nominal_pos v) n i h j

private def colors {n : ℕ} (h : Fin n → I) (t : Fin n → G.ColorIndex) (j : Fin n) := (h j,t j)

def block (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (l : S.Choices) (n : ℕ)
    (i : Active A x F) (h : Fin n → Active A x F) (j : Active A x F) (a b : G.ColorIndex) (V : Config G c) :=
  ∑ t, Trail.tread (-defect T x A F l V) (gramAt T x A F l V) n (i,a) (colors (G:=G) h t) (j,b)

def blockPrice (v : Charges) (A : Stores S) (F : Forest S.ratio) (G : Gauge) (x : ℝ) (n i h j) :=
  (Fintype.card G.ColorIndex:ℝ)^n* labelPrice v A F x n i h j
lemma blockPrice_nn (v : Charges) (A : Stores S) (F : Forest S.ratio) (G : Gauge) (x : ℝ) (n i h j) : 0 ≤ blockPrice v A F G x n i h j :=
  mul_nonneg (by positivity) (labelPrice_pos ..).le

namespace Value
variable (hV : Value v x r T A F l V bp k q g) (n : ℕ) (i : Active A x F) (h : Fin n → Active A x F) (j : Active A x F) (a b : G.ColorIndex)
include hV

private lemma one_ticket (t : Fin n → G.ColorIndex) (o : Site c) :
    Ticket (bp.dirBound o) k V (labelPrice v A F x n i h j) (stretch o (bp.power*k) n i h)
      (fun w => Trail.tread (- defect T x A F l w) (gramAt T x A F l w) n (i,a) (colors (G:=G) h t) (j,b)) := by
  induction n generalizing i a with
  | zero => exact (hV.entries o (i,a) (j,b)).1
  | succ n ih =>
    have he := ((hV.entries o (i,a) (h 0,t 0)).2.indiv (-1:ℝ))
    simp only [norm_neg,norm_one,one_mul,neg_smul,one_smul] at he
    exact he.mul (ih _ (Fin.tail h) _ (Fin.tail t))

theorem block_ticket (o : Site c) : Ticket (bp.dirBound o) k V (blockPrice v A F G x n i h j)
    (stretch o (bp.power*k) n i h) (block T A F x l n i h j a b) := by
  unfold blockPrice
  convert! Ticket.sum (stretch_pos o (bp.power*k) n i h).le (I:=Finset.univ) (fun t _ => hV.one_ticket _ i h j a b t o) using 1
  · simp
  ext w; rw [Finset.sum_apply]; rfl
end Value

namespace Charges
variable (v : Charges) (G : Gauge) (i j : Active A x F)

private lemma ink_covers : (Fintype.card G.ColorIndex:ℝ)^2 * v.price ≤ v.ink G^2 := by
  let n : ℝ := Fintype.card G.ColorIndex
  have hn : 0≤n := Nat.cast_nonneg _
  have hp := v.paid
  unfold ink
  rw [mul_pow,mul_comm (v.price^2)]
  exact mul_le_mul (pow_le_pow_left₀ hn (le_add_of_nonneg_left zero_le_one) 2) (le_self_pow₀ hp (by norm_num))
    (zero_le_one.trans hp) (sq_nonneg _)
private lemma axis_le : (Fintype.card G.ColorIndex : ℝ) ≤ (Fintype.card G.ColorIndex:ℝ)^2 := by
  exact_mod_cast (by nlinarith only [] : Fintype.card G.ColorIndex ≤ Fintype.card G.ColorIndex ^ 2)

lemma hop_covers : (Fintype.card G.ColorIndex:ℝ)^2 * nominal v A F x i j ≤ v.hop x A F G i j ^ 2 := by
  unfold nominal ordinary hop toll; simp only [Matrix.of_apply,mul_pow, ← mul_assoc _ v.price, rate]
  rw [sq (Real.exp _),← Real.exp_add]
  convert! mul_le_mul_of_nonneg_right (v.ink_covers G) (rate_pos (-v.speed) (separation (site i) (site j))).le using 1
  unfold rate; ring_nf

lemma solo_covers (x : ℝ) : (Fintype.card G.ColorIndex:ℝ)*(v.levy x * v.price) ≤ (v.ink G * v.coin x)^2 := by
  rw [mul_pow,v.halves]
  have hv := (mul_le_mul_of_nonneg_right (axis_le G) (zero_le_one.trans v.paid)).trans (v.ink_covers G)
  exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right hv (v.levy_pos x).le)

lemma walk_covers (n : ℕ) (h : Fin n → Active A x F) :
    (Fintype.card G.ColorIndex:ℝ)^2 * blockPrice v A F G x n i h j ≤ v.walkRate x A F G n i h j^2 := by
  induction n generalizing i with
  | zero => exact (le_of_eq (by simp only [blockPrice,pow_zero,one_mul,labelPrice,Trail.tread])).trans (v.hop_covers G i j)
  | succ n ih =>
    let z := h 0
    let p := v.levy x * nominal v A F x i z
    let t : ℝ := Fintype.card G.ColorIndex
    have hp : 0 ≤ p := mul_nonneg (v.levy_pos x).le (nominal_pos v i z).le
    have he : t*p ≤ v.tap x A F G i z^2 := by
      change t*p ≤ (v.coin x * v.hop x A F G i z)^2
      rw [mul_pow,v.halves]
      calc
        _ = v.levy x * (t*nominal v A F x i z) := by unfold p; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (axis_le G) (nominal_pos v i z).le).trans (v.hop_covers ..)) (v.levy_pos x).le
    let W := blockPrice v A F G x n z (Fin.tail h) j
    have ht := mul_le_mul he (ih z (Fin.tail h)) (mul_nonneg (sq_nonneg t) (blockPrice_nn ..)) (sq_nonneg _)
    calc
      _ = t*p*(t^2*W) := by
        change t^2 * (t^(n+1)*(p * labelPrice v A F x n z (Fin.tail h) j)) = _
        unfold W blockPrice; dsimp only [t]; ring
      _ ≤ _ := ht.trans_eq (mul_pow ..).symm
end Charges

lemma block_sum (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (l : S.Choices) (V : Config G c) (m : ℕ)
    (i j : Active A x F) (a b : G.ColorIndex) :
    ∑ h,block T A F x l m i h j a b V = ((-defect T x A F l V)^m * gramAt T x A F l V) (i,a) (j,b) := by
  rw [← Trail.wheels, ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Active A x F) (fun _ => G.ColorIndex)).symm, Fintype.sum_prod_type]
  rfl

namespace Value
variable (h : Value v x r T A F l V bp k q g) (hH : S.patch=H) (hq : v.coin x*v.lifetime H G < 1)
  (hb : v.top G H x ≤ 1) (i j : Active A x F)
include h hH
private lemma row : SectorNext.Vacuum.Round.rowRate (v.coin x*v.lifetime H G) (defect T x A F l V) := by
  rintro ⟨i,a⟩
  have h1 j : ∑ b : G.ColorIndex, |defect T x A F l V (i,a) (j,b)| ≤ v.tap x A F G i j := by
    have he := Finset.sum_le_sum (g:=fun _ => v.levy x*nominal v A F x i j) (fun b (_:b∈Finset.univ) => ((h.entries 0 (i,a) (j,b)).2.base :
      ‖defect T x A F l V (i,a) (j,b)‖ ≤ _))
    simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul, Real.norm_eq_abs] at he
    apply he.trans
    have h1 := v.paid; have h2 : 0 < v.price := zero_lt_one.trans_le h1
    have h3 := v.time_pos; have h4 : 0 < v.speed := v.live
    have h5 (t : ℝ) (n : ℕ) (ht : 0<t) : rate (-t) n ≤ rate (-(t/2)) n := by
      apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    rw [Charges.tap,Matrix.smul_apply,smul_eq_mul]
    unfold Charges.hop nominal; simp only [Matrix.of_apply,Charges.ordinary]
    calc
      _ = v.levy x * ((v.price*Fintype.card G.ColorIndex)*rate (-v.speed) (separation (site i) (site j))) := by ring
      _ ≤ _ := mul_le_mul (h5 _ _ v.time_pos) (mul_le_mul (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) h2.le)
        (h5 _ _ v.live) (rate_pos ..).le (v.ink_pos G).le) (mul_nonneg (mul_nonneg h2.le (by positivity)) (rate_pos ..).le) (v.coin_pos x).le
  rw [Fintype.sum_prod_type]
  obtain ⟨-,ha,-⟩ := (v.hop_pours x A F G hH).scale (v.coin x)
  have hi := ha i
  change (∑ j,rate 0 _ * |v.tap x A F G i j|) ≤ _ at hi
  simp only [rate,zero_mul,Real.exp_zero,one_mul,abs_of_pos (v.coin_pos x),abs_of_pos (v.tap_pos ..)] at hi
  exact (Finset.sum_le_sum fun j _ => h1 j).trans hi

include hq hb
/-- Exact unconditionally convergent (at the financed height and field) series.
Number as desired inside `Slices.difference`. Does NOT construct any local
sector decomposition, ownership of gates/compulsory factors, read supports or
regular extensions of those other terms. No equality for logs of signed factors.
-/
theorem expands (a b : G.ColorIndex) : HasSum (fun (p : Σ n, Tracks (Active A x F) n) => block T A F x l (p.1+1) i p.2 j a b V)
    (((fog A F T x V l)⁻¹ - gramAt T x A F l V) (i,a) (j,b)) := by
  let Z := Σ n, Tracks (Active A x F) n
  let emb : Z → Full (Active A x F) := fun ⟨n,h⟩ => .inr ⟨n,(i,j),h⟩
  have he : Injective emb := by
    rintro ⟨n,y⟩ ⟨m,z⟩ h
    rcases Sigma.mk.inj (Sum.inr.inj h) with ⟨rfl,h⟩
    obtain rfl := congr_arg Prod.snd (eq_of_heq h)
    rfl
  have ht := ((v.priced x A F G hH hq i).1.comp_injective he).of_norm_bounded (f:=fun p : Z => block T A F x l (p.1+1) i p.2 j a b V) ?_
  rotate_left
  · intro ⟨n,t⟩
    have hcard : (1:ℝ) ≤ Fintype.card G.ColorIndex := by exact_mod_cast Fintype.card_pos_iff.mpr (Nonempty.intro a)
    apply ((h.block_ticket _ i t j a b 0).base).trans
    change _ ≤ v.audited x A F G i (emb ⟨n,t⟩); unfold Charges.audited; rw [if_pos (show Arc.meets legs _ i from Or.inl rfl)]
    apply ((le_mul_of_one_le_left (blockPrice_nn ..) (one_le_pow₀ hcard)).trans (v.walk_covers G i j (n+1) t)).trans
    rw [pow_two]; exact mul_le_of_le_one_right (v.walkRate_pos ..).le ((v.pay_alone x A F G hH hq (.inr ⟨_,(i,j),t⟩)).trans hb)
  have hy := mul_nonneg (v.coin_pos x).le (v.lifetime_nn G H)
  obtain ⟨-, -, -, -, -, -, -, H⟩ := split_costs h.otb h.pane.isHermitian rfl (h.row hH) hy hq
  apply (H (i,a) (j,b)).sigma_of_hasSum _ ht
  intro n
  change HasSum _ (((-defect T x A F l V)^(n+1) * gramAt T x A F l V) (i,a) (j,b))
  rw [← block_sum]; exact hasSum_fintype _
end Value

/-- Localized sub-invoice of `Value` (for use also with partly wrong A via
    complete reads; see `Folio`). All calls must still be on one shared
    table and field (with the physical leftDerivs, not moving any junk
    branches at another table). -/
structure Part (ok : Active A x F → Prop) (v : Charges) (r : ℝ) (T : Tube G S)
    (l : S.Choices) (V : Config G c) (bp : BudgetPoint) (k : ℕ) (q : Chi) (g : ℝ) : Prop where
  block_ticket (n i h j) (a b : G.ColorIndex) (o : Site c) : ok i → (∀ t : Fin n,ok (h t)) → ok j →
    Ticket (bp.dirBound o) k V (blockPrice v A F G x n i h j)
      (stretch o (bp.power*k) n i h) (block T A F x l n i h j a b)
  moving (o : Site c) (i : In (G:=G) x A F) (Y) : ok i.1 →
    let ti := grade (bp.power*k) o (front A F i)
    Ticket (bp.dirBound o) k V (v.price * fiery G x S.patch.L) ti (fun w => AnalyticBridge.SectorAffine.Offset.mean T x l A F q r Y w i) ∧
      Ticket (bp.dirBound o) k V (v.levy x * v.price) ti (fun w => headwind T x A F l q r g Y w i)

lemma Value.parts (h : Value v x r T A F l V bp k q g) (ok : Active A x F → Prop) : Part ok v r T l V bp k q g :=
  ⟨fun n i u j a b o _ _ _ => h.block_ticket n i u j a b o, fun o i y _ => h.moving o i y⟩

end YM.PhysicalNext.JointLoad
