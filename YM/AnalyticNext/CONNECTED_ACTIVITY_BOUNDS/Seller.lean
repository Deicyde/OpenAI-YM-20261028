import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount

/-!
# Two-tilt sum expenses

Endpoint-specific caps and tallies stay together when expanding L1 budget of marks.
All on ORIGINAL size-Z projection, with one marginal response vertex bill.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Function MeasureTheory Filter Matrix Finset Topology Centered 
open Centered.Till Progress.StationaryScenes Green
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {ι v : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq v] (t : Till)

def oldTill : Till := ⟨t.floor/2,t.expense/8,half_pos t.floor_pos,div_nonneg t.expense_nn (by norm_num)⟩

def souvenir (W : Tilt ι) : Tilt ι := ⟨10*W.cap,fun i => 2*W.tally i⟩
omit [Fintype ι] [DecidableEq ι] in
lemma sounder {W : Tilt ι} (hp : W.Sound) : (souvenir W).Sound := ⟨mul_nonneg (by norm_num) hp.1,fun i =>
  mul_nonneg (by norm_num) (hp.2 i)⟩
omit [DecidableEq ι] in
lemma payDilation {W : Tilt ι} (hp : W.Sound) (a : ℝ) (hv : a^2≤2) (z : ι→ℝ) :
    10*Ticket W (a • z) ≤ Ticket (souvenir W) z := by
  unfold Ticket; dsimp only [souvenir]; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hp.1)
  rw [Real.exp_le_exp]; apply div_le_div_of_nonneg_right _ (by norm_num); unfold tilt; apply Finset.sum_le_sum; intro i _; dsimp only
  rw [Pi.smul_apply,smul_eq_mul,mul_pow, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg (z i))
  rw [mul_comm _ (a^2)]; exact mul_le_mul_of_nonneg_right hv (hp.2 i)

omit [DecidableEq ι] in
lemma salePriced (W : Tilt ι) : t.sale (souvenir W)=10*sale (oldTill t) W := by
  unfold sale; dsimp only [oldTill,souvenir]; rw [← mul_sum,← mul_assoc 10]
  congr 3; have h := t.floor_pos; field_simp

def cobble (s : Finset v) (P Q : v→Tilt ι) (E : Tilt ι) z := Ticket E z *
    ∏ i∈s,(Ticket (souvenir (P i)) z + Ticket (souvenir (Q i)) z)

def grant (P Q : v→Tilt ι) (i : v) := 10* sale (oldTill t) (P i) +10* sale (oldTill t) (Q i)

omit [DecidableEq ι] in
lemma TKpos {W : Tilt ι} (h : W.Sound) z : 0≤Ticket W z := mul_nonneg h.1 (Real.exp_pos _).le
omit [DecidableEq ι] [DecidableEq v] in
lemma boat_nn (s : Finset v) (P Q : v→Tilt ι) (hp : ∀ i,(P i).Sound) (hq : ∀ i,(Q i).Sound)
    (E : Tilt ι) (he : E.Sound) z : 0 ≤ cobble s P Q E z := mul_nonneg (TKpos he z) <| prod_nonneg fun i _ =>
      add_nonneg (TKpos (sounder (hp i)) z) (TKpos (sounder (hq i)) z)
lemma marked (s : Finset v) (P Q : v→Tilt ι) (hp : ∀ i,(P i).Sound) (hq : ∀ i,(Q i).Sound)
    (hx : ∀ s, occupied (oldTill t) P s) (hv : ∀ s, occupied (oldTill t) Q s) (E : Tilt ι) (he : E.Sound)
    (hw : ∀ i,E.tally i≤t.expense/2) (M : Matrix ι ι ℝ) (hM : t.Safe M) :
    Integrable (cobble s P Q E) (law M) ∧ ∫ z, cobble s P Q E z ∂law M ≤ t.sale E*∏ i∈s,grant t P Q i := by
  let U : Unit ⊕ (v ⊕ v) → Tilt ι := Sum.elim (fun _ => E) (Sum.elim (fun i => souvenir (P i)) (fun i => souvenir (Q i)))
  let w (u : Finset v) := ({()}:Finset Unit).disjSum (u.disjSum (s\u))
  let H (u : Finset v) z := ∏ i∈w u,Ticket (U i) z
  have hh : cobble s P Q E = fun z => ∑ i∈s.powerset,H i z := by
    funext z
    unfold cobble; rw [prod_add,mul_sum]; unfold H w U; simp only [prod_disjSum,prod_singleton,Sum.elim_inl,Sum.elim_inr]
  have h' : t.sale E*∏ i∈s,grant t P Q i=∑ i∈s.powerset, ∏ j∈w i,t.sale (U j) := by
    unfold grant; rw [prod_add,mul_sum]; unfold w U; simp only [prod_disjSum,prod_singleton,Sum.elim_inl,Sum.elim_inr,salePriced]
  have hp i : Integrable (H i) (law M) ∧ ∫ z,H i z∂law M ≤ ∏ j∈w i,t.sale (U j) := by
    have hu i : (U i).Sound := by
      rcases i with i|i|i
      · exact he
      · exact sounder (hp i)
      exact sounder (hq i)
    have he z : ‖H i z‖=H i z := Real.norm_of_nonneg (prod_nonneg fun j _ => TKpos (hu j) z)
    have hf : Continuous (H i) := by unfold H Ticket tilt; fun_prop
    have hf := t.consume U hM (w i) (show occupied t U (w i) by
        intro j; simp only [w,U,sum_disjSum,sum_singleton,Sum.elim_inl,Sum.elim_inr,souvenir, ← mul_sum]
        have h₁ : _ ≤ t.expense/8 := hx i j
        have h₂ : _ ≤ t.expense/8 := hv (s\i) j
        linarith only [hw j,h₁,h₂]) (fun i _=> hu i) (H i) hf.aestronglyMeasurable (fun i => (he i).le)
    simpa only [he] using hf
  rw [hh,h',integral_finsetSum _ (fun i _ => (hp i).1)]
  exact ⟨integrable_finsetSum _ fun i _ => (hp i).1,sum_le_sum fun i _ => (hp i).2⟩
end YM.AnalyticNext.ConnectedActivity.Plotter
