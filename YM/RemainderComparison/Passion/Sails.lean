import YM.RemainderComparison.Passion.Pulses
/-!
After c.Ap orientation: rooted adjusted logs retain root *unions incl old
connectors*. Both field-mask evaluations (placing literal Section headers or
expanding mask to all carriers) charged. Every induced commission survives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable {σ b c e :ℝ} (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι) (V:Plane G n θ) (X:Hol G)
variable (M:SeatD.MaskType)(i:Roll T R Z D)
local notation "W₀" => mapWord D
local notation "T₀"=> T.marks i.val.val
local notation "P"=> T.halls i.val.val
local notation "v₀"=> p.threshold
local notation "Ra₀"=> Ra T R Z V i
local notation "P₁"=> SeatD.PairD
set_option quotPrecheck false
open SeatD
-- retain an explicit MODE which interprets canonical only once. grants on both; architecture for Θ joint proof.Hit
local notation "J₀" => Roll T R Z D
local notation "F'" => area T R Z V (D:=D)
variable (h: Precepts T p R Z D (p.supportExponent+2) b) (hr: Placed R V D){t:ℕ} (he:AxisG p V X c t e)
open PhysicalNext.Repeat Trio Animals

def shores (B u Power k:ℕ) (σ e : ℝ):= ballCost k * (haloExpense σ k Power u B * e)
local notation "δ"=> shores p.B p.order p.power t p.supportExponent e

structure Lodge (D :ι→Finset θ) (b₀:ℝ): Prop where
    budget : ∃ f:Roll T R Z D→ℝ,(∀ i,0 ≤ f i) ∧ Ac.Hit (Passion.area T R Z V) p.B f (p.supportExponent+1) b₀ ∧ ∀ i,
       (∀ U a, ‖amount T p R Z V X M i a U‖≤3*f i∧ ‖leakage T p R Z V X M i a U‖≤4*f i) ∧
       (∀ a U,U∈ T.halls i.val.val→ p.supBounds U (T.halls i.val.val) (Passion.stem T R Z i a) (f i)) ∧
       (∀ z, Passion.Ra T R Z V i=some z→∀ a U,U∈ area T R Z V i→ Palette p (V.visor z) (T.halls i.val.val) M (PairAt T p R Z V X i a z) U (f i))
local notation "Y"=> fun i:J₀=> T.halls i.val.val
local notation "S"=> p.supportExponent
include h he hr
lemma posted : Lodge T p R Z V X M D (δ*b):=by
    obtain ⟨g,hg,hv,hZ⟩:= Passion.visits T p R Z h; let f i:= traceWeight p (coverNumber p.B (area T R Z V i))*(e*g i)
    have he' : 0≤e:= zero_le_one.trans he.warm; have hΩ i :0 ≤ e*g i:= mul_nonneg he' (hg _)
    have hl i:g i≤f i:=(le_mul_of_one_le_left (hg _) he.warm).trans (le_mul_of_one_le_left (hΩ i) (freight p (coverNumber p.B (F' i))))
    have hf i:0 ≤ f i:= (hg i).trans (hl i)
    let q:= (haloExpense p.supportExponent t p.power p.order p.B * e)
    have hq :0 ≤ q:=by apply mul_nonneg _ he'; exact zero_le_one.trans (gear_pay p t)
    have hm i: budgetF p n (F' i) (f i) ≤ q*(Real.exp ((S+2)*↑(coverNumber p.B (Y i))) * (g i)):=by
        unfold f; rw [mul_comm (traceWeight _ _)]
        apply (renewed p t (Y i) (e*g i) _ (hΩ i) (boarded T p R Z V X i hr he)).trans_eq; unfold q; ring
    refine ⟨f,hf,fun x=> ?_, fun i=> ⟨fun U a=>Passion.bracket T p R Z V X M i a h hr he g hZ U,fun a U h=>VerifiedReset.sup_le (hZ i a U h) (hl i), fun z hz a U hu=> Passion.proof T p R Z V X M i a h hr he g hZ U hu hz⟩⟩
    let X':= Lattice.halo t {x}
    refine budget_of_sum (fun i=> by split; exact mul_nonneg (hf i) (Real.exp_pos _).le; exact le_rfl) (fun I=>?_)
    let a (y:Site n) i:= if y∈Y i then g i*Real.exp ((S+2)*↑(coverNumber p.B (Y i))) else 0
    have hA y i:0≤ a y i:=(hv y).1 i
    refine le_trans (b:= ∑ i∈I,∑ j∈X',q*a j i) ?_ ?_
    · refine sum_le_sum fun i hi=> ?_; split; next hh=>
           obtain ⟨y,hy,hh'⟩:= Passion.spans T p R Z V X i hr he x hh -- shadow X
           apply le_trans (b:=q*a y i) ?_ (single_le_sum (fun j _=> mul_nonneg hq (hA j i)) hh'); unfold a; dsimp only; rw [if_pos hy,mul_comm (g i),mul_comm (f i)]; exact hm i
      next=> exact sum_nonneg (fun j _=>mul_nonneg hq (hA j i))
    rw [sum_comm]; apply le_trans (sum_le_sum (g:=fun _=> q*b) (fun i _=> by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (budget_sum (hv i) I) hq)); rw [Finset.sum_const,nsmul_eq_mul] -- edit
    unfold shores; rw [mul_assoc (↑(ballCost t):ℝ)]; exact mul_le_mul_of_nonneg_right (show (↑(X'.card):ℝ)≤(↑(ballCost t):ℝ) from by exact_mod_cast (neighbors_card t x)) (mul_nonneg hq (budget_nonneg (hv x)))
end YM.RemainderComparison.Passion
