import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Reframe
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Tune

/-!
 # Barony total and thermal linkage exact. retains every path term.
 public `unearned` split all V; pressure futures before high. No pert mask. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
local notation "D''" => Meadow.studio X.halo B
open Brim Height Refrain
section bay
variable (X' : Match.Alliance I H 1 0) {χ:Chi} (k:ℕ) {p': BudgetPoint} (x:Site c) {γ t v z : ℝ} (hp : Collection.Local (posting p' I) p' (plusone I X' χ γ) t v) (hq : Meadow.Budget p' (Beam.marquee I p').reg (timbres X' (χ:=χ) γ k|>.logRead) z) (hB:p'.B=radiusB p)
-- Local from Collection
lemma regularA {ι:Type} {V:ι→ Config G c→ℝ} {p:BudgetPoint} {X : Support c} (F: Finset ι) (h : ∀ i∈ F,p.Regular X (V i)) : p.Regular X (∑ i∈ F,V i):= by
  induction F using Finset.induction_on with
  | empty=> rw [sum_empty]; exact CouplingShape.reg_const _
  | @insert x F hv ih=> rw [sum_insert hv]; let t:=∑ i∈F, V i; rw [show V x+t=V x-((-1:ℝ) • t) by simp]; exact CouplingShape.reg_sub (h x (Finset.mem_insert_self ..)) (CouplingShape.reg_scale _ (ih (fun i hi=> h i (mem_insert_of_mem hi))))
include X' hp hB
lemma regularW (i:ℕ) (h:i∈panel I k) : p'.Regular (neighbors D'' x) (garnerAt I p' x i • (plusone I X' χ γ).logRead i) := by
  by_cases hF:garnerAt I p' x i=0; · rw [hF,zero_smul]; exact CouplingShape.reg_const _
  have hM:= (assigned I p' x i h hB hF).2; rw [Beam.rewrite_rule] at hM
  exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hp.smooth i) hM)
omit hB
lemma unearned (V:Config G c) :
    (posting p' I|>.read (plusone I X' χ γ)|>.additive p' V) = (Beam.marquee I p'|>.read (timbres X' (χ:=χ) γ k)|>.additive p' V) +
       ∑ i∈Meadow.panel I k, masked p'.threshold ((Beam.marquee I p').reg i).support ((plusone I X' χ γ).logRead i) V:= by
  let t' i:= masked p'.threshold ((Beam.marquee I p').reg i).support ((plusone I X' χ γ).logRead i) V; let h i:=if i∈ Meadow.panel I k then t' i else 0
  let f i:= ((posting p' I).read (plusone I X' χ γ)).regularOccurrence p' i V; let g i:= ((Beam.marquee I p').read (timbres X' (χ:=χ) γ k)).regularOccurrence p' i V
  have he : g=f-h:= by
    funext i; change masked _ _ ((timbres X' (χ:=χ) γ k).logRead i) V=f i-h i; rw [Meadow.compass]; have hh : f i=t' i:= by unfold t'; rw [Beam.rewrite_rule]; rfl
    rw [hh]; unfold h; split
    next hz=> rw [if_pos ((Meadow.petaled I i).2 hz),sub_self]; simp [masked]
    next hz=> rw [if_neg (mt (Meadow.petaled I i).1 hz),sub_zero]; rfl
  have hs: Summable f:= Roof.Embrasure.series _ _ hp V
  have h':HasSum h (∑ i∈ Meadow.panel I k,t' i):=by
    convert hasSum_sum_of_ne_finset_zero (s:= Meadow.panel I k) (f:=h) (fun i hi=> if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
    infer_instance
  have he': (∑' i, g i)= (∑' i, f i)-∑ i∈ Meadow.panel I k,t' i:= by rw [he]; exact (hs.hasSum.sub h').tsum_eq
  change (∑' i,f i)=(∑' i, g i)+_; rw [he',sub_add_cancel]
variable (he:I.supportP=H.supportP) (hX:R'.path=R.path) (hz:X'.units=Equiv.refl _)
include hB he hX hz
lemma regularY : p'.Regular (neighbors D'' x) (Meadow.barony H χ k γ x):= by rw [aster χ p' X' hX he hz γ k]; exact Meadow.regularA _ fun i hi=> regularW X' k x hp hB i hi
omit hB
variable {β v₀ C L E : ℝ} {Y : BudgetPoint}
local notation "λ₀" => (timbres X' (χ:=χ) γ k)
local notation "P₀" => (posting p' I)
lemma chorus (V:Config G c) (hR:R=Pane.virgin T Y β)
    (ht:S.push β R.eval V=earlyValue (P₀) T.down T.low p' (plusone I X' χ γ) β v₀ γ V) (h':T.down.Bounds T.low C L E)
    (hh:flags p'.threshold V=∅): Token.arrayE T Y β γ V= v₀*(Fintype.card (Site c):ℝ)- (∑ x, Meadow.barony H χ k γ x V) - ∑' i, (λ₀).logRead i V:= by
  -- get ht
  let D i:= (λ₀).logRead i V; have hK : ∑ i∈Meadow.panel I k, masked p'.threshold ((Beam.marquee I p').reg i).support ((plusone I X' χ γ).logRead i) V=
      ∑ x, Meadow.barony H χ k γ x V := by
    simp_rw [aster χ p' X' hX he hz γ k, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i hi
    rw [← Finset.sum_mul, Meadow.paysOne,one_mul]; exact masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
  have hx : (Beam.marquee I p'|>.read (λ₀)|>.additive p' V)= ∑' i, D i:= tsum_congr fun i=> masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
  unfold Token.arrayE; rw [← hR,ht]; have hg : ((P₀).read (plusone I X' χ γ)).gas p' V=1:= Activities.gas_one _ _ hh; have hf: Collection.receipt T.down T.low p' V= secondTerm T.low T.down V:= VerifiedReset.allGoodPrice h' V hh
  unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only; rw [hg,mul_one, ← Real.exp_add,Real.log_exp, Pane.crystalline _ _ _ _ _ hh, hf, unearned X' k hp,hK,hx]; change _= _ -∑' i,D i; ring
end bay
end YM.PhysicalNext.Repeat.Meadow
