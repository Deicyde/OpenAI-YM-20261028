import YM.FullVolume.Shroud.Seeds
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Shroud
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Source Labels Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Next.Foundations Push Precision WilsonStartup
open UVNext.CouplingReset UVNext.PricedKernels Ovens Ovens.Pipes Progress.DirectedRecipe BudgetPoint Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} {P:BudgetPoint}{D:PathData G}{c:Clip}{σ C Λ:ℝ}
open MergeProof
namespace Quake
open VerifiedReset.Seat High Low
-- Keep support exact and oriented E full. no packing economical needed.
abbrev Graft (n:Side):Type := VerifiedReset.Seat n × Worm
local notation "Z"=> (0:Site n)
lemma everywhere (s:VerifiedReset.Seat n):s.spread Finset.univ=Finset.univ:= by
    ext x; refine ⟨fun _=> Finset.mem_univ _,fun _=>?_⟩; obtain ⟨t,ht⟩:= (Push.Local.turnSites s.1 s.2).surjective x; exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,ht⟩
variable (D c) {p:BudgetPoint}(hd:D.Bounds c σ C Λ)(hp: Decent c p)
def herb (i:Graft n): RegularAddress n:= ⟨i.1.2,Finset.univ,Finset.mem_univ _⟩
def grain (t:ℝ)(x:Graft n): Config G n→ℝ:= (t*VerifiedReset.factor) • ((read D c x.2 Z) ∘ x.1.view)
def costs (G:Gauge)(n:Side)(p:BudgetPoint)(v:ℝ)(c:Clip)(σ C:ℝ) := Real.exp (p.supportExponent* (coverNumber p.B (Finset.univ : Support n))) * ((|v*VerifiedReset.factor| * Collection.turnFee p)*(Fintype.card (VerifiedReset.Seat n)*(possible G p c σ C)))
open Geo
include hd hp
lemma honorary (t:ℝ): ∃ b:Graft n→ℝ,(∀ x : Graft n,p.Regular (herb x|>.support) (grain D c t x) ∧ p.supBounds (herb x|>.site) (herb x|>.support) (grain D c t x) (b x)∧grain D c t x 1=0) ∧ SumBudget (fun i=> p.mass (Finset.univ : Support n) (b i)) (costs G n p t c σ C):=by
    let τ:=|t*VerifiedReset.factor| *Collection.turnFee p
    let k:= reckon D c p; let f i:=τ*k (i:Graft n).2; have ha:0 ≤ τ:=mul_nonneg (abs_nonneg _) (turnFee_pos _).le
    have hp₁(x:Graft n):p.Regular Finset.univ (grain D c t x)∧p.supBounds x.1.2 Finset.univ (grain D c t x) (f x)∧ grain D c t x 1=0:=by
       obtain ⟨hv,h,hK⟩:= granted D c hd hp Z x.2; have hz: x.1.spread Finset.univ=Finset.univ:=everywhere _
       have he:= Seat.sup x.1 hv h; have hf:= Seat.regular x.1 hv; rw [hz] at he hf; refine ⟨CouplingShape.reg_scale _ hf,VerifiedReset.sup_le (CouplingShape.sup_scale _ he) (le_of_eq ?_),?_⟩
       · exact (mul_assoc _ _ _).symm
       unfold grain; simp only [Pi.smul_apply, smul_eq_mul]; have hx:x.1.view (1:Config G n) = 1:=by unfold VerifiedReset.Seat.view; funext i; unfold pull Step.read;split <;>simp
       simp [Function.comp_apply,hx,hK]
    refine ⟨f,hp₁,?_⟩; let E:= p.supportExponent* (coverNumber p.B (Finset.univ : Support n)); let y (j:Graft n):=k j.2
    have he:= tours D c hd (p:=p); have hz: Summable y:=by apply (summable_prod_of_nonneg _).mpr; exact ⟨fun i=> he.2.1, Summable.of_finite⟩; exact fun x=> he.1 _
    have ht: SumBudget y (Fintype.card (Seat n)*(possible G p c σ C)):=by
       refine ⟨fun i=> he.1 _,hz,?_⟩; rw [hz.tsum_prod]; rw [tsum_fintype]; change ∑ _ : Seat n, (∑' i,k i) ≤ _; rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_left he.2.2 (by positivity)
    exact Extra.Multi.Budget.scale (Extra.Multi.Budget.scale ht ha) ((Real.exp_pos E).le) -- univ mass target.side implicit p
variable (hw:Width p c σ)
include hw
lemma withherb (t:ℝ)(V:Config G n):
     (∑' x:Graft n, RG.masked p.threshold (herb x|>.support) (grain D c t x) V)=if flags p.threshold V=∅ then t*BetaTransport.kinetic D c p V else 0:=by
    split;next h=>
       rw [replay D c hd hp hw h,← tsum_mul_left]; apply tsum_congr; intro i; rw [masked_eq _ _ _ _ (by rw [Healthy,h]; exact Finset.disjoint_empty_right _)]; unfold grain; simp only [Pi.smul_apply, smul_eq_mul,Function.comp_apply,mul_assoc]
    next h=> exact (tsum_congr (fun i=> masked_ne _ _ _ _ (show ¬Healthy p.threshold (herb i|>.support) V from fun hx=> h (Finset.eq_empty_iff_forall_notMem.mpr (fun x ht=> Finset.disjoint_left.mp hx (Finset.mem_univ _) ht))))).trans tsum_zero
omit hd hp hw
lemma nonwrap (x:Site n) (h:4 ≤ n.val): ¬ Nonwrapping (Finset.univ : Support n) x:=by
    let t:= n.val/2; let p':Cover:=fun _=> (t:ℤ); let i:= wrap n p'+x; have hk : i-x = wrap n p':=add_sub_cancel_right ..
    have hv: Lattice.lift (i-x) = p':= lift_eq_iff.mpr ⟨hk,fun _=> by dsimp only [p',t]; omega⟩; have ht:t≤ separation i x:=by simpa [hv,p',separation] using component_le (i-x) timeAxis
    intro hp; have hp:= hp i (Finset.mem_univ _); unfold t at ht; omega
end Quake
end YM.FullVolume.Shroud
#print axioms YM.FullVolume.Shroud.Quake.withherb
#print axioms YM.FullVolume.Shroud.Quake.nonwrap
#print axioms YM.FullVolume.Shroud.Quake.honorary
