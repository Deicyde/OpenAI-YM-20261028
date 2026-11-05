import YM.FullVolume.Fields.Filled
/-!
# Authorization shroud
A purely auxiliary coercion at the measurement base Level 0 to allow
(the many) estimates on higher fitted levels of the admissible history
and kernel, at real parameters. Not our analytic or unmarked representation.
Works at fixed period: send the recipe kinetic adjustment via *full* support regular
words (affine Hessian condition empty) and force terms for complete
bad state (all vacuum evaluations still identical).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Shroud
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Source Labels Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Next.Foundations Push Precision WilsonStartup
open UVNext.CouplingReset UVNext.PricedKernels Ovens Ovens.Pipes Progress.DirectedRecipe BudgetPoint
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} {P:BudgetPoint}{D:PathData G}{c:Clip}{σ C Λ:ℝ}
open MergeProof
namespace Quake
open VerifiedReset.Seat High Low
-- pay witnesses.C input small.Home enlarge
abbrev Worm := Low ⊕ High
variable (D c)
def read (x : Worm)(o:Site n): Config G n→ℝ := x.elim (fun i U=> Low.mark D c i* Low.plain D i o U) (fun i=> High.plain D i o)
local notation "f"=>read D c
variable {p:BudgetPoint} (hd:D.Bounds c σ C Λ)(hp : Decent c p)
def reckon (p:BudgetPoint)(x:Worm): ℝ:= x.elim (fun i=> |i.mark D c| * lowCost G p (Low.length D i) * p.threshold^2) (fun i=> High.price D i p*p.threshold^3)
local notation "w"=> reckon D c p
open Geo
include hd hp
open Work.F03
lemma granted (o:Site n)(x:Worm): p.Regular Finset.univ (read D c x o) ∧ p.supBounds o Finset.univ (read D c x o) (reckon D c p x)∧ read D c x o 1=0:=by
    cases x with
    | inl j=>
       let X:= j.home D p o -- order
       let P:=j.plain D o; let u:=(Sum.inl j:Worm); have h_ : p.Regular (j.home D p o) (Low.plain D j o):=reg_bill (Low.plain_bill D c j o hp) (Low.plain_cont ..).measurable (j.plain_local D p hp.radius o) (j.plain_gauge D o)
       have he:= Bill.mul_left (Low.mark D c j) (j.plain_bill D c o hp)
       have hP := reg_bill (X:=j.home D p o) he (measurable_const.mul h_.borel) (fun U V ht=>congr_arg (_*·) (h_.sites U V ht)) (fun k U=>congr_arg (_*·) (h_.symmetry k U)) -- missing arg
       refine ⟨reg_larger hP (Finset.subset_univ _),sup_larger (sup_le (Bill.sup he (fun _ h=>h)) ?_) (Finset.subset_univ _),?_⟩
       · unfold reckon lowCost; simp only [Sum.elim_inl]; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); exact le_add_of_nonneg_left (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)⁻¹) (pair_nonneg G p))
       simp [read,Low.plain, atSite_path,WilsonStartup.face_one,G.curvature_unit,G.price_one]
    | inr j=>
       have h:= j.fresh_regular D o hd p (-1) 0; have hv:High.fresh D j o (-1) 0=High.plain D j o:=by funext U; simp [High.fresh]
       rw [hv] at h; have hh: p.supBounds o (j.home D o) (High.plain D j o) (j.price D p *p.threshold^3):= Bill.sup (j.paid D o p) (fun _ h=>h)
       exact ⟨reg_larger h (Finset.subset_univ _),sup_larger hh (Finset.subset_univ _), (congr_fun hv.symm 1).trans (j.fresh_one D o (-1) 0)⟩
omit hp
-- Σ series Uniform bound
open Extra.Multi Geo
set_option quotPrecheck false
def possible (G:Gauge)(p:BudgetPoint)(c:Clip)(σ C:ℝ): ℝ:=lowFee G p σ* lowerSize c C *p.threshold^2+ both G p σ*(C+C)*p.threshold^3
lemma tours : SumBudget (reckon D c p) (possible G p c σ C) :=by
    have hs:= hd.width; have hx {ι:Type}{v:ι→ℝ}{s:ι→ℕ}{b:ℝ}(h:SumBudget (fun i=>v i*Real.exp ((σ/2)*s i)) b)(he:∀ i,0≤ v i) (d:ℕ): SumBudget (fun i=> v i * p.threshold^d) (b*p.threshold^d):=by
        have hp:= Extra.Multi.Budget.mono h he (fun i=> le_mul_of_one_le_right (he i) (Real.one_le_exp (mul_nonneg (by linarith only [hs]) (by positivity)))) le_rfl
        have ht:= Extra.Multi.Budget.scale hp (pow_nonneg p.threshold_pos.le d); simp_rw [mul_comm (p.threshold^d)] at ht; exact ht
    have hA:= hx (low_budget G p D hd) (fun i=> mul_nonneg (abs_nonneg _) (low_nonneg ..)) 2; have ht:=hx (high_budget G p D hd) (fun i=> High.price_nn ..) 3
    exact Extra.Iteration.Cost.sum hA ht
include hp
open Push.BetaTransport
variable (hw:Width p c σ)
include hw
lemma replay {U:Config G n}(he: flags p.threshold U=∅) : kinetic D c p U= ∑' i:Seat n×Worm, VerifiedReset.factor * (read D c i.2 (0:Site n)) (Seat.view i.1 U):=by

     let y(i:Worm) := RG.masked p.threshold Finset.univ (read D c i (0:Site n)); have hy {X:Support n}(b:Seat n):Healthy p.threshold X (b.view U):= b.healthy p.threshold X U|>.mp (by rw [Healthy,he]; exact Finset.disjoint_empty_right _)
     have hh (V:Config G n): Summable fun i=> y i V:=by
        apply (tours D c hd (p:=p)|>.2.1).of_norm_bounded
        intro i; unfold y; have hc:= (granted D c hd hp (0:Site n) i).2.1; by_cases h:Healthy p.threshold Finset.univ V; rw [masked_eq _ _ _ _ h]; exact hc.2 V h [] (Nat.zero_le _) (by simp)
        rw [masked_ne _ _ _ _ h,norm_zero]; exact hc.1
     have hx(a:Seat n): (∑' d, y d (a.view U))= (∑' i:Low, Low.live D c i p 0 (a.view U))+(∑' i:High, summit D p i 0 (a.view U)):=by
        rw [((hh (a.view U)).comp_injective Sum.inl_injective).tsum_sum ((hh _).comp_injective Sum.inr_injective)] -- variant orientation
        refine congr_arg₂ (·+·) (tsum_congr fun i=> ?_) (tsum_congr fun i=>?_)
        · exact (masked_eq _ _ _ _ (hy a)).trans (i.live_plain D c hp _ (hy a)).symm
        unfold VerifiedReset.summit; exact (masked_eq _ _ _ _ (hy a)).trans (masked_eq _ _ _ _ (hy a)).symm
     have ht: layer y U= kinetic D c p U:=by rw [← true_base hd hw U]; simp_rw [layer,hx, Finset.sum_add_distrib,mul_add]
     rw [← ht,layer_total _ _ hh]; exact tsum_congr fun i=> congr_arg (_*·) (masked_eq _ _ _ _ (hy i.1))
end Quake
end YM.FullVolume.Shroud
#print axioms YM.FullVolume.Shroud.Quake.granted
#print axioms YM.FullVolume.Shroud.Quake.replay
