import YM.RG08.Cell.Port

/-!
# Unwrapped flat covariance and tree-slice predictor price
-/
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
set_option autoImplicit false
variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices}

variable {σ θ τ p q : ℝ} {Q : MapPrices} {b b':Bed}

def sliced (P : Patch)(K : KernelChoices)(G : Gauge)(b : Bed): Kernel (Loc G 1) (Loc G 1):= Cell.spread P.L (warm P K G b)
def plotted (P : Patch)(K : KernelChoices)(G : Gauge)(b : Bed): Kernel (Loc G 1) (Loc G 1):= Cell.out (predictor P K G b)

theorem viewed (h:Warm G K P b σ p)(he:0≤σ)(hs:σ≤1)(hc:f.val=c.val*P.L.val) : let S := (StepData.mk P K hc : StepData c f); Matches (sliced P K G b) (NativeLine S G b) ∧ Matches (plotted P K G b) (RootField K G S b) := by
  have hi : f=c*P.L:= Subtype.ext hc; subst f
  refine ⟨release_match (habitat P K c) ?_, out_hall (habitat P K c) ?_⟩
  · have he:=h.bill.seen c; erw [← native_paid]; exact he
  -- h doesn't say 0≤σ for billing; to get predictor select? use rowCost demands require ≥0. add.
  erw [root_read]; exact (predictor_price P K G b h he hs).seen c

theorem bind_gap {α β γ : Type} [Fintype β]{A B:Kernel α β}{W:Kernel β γ}
    (ha : Priced σ p A)(hb:Priced σ p B)(hg:Priced σ q W)(hs:0≤σ) : Pert.Bulk.bind (A-B) W=Pert.Bulk.bind A W-Pert.Bulk.bind B W:= by
  funext x y
  have he (i:β) {S : Kernel α β}(h:Priced σ p S) : Summable fun z:Cover=>S x (z,i)*W (z,i) y := by
    have hp:= (produce_any h.row hg.row hs hs x i y.2).of_norm (f:=fun w:Cover×Cover=> S x (w.1,i)*W (w.1,i) (w.2,y.2))
    exact hp.prod_symm.prod_factor y.1
  change _ = (Pert.Bulk.bind _ _ x y - Pert.Bulk.bind _ _ x y)
  simp only [bind_apply, tagged,Pi.sub_apply,sub_mul,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>?_
  exact Summable.tsum_sub (he i ha) (he i hb)

lemma hot_gap {A : ℝ}(h : Warm G K P b σ p)(ht : Warm G K P b' σ p)(he:0≤θ)(hθ: θ≤σ)(hσ:σ≤1)(hv : Priced θ A (warm P K G b'-warm P K G b)) :
    Priced θ (key G P K*A) (predictor P K G b'-predictor P K G b):=by
  let Q:= swap (probe_receipt P K G)
  let C:= toll_probe P K G
  have hf : Priced θ C Q:= ((probes_on P K G).toPriced.mono (hθ.trans hσ) le_rfl).rear he
  have hp:= (hv.mul hf he).smul K.penalty
  rw [bind_gap (ht.bill.toPriced.mono hθ le_rfl) (h.bill.toPriced.mono hθ le_rfl) hf he, smul_sub,abs_of_nonneg K.penalty_pos.le] at hp
  convert hp using 1
  unfold key; ring
  rfl

/-- Ready to apply under length/delay gates. Difference already at operation-level kernel, not
requiring additional division by pole in the consumer. -/
theorem trays {A B σ θ:ℝ}(h:Warm G K P b σ B)(hT:Warm G K P b' σ B)(hpos:0<θ)(hs:θ≤σ)(hσ:σ≤1)(hk:Priced θ A (warm P K G b' - warm P K G b)) :
 marketBill P.L (sliced P K G b'-sliced P K G b) θ (laneTax P.L*A) ∧ outward (plotted P K G b'-plotted P K G b) P.L θ (laneTax P.L*(key G P K*A)) := by
  have hp := hot_gap h hT hpos.le hs hσ hk
  have hx:=out_bill hpos.le hp
  have hA : (P.L.val:ℝ)^4*Real.exp (4*θ) ≤ laneTax P.L := by unfold laneTax; have ht:=hs.trans hσ; gcongr; linarith
  exact ⟨market_release hk hpos.le (hs.trans hσ), ⟨fun x i=>(hx.row x i).trans (by gcongr; exact hp.pos),fun i x=>(hx.col i x).trans (by gcongr; exact hp.pos), hx.marked⟩⟩
end YM.RG08.Cell
