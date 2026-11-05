import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Manifesto

/-!
# Back to the actual push step (pre fluctuation reset)

One true probability Haar, K gauge/branch arrays common. F held even
in scalar correction; no reselection. Ξ all expanded with preserved labels/cuts.
Normalize extensive scalar separately from hit; this step does **not** commit
a regrouped history with log, nor show history stability/symmetries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Matter
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {p : Molecule S} {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F)

def overhead (X : Coat T F) (R : Rep G f) (Ñ : ChartRatio G) := X.levy R * X.deducted Ñ R.beta

def Packed (S : StepData c f) := Stores S × (Finset ℕ × ListsAt c f)

def crew (T : StepData c f) (l b : ℕ) (p : Packed T) : Molecule T := issue (Layout.rolls p.1 l b) p.2.1 p.2.2

def obtainBack (p : Molecule S) : Packed S := (roster p,own p,(p.toRight.toRight.toRight,p.toRight.toRight.toLeft))

lemma deposit (z : Packed S) : obtainBack (crew S l b z)=z := by
  rcases z with ⟨i,k,q⟩
  let p:= crew S l b ⟨i,k,q⟩
  have hx : p.toLeft=Layout.rolls i l b := Finset.toLeft_disjSum ..
  have he : Layout i l b p.toLeft := hx.symm ▸ Layout.enlists ..
  unfold obtainBack; rw [branches p he]; simp only [own,crew,issue,toRight_disjSum,toLeft_disjSum,Prod.mk.eta]

lemma recovery (h : Layout (roster p) l b p.toLeft) : crew S l b (obtainBack p)=p := by
  unfold crew obtainBack; dsimp only; rw [← Layout.roots_equal h]; unfold issue own
  ext i; rcases i with i|i|i|i <;> simp

section prep
variable (H : Cash W X.x μ L Q o C T R) (he : X.width=o.K)
include H he

lemma taxable (s : Molecule S) (l : Finset ℕ) (Z : Coat T F) (h : Z.x=X.x) (hk : Z.width=X.width) :
    ‖Z.blessing R l Q.table W o.a Q.halo s‖ ≤ ∏ i∈s,H.text i := by
  unfold blessing; split
  next hZ => exact (norm_integral_le_integral_norm _).trans (H.statements Z h (hk.trans he) hZ.1 l s)
  rw [norm_zero]; exact prod_nonneg fun i _=> H.positive i

omit H he in
lemma visitsM (j : Stores S) (k : S.Choices) (Ñ : ChartRatio G) (R : Rep G f) :
    overhead ((preps X j).taggedL k) R Ñ=overhead X R Ñ := by unfold overhead levy deducted; rw [neutral _ X (show _=_ from rfl)]; rfl

def people (s : Molecule S) (k : S.Choices) :=
    let Y := roster s
    let p:=(preps X Y).taggedL k
    p.tribute R Q.table * p.blessing R (own s) Q.table W o.a Q.halo s

lemma incomeK (j : Stores S) (k : S.Choices) :
    let Y:= (preps X j).taggedL k
    let g (s : Finset ℕ × ListsAt c f) := people (R:=R) (Q:=Q) (o:=o) X (crew S Q.halo X.B (j,s)) k
    HasSum g (∫ y, Y.χ.distribute j Y.x W (F.drape y) k X.V *(taggedKernel S R.beta k (F.drape y) X.V * R.eval (F.drape y)) ∂F.order G) := by
  intro Y g
  let V:= Layout.rolls j Q.halo X.B
  have hc (s : Finset ℕ × ListsAt c f) : obtainBack (crew S Q.halo X.B (j,s))=(j,s) := deposit (S:=S) _
  have hv (p : Finset ℕ × ListsAt c f) : g p= Y.tribute R Q.table*Y.blessing R p.1 Q.table W o.a Q.halo (issue V p.1 p.2) := by
    unfold g people; dsimp only; rw [show roster _ = j from congr_arg Prod.fst (hc p), show own _ = p.1 from congr_arg (fun i : Packed S=> i.2.1) (hc p)]; rfl
  have hs : Summable H.text := Summable.sum _ (hasSum_fintype _).summable (budgets_arr H)
  have ht : Summable g := by
    apply Summable.of_norm_bounded (g:=fun p => ‖Y.tribute R Q.table‖*(∏ i∈crew S Q.halo X.B (j,p),H.text i)) ?_
    · intro i; rw [hv,norm_mul]; exact mul_le_mul_of_nonneg_left (taxable X H he (crew S Q.halo X.B (j,i)) _ Y rfl rfl) (norm_nonneg _)
    apply Summable.mul_left; apply (summable_finsetProd_of_summable_nonneg H.positive hs).comp_injective
    intro s t hk; exact congr_arg Prod.snd ((hc s).symm.trans ((congr_arg obtainBack hk).trans (hc t)))
  convert! ht.hasSum using 1
  rw [ht.tsum_prod]
  simp_rw [hv, (Y.perK _ V H he (Layout.enlists j Q.halo X.B)).tsum_eq]; exact
    ((Y.sum_tangible H.laws.intake H.laws.data.W_pos H.laws.data.room.fiery).2.tsum_eq).symm

omit H he in
lemma distributed (s : Packed S) :
    let T := crew S Q.halo X.B s
    ∑ k:S.Choices, people (R:=R) (Q:=Q) (o:=o) X T k = overhead X R Q.table * receiptM R X W o.a Q.halo Q.table T := by
  intro z'; let Y := preps X (roster z'); let a:= overhead X R Q.table; let b : ℝ := Fintype.card S.Choices
  have he' k : (Y.taggedL k).tribute R Q.table=b⁻¹*a := by
    rw [← show overhead (Y.taggedL k) R Q.table=a from visitsM X _ k _ R]
    unfold b overhead tribute; ring
  have hg : roster z'= s.1 := congr_arg Prod.fst (deposit (l:=Q.halo) (b:=X.B) s)
  have hz : Layout (roster z') Q.halo X.B z'.toLeft := by
    rw [hg, show z'.toLeft=Layout.rolls s.1 Q.halo X.B from toLeft_disjSum ..]; exact Layout.enlists ..
  by_cases ht' : Y.approve (own z') R
  · simp only [receiptM, if_pos (show (preps X _).approve (own z') R∧Layout .. from ⟨ht',hz⟩)];
    have hx k : people (R:=R) (Q:=Q) (o:=o) X z' k=(b⁻¹*a)*(Y.taggedL k).attains R Q.table W o.a (own z') Q.halo z' := by
      rw [← he' k]; exact congr_arg ((Y.taggedL k).tribute R Q.table * ·) (show (Y.taggedL k).blessing R (own z') Q.table W o.a Q.halo z'= _ from if_pos (show (Y.taggedL k).approve (own z') R from ht'))
    simp_rw [hx,← Finset.mul_sum];
    change _ = a*(b⁻¹* _); ring_nf; rfl
  have hv k : people (R:=R) (Q:=Q) (o:=o) X z' k=0 := by unfold people blessing; dsimp only; rw [if_neg (show ¬(Y.taggedL k).approve (own z') R from ht'),mul_zero]
  unfold receiptM; dsimp only; rw [if_neg (fun h=> ht' h.1),mul_zero]; simp_rw [hv,sum_const_zero]
end prep
end YM.ConnectedActivityE6.Matter
