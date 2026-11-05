import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Buoy
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tickets


/-!
# Include integral exchange
Back at the very same allocated column. Combine physical inputs, support incidence
remembered. `licenses` rejects entire label family if flags incompatible. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F)

namespace Cash

lemma fair_summable (K : Cash W A μ L Q o C T R) : Summable K.fair := by
  have hA := budgets_arr K
  let u := Sum.inr (α:=ℕ) ∘ Sum.inl (α:=LogIndex c f) (β:=WarningAt c f)
  have hp := hA.comp_injective (Sum.inr_injective.comp Sum.inl_injective : Injective u)
  have he : Summable (fun i=> K.opt (.inl i)) := hA.comp_injective Sum.inl_injective
  exact Summable.sum _ (hasSum_fintype _).summable (Summable.sum _ he (Summable.sum _ hp (hasSum_fintype _).summable))
end Cash

namespace Coat
variable (k : Finset ℕ) (Y : Finset (Stores S)) (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)

include hk K in
theorem uplink (h : X.manifest) (hY : Layout X.seeds Q.halo X.B Y) : Integrable
    (fun i : F.Slice G × Air f G=> (X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y) ((F.order G).prod X.dice) := by
  have hr:= K.laws.data; have hP:= K.laws.intake
  let f' l := X.body R Q.table W o.a k Q.halo (issue Y k l); let g l := ∏ i∈issue Y k l,K.fair i
  have hf (i) : Measurable (f' i) := X.body_b Q.table_exists hP (hk.symm ▸ hr.access) ..
  have hg : Summable g := by
    apply (summable_finsetProd_of_summable_nonneg K.fair_price K.fair_summable).comp_injective
    rintro ⟨a,b⟩ ⟨u,v⟩ hh
    have hi w : blaze (issue Y k w)=w.1 := by simp only [blaze,issue,toRight_disjSum]
    have hu (w : ListsAt c f) : (issue Y k w).toRight.toRight.toLeft=w.2 := by simp only [issue,toLeft_disjSum,toRight_disjSum]
    exact Prod.ext (by rw [← hi (_, _),hh,hi]) (by rw [← hu (_, _),hh,hu])
  have he (i : F.Slice G × Air f G) : (∑' l,f' l i)=(X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y :=
    (luxury (X.wrapY i.1) k K hk h hY i.2).tsum_eq
  have hh : Dominated f' := ⟨g,hg,fun j ⟨a,b⟩ => K.every X rfl hk h k (issue Y k j) a b⟩
  simp_rw [← he]; exact (show Envelope (fun i=> ∑' j,f' j i) from ⟨Measurable.tsum hf,hh.bound⟩).integrable _

/-- Auxiliary signed selection; expand only legitimate incidences. Still
ALLOCATION, same Rep, before disconnected factorization. -/
def approve (X : Coat T F) (l : Finset ℕ) (R : Rep G f) := X.manifest ∧ Contract.sealed R l ∧ Contract.incidence R l X.seeds

def blessing (R : Rep G f) (l : Finset ℕ) (Ñ : ChartRatio G) (W a : ℝ) (m : ℕ) (p : Molecule S) := if X.approve l R then
    ∫ i,X.body R Ñ W a l m p i ∂((F.order G).prod X.dice) else 0

def tribute (R : Rep G f) (Ñ : ChartRatio G) := (Fintype.card S.Choices:ℝ)⁻¹ * X.levy R * X.deducted Ñ R.beta

include K hk in
theorem perK (hY : Layout X.seeds Q.halo X.B Y) :
    HasSum (fun l=> X.tribute R Q.table * X.blessing R k Q.table W o.a Q.halo (issue Y k l))
      (∫ i, X.tangible R W i k ∂F.order G) := by
  have h := K.laws.data
  have hr := K.laws.intake
  by_cases hp : X.approve k R
  · simp_rw [Coat.blessing,if_pos hp]
    convert! (recede X k K hY hp.1 hk).mul_left (X.tribute R Q.table) using 1
    rw [X.shore_tangible k hr h.W_pos h.room.fiery, integral_prod _ (X.uplink k Y K hk hp.1 hY),← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall (fun i=> ?_));
    exact (X.wrapY i).ticket K hp.1 hk k Y hY hp.2.1
  have hF (i) : X.tangible R W i k=0 := by
    by_contra hn; apply hp
    let P:= X.χ.profiles G S X.x W h.W_pos h.room.fiery
    have hu : P.bill X.seeds X.k (F.drape i) X.V≠0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
    have hj : R.activities.gasOccurrence R.p k (F.drape i) ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul hn))
    have hc := Contract.needs hr k P _ _ _ hu hj; rw [Contract.release hr] at hj
    have hs : Seeded X.seeds (F.drape i) X.k X.V X.x W := P.actual _ _ _ _ hu
    exact ⟨hs.exactFlags, (by by_contra hg; exact hj (if_neg hg)),hc⟩
  simp_rw [hF, Coat.blessing, if_neg hp, integral_zero,mul_zero]; exact hasSum_zero

include K hk in
lemma sum_alloc (hY : Layout X.seeds Q.halo X.B Y) : HasSum
    (fun k => X.tribute R Q.table*∑' i,X.blessing R k Q.table W o.a Q.halo (issue Y k i))
    (∫ Y, X.χ.distribute X.seeds X.x W (F.drape Y) X.k X.V*
        (taggedKernel S R.beta X.k (F.drape Y) X.V * R.eval (F.drape Y)) ∂F.order G) := by
  simp_rw [← tsum_mul_left, (X.perK _ Y K hk hY).tsum_eq]; exact
    (X.sum_tangible K.laws.intake K.laws.data.W_pos K.laws.data.room.fiery).2
end Coat
end YM.ConnectedActivityE6
