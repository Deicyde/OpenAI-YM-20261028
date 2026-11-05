import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Lodge


/-!
 Adapted (necessary new cross-Forest support) from accepted E6 Hood.
# complete support relation and capacity of an anchor
Actual dependence on topology and Y and z; inverse windows farther in
than support. Use ALL potential arguments. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {x : Site c} {p : Bond f} {X : Coat T F} {X' : Coat T F'} {a d : ℕ} {η r Q Y : ℝ}
variable {R : Rep G f} {Z Z' : Support c} {k k' : Finset ℕ} {w v : Air f G}

structure Crop (X : Coat T F) (X' : Coat T F') (Z : Support c) : Prop where
  weather : X.x=X'.x
  width : X.width=X'.width
  chi : X.χ=X'.χ
  places (y) (he : y∈Z) : y∈X.seeds.place ↔ y∈X'.seeds.place
  wood (p : Bond f) (hp : atEdge S p∈Z) : (p∈F.trunks ↔ p∈F'.trunks) ∧ F.drape X.Y p=F'.drape X'.Y p
  site y (hp : y∈Z) : X.k.1 y=X'.k.1 y
  bond p (hp : p.1∈Z) : X.k.2 p=X'.k.2 p
  actual : Agrees Z X.V X'.V

structure Clump (X : Coat T F) (X' : Coat T F') (Z : Support c) (w v : Air f G) (k k' : Finset ℕ) (R : Rep G f) : Prop extends
    Crop X X' Z where
  airs (p : Tubular f G) (he : p∈podium S G Z X.B) : w p=v p
  covering (i : Site f) (he : S.ratio.parent i ∈ Z) : i∈Contract.covered R k ↔ i∈Contract.covered R k'


lemma Crop.social (h : Crop X X' Z) (he : Cleanroom Z (a+1) x) : Tuft X X' x a := by
  refine ⟨h.weather,h.width,h.chi,fun y hy=> h.places _ (he y (by omega)),fun i hi=> h.wood i (he _ (le_trans hi (by omega))),
    fun i hi => h.actual i (he _ (le_trans hi (by omega))) ?_, fun y hp=> h.site _ (he y (by omega)),
    fun i hi=> h.bond _ (he _ (by omega))⟩
  exact he _ ((separation_triangle x i.1 _).trans (add_le_add hi (sep_step i.1 i.2)))
lemma Crop.same_cov (h : Crop X X' Z) (hk : Room P S T X.x) (p : Tubular f G) (he : p ∈ podium S G Z X.B) (q) :
    X.relating q p=X'.relating q p := by
  have hp := (mem_filter.mp he).2
  exact (h.social (x:=along S p) (a:=17*X.B) (fun i hi => hp i (hi.trans (by have hx : 100 ≤ X.B := hk.sight.1; omega)))).cL hk p rfl q le_rfl

namespace Clump
variable (h : Clump X X' Z w v k k' R) (hk : Room P S T X.x)
include h
lemma B : X.B=X'.B := congr_arg radiusB h.weather
lemma flame : X.t=X'.t := by unfold t; rw [h.weather]
lemma social (he : Cleanroom Z (a+1) x) : Tuft X X' x a := h.toCrop.social he


include hk
lemma lodge (he : Cleanroom Z (25*X.B) (atEdge S p)) : X.μ p=X'.μ p ∧ X.atmos w p=X'.atmos v p := by
  have hh := h.social (a:=17*X.B) (x:=atEdge S p) (fun i hi=> he i (by have hh : 100≤X.B := hk.sight.1; omega))
  constructor
  · ext i; exact hh.driftL hk (p,i) rfl le_rfl
  ext i; exact h.airs (p,i) (mem_filter.mpr ⟨mem_univ _,he⟩)
lemma house (he : Cleanroom Z (25*X.B) (atEdge S p)) (β : ℝ) : X.liftA β w p=X'.liftA β v p := by
  simp only [liftA,Pi.add_apply,Pi.smul_apply,(h.lodge hk he).1,(h.lodge hk he).2]
lemma quarters (he : Cleanroom Z (25*X.B) (atEdge S p)) : X.input (X.liftA R.beta w) p=X'.input (X'.liftA R.beta v) p := by
  have hr : 100≤X.B := hk.sight.1
  have hh := h.social (a:=12*X.B) (x:=atEdge S p) (fun i hi=> he i (by omega))
  exact (hh.reports p (by unfold distAt; rw [separation_self]; omega) (fun _=> h.house hk he R.beta)).1
lemma coin (he : Cleanroom Z (25*X.B) (atEdge S p)) (β b : ℝ) : X.cone b (X.liftA β w) p=X'.cone b (X'.liftA β v) p := by
  unfold cone; rw [h.chi,h.flame,h.house hk he β]
lemma vale (he : Cleanroom Z (25*X.B) (atEdge S p)) (Ñ : ChartRatio G) (b : ℝ) :
    X.gentry Ñ b (X.liftA R.beta w) p=X'.gentry Ñ b (X'.liftA R.beta v) p := by unfold gentry; rw [h.coin hk he,h.house hk he]

lemma passes (O : Support c) (hc : ∀ i∈O,Cleanroom Z (30*X.B) i) : X.plaza O=X'.plaza O := by
  ext i; simp only [plaza,mem_filter,mem_univ,true_and]; refine and_congr_left fun he=> ?_
  obtain ⟨y,hp,hg⟩ := Finset.not_disjoint_iff.mp he
  have he : 100 ≤ X.B := hk.sight.1
  apply (h.social (x:=y) (a:=14*X.B) (fun j hj => hc y hp j (by omega))).tides i (by have hv:= stride i hg; omega)
lemma enforces (O : Support c) (hc : ∀ i∈O,Cleanroom Z (30*X.B) i) (a : ℝ) :
    X.enforce a (X.liftA R.beta w) (X.plaza O)=X'.enforce a (X'.liftA R.beta v) (X'.plaza O) := by
  unfold enforce; rw [h.passes hk O hc]; apply prod_congr rfl; intro i hi
  obtain ⟨y,hp,hg⟩ := Finset.not_disjoint_iff.mp (mem_filter.mp hi).2.2
  apply h.coin hk (fans (hc y hp) (by have hh := stride i hg; have hz : 100≤X.B:=hk.sight.1; unfold distAt at hh; omega))
end Clump
end YM.ConnectedActivityE6
