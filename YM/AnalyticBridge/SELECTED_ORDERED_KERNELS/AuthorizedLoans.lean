import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Finished
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorLie
import YM.Push.STRESS_FLUX.Ward


/-!
# Pay `Higher` too at this scope, hence unconditional (jet-input-wise) Loans

Actual finite BAKE data *when supplied* in a post-L Teller range. Includes
field-dependent shot/guard selection at centre; ordered derivatives on
link fields with shots and A held, exactly as in `Sector`. No additional
assumption on branch/log jets, and no small-field restriction outside the
patches actually queried. NOT a theorem applying before purchasing those
Teller inputs/delays or specifying/scheduling them. Growth and saving
structure in the resulting Loans in `SectorData`, `SectorWindows` etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations
  Rows YM.Pressure YM.Pressure.Stores FreeResolvent Affine TestD Push.Uniform Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {n : ℕ} {C : ℝ}
  {x : ℝ} {A : Stores S} {T U : Forest S.ratio} {k : S.Choices} {V : Config G c}
  {H : Tube G S} {Pt : Teller G}

lemma fund_sheet (hT : Pt.Funds S H) : Sheet H.up Pt.top.width Pt.top.paths := by
  obtain ⟨_,_,h,-⟩ := hT.feeds; exact h.rows

lemma Sharing.higher (h : Sharing x A T U k V (n+1) C) (hC : 0 ≤ C) (hT : Pt.Funds S H) :
    Sector.Higher H x A T k V n (tier Pt.top.width n) (marketFee S.patch G S.kernel H.high Pt.top.width n C Pt.top.paths) := by
  constructor; intro l _ hl
  have hs : S.patch.Branches S.kernel G := hT.knobs ▸ hT.kernel
  have hw := Pt.top.width_pos; have hW := fund_sheet hT
  have hm := h.market_priced hs hw hC Pt.top.paths_pos.le hW (ordering hw n).1.le le_rfl H.high (shorter (till x))
  exact ((hm.compress (attach_inj (x:=x) G A T)).glue (market_chart hs hw.le hW h).symm).bound l hl

/-- `Sector.commissioned` can now be invoiced (not assuming its Higher
from another task); this includes `Sector.piece` and `marginal_force`'s
inverse jet inputs on physical matrices. The underlying log derivatives do
not commute by fiat. All rates/fees common across trees, k, periods satisfying
the size and Funds/patch/temperature requirements. Savings also when x
tends to infinity after L. Not a recipe/L producer. -/
theorem authorized_loans (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) :
    ∃ s M r g : ℝ, 0 < s ∧ 0 ≤ M ∧ 0 < r ∧ 0 < g ∧ ∀ n : ℕ, ∃ t N : ℝ, 0 < t ∧ 0 ≤ N ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (H : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S H →
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
      Sector.Ground H x A F k V s M r g ∧ Sector.Higher H x A F k V n t N ∧ Sector.Query H x A F k V n (min t s) (max M N) r g := by
  obtain ⟨s,M,r,g,hs,hM,hr,hg,h⟩ := Sector.commissioned G P Pt hp
  refine ⟨s,M,r,g,hs,hM,hr,hg,?_⟩; intro n
  obtain ⟨C,hC,h'⟩ := sharing G P Pt.bind hp (n+1)
  let t := tier Pt.top.width n
  let N := marketFee P G Pt.bind Pt.top.clip Pt.top.width n C Pt.top.paths
  have ht : 0 < t := (ordering Pt.top.width_pos n).1
  refine ⟨t,N, ht,market_nn _ _ Pt.top.width_pos hC Pt.top.paths_pos.le,?_⟩
  filter_upwards [h,h'] with x hx hx'
  intro c f S H hS hR hT A F k V hV
  obtain ⟨h1,h2⟩ := hx S H hS hR hT A F k V hV
  have he := (hx' S hS hT.knobs hR A F F k V hV).higher hC hT
  rw [hT.knobs,hT.high,hS] at he
  exact ⟨h1, he, h2 n t N ht he⟩
end YM.SelectedOrderedKernels.Selected
