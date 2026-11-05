import YM.Further.DENSE_MIXED_KERNELS.Frost
import YM.Further.DENSE_MIXED_KERNELS.Tarpaulin

/-!
# Sample with the real tag normalization in Workable.earns

Denotes exactly a Word pre identity, even for ANY fixed settlement/V.
Use when coding the first-system mark terms, one actual seed pack
letter in β. Must still preserve sector tables when generating F.
Having these formulas on their own does not establish the ``log matches''
or that restoring/wrapping in this grammar preserves the steps.
The packed address test CAN use this on the full aggregated
choice containing all markers of a connected X at a Throng Y.
Proofs here include one term with the entire input masked exponential
and all unmarked K-compatible completions at J. Not applying to
smaller connected regions through any assumption of terms vanishing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona Overlay Extra.Multi Labels Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical NNReal ENNReal
variable {c f : Side} {G : Gauge} {A : ChartRatio G} {H : Port A}
    {S : StepData c f} {F : Forest S.ratio} {x W γ σ σ' C C' Λ Λ' δ δ' w w' : ℝ}
    {R : Rep G f} {T : Tube G S} {V α β : Type} [DecidableEq V] {L : Census V}
namespace Throng
variable {X : Chain (α⊕β)} (D : Bands L R) (ρ : α→Pieces) (F : Forest S.ratio) (H : Port A)
    (K : Allocation G S x W) (Y : Stores S) (P : Rep G c) (l : ℝ) (J : Finset ℕ) (o : X.Index)

open Frost
/-- One kernel-letter tallies all the sector/density defects.
Placement i=o must be a vac (unmarked address) chosen for the appropriate
Store. All regular/forced marks factored into `cast`. J marks the owned gas
**labels of D**. No pricing assertion in data. -/
def brand : Word H F X D ρ := {
  model := Frost.view F H
  beacon := fun _ _ _ _ _ _ => mem_union_right _ (mem_univ _)
  initial := fun i V p => if i=o then
    Throng.weight K Y P R l J p.1.1 (F.drape (all F H p.1)) V else 1 }

lemma branded (g : ℝ) (V) (p) : (brand D ρ F H K Y P l J o).pre g V p = ink D X ρ (F.drape (all F H p.1)) *
    Throng.weight K Y P R l J p.1.1 (F.drape (all F H p.1)) V := by
  change ink _ _ _ ((view F H).config V g p) * _ = _
  rw [shared]; simp only [brand,prod_ite_eq',mem_univ,↓reduceIte]

variable {l} {e : Pieces → ℝ} (h : Throng Y x) (hr : R.Lawful σ C Λ δ w) (hp : P.Lawful σ' C' Λ' δ' w')
    (hb : 0≤ R.beta) (hT : Throng.Fits T P R x) (hm : S.patch.Branches S.kernel G) (ht : PointCharge T x W γ)
    (hw : 0≤w) {m : ℝ} (he : 0≤m) (hy : l≤m)

section meas
include hm hr
lemma hold_weigh (V : Config G c) (l : ℝ) : Measurable (fun k : Keyed S × F.Slice G => Throng.weight K Y P R l J k.1 (F.drape k.2) V) := by
  apply measurable_from_prod_countable_right
  intro i
  have hF : Measurable (fun k : F.Slice G => K.bill Y i.key (F.drape k) V * Keyed.card S * taggedKernel S R.beta i.key (F.drape k) V *
      Real.exp (R.exponent (F.drape k))) := by
    exact ((((K.envelope hm F.continuous_drape.measurable (V:=fun _ => V) measurable_const _ _).meas.mul measurable_const).mul
      ((env_tagged R.beta _ hm F.continuous_drape.measurable (V:=fun _ => V) measurable_const).meas)).mul
      ((R.exponentEnv hr).exp.meas.comp F.continuous_drape.measurable))
  exact Complex.continuous_ofReal.measurable.comp ((hF.div measurable_const).mul
    ((env hr J).meas.comp F.continuous_drape.measurable))
end meas

include h hr hp hb hT hm ht hw he hy



-- Relative to selected **literal** gas column weights. Genuine φ integrand before any visit.
omit h hr hp hb hT hm ht hw he hy in
def ticket (D : Bands L R) (X : Chain (α⊕β)) (ρ : α → Pieces) (J : Finset ℕ) (U : Config G f) : ℂ :=
    ↑(Real.exp (R.exponent U) * waiting R J U) * ink D X ρ U

omit h hp hb hT hm ht he hy hw in
theorem ticket_env {z : ℝ} (hI : D.Active) (hk : Inbox D z e) (hZ : z ≤ 1) : Envelope (ticket D X ρ J) := by
  let y := ((R.exponentEnv hr).exp.mul (env hr J))
  have hh : Envelope (ink D X ρ) := ⟨ink_meas D X ρ hI,_, ink_bound D X ρ hI hk hZ⟩
  have heq : ticket D X ρ J = (fun x => (Real.exp (R.exponent x) * waiting R J x) • ink D X ρ x) := funext fun x => by rw [ticket,Complex.real_smul]
  rw [heq]; exact Env.scale y hh

theorem travels {z : ℝ} (g : ℝ) (V : Config G c) (hI : D.Active) (hk : Inbox D z e) (hZ : z ≤ 1) :
    Integrable ((brand D ρ F H K Y P l J o).pre g V) (((brand D ρ F H K Y P l J o).model.base V).ante (brand D ρ F H K Y P l J o).model.fare) ∧
      base S P R l V • ((brand D ρ F H K Y P l J o).value g V) = (oneWord X) • output K F R.beta (ticket D X ρ J) Y V := by
  -- Apply boarding and unwrap all free tags. Use nonzero Base, canonical fixed at P not forecast.
  let φ (a : Keyed S × F.Slice G) := ink D X ρ (F.drape a.2) * Throng.weight K Y P R l J a.1 (F.drape a.2) V
  let M := (Keyed.primary S).prod (F.order G)
  have hφ : Measurable φ := ((ink_meas D _ _ hI).comp (F.continuous_drape.measurable.comp measurable_snd)).mul (hold_weigh F K Y P J hr hm _ _)
  let c := Real.exp ((booked S.patch σ C Λ δ w σ' C' x m R.beta R.p - R.beta*(γ*(fiery G x S.patch.L)^2))*Y.shares)
  have Hφ : Integrable φ M := Integrable.of_bound hφ.aestronglyMeasurable ((∏ i,metric ρ e (X.2 i))*c) (Eventually.of_forall fun k => by
    unfold φ; rw [norm_mul]
    refine mul_le_mul (ink_bound D X ρ hI hk hZ _) (owes K Y hr hp hb hT hm ht hw h he hy ..) (norm_nonneg _)
      ((norm_nonneg _).trans (ink_bound D X ρ hI hk hZ (F.drape k.2))))
  let B := base S P R l V
  have hh := boarding F H V
  have hQ : (brand D ρ F H K Y P l J o).pre g V=φ ∘ (drop F H ∘ Prod.fst) := by ext1 p; exact branded ..
  refine ⟨hQ ▸ hh.integrable_comp_of_integrable Hφ,?_⟩
  unfold Word.value; rw [hQ,smul_comm (base S P R l V)]
  apply congr_arg (fun a : ℂ => oneWord X • a)
  have H := (integral_map hh.aemeasurable hφ.aestronglyMeasurable).symm; rw [hh.map_eq] at H
  refine Eq.trans (congr_arg (fun g : ℂ => B • g) H) ?_
  change B • (∫ k,φ k ∂ (Keyed.primary S).prod (F.order G))=_
  rw [integral_prod φ (show Integrable φ ((Keyed.primary S).prod (F.order G)) from Hφ)]
  let y := ticket D X ρ J
  let f := through S F R.beta V (fun _ x => y (F.drape x))
  let P' := K.portion Y F V f
  have hi (i) : Integrable (P' i) (F.order G) := K.portion_integrable hm Y F V f i (through_integrable F R.beta V _ hm i
    (Env.integrableX (Env.along (F:=ticket D X ρ J) (g:=F.drape) (ticket_env D ρ J hr hI hk hZ) F.continuous_drape.measurable) _))
  change B • _=tagTotal F P'
  rw [(Keyed.holds S F P' hi).1,← integral_smul]
  apply integral_congr_ae; filter_upwards with i
  rw [← integral_smul]
  apply integral_congr_ae; filter_upwards with x
  unfold φ P' Throng.weight Throng.toll Allocation.portion f through y ticket; simp only [B,Complex.real_smul, Complex.ofReal_mul,Complex.ofReal_div]
  have hb := stable S P R l V; field_simp [hb.ne']
end Throng
end YM.Further.DenseMixedKernels
