import YM.Primitives.SMALL_FIELD_EXTERIOR.HaarCoin
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting
import YM.Work.F05.Measure

/-!
# Use the actual log chart inside the tree slice

Keep the event `shed`: a choice of compact box in LOG space relative
to this background/coarse root. This is an exact localization on the
Haar tree integral, not assumed to agree with any of the Stencils/Frozen
cuts. Includes Jacobian of probability Haar; no access to derivatives
of a hard mask required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior.Forestage
open Function Set Filter Metric MeasureTheory Matrix
open Lattice Precision Wilson RG Tree Push.Uniform HaarCoin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ENNReal Classical

variable {G : Gauge} {c f : Side} {g : Ratio c f} (B : Forest g) {P : ChartRatio G} {r R m k : ℝ}

def roof (G : Gauge) (x : Positions (Primary c G)) : Config G c := represent (tint G _ x)

def convertSlice (B : Forest g) (x : Positions (Primary c G)) (y : Positions (Key B G)) : B.Slice G :=
  Work.F05.exposure B (tint G _ x) (tint G _ y)

def shed (x : Positions (Primary c G)) (r : ℝ) : Set (B.Slice G) := convertSlice B x '' (SmallFieldExterior.cube (Key B G) r)

lemma convertSlice_cont (x : Positions (Primary c G)) : Continuous (convertSlice B x) :=
  (Work.F05.exposure_continuous B).comp (f:=fun y => (tint G _ x,tint G _ y)) (continuous_const.prodMk (tint G _).continuous)



def coin (P : ChartRatio G) (x : Positions (Key B G)) := Work.F05.load B P (tint G _ x)
lemma coin_exp (h : HaarCoin.Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) (x : Positions (Key B G)) (hx : x∈cube _ r) :
    coin B P x=Real.exp (-HaarCoin.dues P B.Free x) := by
  unfold coin Work.F05.load dues wag taxes
  rw [Finset.sum_apply,← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have he := picked x i
  have hh := h.stays (pick G i x) (pick_mem h hr hp _ hx _)
  simp only [Function.comp_apply,neg_neg, he] at *
  exact (Real.exp_log (h.levy.trans_le hh)).symm
lemma coin_floor (h : HaarCoin.Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) (x : Positions (Key B G)) (hx : x∈cube _ r) :
    m ^ Fintype.card B.Free ≤ coin B P x := by
  have ht (i : B.Free) : m ≤ P.scale * P.J ((tint G _ x) i) := h.stays (pick G i x) (pick_mem h hr hp _ hx i)
  unfold coin Work.F05.load
  rw [← Finset.card_univ (α:=B.Free), ← Finset.prod_const]; exact Finset.prod_le_prod (fun _ _ => h.levy.le) fun i _ => ht i
lemma coin_meas (h : LocalRatio P) : Measurable (coin B P) := by
  unfold coin Work.F05.load; refine Finset.measurable_fun_prod _ (fun i _ => measurable_const.mul (h.borel.comp ?_))
  exact ((continuous_apply i).comp (tint G _).continuous).measurable

def taxMeasure (P : ChartRatio G) (r : ℝ) := (volume.restrict (cube _ r)).withDensity (fun x => ENNReal.ofReal (coin B P x))

lemma preservation (h : HaarCoin.Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) (x : Positions (Primary c G)) :
    MeasurePreserving (convertSlice B x) (taxMeasure B P r) ((B.order G).restrict (shed B x r)) := by
  let F := convertSlice B x
  let I := cube (Key B G) r
  let A := taxMeasure B P r
  have hc := convertSlice_cont B x
  refine ⟨hc.measurable,?_⟩
  have he (s : Set (B.Slice G)) (hs : IsClosed s) : ((B.order G).restrict (shed B x r)) s=(A.map F) s := by
    let J := F ⁻¹' s ∩ I
    have hJ : IsCompact J := (cube_compact r).inter_left (hs.preimage hc)
    have hI : s ∩ (shed B x r) = F '' J := by
      change s ∩ F '' I = F '' (F ⁻¹' s ∩ I)
      rw [inter_comm (F ⁻¹' s), image_inter_preimage]; exact inter_comm ..
    rw [Measure.restrict_apply hs.measurableSet, hI, Measure.map_apply hc.measurable hs.measurableSet]
    unfold A taxMeasure
    have hm : MeasurableSet (F ⁻¹' s) := hc.measurable hs.measurableSet
    rw [withDensity_apply _ hm, Measure.restrict_restrict hm]
    change (B.order G) ((Work.F05.exposure B (tint G _ x) ∘ tint G B.Free) '' J) = ∫⁻ a in J, _
    let L := tint G B.Free
    have hy : L '' J ⊆ Work.F05.parcel B P := by
      rintro _ ⟨y,hy,rfl⟩ i _; exact h.fits (pick_mem h hr hp y hy.2 i)
    rw [Set.image_comp, Work.F05.order_exposed B h.paid _ _ (hJ.image L.continuous) hy]
    let Y := YM.Next.SectorChange.tape (G:=G) (ι:=B.Free)
    change (∫⁻ a in Y '' J, ENNReal.ofReal (Work.F05.load B P a)) = ∫⁻ a in J, ENNReal.ofReal (Work.F05.load B P (Y a))
    exact (by
      have hx := (YM.Next.SectorChange.tape_volume (G:=G) (ι:=B.Free)).setLIntegral_comp_preimage_emb Y.measurableEmbedding
        (fun a => ENNReal.ofReal (Work.F05.load B P a)) (Y '' J)
      change (∫⁻ a in Y ⁻¹' (Y '' J), ENNReal.ofReal (Work.F05.load B P (Y a))) = _ at hx
      rw [Y.injective.preimage_image] at hx; exact hx.symm)
  apply Eq.symm; refine ext_of_generate_finite _ ?_ isPiSystem_isClosed he (he _ isClosed_univ)
  exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed

lemma uses (h : HaarCoin.Stamp P R m k) (hr : 0 ≤ r) (hp : r ≤ R) (x : Positions (Primary c G))
    (b : B.Slice G → ℝ) (hi : IntegrableOn b (shed B x r) (B.order G)) :
    (∫ y in shed B x r,b y ∂B.order G)= ∫ v in cube _ r, coin B P v * b (convertSlice B x v) := by
  have ht := preservation B h hr hp x
  rw [← ht.map_eq, integral_map ht.measurable.aemeasurable (ht.map_eq.symm ▸ hi.1)]
  unfold taxMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (coin_meas B h.paid |>.ennreal_ofReal) (Eventually.of_forall fun _ => by simp)]
  apply setIntegral_congr_fun (cube_meas _); intro y hy
  simp only [smul_eq_mul,ENNReal.toReal_ofReal ((pow_pos h.levy _).le.trans (coin_floor B h hr hp y hy))]
end YM.Primitives.SmallFieldExterior.Forestage
