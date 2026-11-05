import YM.Further.GAUSSIAN_SCALAR_LEDGER.Completion
import YM.SectorNext.VACUUM_NORMALIZATION.Relative
import YM.Work.A05.Window
import YM.Work.B09.Shell


set_option warningAsError false

/-!
# Plugging into the correct sector integral

Fixed output field, Store
(seed/mask address), one shared physical tag, one fixed tree slice. Product Lebesgue only on real COLOR coordinates for non-tree nonfrozen
links. Probability Haar on the held positions. Chart radius may be
chosen separately per record; physical Jacobian calibration must work at
all of those sizes. Includes a bounded curtain, accommodating $γ_e$,
even a hard cutoff at this level. We prove finite-volume integrability
for this formulation before using it. No Taylor, no pointwise positivity
of the proposed R assumed. Does *not* purchase the measure identity or
sector chart sizes or margins.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Function MeasureTheory Filter Set
open Lattice RG Wilson Tree Precision SectorNext.Vacuum Pressure Push.SectorMeasure
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {c f : Side} {S : StepData c f} {r : Ratio c f} {G : Gauge}

section curtain
variable {F : Forest r}

structure Curtain (O : ChartRatio G) (H : Finset F.Free) where
  size : ℝ
  pos : 0 ≤ size
  small : size < O.radius
  read : Standing H → G.Color → ℝ
  borel i : Measurable (read i)
  nonneg i t : 0 ≤ read i t
  top i t : read i t ≤ 1
  off i t : size < ‖t‖ → read i t = 0

/-- Held positions (probability Haar, *not* log coordinates). -/
abbrev Frozen (H : Finset F.Free) (G : Gauge) := ↥H → G.El

def bins (H : Finset F.Free) (G : Gauge) : Measure (Frozen H G) := Measure.pi fun _ => G.probHaar
instance (H : Finset F.Free) : IsProbabilityMeasure (bins H G) := by unfold bins; infer_instance

variable {H : Finset F.Free}

def hue (i : Standing H) (a : VV (Bits G H)) : G.Color := WithLp.toLp 2 (fun j => a (i,j))

lemma hue_meas (i : Standing H) : Measurable (hue (G:=G) i) :=
  (MeasurableEquiv.toLp 2 _).measurable.comp (measurable_pi_lambda _ fun k => measurable_pi_apply (i,k))

/-- Store, V and orientation fixed throughout. Use `replica` in common
positive convention. Use the formula on steps where `replica` is the
desired lift (the API uses c>1 for the crossing interpretation); the
results below are about this formula only. -/
def included (V : Config G c) (h : Frozen H G) (a : VV (Bits G H)) : F.Slice G :=
  fun i => if hn : i∈H then h ⟨i,hn⟩ else G.lieExp (hue ⟨i,hn⟩ a) * replica r V i

lemma included_meas (V : Config G c) :
    Measurable (fun x : Frozen H G × VV (Bits G H) => included V x.1 x.2) := by
  apply measurable_pi_lambda; intro i
  unfold included
  split
  · exact (measurable_pi_apply _).comp measurable_fst
  next he => exact ((G.lieExp_cont.measurable.comp (hue_meas (H:=H) ⟨i,he⟩)).comp measurable_snd).mul measurable_const

variable (O : ChartRatio G) (Z : Curtain O H)

def leafPrice (a : VV (Bits G H)) :=
  ∏ i : Standing H, Z.read i (hue i a) * (O.scale*O.J (hue i a))
def leafRatio (a : VV (Bits G H)) :=
  ∏ i : Standing H, Z.read i (hue i a) * O.J (hue i a)

lemma leaf_order : leafPrice O Z = fun a => O.scale^(nt F-H.card) * leafRatio O Z a := by
  funext a
  unfold leafPrice leafRatio
  simp_rw [mul_left_comm (Z.read _ _) O.scale _, Finset.prod_mul_distrib]
  rw [Finset.prod_const,Finset.card_univ,count_stand]

lemma leaf_bound (hO : LocalRatio O) : Envelope (leafPrice O Z) := by
  rw [leaf_order]
  refine (Envelope.const _).mul ?_
  let B := Metric.closedBall (0:G.Color) Z.size
  have hb : IsCompact B := ProperSpace.isCompact_closedBall ..
  have hr : ContinuousOn O.J B := fun _ he =>
    ((hO.germ _ (Metric.closedBall_subset_ball Z.small he)).continuousAt).continuousWithinAt
  obtain ⟨L,hL⟩ := hb.bddAbove_image hr.norm
  let C : ℝ := max 1 L
  have hk : 0 ≤ C := le_trans zero_le_one (le_max_left ..)
  unfold leafRatio
  refine ⟨Finset.measurable_fun_prod _ (fun i _ =>
    ((Z.borel i).mul hO.borel).comp (hue_meas _)), C ^ Fintype.card (Standing H), fun a => ?_⟩
  have hx (i : Standing H) (x : G.Color) : ‖Z.read i x * O.J x‖ ≤ C := by
    by_cases he : x ∈ B
    · rw [norm_mul,Real.norm_of_nonneg (Z.nonneg ..)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Z.top ..)).trans
        ((hL (mem_image_of_mem _ he)).trans (le_max_right ..))
    have hs : Z.size < ‖x‖ := by simpa [B] using he
    rw [Z.off _ _ hs,zero_mul,norm_zero]; exact hk
  rw [norm_prod]
  exact (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i _)).trans_eq
    (by rw [Finset.prod_const,Finset.card_univ])

lemma leaf_support : support (leafPrice O Z) ⊆ Metric.closedBall 0 Z.size := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg Z.pos]
  rintro ⟨i,j⟩
  have he : ‖hue i x‖ ≤ Z.size := by
    by_contra! hs
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) (show Z.read i (hue i x)*_=0 from by rw [Z.off _ _ hs,zero_mul]))
  exact (PiLp.norm_apply_le (hue i x) j).trans he
end curtain

section weight
variable {F : Forest S.ratio} {H : Finset F.Free} {x W : ℝ} (O : ChartRatio G) (Z : Curtain O H)
  (d : Allocation G S x W) (P : Stores S) (k : S.Choices) (V : Config G c)

def raw (a : F.Slice G) := d.bill P k (F.drape a) V * broad k (F.drape a)

def coupon (L : F.Slice G → ℝ) (h : Frozen H G) (a : VV (Bits G H)) :=
  leafPrice O Z a * (raw d P k V (included V h a) * L (included V h a))

/-- Specify (not assume as a theorem) the physical measure change. Can
be plugged in e.g. with proofs using `LocalRatio.actual` and a theorem
that every positive-bill, positive-likelihood `a` here has its non-H
coordinates on the `read=1` true chart. Cutter-producer responsibility.
No independence when passing to predictor prices. Doesn't ask a Gaussian
or Gram formula itself as an input. -/
def Opened := ∀ L : F.Slice G → ℝ, Envelope L →
    (∫ a, raw d P k V a * L a ∂F.order G) =
       ∫ h, ∫ a, coupon O Z d P k V L h a ∂volume ∂bins H G

lemma raw_env (hm : S.patch.Branches S.kernel G) : Envelope (raw (F:=F) d P k V) := by
  have he := F.continuous_drape (G:=G) |>.measurable
  exact (d.envelope hm he measurable_const P k).mul
    ((Envelope.const _).mul (env_likelihood k hm he))

lemma coupon_env (hm : S.patch.Branches S.kernel G) (hO : LocalRatio O)
    (L : F.Slice G → ℝ) (h : Envelope L) :
    Envelope (fun t : Frozen H G × VV (Bits G H) => coupon O Z d P k V L t.1 t.2) :=
  (Env.along (leaf_bound _ _ hO) measurable_snd).mul
    (Env.along ((raw_env _ _ _ _ hm).mul h) (included_meas _))

private lemma funded {X : Type*} [MeasurableSpace X] [TopologicalSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {F : X → ℝ} {s : Set X} (hs : IsCompact s) (he : support F ⊆ s)
    (hF : Envelope F) : Integrable F μ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs.measure_ne_top
  exact (integrableOn_iff_integrable_of_support_subset he).mp (hF.integrable _)

/-- Need even non-a.e. fibers (holding frozen link values fixed). -/
theorem coupon_cost (hm : S.patch.Branches S.kernel G) (hO : LocalRatio O)
    (L : F.Slice G → ℝ) (h : Envelope L) :
    Integrable (fun a => raw d P k V a * L a) (F.order G) ∧
    Integrable (fun t : Frozen H G × VV (Bits G H) => coupon O Z d P k V L t.1 t.2)
        ((bins H G).prod volume) ∧
    ∀ h, Integrable (coupon O Z d P k V L h) := by
  have hs := coupon_env O Z d P k V hm hO L h
  have he (b : Frozen H G) : support (coupon O Z d P k V L b) ⊆ Metric.closedBall 0 Z.size := by
    intro a hh; exact leaf_support O Z (left_ne_zero_of_mul (mem_support.mp hh))
  refine ⟨((raw_env d P k V hm).mul h).integrable _,
    funded _ (isCompact_univ.prod (ProperSpace.isCompact_closedBall (0:VV (Bits G H)) Z.size))
      (fun p hp => ⟨Set.mem_univ _,he _ hp⟩) hs, fun Y => ?_⟩
  exact funded _ (ProperSpace.isCompact_closedBall ..) (he _) (Env.along hs (measurable_const.prodMk measurable_id))

-- True exponent left after stripping v. `broad` already priced in raw.
def pressureRows (R : Rep G f) (a : F.Slice G) := post R.beta k V (F.drape a) * stripped R (F.drape a)

lemma pressure_env (hm : S.patch.Branches S.kernel G) {σ C Λ δ w : ℝ} {R : Rep G f}
    (hR : R.Lawful σ C Λ δ w) : Envelope (pressureRows (F:=F) k V R) := by
  have he := F.continuous_drape (G:=G) |>.measurable
  have h (i : _) : Envelope (fun a : F.Slice G => G.price (V i * (S.prediction (F.drape a) k i)⁻¹)) := by
    have hy := (measurable_pi_apply i).comp ((S.prediction_meas hm k).comp he)
    refine ⟨G.continuous_price.measurable.comp (measurable_const.mul hy.inv),2, fun x => ?_⟩
    exact (Real.norm_of_nonneg (G.price_range _).1).trans_le (G.price_range _).2
  have hx := (Envelope.const S.kernel.penalty).mul (Envelope.sum Finset.univ _ h)
  exact (hx.neg.mul (Envelope.const R.beta)).exp.mul
    (Env.along ((Envelope.const _).mul (R.envelope hR)) he)

lemma press (hm : S.patch.Branches S.kernel G) {σ C Λ δ w : ℝ}
    {R : Rep G f} (hR : R.Lawful σ C Λ δ w) (ho : Opened O Z d P k V) :
    balance d F R.beta (stripped R) P k V =
      ∫ h, ∫ a, coupon O Z d P k V (pressureRows k V R) h a ∂volume ∂bins H G := by
  rw [← ho _ (pressure_env k V hm hR)]
  unfold balance; simp_rw [pressureRows, raw, smul_eq_mul, mul_assoc]

end weight
end YM.Further.GaussianScalar
