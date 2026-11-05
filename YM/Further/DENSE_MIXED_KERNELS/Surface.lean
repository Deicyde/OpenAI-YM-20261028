import YM.Further.DENSE_MIXED_KERNELS.Drape
import YM.Further.DENSE_MIXED_KERNELS.Marginal


/-!
# Marginal on **one** tag/parameter ensemble and its shifted copy

No ι-fold resampling.

Length of the held word can change
both index sets; no product formula for the covariance across different
pieces of a single word is used.

Measurable operations for each committed
choice V, even when using off-support data to implement the marginal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

section Sharing
variable {Ω X Y : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]

lemma readings (μ : Measure Ω) (ν : Measure X) [SFinite ν] {f : Ω × X → ℝ≥0∞} (h : Measurable f)
    {φ : Ω × X → ℝ≥0∞} (hh : Measurable φ) : (∫⁻ x,φ x ∂(μ.prod ν).withDensity f) =
      (∫⁻ i, ∫⁻ x,φ (i,x) ∂ν.withDensity (fun x => f (i,x)) ∂μ) := by
  rw [lintegral_withDensity_eq_lintegral_mul _ h hh,lintegral_prod _ (h.mul hh).aemeasurable]
  refine lintegral_congr fun i => ?_
  rw [lintegral_withDensity_eq_lintegral_mul ν (show Measurable (fun x : X => f (i,x)) from h.comp measurable_prodMk_left)
    (show Measurable (fun x:X => φ (i,x)) from hh.comp measurable_prodMk_left)]; rfl

/-- Fiberwise map; restrict the domain on **these same** tags, positions,
and any unused integration variables. -/
lemma apply_fibers (μ : Measure Ω) (ν : Measure X) (ν' : Measure Y) [SFinite ν] [SFinite ν']
    (f : Ω × X → Y) {s : Set (Ω × X)} (he : Measurable f) (hs : MeasurableSet s)
    {k : Ω × X→ℝ≥0∞} (hk : Measurable k) {k' : Ω × Y→ℝ≥0∞} (hk' : Measurable k')
    (ht : ∀ y : Ω, Measure.map (fun x => f (y,x)) ((ν.withDensity (fun x => k (y,x))).restrict {x | (y,x)∈s}) =
      ν'.withDensity (fun x => k' (y,x))) :
    Measure.map (fun v : Ω × X => (v.1,f v)) (((μ.prod ν).withDensity k).restrict s) = (μ.prod ν').withDensity k' := by
  let j (v : Ω × X) := (v.1,f v); have hj : Measurable j := measurable_fst.prodMk he
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)
  change (∫⁻ x,φ x ∂Measure.map j _)=_
  rw [lintegral_map hφ hj, ← lintegral_indicator hs, readings μ ν hk (((show Measurable (fun x => φ (j x)) from hφ.comp hj)).indicator hs), readings μ ν' hk' hφ]
  refine lintegral_congr fun i => ?_
  let d := {x | (i,x)∈s}
  have hd : MeasurableSet d := measurable_prodMk_left hs
  let g x := φ (j (i,x))
  rw [← ht i,lintegral_map (show Measurable (fun y:Y => φ (i,y)) from hφ.comp measurable_prodMk_left)
    (show Measurable (fun x:X => f (i,x)) from he.comp measurable_prodMk_left)]
  refine Eq.trans ?_ (lintegral_indicator (μ:=ν.withDensity (fun x => k (i,x))) hd g)
  refine lintegral_congr fun x => ?_
  by_cases hi : x∈d
  · rw [indicator_of_mem hi,indicator_of_mem (show (i,x)∈s from hi)]
  rw [indicator_of_notMem hi,indicator_of_notMem (show (i,x)∉s from hi)]
end Sharing

variable {G : Gauge} {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    {A : ChartRatio G} {H : Port A}

/-- At one V, Ω the base (tags, frozen variables). -/
structure Surface {A : ChartRatio G} (H : Port A) (ι κ : Type) [Fintype ι] [Fintype κ] (Ω : Type) where
  mean : Ω → H.Room ι
  orient : Ω → H.Bound ι
  B : Ω → Gaussian.Quad (H.front ι (H.Room κ))

namespace Surface
open Port Gaussian
variable (S : Surface H ι κ Ω)
local notation "X" => H.front ι (H.Room κ)
local notation "Y" => H.back ι (H.Room κ)

/-- Outputs with physical gaussian law depend on the complete V everywhere
read, and domains are checked at that same V. These are per-V tests. -/
structure Valid : Prop where
  firm (x) : Firm (S.B x)
  borel : Measurable fun p : Ω × X => S.B p.1 p.2 p.2
  m : Measurable S.mean
  v : Measurable S.orient

theorem add_haar (H : Port A) (ι κ : Type) [Fintype ι] [Fintype κ] :
    (volume : Measure (H.front ι (H.Room κ))).IsAddHaarMeasure := by
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure (H.Room ι)) (volume : Measure (H.Room κ))

variable {S}

def lifted (S : Surface H ι κ Ω) (p : Ω × X) := pdf volume (S.B p.1) p.2
def gateway (S : Surface H ι κ Ω) (g : ℝ) := {x : Ω × X | x.2.1∈H.zone g (S.mean x.1)}
def confirm (S : Surface H ι κ Ω) (g : ℝ) (p : Ω × Y) := H.route g (S.mean p.1) (S.orient p.1)
    (pdf volume (S.B p.1)) p.2

def mapDown (S : Surface H ι κ Ω) (g : ℝ) : Ω × X → Ω × Y := fun p => (p.1,H.jump g (S.mean p.1) (S.orient p.1) p.2)
def mapUp (S : Surface H ι κ Ω) (g : ℝ) : Ω × Y → Ω × X := fun p => (p.1,H.slideBack g (S.mean p.1) (S.orient p.1) p.2)

omit [MeasurableSpace Ω] in
lemma upDown (g : ℝ) (hh : 0<g) {p : Ω×X} (he : p∈S.gateway g) : S.mapUp g (S.mapDown g p)=p :=
  Prod.ext rfl (Prod.ext (line_ok H g hh _ _ he) rfl)

lemma Valid.lifted_meas (h : S.Valid) : Measurable S.lifted := by
  let e (p : Ω × X) := Real.exp (-S.B p.1 p.2 p.2)
  have he : Measurable e := h.borel.neg.exp
  have hm : Measurable fun x : Ω => ∫ z,e (x,z) := he.stronglyMeasurable.integral_prod_right'.measurable
  exact he.div (hm.comp measurable_fst)

lemma Valid.lifted_pos (h : S.Valid) (p : Ω × X) : 0 < S.lifted p := by
  have := add_haar H ι κ
  obtain ⟨_,hp,hp'⟩ := h.firm p.1
  exact pdf_pos volume hp hp' _

lemma Valid.gate_meas (h : S.Valid) (g : ℝ) : MeasurableSet (S.gateway g) :=
  let hm : Measurable (fun p : Ω × X => g • p.2.1 + S.mean p.1) :=
    ((measurable_fst.comp measurable_snd).const_smul g).add (h.m.comp measurable_fst)
  hm H.open_present.measurableSet

lemma Valid.down_meas (h : S.Valid) (g : ℝ) : Measurable (S.mapDown g) := by
  let B (p : Ω × X) := H.swing g (S.mean p.1) p.2.1
  let L (p : Ω × X) := S.orient p.1
  have hm : Measurable B := ((measurable_fst.comp measurable_snd).const_smul g).add (h.m.comp measurable_fst)
  have hh : Measurable L := h.v.comp measurable_fst
  have he (i : ι) : Measurable fun p : Ω × X => G.lieExp (B p i) * L p i := by
    exact (G.lieExp_cont.measurable.comp ((measurable_pi_apply i).comp hm)).mul ((measurable_pi_apply i).comp hh)
  have hv : Measurable (fun p : Ω × X => H.field g (S.mean p.1) (L p) p.2.1) :=
    show Measurable (fun p : Ω × X => fun i : ι => G.lieExp (B p i)*L p i) from measurable_pi_lambda _ he
  exact measurable_fst.prodMk (hv.prodMk (measurable_snd.comp measurable_snd))

lemma Valid.touch_meas (h : S.Valid) : Measurable fun p : Ω × Y => H.hear (S.orient p.1) p.2.1 := by
  refine measurable_pi_lambda _ fun i => H.undo_meas.comp (((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).mul
    ((measurable_pi_apply i).comp (h.v.comp measurable_fst)).inv)

lemma Valid.up_meas (h : S.Valid) (g : ℝ) : Measurable (S.mapUp g) := by
  have hm := (h.touch_meas.sub (h.m.comp measurable_fst)).const_smul g⁻¹
  exact measurable_fst.prodMk (hm.prodMk (measurable_snd.comp measurable_snd))

/-- Held region at this V. Smoothness hypotheses will need more than this
one set. -/
def Perch (S : Surface H ι κ Ω) : Set (Ω × Y) := {p | p.2.1∈H.touch (S.orient p.1)}
lemma Valid.perch_meas (h : S.Valid) : MeasurableSet S.Perch := by
  unfold Perch touch
  simp only [Set.mem_pi,mem_univ,true_imp_iff,mem_setOf_eq,setOf_forall]
  refine MeasurableSet.iInter fun i : ι => ?_
  have he : Measurable fun p : Ω × Y => p.2.1 i * (S.orient p.1 i)⁻¹ :=
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).mul
      (((measurable_pi_apply i).comp (h.v.comp measurable_fst)).inv)
  exact he H.around.measurableSet

lemma Valid.confirm_meas (h : S.Valid) (g : ℝ) : Measurable (S.confirm g) := by
  let f (p : Ω×Y) := (g^H.dimension ι)⁻¹ * (H.stamp (H.hear (S.orient p.1) p.2.1))⁻¹ * S.lifted (S.mapUp g p)
  have hL : Measurable f := (measurable_const.mul (H.stamp_meas.comp h.touch_meas).inv).mul
    (h.lifted_meas.comp (h.up_meas g))
  have he : confirm S g = S.Perch.indicator f := by
    ext x; unfold confirm Port.route; split_ifs with hx
    · exact (indicator_of_mem (show x∈S.Perch from hx) f).symm
    exact (indicator_of_notMem (show x∉S.Perch from hx) f).symm
  rw [he]; exact hL.indicator h.perch_meas
lemma Valid.confirm_positive (h : S.Valid) (g : ℝ) (hp : 0<g) (p : Ω × Y) (hv : p ∈ S.Perch) : 0 < S.confirm g p := by
  unfold confirm Port.route; rw [if_pos (show p.2.1∈H.touch (S.orient p.1) from hv)]
  exact mul_pos (mul_pos (by positivity) (inv_pos.mpr (H.demanded (H.heard_mem hv)))) (h.lifted_pos (S.mapUp g p))
lemma Valid.confirm_nonneg (h : S.Valid) (g : ℝ) (hp : 0<g) (p : Ω×Y) : 0≤ S.confirm g p := by
  by_cases hv : p∈S.Perch
  · exact (h.confirm_positive g hp p hv).le
  unfold confirm Port.route; rw [if_neg (show p.2.1∉H.touch (S.orient p.1) from hv)]

def ante (S : Surface H ι κ Ω) (μ : Measure Ω) : Measure (Ω × X) := (μ.prod volume).withDensity fun x => ENNReal.ofReal (S.lifted x)

def ambient (H : Port A) (ι κ : Type) [Fintype ι] [Fintype κ] {Ω} [MeasurableSpace Ω] (μ : Measure Ω) :
    Measure (Ω × H.back ι (H.Room κ)) := μ.prod (Port.heldLaw.prod volume)
def aboard (S : Surface H ι κ Ω) (μ : Measure Ω) (g : ℝ) := (ambient H ι κ μ).withDensity fun x => ENNReal.ofReal (S.confirm g x)

lemma Valid.hold (h : S.Valid) (g : ℝ) (hp : 0<g) (μ : Measure Ω) :
    Measure.map (S.mapDown g) ((S.ante μ).restrict (S.gateway g))=S.aboard μ g := by
  have hS (x : Ω): H.zone g (S.mean x) ×ˢ (Set.univ : Set (H.Room κ)) = {y | (x,y) ∈ S.gateway g} := by ext p; simp [gateway]
  have he x := H.replaces volume g hp (S.mean x) (S.orient x) (f:=pdf volume (S.B x))
    (show Measurable (pdf volume (S.B x)) from h.lifted_meas.comp (show Measurable (fun z : X => (x,z)) from measurable_prodMk_left))
    (fun y => (h.lifted_pos (x,y)).le)
  refine apply_fibers μ (volume : Measure X) (Port.heldLaw.prod (volume : Measure (H.Room κ))) (fun p => (S.mapDown g p).2)
    (s:=S.gateway g) (k:=fun p => ENNReal.ofReal (S.lifted p)) (k':=fun p => ENNReal.ofReal (S.confirm g p))
    (h.down_meas g).snd (h.gate_meas g) h.lifted_meas.ennreal_ofReal (h.confirm_meas g).ennreal_ofReal ?_
  intro y; rw [← hS y]; exact he y

theorem Valid.total (h : S.Valid) (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (S.ante μ) := by
  have := add_haar H ι κ
  have he (x : Ω) : (∫⁻ z : X,ENNReal.ofReal (S.lifted (x,z)))=1 := by
    obtain ⟨c,hc,Hc⟩ := h.firm x
    change (∫⁻ z : X, ENNReal.ofReal (pdf volume (S.B x) z))=_
    rw [← ofReal_integral_eq_lintegral_ofReal (pdf_integrable volume hc Hc) (Eventually.of_forall fun i => (pdf_pos volume hc Hc i).le), normalized volume hc Hc,ENNReal.ofReal_one]
  refine ⟨?_⟩; unfold ante
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_prod _ h.lifted_meas.ennreal_ofReal.aemeasurable]
  simp_rw [he]; simp

lemma Valid.sub_one (h : S.Valid) (g : ℝ) (hp : 0<g) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    S.aboard μ g Set.univ ≤ 1 := by
  have := h.total μ
  rw [← h.hold g hp μ,Measure.map_apply (h.down_meas g) MeasurableSet.univ,Set.preimage_univ]
  exact Measure.restrict_le_self _ |>.trans (le_of_eq measure_univ)
lemma Valid.landed (h : S.Valid) (g : ℝ) (hp : 0<g) (μ : Measure Ω) [IsProbabilityMeasure μ] : IsFiniteMeasure (S.aboard μ g) :=
  ⟨lt_of_le_of_lt (h.sub_one g hp μ) ENNReal.one_lt_top⟩

end Surface
end YM.Further.DenseMixedKernels
