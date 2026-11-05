import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Tags
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger


/-!
# Same sector and Gaussian normalization

`body` is the *actual* integrand for this comparison, relative to the
uniform tag law and the piHaar×**probability** Gaussian on this Store **and
this k**, with output base and common ledger separated. See `undecorated`
for equality to the retained costs and actual `sleeves` (and hence dyed).

Don't mix the relative convention with counting Choices on the original
slice! Works even with additional Borel densities (say coefficient with
many marked spectators), with its L¹ license. No estimates about those
source histories are asserted here.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open Pressure Pressure.Tube Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}

abbrev Room (G : Gauge) (x : ℝ) (F : Forest S.ratio) (A : Stores S) :=
    LinkArray G (Frozen A x F) × Prices G (Active A x F)

/-- 'Read' as a numerical input, does not claim it's a valid component of
any history. No forcing gauge invariance for working *on this slice*. -/
abbrev ReadAt (S : StepData c f) (G : Gauge) := S.Choices → Config G f → ℝ

def touch (F : Forest S.ratio) (D : Allocation G S x W) (β : ℝ) (V : Config G c) (A : Stores S) (g : ReadAt S G)
    (k : S.Choices) : F.Slice G → ℝ := D.portion A F V (through S F β V fun k a => g k (F.drape a)) k

/-- True Haar sector integral against an arbitrary signed input density.
Fixed-V, not omitting output noise denominator. Use with `each_touch`. -/
def amount (F : Forest S.ratio) (D : Allocation G S x W) (β : ℝ) (V : Config G c) (A : Stores S) (g : ReadAt S G) :=
    ∑ k,∫ a,touch F D β V A g k a ∂F.order G

lemma each_touch (F : Forest S.ratio) (D : Allocation G S x W) (hm : S.patch.Branches S.kernel G) (β : ℝ)
    (V : Config G c) (A : Stores S) (g : ReadAt S G) (k : S.Choices) (h : Envelope (g k)) :
    Integrable (touch F D β V A g k) (F.order G) :=
  D.portion_integrable hm A F V _ k
    (through_integrable F β V _ hm k ((Env.along h F.continuous_drape.measurable).integrable _))

lemma touch_wrong (F : Forest S.ratio) (D : Allocation G S x W) (β : ℝ) (V : Config G c) (A : Stores S)
    (g : ReadAt S G) (h : A.flags≠RG.flags (temp x) V) :
    amount F D β V A g=0 := by
  have hu k U : D.bill A k U V=0 := not_not.mp fun hx => h (D.actual _ _ _ _ hx).exactFlags
  unfold amount touch Allocation.portion; simp_rw [hu, zero_smul, integral_zero, Finset.sum_const_zero]

/-- Data named once.

The comparison is at this lottery (may be instantiated
with `fog`, `meanLog`, `shots` exactly).

In particular it does NOT vary with locations of requests. -/
structure Almanac (T : Tube G S) (_D : Allocation G S x W) (_R : Rep G f) (F : Forest S.ratio) where
  point : BudgetPoint
  H : Gaussian.Table (F.Free × G.ColorIndex)
  J : ChartRatio G
  d : ℝ
  q : Chi
  list : Stores S → Stencils S
  C : (A : Stores S) → Config G c → S.Choices → Gaussian.Table (Rows.In x A F (G:=G))
  m : (A : Stores S) → Config G c → S.Choices → LinkArray G (Frozen A x F) → Prices G (Active A x F)

namespace Almanac
variable {T : Tube G S} {R : Rep G f} {F : Forest S.ratio} {D : Allocation G S x W}
  (L : Almanac T D R F) (V : Config G c) (A : Stores S) (k : S.Choices)

structure Available : Prop where
  beta : 0 < R.beta
  ratio : LocalRatio L.J
  refPrice : L.H.PosDef
  keeps : L.point.threshold=temp x
  trueCov (A : Stores S) (k : S.Choices) : A.flags=RG.flags (temp x) V →
    Permitted x V k A F D L.J L.d R.beta (L.C A V k) (L.m A V k)
  gram (A : Stores S) (k : S.Choices) : A.flags=RG.flags (temp x) V → (Rows.gram T x V k (L.list A) A F).PosDef

def ledger := Real.exp R.scalar * prefactor S G R.beta * spare L.J R.beta ^ Fintype.card F.Free *
    (Real.sqrt L.H.det)⁻¹

def rate := banker T L.point V R.beta * L.ledger

lemma ledger_pos (h : L.Available V) : 0 < L.ledger := by
  unfold ledger
  exact mul_pos (mul_pos (mul_pos (Real.exp_pos _) (prefactor_pos _))
    (pow_pos (spare_pos L.J h.ratio h.beta) _)) (inv_pos.mpr (Real.sqrt_pos.mpr h.refPrice.det_pos))
lemma rate_pos (h : L.Available V) : 0 < L.rate V := mul_pos (Real.exp_pos _) (L.ledger_pos V h)

/-- Still to be paid, **not** a per-volume upper bound. -/
def fees :=
  let Q := Rows.gram T x V k (L.list A) A F
  Real.exp (-(Fintype.card (Frozen A x F):ℝ)*Real.log (spare L.J R.beta) -
    (1/2)*(Real.log Q.det-Real.log L.H.det) + (1/2)*Real.log (1+(Q*L.C A V k-1)).det)

lemma aligned (h : L.Available V) (hv : A.flags=RG.flags (temp x) V) :
    L.J.scale ^ Fintype.card (Active A x F)*chartCost (L.C A V k) (coupling R.beta) =
      spare L.J R.beta ^ Fintype.card F.Free * (Real.sqrt L.H.det)⁻¹ * L.fees V A k := by
  rw [scalars_align x A R F L.J]
  exact solvent_ledger x A R F L.J L.point _ _ _ h.refPrice (h.gram A k hv)
    ((h.trueCov A k hv).nativePos) h.ratio h.beta

abbrev climate := (piHaar G (Frozen A x F)).prod (cloud (L.C A V k))

def pattern (y : Room G x F A) := displaced (L.m A V k y.1) (coupling R.beta) y.2

def texture (y : Room G x F A) := physical A F V y.1 (L.pattern V A k y)

private def atlas (g : ReadAt S G) (y : Room G x F A) :=
  Real.exp (force (L.C A V k) y.2/2) * regularized D A F V k L.q L.J L.d
    (fun U => S.noise R.beta (S.prediction U k) V * g k U) y.1 (L.pattern V A k y)

/-- Exact data whose pointwise expansion should be bought. The real mark
input may be signed (even a nonmultiplicative rep coefficient). -/
def body (g : ReadAt S G) (y : Room G x F A) :=
    ((Fintype.card S.Choices:ℝ) * L.fees V A k *
      (banker T L.point V R.beta * Real.exp R.scalar * prefactor S G R.beta)⁻¹) *
    L.atlas V A k g y

lemma adjusted_body (g u : ReadAt S G) (y : Room G x F A) :
    L.body V A k (fun k x => u k x*g k x) y = u k (L.texture V A k y) * L.body V A k g y := by
  unfold body atlas regularized attending texture; simp only [physical, smul_eq_mul]; ring

-- Payment pipeline with integrable at actual content and
-- before any hypothetical expansion, including the norm integral.
set_option maxHeartbeats 500000 in
private lemma stage (hS : S.patch.Branches S.kernel G) (g : ReadAt S G) (hg : Envelope (g k))
    (h : L.Available V) (hx : A.flags=RG.flags (temp x) V) :
    Integrable (L.atlas V A k g) (L.climate V A k) ∧
    (∫ a,touch F D R.beta V A g k a ∂F.order G) = L.J.scale^ Fintype.card (Active A x F) *
      chartCost (L.C A V k) (coupling R.beta) * ∫ y,L.atlas V A k g y ∂L.climate V A k := by
  let C := L.C A V k
  let Z := cloud C
  let M := piHaar G (Frozen A x F)
  let cost := chartCost C (coupling R.beta)
  let u := L.atlas V A k g
  let w U := S.noise R.beta (S.prediction U k) V * g k U
  let r := regularized D A F V k L.q L.J L.d w
  have hu y z : u (y,z)=Real.exp (force C z/2) • r y (L.pattern V A k (y,z)) := rfl
  have he : Envelope w := (env_noise S R.beta (S.prediction_meas hS k) measurable_const).mul hg
  have hp := h.trueCov A k hx
  have hm : Measurable (L.pattern V A k) :=
    tape.measurable.comp ((hp.shift.comp measurable_fst).add (by fun_prop))
  have hf : Continuous (fun z : Prices G (Active A x F) => force C z) := by unfold force dotProduct mulVec; fun_prop
  have ha : Measurable u := by
    have h₁ : Measurable (fun y : Room G x F A => Real.exp (force C y.2/2)) :=
      ((hf.measurable.comp measurable_snd).div_const 2).exp
    have h₂ : Measurable (uncurry r) := regularized_meas D A F V k hp.trueChart L.q hp.doorPos hp.scalePaid w hS he
    change Measurable (fun y : Room G x F A => Real.exp (force C y.2/2) * r y.1 (L.pattern V A k y))
    let E (y : Room G x F A) := (y.1,L.pattern V A k y)
    have ht : Measurable E := measurable_fst.prodMk hm
    have hc : Measurable (fun y : Room G x F A => (uncurry r) (E y)) := h₂.comp ht
    have hg : Measurable (fun y : Room G x F A => r y.1 (L.pattern V A k y)) := by
      exact hc
    have hE := h₁.mul hg; exact hE
  obtain ⟨hi,hy,hπ,_,hr⟩ := regularized_price D A F V k hp.trueChart L.q hp.doorPos hp.scalePaid hp.core w hS he
  have hh (Y) (v : LogArray G (Active A x F) → ℝ) := at_price C hp.nativePos (coupling_pos hp.bpos)
    (L.m A V k Y) v
  have hI : Integrable u (M.prod (cloud (L.C A V k))) := by
    refine (integrable_prod_iff ha.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall (fun i => (hh i (r i)).1.mp (hy i)),?_⟩
    let e (y : LinkArray G (Frozen A x F)) := ∫ z, ‖u (y,z)‖ ∂Z
    have he y : (∫ a, ‖r y a‖) = cost * e y := by
      unfold e
      simp_rw [hu,norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (hh y (fun a => ‖r y a‖)).2
    change Integrable (fun Y => ∫ a, ‖r Y a‖) M at hπ
    simp_rw [he] at hπ
    have hq := hπ.smul cost⁻¹
    change Integrable (cost⁻¹ • cost • e) M at hq
    have hf : 0 < cost := chartCost_pos C hp.nativePos (coupling_pos hp.bpos)
    rw [smul_smul,inv_mul_cancel₀ hf.ne',one_smul] at hq
    exact hq
  refine ⟨hI,?_⟩
  have hT : touch F D R.beta V A g k = attending D A F V k w := by
    funext y
    unfold touch Allocation.portion attending through w taggedKernel
    simp only [smul_eq_mul]; ring
  rw [hT,hr,integral_prod _ hI]
  have ht y : (∫ a,r y a)=cost * (∫ z, u (y,z)∂ Z) := (hh y (r y)).2
  change _ * (∫ Y, (∫ a,r Y a)∂M)=_*cost * ∫ y, (∫ z,u (y,z)∂Z) ∂M
  simp_rw [ht,integral_const_mul]; ring

lemma body_tag (hm : S.patch.Branches S.kernel G) (g : ReadAt S G) (hg : Envelope (g k))
    (h : L.Available V) (hx : A.flags=RG.flags (temp x) V) :
    Integrable (L.body V A k g) (L.climate V A k) ∧
    (∫ a,touch F D R.beta V A g k a ∂F.order G) = L.rate V * SectorNext.Vacuum.tagRef k *
      ∫ y,L.body V A k g y ∂L.climate V A k := by
  obtain ⟨hT,hi⟩ := L.stage V A k hm g hg h hx
  refine ⟨hT.const_mul _,?_⟩
  rw [hi,L.aligned V A k h hx]
  unfold body
  rw [integral_const_mul]
  unfold Almanac.rate ledger SectorNext.Vacuum.tagRef
  letI : Nonempty S.Choices := Tags.populated hm
  have hp : (Fintype.card S.Choices:ℝ) ≠ 0 := Tags.pos.ne'
  have hb : banker T L.point V R.beta ≠ 0 := (Real.exp_pos _).ne'
  have hs : prefactor S G R.beta ≠ 0 := (prefactor_pos _).ne'
  field_simp

theorem body_column (hS : S.patch.Branches S.kernel G) (g : ReadAt S G)
    (hg : ∀ k, Envelope (g k)) (h : L.Available V) (hx : A.flags=RG.flags (temp x) V) :
    amount F D R.beta V A g = L.rate V * Tags.average (fun k =>
      ∫ y,L.body V A k g y ∂L.climate V A k) := by
  unfold amount
  rw [Tags.vacuum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
  rw [(L.body_tag V A k hS g (hg k) h hx).2,mul_assoc]

/-- Calibration to the existing sector formula. The zeroth-mark call,
pointwise even before summing any choices or taking any volume comparison.
No re-running of the lottery. -/
theorem undecorated {P : Teller G} (hT : P.Funds S T) (ht : Fits T R x) (h : L.Available V)
    (y : Room G x F A) :
    L.body V A k (fun _ => R.eval) y =
      Fintype.card S.Choices * L.fees V A k *
        sleeves T x V k A R (L.list A) F D L.q L.J L.d L.point (L.C A V k) (L.m A V k) y.1 y.2 := by
  let w U := S.noise R.beta (S.prediction U k) V * R.eval U
  have h₀ U : S.likelihood U k * w U = sieve T R.beta x V * (S.likelihood U k * garments T x V k A R U) := by
    rw [clothed _ _ _ _ _ _ (funds_branch hT), ← use_gap ht]
    unfold w taggedKernel; ring
  obtain ⟨_,_,hl,_⟩ := hT.feeds
  let Y (f : Config G f → ℝ) := regularized D A F V k L.q L.J L.d f
  let m := L.pattern V A k y
  have hf : Y w y.1 m = sieve T R.beta x V * Y (garments T x V k A R) y.1 m := by
    unfold Y regularized attending
    simp only [smul_eq_mul, mul_assoc,h₀]; ring
  let b := banker T L.point V R.beta
  let s := prefactor S G R.beta
  let f := dyed T x V k A R (L.list A) F D L.q L.J L.d (L.C A V k) (L.m A V k) y.1 y.2
  have he : L.atlas V A k (fun _ => R.eval) y = sieve T R.beta x V * (s * f) := by
    rw [show s * f = Real.exp (force (L.C A V k) y.2/2) * Y (garments T x V k A R) y.1 m from
      recolored T x V k A R _ F D L.q L.d hl h.beta _ _ _ _]
    change _ * Y w y.1 m = _
    rw [hf]; ring
  unfold body
  rw [he,convert_full T x V _ _ h.keeps,sleeves_unfold]
  -- same coarse/fine scalar conventions
  change (_*L.fees _ _ _* (b*Real.exp R.scalar*s)⁻¹) * (b * Real.exp _*(s*f)) =
    _ * L.fees V A k * (Real.exp (coarseTail T x L.point V R.beta-R.scalar)*f)
  have hs : s≠0 := (prefactor_pos _).ne'
  have hb : b≠0 := (Real.exp_pos _).ne'
  rw [Real.exp_sub]; field_simp
end Almanac
end YM.AnalyticBridge.Sharp
