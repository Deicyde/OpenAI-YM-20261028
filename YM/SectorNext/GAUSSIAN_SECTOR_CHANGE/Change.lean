import YM.Next.BOUNDARY.Core
import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder
import YM.Work.A05


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Gaussian change on the *actual* sector integral

orientation average incl noise. Kept here as a relative
cut-base formula: see `convert_full` in Ledger for pulling the remaining full
base *also* into the output. All identities and L¹ on actual Rep, fixed V,
even if some A.V records wrong/nonrealizable. Arbitrary m(Y), C fixed
per A,F,V,k as will even be the case for the exact window. Struct conclusion
permits subsequent quantitative estimates but none of the chain/locality
arguments assumed here. Preserve likelihood, masks, and all true tails.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x w : ℝ}

/-- Actual g of the Rep step (not its numerical hat). -/
def coupling (β : ℝ) := (Real.sqrt β)⁻¹
lemma coupling_pos {β : ℝ} (h : 0 < β) : 0 < coupling β := inv_pos.2 (Real.sqrt_pos.2 h)
lemma by_coupling {β : ℝ} (h : 0 < β) : (coupling β ^ 2)⁻¹ = β := by rw [coupling,inv_pow,Real.sq_sqrt h.le,inv_inv]

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (R : Rep G f)
/-- All non-quadratic-chart multiplier terms (and literal uncut inputs)
in a Borel envelope. Includes v unchanged. Still needs summability
receipts for genuine evaluation. -/
def garments (U : Config G f) :=
  prefactor S G R.beta * exposed R (till x) U * Real.exp (-R.beta * fee T x V k A U)

lemma clothed (h : S.patch.Branches S.kernel G) (U : Config G f) :
    S.likelihood U k * garments T x V k A R U = exposed R (till x) U * enters T R.beta x k V U := by
  rw [enters_eq h A, leaves, garments, fee,mul_add,Real.exp_add]; ring

lemma fully_clothed {σ C Λ δ l : ℝ} {P : Teller G} (h : R.Lawful σ C Λ δ l) (hT : P.Funds S T) :
    Envelope (garments T x V k A R) := by
  exact (((Envelope.const _).mul (env_exposed R h _)).mul (((Envelope.const _).mul (fee_envelope T x V k A hT)).exp))

variable (W : Stencils S) (F : Forest S.ratio) (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)

/-- E equation: transformed term, on its true cutoffs.

The regular link
U's on reads are `exp(a) replica`, Y held, and all appear inside the
same likelihood, energy and cutoff predicates as before.

Inactive identity completions are *not* among the n_a priced in chartCost. -/
def dyed (C : Gaussian.Table (Rows.In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) :=
  let g := coupling R.beta
  let a := (m Y + g • z)
  let y := tape a
  let U := physical A F V Y y
  reserve q J d y * doors q d y * D.bill A k U V * S.likelihood U k * exposed R (till x) U *
    Real.exp (-R.beta * averaged (residual T x V k W A F q d Y U a) +
        adjustment T x V k W A F q d Y C (m Y) g z)

lemma recolored {J} {o σ Λ E} (h : T.up.Bounds o σ E Λ) (hh : 0<R.beta)
    (C : Gaussian.Table (Rows.In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) :
    prefactor S G R.beta * dyed (J:=J) T x V k A R W F D q d C m Y z = Real.exp (force C z/2) *
      regularized D A F V k q J d (garments T x V k A R) Y (displaced (m Y) (coupling R.beta) z) := by
  let g := coupling R.beta
  let a := (m Y + g • z)
  let y := tape a
  let U := physical A F V Y y
  let e := guide T x V k W A F q d Y a
  have he : fee T x V k A U = averaged (residual T x V k W A F q d Y U a) + e := by
    rw [exact_fee, compose_residual _ _ _ _ _ _ _ _ _ _ h]
  have ht := adjusted T x V k W A F q d Y C (m Y) z (coupling_pos hh)
  change adjustment T x V k W A F q d Y C (m Y) g z = force C z / 2 - e/g^2 at ht
  change prefactor .. * (reserve q J d y*doors q d y*D.bill A k U V*S.likelihood U k *
    exposed R (till x) U*Real.exp (-R.beta*averaged (residual T x V k W A F q d Y U a)+_)) =
      Real.exp _*((reserve q J d y*doors q d y)*((D.bill A k U V*S.likelihood U k)*garments T x V k A R U))
  have hb : e/g^2 = R.beta*e := by rw [div_eq_mul_inv,by_coupling hh]; ring
  rw [ht,hb, show -R.beta*averaged (residual T x V k W A F q d Y U a)+(force C z/2-R.beta*e)=
    force C z/2-R.beta*fee T x V k A U by rw [he]; ring,sub_eq_add_neg, Real.exp_add, ← neg_mul,garments]
  ring

structure Permitted (β : ℝ) (C : Gaussian.Table (Rows.In x A F (G:=G)))
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F)) : Prop where
  nativePos : C.PosDef
  bpos : 0 < β
  shift : Measurable m
  core : Standing (F:=F) (A:=A) D J d k V
  trueChart : LocalRatio J
  doorPos : 0<d
  scalePaid : 4*d < J.radius

lemma dyed_meas {C : Gaussian.Table (Rows.In x A F (G:=G))} {m : LinkArray G (Frozen A x F) → Prices G (Active A x F)}
    (hp : Permitted x V k A F D J d R.beta C m)
    {σ n Λ δ l : ℝ} {P : Teller G} (h : R.Lawful σ n Λ δ l) (hT : P.Funds S T) :
    Measurable (Function.uncurry (dyed T x V k A R W F D q J d C m)) := by
  let r := regularized D A F V k q J d (garments T x V k A R)
  have hr : Measurable (uncurry r) := regularized_meas D A F V k hp.trueChart q hp.doorPos hp.scalePaid _
    (funds_branch hT) (fully_clothed _ _ _ _ _ _ h hT)
  have hm : Continuous (fun z : Prices G (Active A x F) => force C z) := by unfold force dotProduct mulVec; fun_prop
  let p (y : LinkArray G (Frozen A x F) × Prices G (Active A x F)) := (y.1,displaced (m y.1) (coupling R.beta) y.2)
  have he : Measurable p := measurable_fst.prodMk (tape.measurable.comp
    ((hp.shift.comp measurable_fst).add (by fun_prop)))
  convert! (measurable_const (a:= (prefactor S G R.beta)⁻¹)).mul
    ((Real.continuous_exp.measurable.comp ((hm.measurable.comp measurable_snd).div_const 2)).mul (hr.comp he)) using 1
  obtain ⟨hk,hh,hH,-⟩ := hT.feeds
  funext y
  change dyed .. = (prefactor S G R.beta)⁻¹ * (Real.exp (force C y.2/2)*r _ _)
  have he := recolored T x V k A R W F D q d (J:=J) hH hp.bpos C m y.1 y.2
  change _ = Real.exp _ * r (p y).1 (p y).2 at he
  rw [← he,← mul_assoc,inv_mul_cancel₀ (prefactor_pos (G:=G) (S:=S) _).ne',one_mul]

/-- Entire transformed integrand (not asserting this L¹ after dropping
any of the defaults or guards). -/
structure Licenses (C : Gaussian.Table (Rows.In x A F (G:=G)))
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F)) : Prop where
  literal : Integrable (D.portion A F V (fun k a => exposed R (till x) (F.drape a) * enters T R.beta x k V (F.drape a)) k)
    (F.order G)
  sectionEach (Y : LinkArray G (Frozen A x F)) : Integrable (dyed T x V k A R W F D q J d C m Y) (cloud C)
  integer : Integrable (uncurry (dyed T x V k A R W F D q J d C m)) ((piHaar G (Frozen A x F)).prod (cloud C))
  result : (∫ a, D.portion A F V (fun k a => exposed R (till x) (F.drape a) * enters T R.beta x k V (F.drape a)) k a ∂F.order G) =
    prefactor S G R.beta * J.scale ^ Fintype.card (Active A x F) * chartCost C (coupling R.beta) *
      ∫ Y, (∫ z, dyed T x V k A R W F D q J d C m Y z ∂cloud C) ∂piHaar G (Frozen A x F)

theorem authorized_change {C : Gaussian.Table (Rows.In x A F (G:=G))} {m : LinkArray G (Frozen A x F) → Prices G (Active A x F)}
    (hp : Permitted x V k A F D J d R.beta C m) {σ n Λ δ l : ℝ} {P : Teller G}
    (h : R.Lawful σ n Λ δ l) (hT : P.Funds S T) : Licenses T x V k A R W F D q J d C m := by
  obtain ⟨hk,hh,hH,-⟩ := hT.feeds
  let b := coupling R.beta
  have hb : 0<b := coupling_pos hp.bpos
  let r := regularized D A F V k q J d (garments T x V k A R)
  let v := dyed T x V k A R W F D q J d C m
  let u (a : F.Slice G) := attending D A F V k (garments T x V k A R) a
  let M := piHaar G (Frozen A x F)
  obtain ⟨hl,hY,hπ,hv,hτ⟩ := regularized_price D A F V k hp.trueChart q hp.doorPos hp.scalePaid hp.core _
    (funds_branch hT) (fully_clothed _ _ _ _ _ _ h hT)
  let s := prefactor S G R.beta
  let c := chartCost C b
  have hs : 0<s := prefactor_pos _
  have hc : 0<c := chartCost_pos C hp.nativePos hb
  have he (Y) :
      (fun z => Real.exp (force C z/2) • r Y (displaced (m Y) b z))=fun z => s • v Y z :=
    funext fun z => (recolored T x V k A R W F D q d (J:=J) hH hp.bpos C m Y z).symm
  have hr (Y) : (∫ a, r Y a)=c*s*∫ z,v Y z ∂cloud C := by
    have ht := (at_price C hp.nativePos hb (m Y) (r Y)).2
    simp_rw [congr_fun (he Y),integral_smul,smul_eq_mul] at ht
    rw [ht]; unfold c; ring
  have hy Y : Integrable (v Y) (cloud C) := by
    have hi := (at_price C hp.nativePos hb (m Y) (r Y)).1.mp (hY Y)
    change Integrable (fun z => Real.exp _ • r Y _) _ at hi
    simp_rw [congr_fun (he Y)] at hi
    have hu := hi.smul s⁻¹
    change Integrable (s⁻¹ • s • v Y) _ at hu
    simpa only [smul_smul,inv_mul_cancel₀ hs.ne',one_smul] using hu
  have ho : Integrable (uncurry v) (M.prod (cloud C)) := by
    have hm := dyed_meas T x V k A R W F D q J d hp h hT
    let τ (Y : LinkArray G (Frozen A x F)) := ∫ z, ‖v Y z‖ ∂cloud C
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hy,?_⟩
    have hx (Y) : (∫ a, ‖r Y a‖) = (c*s)*τ Y := by
      have ht (z : Prices G (Active A x F)) := congr_arg (‖·‖) (congr_fun (he Y) z)
      simp only [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg hs.le] at ht
      calc
        _ = c * ∫ z, Real.exp (force C z/2) * ‖r Y (displaced (m Y) b z)‖ ∂cloud C :=
             (at_price C hp.nativePos hb (m Y) (fun a => ‖r Y a‖)).2
        _ = _ := by simp_rw [ht,integral_const_mul]; unfold τ; ring
    change Integrable (fun Y => ∫ a, ‖r Y a‖) M at hπ
    simp_rw [hx] at hπ
    have hi := hπ.smul (c*s)⁻¹
    change Integrable ((c*s)⁻¹ • (c*s) • τ) _ at hi
    rw [smul_smul, inv_mul_cancel₀ (mul_pos hc hs).ne', one_smul] at hi
    exact hi
  have hz : D.portion A F V (fun k a => exposed R (till x) (F.drape a) * enters T R.beta x k V (F.drape a)) k = u := by
    funext a; unfold u Allocation.portion attending; simp only [smul_eq_mul,mul_assoc,clothed _ _ _ _ _ _ (funds_branch hT)]
  refine ⟨hz.symm ▸ hl,hy,ho,?_⟩
  rw [hz]
  change (∫ a,u a ∂F.order G) = s*_ *c*∫ Y,(∫ a,v Y a ∂cloud C)∂M
  change (∫ a,u a ∂F.order G) = _ • ∫ Y,(∫ a, r Y a)∂M at hτ
  simp_rw [hτ, hr, integral_const_mul, smul_eq_mul]
  ring

section total
variable {σ n Λ δ l : ℝ} {P : Teller G} (h : R.Lawful σ n Λ δ l) (hT : P.Funds S T) (ht : Fits T R x)
include h hT ht


end total
end YM.Next.SectorChange
