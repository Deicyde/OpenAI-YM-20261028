import YM.AnalyticBridge.RESET_INCOME_PORT.Plate
import YM.Next.FREE_KERNELS.Amend

set_option warningAsError false

/-!
# The *charged* positive remainder on the same Gaussian plate

The RHS of CouplingReset.Split charges even potentially REAL SIGNED
remainders; the tails bill is a positive integral *before cancellations*.
It isn't in general an integral of `abs color` at the sector price either:
a sometimes very expensive multiplier `reverseFee` must be put back. Here
it too gets the same scalar ledger, with equality, so relative tail price
hypotheses can be made on actual normalized integrals without pretending
the unnormalized LARGE_FIELD_REMAINDERS ticket can pay them.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome.Plate

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (e : Plate G S) (R : Rep G f) (A : Stores S) (V : Config G c) (k : S.Choices)

def image (z : e.Sample A) : Config G f := physical A e.forest V z.1
    (displaced (e.center A V k z.1) (coupling R.beta) z.2)

def reverseFee (κ : ℝ) (U : Config G f) := Real.exp
    (R.beta * (meanEnergy A e.tube e.x U k V - κ * (fiery G e.x S.patch.L)^2 * A.shares))

def recoil (κ : ℝ) (z : e.Sample A) : ℝ := ‖e.color R A V k z‖ * e.reverseFee R A V k κ (e.image R A V k z)

def expense (κ : ℝ) := if e.matched A V then
    Real.exp (e.cost R A V k) * ∫ z, e.recoil R A V k κ z ∂(e.law A V k) else 0

lemma env_reverse {P : Teller G} (hP : P.Funds S e.tube) (κ : ℝ) : Envelope (e.reverseFee R A V k κ) := by
  have hm : Envelope (fun U : Config G f => meanRest A e.tube e.x U k V) := env_mean
    (F:=fun s U => unassigned (turnStore s A) e.tube e.x (pull s 0 U) (choice s k) (pull s 0 V))
    fun s => env_unassigned hP e.x _ (continuous_pull ..).measurable measurable_const _
  let C := κ * (fiery G e.x S.patch.L)^2 * A.shares
  have hh : e.reverseFee R A V k κ = fun U => Real.exp
      (R.beta * (fee e.tube e.x V k A U-meanRest A e.tube e.x U k V-C)) := by
    funext U; unfold reverseFee C fee; rw [add_sub_cancel_right]
  rw [hh]; exact ((Envelope.const _).mul (Env.sub (Env.sub (fee_envelope e.tube e.x V k A hP) hm) (Envelope.const _))).exp

private lemma at_image (F : Forest S.ratio) (x b : ℝ)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (hp : Measurable m) : Measurable (fun z : LinkArray G (Frozen A x F) × Prices G (Active A x F) =>
        physical A F V z.1 (displaced (m z.1) b z.2)) := by
  let p (z : LinkArray G (Frozen A x F) × Prices G (Active A x F)) := (z.1, displaced (m z.1) b z.2)
  have hu : Measurable p := measurable_fst.prodMk (tape.measurable.comp ((hp.comp measurable_fst).add (by fun_prop)))
  change Measurable ((uncurry (physical A F V (x:=x))) ∘ p)
  exact (physical_meas (x:=x) A F V).comp hu

lemma measurable_image (hp : Measurable (e.center A V k)) : Measurable (e.image R A V k) :=
    at_image A V _ _ _ _ hp

lemma recoil_int {P : Teller G} (h : e.Receipt R) (hP : P.Funds S e.tube) (κ : ℝ) :
    Integrable (e.recoil R A V k κ) (e.law A V k) := by
  by_cases he : e.matched A V
  · have hm := (h.matchPos _ _ he k).2.shift
    have hv := Env.along (e.env_reverse R A V k hP κ) (e.measurable_image R A V k hm)
    have hp := Env.smul_L1 hv (integrable_color h A V k).norm
    apply hp.congr; filter_upwards with x; unfold recoil; rw [mul_comm]; rfl
  have hz : e.recoil R A V k κ = 0 := by funext u; simp [recoil,color,sleeves,Plate.wrong he,uncurry]
  rw [hz]; exact integrable_zero ..

variable {e R A V k}
/-- Absolute licensing also with an additional envelope factor pulled
through the actual nonlinear map, BEFORE summing or dividing. (Caller
checks logs/d & signs; this lemma is still at fixed A,k,V.) -/
private lemma pay_abs {σ n Λ δ l : ℝ} {P : Teller G} (h : R.Lawful σ n Λ δ l)
    (hT : P.Funds S e.tube) (hp : Permitted e.x V k A e.forest e.book e.chart e.d R.beta
      (e.Cov A V k) (e.center A V k)) {L : Config G f → ℝ} (he : Envelope L) :
    let u := e.book.portion A e.forest V (fun k a => exposed R (till e.x) (e.forest.drape a) *
      enters e.tube R.beta e.x k V (e.forest.drape a)) k
    let v := dyed e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip e.chart e.d (e.Cov A V k) (e.center A V k)
    (∫ a, ‖u a‖ * L (e.forest.drape a) ∂e.forest.order G) = prefactor S G R.beta *
      e.chart.scale ^ Fintype.card (Active A e.x e.forest) * chartCost (e.Cov A V k) (coupling R.beta) *
        ∫ Y, (∫ z, ‖v Y z‖ * L (e.image R A V k (Y,z)) ∂ cloud (e.Cov A V k)) ∂ piHaar G (Frozen A e.x e.forest) := by
  intro u v
  let g := fun U => ‖garments e.tube e.x V k A R U‖
  have ht : Envelope g := by
    obtain ⟨hs,B,hB⟩ := fully_clothed e.tube e.x V k A R h hT
    exact ⟨hs.norm,B,fun y => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hB y)⟩
  let g' := fun U => g U * L U
  obtain ⟨-,-,-,-,H⟩ := regularized_price e.book A e.forest V k hp.trueChart e.chip hp.doorPos hp.scalePaid hp.core
    g' (funds_branch hT) (ht.mul he)
  obtain ⟨_,_,hr,_⟩ := hT.feeds
  let C := e.Cov A V k
  let t := prefactor S G R.beta
  let b := coupling R.beta
  let j := regularized e.book A e.forest V k e.chip e.chart e.d g
  let l := regularized e.book A e.forest V k e.chip e.chart e.d g'
  let m := e.center A V k
  have he (Y z) : Real.exp (force C z/2) * l Y (displaced (m Y) b z) = t * (‖v Y z‖ * L (e.image R A V k (Y,z))) := by
    have ho {Y} {y : LogArray G (Active A e.x e.forest)} :
        ‖regularized e.book A e.forest V k e.chip e.chart e.d (garments e.tube e.x V k A R) Y y‖ = j Y y := by
      have hx : 0 ≤ doors e.chip e.d y := Finset.prod_nonneg fun i _ => (broad_range e.chip (y i) _).1
      unfold regularized attending j g
      simp only [norm_smul,norm_mul,Real.norm_of_nonneg (reserve_pos ..).le,Real.norm_of_nonneg hx,
        Real.norm_of_nonneg (e.book.nonneg ..), Real.norm_of_nonneg (S.likelihood_pos ..)]; rfl
    have hl := congr_arg (‖·‖) (recolored e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip e.d (J:=e.chart)
      hr hp.bpos C m Y z)
    simp_rw [norm_mul, Real.norm_of_nonneg (prefactor_pos R.beta).le, Real.norm_of_nonneg (Real.exp_pos _).le, ho] at hl
    have ha : l Y (displaced (m Y) b z) = j Y (displaced (m Y) b z) * L (e.image R A V k (Y,z)) := by
      unfold l j regularized attending g' image
      simp only [smul_eq_mul,mul_assoc,physical,m,b]
    change t*‖v Y z‖=Real.exp (force C z/2) * j Y _ at hl
    rw [ha,←mul_assoc, ← hl, mul_assoc]
  let s := e.chart.scale ^ Fintype.card (Active A e.x e.forest)
  let M := chartCost C b
  let π := piHaar G (Frozen A e.x e.forest)
  have h' (Y) : (∫ a, l Y a)=M*t*∫ z, ‖v Y z‖ * L (e.image R A V k (Y,z)) ∂cloud C := by
    have hx := (at_price C hp.nativePos (coupling_pos hp.bpos) (m Y) (l Y)).2
    simp_rw [smul_eq_mul,show coupling R.beta=b from rfl,he,integral_const_mul] at hx
    rw [hx]; unfold M; ring
  rw [show (fun a => ‖u a‖*L (e.forest.drape a)) = attending e.book A e.forest V k g' from ?_,H]
  · change s * (∫ Y, (∫ a, l Y a) ∂π) = t*s*M*∫ Y, (∫ z, ‖v Y z‖*_ ∂cloud C) ∂π
    simp_rw [h',integral_const_mul]; ring
  funext a
  unfold u Allocation.portion attending g' g; simp only [smul_eq_mul]
  rw [← clothed e.tube e.x V k A R (funds_branch hT), norm_mul,norm_mul,Real.norm_of_nonneg (e.book.nonneg ..),
    Real.norm_of_nonneg (S.likelihood_pos ..)]; ring

private lemma pair {σ n Λ δ l : ℝ} {P : Teller G} (h : e.Receipt R) (hP : P.Funds S e.tube)
    (hR : R.Lawful σ n Λ δ l) (A : Stores S) (V : Config G c) (k : S.Choices) (κ : ℝ) :
    let p := e.book.portion A e.forest V (fun k a => ‖exposed R (till e.x) (e.forest.drape a)‖ *
        leaves A e.tube R.beta e.x k V (e.forest.drape a)) k
    earn S G e.x κ R.beta A.shares * sieve e.tube R.beta e.x V * (∫ z, p z ∂ e.forest.order G) =
      Real.exp (e.outside R V) * e.expense R A V k κ := by
  intro p
  unfold expense
  split <;> rename_i he
  swap
  · simp [p,Allocation.portion,Plate.wrong he]
  obtain ⟨hQ,hC⟩ := h.matchPos _ _ he k
  let u := e.book.portion A e.forest V (fun k a => exposed R (till e.x) (e.forest.drape a) *
          enters e.tube R.beta e.x k V (e.forest.drape a)) k
  let v := dyed e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip e.chart e.d (e.Cov A V k) (e.center A V k)
  let L := e.reverseFee R A V k κ
  let t := earn S G e.x κ R.beta A.shares
  have hl z : t * p z = ‖u z‖ * L (e.forest.drape z) := by
    unfold t u p L earn Allocation.portion reverseFee; simp only [smul_eq_mul,enters_eq (funds_branch hP) A]
    let a := e.forest.drape z
    have hy : 0 ≤ leaves A e.tube R.beta e.x k V a := mul_nonneg (S.likelihood_pos ..) (Real.exp_pos _).le
    dsimp only [a] at hy
    simp_rw [norm_mul,Real.norm_of_nonneg (prefactor_pos _).le,Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (e.book.nonneg ..),Real.norm_of_nonneg hy]
    rw [mul_sub, Real.exp_sub,neg_mul,neg_mul,Real.exp_neg,Real.exp_neg]; field_simp
  have hh := pay_abs hR hP hC (e.env_reverse R A V k hP κ)
  let m := e.Cov A V k
  let q := Real.exp (e.outside R V)
  let b := Real.exp (coarseTail e.tube e.x e.point V R.beta-R.v*Fintype.card (Site f))
  let s := spare e.chart R.beta
  let r := chartCost m (coupling R.beta)
  let M := piHaar G (Frozen A e.x e.forest)
  let y := prefactor S G R.beta
  let i := sieve e.tube R.beta e.x V
  let a := e.chart.scale ^ Fintype.card (Active A e.x e.forest)
  let g := Real.exp (e.cost R A V k)
  have hz Y z : e.recoil R A V k κ (Y,z)= b*(‖v Y z‖ * L (e.image R A V k (Y,z))) := by
    simp only [recoil, color, uncurry, sleeves_unfold, norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,b,v,L,mul_assoc]
  have hk : a*r = s ^ Fintype.card e.forest.Free * (Real.sqrt e.Flat.det)⁻¹*g := by
    unfold a r g cost
    rw [scalars_align e.x A R e.forest e.chart,solvent_ledger e.x A R e.forest e.chart e.point (e.Gram A V k) m _ h.solvent
      hQ hC.nativePos h.ratio h.bp]
  have hv : i * y * a*r=q*b*g := by
    let X := banker e.tube e.point V R.beta
    let N := R.v * Fintype.card (Site f)
    let Z := Real.exp (coarseTail e.tube e.x e.point V R.beta)
    have hN : Real.exp N*b = Z := by unfold N b Z; rw [← Real.exp_add]; ring_nf
    have hX : i=X*Z := convert_full _ _ _ _ _ h.radius
    have hf : q=X*(Real.exp N*y*s^Fintype.card e.forest.Free*(Real.sqrt e.Flat.det)⁻¹) := outside_exp h V
    calc
      _ = (X*y*Z)*(a*r) := by rw [hX]; ring
      _ = _ := by rw [hk,hf,←hN]; ring
  rw [law,integral_prod _ (e.recoil_int R A V k h hP κ)]
  simp_rw [hz,integral_const_mul]
  let w := ∫ Y, (∫ z, ‖v Y z‖ * L (e.image R A V k (Y,z)) ∂ cloud m) ∂ M
  change (∫ z, ‖u z‖ * L _ ∂ e.forest.order G) = y*a*r*w at hh
  simp_rw [← hl, integral_const_mul] at hh
  change t*i*_=q*(g*(b*w))
  rw [mul_comm t, mul_assoc, hh]
  calc
    _ = (i*y*a*r)*w := by ring
    _ = _ := by rw [hv]; ring

/-- True tail numerator in the *same* normalization. No normalized bound
for it from merely the integrability here. -/
theorem earn_eq {σ n Λ δ l : ℝ} {P : Teller G} (h : e.Receipt R) (hP : P.Funds S e.tube)
    (hR : R.Lawful σ n Λ δ l) (A : Stores S) (V : Config G c) (κ : ℝ) :
    earn S G e.x κ R.beta A.shares * leftOver e.book e.forest e.tube R A V =
      Real.exp (e.outside R V) * ∑ k, e.expense R A V k κ := by
  unfold leftOver Allocation.column tagTotal
  rw [←mul_assoc,Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => pair h hP hR A V k κ
end YM.AnalyticBridge.ResetIncome.Plate
