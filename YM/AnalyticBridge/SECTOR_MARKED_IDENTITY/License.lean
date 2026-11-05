import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Recut

set_option warningAsError false

/-!
# Actual tagged transition of a marked vector density

`Permission` supplies absolute integrability (slice, each frozen section and
joint; integrals against the Gaussian with the guards **still present**)
as well as equality, even with norms INSIDE. Just `Envelope` on the input
observable, on this fixed finite volume. No need for e.g. derivatives of
forced occurrences or nonvanishing of R.eval. Summing all stores and tags
of an actual gauge invariant input gives the push pointwise. This sums k
only once regardless of the number of marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Gaussian Rows YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid
open YM.Push.SectorMeasure YM.Next.Fluctuations.Sector
open YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x w : ℝ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (R : Rep G f)
  (W : Stencils S) (F : Forest S.ratio) (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)
  (C : Gaussian.Table (Rows.In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))

def before (u : Config G f → X) := D.portion A F V (through S F R.beta V (fun _ a => u (F.drape a))) k

/-- All unmarked scalar factors appropriate to `ink`; e.g., for u carrying
the v-volume exponent, that v part remains inside recut. Chart/determinant
charge computed on active positions only, not on any identity completion. -/
def outside : ℝ := sieve T R.beta x V * prefactor S G R.beta *
    J.scale ^ Fintype.card (Active A x F) * chartCost C (coupling R.beta)

def afterChange (u : Config G f → X) :=
  outside T x V A R F J C • ∫ Y, (∫ z, ink T x V k A R W F D q J d C m u Y z ∂cloud C)
    ∂piHaar G (Frozen A x F)

lemma before_eq (ht : Fits T R x) (h : S.patch.Branches S.kernel G) (u : Config G f → X) :
    before x V k A R F D u = fun a => sieve T R.beta x V • attending D A F V k (dress T x V k A R u) a := by
  funext a; unfold before Allocation.portion through attending
  rw [uncover ht u, ← dress_eq _ _ _ _ _ _ h, mul_smul, smul_comm]

lemma before_norm (u : Config G f → X) :
    before x V k A R F D (fun U => ‖u U‖) = fun a => ‖before x V k A R F D u a‖ := by
  funext a; unfold before Allocation.portion through
  simp only [smul_eq_mul,norm_smul, Real.norm_of_nonneg (D.nonneg ..), Real.norm_of_nonneg (kernel_nonneg ..)]

/-- CompleteSpace needed when *using* the equality. No positivity price from
`outside` claimed on wrong-flag records, which contribute zero. -/
structure Permission (u : Config G f → X) : Prop where
  slice : Integrable (before x V k A R F D u) (F.order G)
  fibre : ∀ Y, Integrable (ink T x V k A R W F D q J d C m u Y) (cloud C)
  pair : Integrable (uncurry (ink T x V k A R W F D q J d C m u))
    ((piHaar G (Frozen A x F)).prod (cloud C))
  result : (∫ a, before x V k A R F D u a ∂F.order G) = afterChange T x V k A R W F D q J d C m u
  absolute : (∫ a, ‖before x V k A R F D u a‖ ∂F.order G) = outside T x V A R F J C *
    ∫ Y, (∫ z, ‖ink T x V k A R W F D q J d C m u Y z‖ ∂cloud C) ∂piHaar G (Frozen A x F)

lemma wrong (hV : A.flags≠RG.flags (temp x) V) (u : Config G f → X) :
    before x V k A R F D u = 0 ∧ ink T x V k A R W F D q J d C m u = 0 := by
  have he (U : Config G f) : D.bill A k U V = 0 := not_not.mp fun hx => hV (D.actual _ _ _ _ hx).exactFlags
  constructor
  · funext a; simp [before,Allocation.portion, he]
  funext Y z; simp [ink,backdrop, he]

section License
variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]
variable {σ n Λ δ l : ℝ} {P : Teller G} {C m}
    (h : R.Lawful σ n Λ δ l) (hT : P.Funds S T) (ht : Fits T R x)

include h hT ht
private theorem transport (hp : Permitted x V k A F D J d R.beta C m) {u : Config G f → X}
    (hg : Envelope u) :
    let v := ink T x V k A R W F D q J d C m u
    let p := before x V k A R F D u
    Integrable p (F.order G) ∧
      (∀ Y, Integrable (v Y) (cloud C)) ∧
      Integrable (uncurry v) ((piHaar G (Frozen A x F)).prod (cloud C)) ∧
      ((∫ a, p a ∂F.order G) = afterChange T x V k A R W F D q J d C m u) := by
  intro v p
  obtain ⟨_, _, hH,_⟩ := hT.feeds
  let r := regularized D A F V k q J d (dress T x V k A R u)
  let s := prefactor S G R.beta
  let b := coupling R.beta
  let t := chartCost C b
  have hh := dress_envelope T x V k A R h hT hg
  obtain ⟨hl,hY,hπ,_,hr⟩ := regularized_price D A F V k hp.trueChart q hp.doorPos hp.scalePaid hp.core _
    (funds_branch hT) hh
  have hb : 0<b := coupling_pos hp.bpos
  have hs : 0<s := prefactor_pos _
  have ht' : 0<t := chartCost_pos C hp.nativePos hb
  have he (Y z) : Real.exp (force C z/2) • r Y (displaced (m Y) b z) = s • v Y z :=
    (ink_regularized T x V k A R W F D q J d C m hH hp.bpos u Y z).symm
  have hy Y : Integrable (v Y) (cloud C) := by
    have hi := (at_price C hp.nativePos hb (m Y) (r Y)).1.mp (hY Y)
    simp_rw [he] at hi
    have hu := hi.smul s⁻¹
    change Integrable (s⁻¹ • s • v Y) _ at hu
    simpa only [smul_smul,inv_mul_cancel₀ hs.ne',one_smul] using hu
  have hm : Measurable (uncurry v) := by
    let L (y : LinkArray G (Frozen A x F) × Prices G (Active A x F)) := (y.1, displaced (m y.1) b y.2)
    have hL : Measurable L := measurable_fst.prodMk (tape.measurable.comp
      ((hp.shift.comp measurable_fst).add (by fun_prop)))
    have hf : Continuous (fun z : Prices G (Active A x F) => force C z) := by unfold force dotProduct mulVec; fun_prop
    have hM : Measurable (uncurry r) := regularized_meas D A F V k hp.trueChart q hp.doorPos hp.scalePaid _
      (funds_branch hT) hh
    convert! (measurable_const (a:=s⁻¹)).smul
      ((Real.continuous_exp.measurable.comp ((hf.measurable.comp measurable_snd).div_const 2)).smul (hM.comp hL)) using 1
    funext y
    change v y.1 y.2 = s⁻¹ • (Real.exp (force C y.2/2) • r y.1 (displaced (m y.1) b y.2))
    rw [he, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  refine ⟨?_,hy,(integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall hy,?_⟩,?_⟩
  · unfold p; rw [before_eq T x V k A R F D ht (funds_branch hT)]; exact hl.smul _
  · let M := piHaar G (Frozen A x F)
    let τ (Y : LinkArray G (Frozen A x F)) := ∫ z, ‖v Y z‖ ∂cloud C
    have hx (Y) : (∫ a, ‖r Y a‖) = (t*s)*τ Y := by
      have ho (z : Prices G (Active A x F)) := congr_arg (‖·‖) (he Y z)
      simp only [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg hs.le] at ho
      calc
        _ = t * ∫ z, Real.exp (force C z/2) * ‖r Y (displaced (m Y) b z)‖ ∂cloud C :=
             (at_price C hp.nativePos hb (m Y) (fun a => ‖r Y a‖)).2
        _ = _ := by simp_rw [ho,integral_const_mul]; unfold τ; ring
    change Integrable (fun Y => ∫ a, ‖r Y a‖) M at hπ
    simp_rw [hx] at hπ
    have hi := hπ.smul (t*s)⁻¹
    change Integrable ((t*s)⁻¹ • (t*s) • τ) _ at hi
    rw [smul_smul, inv_mul_cancel₀ (mul_pos ht' hs).ne', one_smul] at hi
    exact hi
  have ht'' (Y) : (∫ a, r Y a)=(t*s) • ∫ z,v Y z ∂cloud C := by
    have hw := (at_price C hp.nativePos hb (m Y) (r Y)).2
    simp_rw [he,integral_smul, smul_smul] at hw
    exact hw
  unfold p; rw [before_eq T x V k A R F D ht (funds_branch hT), integral_smul, hr]
  change sieve T R.beta x V • (J.scale ^ Fintype.card (Active A x F) • ∫ Y, (∫ a, r Y a) ∂_) =
    (_ * s * _ * t) • ∫ Y, (∫ a, v Y a ∂cloud C) ∂_
  simp_rw [ht'', integral_smul, smul_smul]
  ac_rfl

/-- The fixed Output V theorem. No GI requirement here; the multiplier can be
made after local choices of tag-dependent data. For going all the way back to
the physical `StepData.push` use a common gauge invariant u. -/
theorem fixed (hp : A.flags=RG.flags (temp x) V → Permitted x V k A F D J d R.beta C m)
    {u : Config G f → X} (hg : Envelope u) : Permission T x V k A R W F D q J d C m u := by
  by_cases he : A.flags=RG.flags (temp x) V
  · obtain ⟨hp',hY,hπ,H⟩ := transport T x V k A R W F D q J d h hT ht (hp he) hg
    have hn : Envelope (fun U => ‖u U‖) := by
      obtain ⟨hs,B,hB⟩ := hg
      exact ⟨hs.norm,B,fun U => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hB U)⟩
    have hx := (transport T x V k A R W F D q J d h hT ht (hp he) hn).2.2.2
    rw [before_norm] at hx
    simp_rw [afterChange, ink_norm] at hx
    exact ⟨hp',hY,hπ,H,hx⟩
  obtain ⟨hz,hθ⟩ := wrong T x V k A R W F D q J d C m he u
  constructor
  · rw [hz]; exact integrable_zero ..
  · intro Y; rw [hθ]; exact integrable_zero ..
  · rw [hθ]; exact integrable_zero ..
  · simp only [afterChange, hz,hθ]; simp
  · rw [hz,hθ]; simp

end License
end YM.Next.SectorChange.Marked
