import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Receipts
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Sensitive
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Suppression

/-!
# Held conditional integral comparison for the normalized Gaussian input

First use only moving arguments inside central guards: Healthy flag predicates
at X pass there. Then remove Γ from polynomial evaluation of the first-order
forecast, on the target covariance. Compare forecasts using established
weighted prices. Can even remove Γ on actual tested moments with or without
the mask by paying enough from the *same* Gaussian tail amount. This is not
comparing at any further occurrence multipliers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid Gaussian
open Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local
open MeasureTheory SectorTools.PhysicalGaussianSwitch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

open FreeResolvent (treeInverse insertion ix flatten tensor)
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S}
  {I : Type} {F : Forest S.ratio}

/-- A Gaussian payment on one held neighborhood. No conclusion about
health farther than those monitored plaquettes. Q positive issued by h.Read,
D set by requesting application family, and ζ rebased in same gauge. -/
structure Paying (x β : ℝ) (Pt : Patch) {o : Site c} (T : Tube G S) (H L : Bed) (V : Config G c)
    (v : Dir G c) (Q : Gaussian.Table (In x A F (G:=G))) (a : Vec (In x A F (G:=G)))
    (Y : LinkArray G (Frozen A x F)) (ε : ℝ) (X : Support f) (W : Finset (Bond f)) (l D : ℕ) (U : ℝ) : Prop where
  frame : Clears A x o (radiusB x)
  reachable : Reachable S o x W
  watches : Covers X W
  radius : 0 < ε
  charges : Rates G Pt D x β U
  block : S.patch=Pt
  truePrice : ReadPrice Q (treeInverse G S F H.metric 0) a (portrait_head T F v) (coupling β)
    (accessing A F x W G) (loading A F x W G) x U
  core : ∀ Z, Guards W Z (ε*(fiery G x Pt.L/coupling β)) → Central (o:=o) v V T H L a Z Y X W (coupling β) (fiery G x Pt.L) l
  remain : (cloud Q).real (away W (ε*(fiery G x Pt.L/coupling β)/2)) ≤ x^(-(↑D+2):ℝ)

section
variable {Pt : Patch} {x β : ℝ} {o : Site c} {a : Vec (In x A F (G:=G))}
  {T : Tube G S} {Q : Gaussian.Table (In x A F (G:=G))}
  {H L : Bed} {v : Dir G c} {V : Config G c} {Y : LinkArray G (Frozen A x F)} {ε : ℝ}
  {X : Support f} {W : Finset (Bond f)} {l D : ℕ} {U : ℝ}
  [Fintype I] [DecidableEq I] (P : I → Occasion G f) (r : I → G.El)
variable {Γ : Vec (In x A F (G:=G)) → ℝ}

omit [DecidableEq I] in
lemma Paying.foreseen (h : Paying x β Pt (o:=o) T H L V v Q a Y ε X W l D U) (hP : Looks P X l x) :
    ‖forecast P r H L T (coupling β) V‖ ≤ fiery G x Pt.L/coupling β := by
  let t:= fiery G x Pt.L; let g:=coupling β
  have ht : 0<t := h.charges.alive; have hg : 0<g := coupling_pos h.charges.high
  refine ((h.core 0 (fun i => ?_)).sighted P r hg h.charges.big ht hP).1
  have hf : 0 < ε := h.radius
  change ‖(0 : G.Color)‖ ≤ ε*(t/g); rw [norm_zero]; positivity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {R : Vec I → E} {a' : ℝ} {u : Vec I}

-- exact read measure & mean normalization (uses weighted exact shifts)


omit [DecidableEq I] [CompleteSpace E] in
lemma Paying.dropping (h : Paying x β Pt (o:=o) T H L V v Q a Y ε X W l D U) (hP : Looks P X l x)
    (hΓ : GuardPrice W Γ (ε*(fiery G x Pt.L/coupling β)))
    (hu : ‖u‖ ≤ fiery G x Pt.L/coupling β) (hR : TestPrice R D a') :
    let g:=coupling β; let m:=forecast P r H L T g V - u
    let Φ z := R (m+wind P r (rebase T v a g W z))
    Integrable Φ (cloud Q) →
    ‖(∫ z, Γ z • Φ z ∂cloud Q) - ∫ z,Φ z ∂cloud Q‖ ≤ a'*x^(-(1/16):ℝ) := by
  intro g m B hI
  let t:=fiery G x Pt.L
  have hg : 0 < g := coupling_pos h.charges.high
  have hv : t/g ≤ 4*meter x := h.charges.forecastPrice
  have hm : ‖m‖ ≤ 8*meter x := (norm_sub_le ..).trans
    ((add_le_add ((h.foreseen P r hP).trans hv) (hu.trans hv)).trans_eq (by ring))
  have H' := forecast_price P r hP h.frame h.watches h.reachable hm hR (F:=F)
  let s:=away (F:=F) (A:=A) (x:=x) (G:=G) W (ε*(t/g)/2)
  have hs : MeasurableSet s := away_meas ..
  apply (drop_guard hΓ.borel hΓ.probability s hs (fun z he => hΓ.plateau z (not_not.mp he)) hI).trans
  let N:= rebase T v a g W
  have hρ := h.truePrice.targetLaw
  rw [show inUnits _ _ ∘ physicalRead _ _ _=N from ?_] at hρ
  swap; exact (funext fun z => (rebase_equal T v a hg.ne' W z).symm)
  have hf : 0 ≤ a' := hR.nonneg
  have hx := h.charges.big
  have hl := small_payment hρ ((h.truePrice.paid.moments (ceiling_pays Pt A F h.block h.reachable G) (highMoment D)).1)
    (D:=D) (by unfold highMoment; omega) B (a'*forecastFare G D x) H'.nonneg hI (fun z => H'.size _) s hs x (by linarith)
  apply hl.trans
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hf
  let k := ceiling G Pt x; let y:=momentFare k D U;let Z:= forecastFare G D x
  have hh : (cloud Q).real s ≤ x^(-(2:ℝ)) := h.remain.trans
    (Real.rpow_le_rpow_of_exponent_le hx (by have hD : (0:ℝ) ≤ D := Nat.cast_nonneg _; linarith only [hD]))
  apply le_trans _ h.charges.flagPrice
  rw [mul_add]; apply add_le_add
  · exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (by linarith)) (forecastFare_nn ..)).trans_eq (mul_comm ..)
  exact le_rfl

-- Paid on the true full Gaussian for either masked/unmasked use.
-- Don't let this license integrability over interactions.
omit [DecidableEq I] [CompleteSpace E] [NormedSpace ℝ E] in
theorem Paying.globally (h : Paying x β Pt (o:=o) T H L V v Q a Y ε X W l D U)
    (hu : ‖u‖ ≤ fiery G x Pt.L/coupling β) (hR : Sensitive R D a') :
    let g:=coupling β; let t:=fiery G x Pt.L
    let f' z := physical A F V Y (tape (a+g • z))
    let V' y := R (sampled P r g y - u)
    let V z := V' (f' z); let Z z := masked t X V' (f' z)
    Integrable V (cloud Q) ∧ Integrable Z (cloud Q) ∧
    ∀ z, ‖V z‖ ≤ a'*x^D ∧ ‖Z z‖ ≤ a'*x^D := by
  intro g t f' V' B Z
  obtain ⟨H,hv⟩ := sample_price P r h.charges R hR.toTestPrice u hu
  have hm : Measurable f' := by
    have H' : Measurable (fun z : Vec (In x A F (G:=G)) => a+g • z) :=
      Continuous.measurable (by fun_prop)
    let q (z : Vec (In x A F (G:=G))) := tape (a+g • z)
    have he : Measurable (fun z : Vec (In x A F (G:=G)) => (Y,q z)) :=
      measurable_const.prodMk (tape.measurable.comp H')
    change Measurable (uncurry (Next.SectorChange.physical A F V) ∘ (fun z => (Y,q z)))
    have hv := Measurable.comp (physical_meas (x:=x) A F V) he
    exact hv
  let M := cloud Q
  have hd := hR.nonneg
  have hx : 1≤x := h.charges.big
  have hB z : ‖Z z‖ ≤ a'*x^D := by
    unfold Z
    by_cases he : Healthy t X (f' z)
    · rw [masked_eq _ _ _ _ he]; exact hv _
    rw [masked_ne _ _ _ _ he,norm_zero]; positivity
  have he : StronglyMeasurable Z := by
    have ht : StronglyMeasurable (masked t X V') := H.indicator ((healthy_closed t X).measurableSet)
    exact ht.comp_measurable hm
  have hi := integrable_const (μ:=cloud Q) (a'*x^D)
  exact ⟨hi.mono' ((H.comp_measurable hm).aestronglyMeasurable) (Eventually.of_forall fun z => hv (f' z)),
    hi.mono' he.aestronglyMeasurable (Eventually.of_forall hB), fun z => ⟨hv _,hB z⟩⟩

omit [DecidableEq I] [CompleteSpace E] in
lemma Paying.guarded (h : Paying x β Pt (o:=o) T H L V v Q a Y ε X W l D U) (hP : Looks P X l x)
    (hΓ : GuardPrice W Γ (ε*(fiery G x Pt.L/coupling β))) (hu : ‖u‖ ≤ fiery G x Pt.L/coupling β) (hR : Sensitive R D a') :
    let g:=coupling β; let t:=fiery G x Pt.L
    let S' z := physical A F V Y (tape (a+g • z))
    let m:=forecast P r H L T g V - u
    let f' y := R (sampled P r g y - u)
    let V z := f' (S' z); let Z z := masked t X f' (S' z)
    let f' z := R (m+wind P r (rebase T v a g W z))
    Integrable f' (cloud Q) →
    (∀ z, Γ z • V z=Γ z • Z z) ∧
      Integrable (fun z => Γ z • Z z) (cloud Q) ∧
      ‖(∫ z, Γ z • Z z ∂cloud Q) - ∫ z,Γ z • f' z ∂cloud Q‖ ≤ a'*x^(-(1/16):ℝ) := by
  intro g t S' m f' B B' Φ hI
  let M := cloud Q; let E':= x^(-(1/16):ℝ)
  have ht : 0<t := h.charges.alive
  have hx := h.charges.big
  have hX := zero_lt_one.trans_le hx
  have he : 0 ≤ a'*E' := mul_nonneg hR.nonneg (Real.rpow_nonneg hX.le _)
  have HZ z (hz : Γ z≠0) := h.core z (hΓ.support z hz)
  have hh z (hz : Γ z≠0) : B z=B' z := (masked_eq t X f' (S' z) ((HZ z hz).heat _ ht.le Y)).symm
  have h' z : Γ z • B z=Γ z • B' z := by by_cases hz : Γ z=0; rw [hz,zero_smul,zero_smul]; rw [hh z hz]
  have hJ := integrable_product (h.globally P r hu hR).2.1 hΓ.borel hΓ.probability
  refine ⟨h',hJ,?_⟩
  apply inside hJ (integrable_product hI hΓ.borel hΓ.probability)
  intro z
  rw [← h' z,← smul_sub]
  by_cases hz : Γ z=0
  · rw [hz,zero_smul,norm_zero]; exact he
  rw [norm_smul,Real.norm_of_nonneg (hΓ.probability z).1]
  refine (mul_le_of_le_one_left (norm_nonneg _) (hΓ.probability z).2).trans ?_
  obtain ⟨-,hb,hb'⟩ := (HZ z hz).sighted P r (coupling_pos h.charges.high) hx h.charges.alive hP
  let w := sampled P r g (S' z);let j := wind P r (rebase T v a g W z);let a := w-u;let b := m+j
  let Q' := 1 + 8*meter x;let d:=x^(-(1/8):ℝ)
  have hv : ‖a-b‖ ≤ d := by
    rw [show a-b=w-(forecast P r H L T g V+j) by unfold a b m; abel]
    exact hb'
  have hp : 0 ≤ 8*meter x := by have := meter_pos x; positivity
  have hf : 1 ≤ Q' := le_add_of_nonneg_right hp
  have ha : ‖a‖ ≤ 8*meter x := (norm_sub_le ..).trans ((add_le_add (hb.trans h.charges.forecastPrice) (hu.trans h.charges.forecastPrice)).trans_eq (by ring))
  have hl := Real.rpow_le_one_of_one_le_of_nonpos hx (show -(1/8:ℝ)≤0 by norm_num)
  have ht : ‖b‖ ≤ Q' := (norm_le_norm_sub_add ..).trans (add_le_add ((norm_sub_rev _ _).le.trans (hv.trans hl)) ha)
  exact (hR.stable a b Q' hf (ha.trans (le_add_of_nonneg_left zero_le_one)) ht).trans
    ((mul_le_mul_of_nonneg_left hv (mul_nonneg hR.nonneg (by positivity))).trans
      (Eq.trans_le (mul_assoc ..) (mul_le_mul_of_nonneg_left h.charges.closePrice hR.nonneg)))

omit [Fintype I] [DecidableEq I] [CompleteSpace E] in
lemma Paying.other_side (h : Paying x β Pt (o:=o) T H L V v Q a Y ε X W l D U)
    (hΓ : GuardPrice W Γ (ε*(fiery G x Pt.L/coupling β)))
    {a' : ℝ} (he : 0≤a') {f : Vec (In x A F (G:=G)) → E} (hI : Integrable f (cloud Q))
    (hs : ∀ z, ‖f z‖≤a'*x^D) :
    ‖(∫ z,Γ z • f z ∂cloud Q)-(∫ z,f z ∂cloud Q)‖ ≤ a'*x^(-(1/16):ℝ) := by
  let s:=away W (F:=F) (x:=x) (A:=A) (G:=G) (ε*(fiery G x Pt.L/coupling β)/2)
  have hm : MeasurableSet s := away_meas ..
  apply (drop_guard hΓ.borel hΓ.probability s hm (fun z hz => hΓ.plateau z (not_not.mp hz)) hI).trans
  have hv : 0 ≤ x := zero_le_one.trans h.charges.big
  let c := a'*x^D; let H:=cloud Q
  calc
    _ ≤ ∫ _z in s, c ∂H := setIntegral_mono_on hI.norm.integrableOn (integrable_const _) hm fun z _ => hs z
    _ = H.real s * c := by rw [setIntegral_const]; rfl
    _ ≤ x^(-(↑D+2):ℝ)* (a'*x^D) := mul_le_mul_of_nonneg_right h.remain (show 0≤a'*x^D by positivity)
    _ ≤ _ := by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left h.charges.tailPrice he
end
end YM.PhysicalNext.PhysicalGuard7f546.Curved
