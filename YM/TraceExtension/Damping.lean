import YM.Work.C23
import YM.Heat.Duration

/-!
# Single insertion point states and spectral representation

Work with the Hull on the *specified* contours so the normalization/edge and
field labels cannot slip. We use symmetric imaginary heights. No mass gap
or cone-support result for the chamber is assumed; at first we know only the
time-half-space support. Fourier convention `Probe.plane`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Complex Mink Boundary Spectral OS
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace

variable {G : Gauge} {L : Register G} {S T : Table L} {C : Chamber T timeAxis}
  {F : Waves S} {B : Small S C} {J : StarOp S}

/-- imaginary heights of the two-point continuation -/
def pairH (s : ℝ) : Heights 2 := Bid.bothH (n := 1) (m := 1) (fun _ => s) (fun _ => s)
def pairV (J : StarOp S) (v : S.Union) : Fin 2 → S.Union :=
    Bid.bothT (n := 1) (m := 1) (fun _ => v) (fun _ => v) J

@[simp] lemma pairH_zero (s) : pairH s 0 = -s := rfl
@[simp] lemma pairH_one (s) : pairH s 1 = s := rfl

@[simp] lemma pairV_zero (J : StarOp S) (v) : pairV J v 0 = J v := rfl
@[simp] lemma pairV_one (J : StarOp S) (v) : pairV J v 1 = v := rfl

lemma ample_single {p : ℝ≥0} {s : ℝ} : Small.ample p (fun _ : Fin 1 => s) ↔
    0 < p ∧ p < 1 ∧ 4*(p:ℝ)<s := by
  constructor
  · intro h; exact ⟨h.1.1,h.1.2.1,h.2 0⟩
  rintro ⟨hp,hq,h⟩; exact ⟨⟨hp,hq, fun i j e => False.elim ((ne_of_lt e) (Subsingleton.elim i j))⟩, fun _ => h⟩

lemma ample_logD {s : ℝ} (hs : 0 < s) : Small.ample (Small.logD s) (fun _ : Fin 1 => s) := by
  have h := Small.suitable (n := 1) hs
  rwa [show Small.profile s 1=(fun _ : Fin 1 => s) by
    funext i; rw [Subsingleton.elim i 0]; simp [Small.profile]] at h

lemma positive_single {s : ℝ} (hs : 0<s) : (fun _ : Fin 1 => s) ∈ positiveHeight 1 :=
  ⟨fun _ _ h => False.elim (ne_of_lt h (Subsingleton.elim ..)),fun _ => hs⟩

lemma east_pairH {s : ℝ} (hs : 0<s) : pairH s ∈ east 2 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd h (by decide)) | simpa using (neg_lt_self hs)

lemma self_ample (h : Bid.Hull B F J) (v : S.Union) (s : ℝ) (hs : 0<s) {p q : ℝ≥0}
    (hp : Small.ample p (fun _ : Fin 1 => s)) (hq : Small.ample q (fun _ : Fin 1 => s)) :
    B.shot p 1 (fun _ => v) (fun _ => s) 0 = B.shot q 1 (fun _ => v) (fun _ => s) 0 := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [h.join 1 1 _ _ p p _ _ (positive_single hs) (positive_single hs) hp hp,
             h.join 1 1 _ _ p q _ _ (positive_single hs) (positive_single hs) hp hq,
             h.join 1 1 _ _ q p _ _ (positive_single hs) (positive_single hs) hq hp,
             h.join 1 1 _ _ q q _ _ (positive_single hs) (positive_single hs) hq hq, sub_self]

/-- State at spatial and real-time zero with positive imaginary height `s` (junk at zero). -/
def pointState (B : Small S C) (v : S.Union) (s : ℝ≥0) : C.H :=
  B.shot (Small.logD s) 1 (fun _ => v) (fun _ => (s:ℝ)) 0

private lemma shot_eq_flow (v : S.Union) (p s : ℝ≥0) (hs : p<s) :
    B.shot p 1 (fun _ => v) (fun _ => (s:ℝ)) 0 = C.flow.E (s-p) (B.bar p v C.omega) := by
  have hi : Small.interval (shift (0:Points 1) (fun _ => (s:ℝ)) 0) p = OS.Semigroup.duration (s-p) := by
    apply Complex.ext <;> simp [Small.interval,shift,OS.Semigroup.duration, NNReal.coe_sub hs.le]
  have hy : Small.bufferF (trace (0:Points 1) 0)=0 := by
    apply Subtype.ext; apply ext_by
    · change spatial (position _ 0) = spatial 0; simp [trace]
    change time (position _ 0) = time 0; simp
  change C.flow.F _ (C.flow.U _ (B.bar p v C.omega)) = _
  rw [hi, C.flow.roots_heat (tsub_pos_of_lt hs), hy,C.flow.uZero]
  rfl

lemma pointState_add (h : Bid.Hull B F J) (v : S.Union) (s t : ℝ≥0) (hs : 0<s) :
    pointState B v (s+t) = C.flow.E t (pointState B v s) := by
  let p := Small.logD s
  have hc : 0<(s:ℝ) := hs; have hh : 0<((s+t:ℝ≥0):ℝ) := by positivity
  have hp : 0<p ∧ p<1 ∧ 4*(p:ℝ)<s := ample_single.mp (ample_logD hc)
  have hm : s ≤ s+t := le_self_add
  have he : Small.ample p (fun _ : Fin 1 => ((s+t:ℝ≥0):ℝ)) :=
    ample_single.mpr ⟨hp.1,hp.2.1,hp.2.2.trans_le hm⟩
  have hu : p<s := by change (p:ℝ)<(s:ℝ); linarith [hp.2.2,p.property]
  rw [pointState,self_ample h v _ hh (ample_logD hh) he,shot_eq_flow v p (s+t) (hu.trans_le hm)]
  change _=C.flow.E t (B.shot p 1 (fun _ => v) (fun _ => (s:ℝ)) 0)
  rw [shot_eq_flow v p s hu, ← ContinuousLinearMap.comp_apply (C.flow.E t), ← OS.Semigroup.time]
  congr 1
  rw [add_comm s,add_tsub_assoc_of_le hu.le]

lemma shifted_state (B : Small S C) (v : S.Union) (s : ℝ≥0) (hs : 0<s) (x : E4) :
    B.shot (Small.logD s) 1 (fun _ => v) (fun _ => (s:ℝ)) (points (fun _ => x)) =
      C.flow.unit.translation x (pointState B v s) := by
  rw [← zero_add (points (n := 1) (fun _ => x))]
  exact Work.C23.shot_shift B _ 1 _ _ 0 x (ample_logD hs)

private lemma orbit_inner {H : Hilbert} (U : Orbit H E4) (a b : E4) (v w : H) :
    inner ℂ (U.translation a v) (U.translation b w) = inner ℂ v (U.translation (b-a) w) := by
  let I : H →ₗᵢ[ℂ] H := ⟨(U.translation a).toLinearMap, U.unitary a⟩
  have hh : U.translation a (U.translation (b-a) w) = U.translation b w := by
    rw [← ContinuousLinearMap.comp_apply, U.sends, add_sub_cancel]
  rw [← hh]; exact I.inner_map_map ..

lemma pair_restricted (h : Bid.Hull B F J) (v : S.Union) (s : ℝ≥0) (hs : 0<s) (x : Points 2) :
    F.restricted (pairV J v) (pairH s) x =
      charFun (C.flow.ℚmeasure.diagonal (pointState B v s)) (x 1 - x 0) := by
  let p : Points 1 := points (fun _ => x 0); let q : Points 1 := points (fun _ => x 1)
  have he := h.join 1 1 (fun _ => v) (fun _ => v) (Small.logD s) (Small.logD s) _ _
    (positive_single (show 0 < (s:ℝ) from hs)) (positive_single (show 0 < (s:ℝ) from hs)) (ample_logD hs) (ample_logD hs) p q
  change _=F.restricted (pairV J v) (pairH s) _ at he
  have hx : Bid.bothP p q = x := by
    ext1 i; fin_cases i <;> rfl
  rw [hx] at he; dsimp only [p,q] at he
  rw [← he, C.flow.joint,shifted_state B v s hs,shifted_state B v s hs,orbit_inner]

/-- Undamped positive Borel measure. Fixed reference height 1. -/
def spectralMeasure (B : Small S C) (v : S.Union) : Measure E4 :=
    OS.Semigroup.transform timeAxis (-2:ℝ) (C.flow.ℚmeasure.diagonal (pointState B v 1))

lemma undamp (h : Bid.Hull B F J) (v : S.Union) (s : ℝ≥0) (hs : 0<s) : spectralMeasure B v =
    OS.Semigroup.transform timeAxis (-2*(s:ℝ)) (C.flow.ℚmeasure.diagonal (pointState B v s)) := by
  have he a (ha : 0 < a) (b : ℝ≥0) :
      OS.Semigroup.transform timeAxis (-2*((a+b:ℝ≥0):ℝ)) (C.flow.ℚmeasure.diagonal (pointState B v (a+b))) =
      OS.Semigroup.transform timeAxis (-2*(a:ℝ)) (C.flow.ℚmeasure.diagonal (pointState B v a)) := by
    rw [pointState_add h v _ _ ha, C.flow.damp, OS.Semigroup.growth]; congr 1; push_cast; ring
  rw [← he _ hs 1, add_comm s, he _ one_pos s]; simp only [NNReal.coe_one,mul_one]; rfl

lemma damp (h : Bid.Hull B F J) (v : S.Union) (s : ℝ≥0) (hs : 0<s) :
    OS.Semigroup.transform timeAxis (2*(s:ℝ)) (spectralMeasure B v)=C.flow.ℚmeasure.diagonal (pointState B v s) := by
  rw [undamp h _ _ hs, OS.Semigroup.growth, show -2*(s:ℝ)+2*(s:ℝ)=0 by ring, OS.Semigroup.stays_put]

instance (v : S.Union) : SigmaFinite (spectralMeasure B v) := SigmaFinite.withDensity_of_ne_top
    (ae_of_all _ fun _ => ENNReal.coe_ne_top)
lemma ae_time (v : S.Union) : ∀ᵐ p ∂spectralMeasure B v, 0 ≤ time p :=
  (C.flow.bright _).filter_mono (Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous ..))

lemma pair_at (h : Bid.Hull B F J) (v : S.Union) (s : ℝ≥0) (hs : 0 < s) (x : Points 2) :
    F.restricted (pairV J v) (pairH s) x = ∫ p, Real.exp (- (2*(s:ℝ)) * time p) • Probe.plane p (x 1-x 0) ∂ spectralMeasure B v := by
  rw [pair_restricted h v s hs,← damp h v s hs,charFun_apply, OS.Semigroup.transform,
      integral_withDensity_eq_integral_smul (OS.Semigroup.measurable ..)]
  rfl

end YM.TraceExtension
