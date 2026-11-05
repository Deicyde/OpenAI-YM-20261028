import YM.Push.CORRECTED_COLUMNS.Calibration
import YM.Push.CUTOFF_PROJECTORS.Passage


/-!
# E(kpc)--(KCis) scales at fixed weak depths

`p` (nat) is the Family period index; `clock.monitor` (real) is E's p.
Use the ACTUAL β of the running represented trajectory (at m, NOT the
bare β of N); the thresholds are old hatted thresholds. These are matrices
on the actual sup-norm reference frames. No field-space rank supposition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Function Lattice Wilson Labels RG Cells Source Filter Extraction
open Push.Corrected Push.CutoffProjectors
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {d m k N p : ℕ}

abbrev θ (C : Family G) (m : ℕ) : ℝ := (C.path.levels.budget m).threshold
def actualG (C : Family G) (m N p : ℕ) : ℝ := (Real.sqrt (C.path.β N p m))⁻¹
def ratio (C : Family G) (m N p : ℕ) : ℝ := actualG C m N p / θ C m

lemma actualG_pos (h : C.Makes) (p) (hm : m ≤ N) : 0 < actualG C m N p := by
  apply inv_pos.mpr
  apply Real.sqrt_pos.2
  exact lt_of_lt_of_le (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed m)))
    (h.wilson.represents N p m hm).band.1

lemma ratio_pos (h : C.Makes) (p) (hm : m ≤ N) : 0 < ratio C m N p :=
  div_pos (actualG_pos h p hm) (C.path.levels.budget m).threshold_pos

private lemma squared (h : C.Makes) (p) (hm : m ≤ N) :
    (ratio C m N p)^2 * (C.path.levels.clock.monitor m)^2 =
      C.path.levels.clock.hatBeta m / C.path.β N p m := by
  let H := C.path.levels.clock
  let b := H.hatBeta m
  let p' := H.monitor m
  have hb : 0 < b := zero_lt_one.trans (C.path.levels.fits.delayed m)
  let B := C.path.β N p m
  have hB : 0 < B := lt_of_lt_of_le (half_pos hb) (h.wilson.represents N p m hm).band.1
  have hp : 0 < p' := Real.exp_pos _
  change ((Real.sqrt B)⁻¹ / ((Real.sqrt b)⁻¹ * p'))^2 * p'^2 = b/B
  rw [div_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hb.le, Real.sq_sqrt hB.le]
  field_simp

lemma ratio_budget (h : C.Makes) (p) (hm : m ≤ N) :
    1/2 ≤ (ratio C m N p)^2 * (C.path.levels.clock.monitor m)^2 ∧
      (ratio C m N p)^2 * (C.path.levels.clock.monitor m)^2 ≤ 2 := by
  rw [squared h p hm]; have hb := (h.wilson.represents N p m hm).band
  have he : 0<C.path.β N p m := lt_of_lt_of_le
    (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed m))) hb.1
  exact ⟨(le_div_iff₀ he).mpr (by linarith [hb.2]),(div_le_iff₀ he).mpr (by linarith [hb.1])⟩

lemma ratio_crude (h : C.Makes) (p) (hm : m ≤ N) :
    ratio C m N p ≤ 2 ∧ (ratio C m N p)⁻¹ ≤ 2*C.path.levels.clock.monitor m := by
  let s := ratio C m N p * C.path.levels.clock.monitor m
  have hR := ratio_pos h p hm
  have hs : s^2 ≤ 2 := by rw [show s^2=_ from mul_pow ..]; exact (ratio_budget h p hm).2
  have ht : 1/2 ≤ s^2 := by rw [show s^2=_ from mul_pow ..]; exact (ratio_budget h p hm).1
  have hp : 1 ≤ C.path.levels.clock.monitor m := Real.one_le_exp (sq_nonneg _)
  have hP : 0 < s := mul_pos hR (zero_lt_one.trans_le hp)
  refine ⟨(le_mul_of_one_le_right hR.le hp).trans (show s ≤ 2 by nlinarith only [hs]), ?_⟩
  have hh : 1/2 ≤ s := by nlinarith only [ht,hP]
  rw [← one_div, div_le_iff₀ hR, mul_assoc, mul_comm (C.path.levels.clock.monitor m)]
  linarith only [show 1/2 ≤ ratio C m N p*C.path.levels.clock.monitor m from hh]

/-- Reference norm. Convert only explicitly to orbit/chart norms and F.coeffSize. -/
abbrev Mat (C : Family G) (d : ℕ) := C.label d →L[ℂ] C.label d

/-- Use all canonical terms, **reference** coordinate v, then actual
`Factory` primary over m (including mesh/schedule scalars).
-/
def primaryMatrix (h : C.Makes) (p : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N) : Mat C d :=
  let T := C.factory d N p
  let A := (IsLinearMap.mk' _ (((h.calibrated _ _ p (hr.trans hm)).linear m hr hm).1))
  ((((C.S.a m:ℂ)^d)⁻¹) • (A.comp T.terminal.symm.toLinearMap)).toContinuousLinearMap

lemma primary_apply (h : C.Makes) (hr : C.ref d ≤ m) (hm : m ≤ N) (v : C.label d) :
    primaryMatrix h p hr hm v = Issue.primary C v m N p := rfl







/-- Scale for the lens geometry. Not slot scaling. -/
def zoom (F : Labels.Frame G d) (r : ℝ) : F.Coeff →ₗ[ℂ] F.Coeff where
  toFun v i := (↑(r^(F.grades i).1) : ℂ) * v i
  map_add' v w := by ext1; simp [mul_add]
  map_smul' c v := by ext1; simp; ring

lemma zoom_pure (F : Labels.Frame G d) (r : ℝ) (a : ℕ × ℕ) {x : Label G d} (h : x ∈ Grade a) :
    zoom F r (F.coords x) = (↑(r^a.1) : ℂ) • F.coords x := by
  funext i; by_cases he : a=F.grades i
  · rw [he]; rfl
  change _ * F.coords x i = _ * F.coords x i
  rw [F.power_coefficient i he h]; simp

lemma zoom_turn (F : Labels.Frame G d) (r : ℝ) (s : Ortho) (c : F.Coeff) :
    F.act s (zoom F r c) = zoom F r (F.act s c) := by
  obtain ⟨x,rfl⟩ := F.coords.surjective c
  have H : F.act s ∘ₗ zoom F r ∘ₗ F.coords.toLinearMap = zoom F r ∘ₗ F.act s ∘ₗ F.coords.toLinearMap := by
    refine F.basis.ext fun i => ?_
    let B := F.basis i
    have h : tensor s B ∈ Grade (F.grades i) := by
      have hx := gradePart_mem (F.grades i) (tensor s B)
      rw [gradePart_turn, gradePart_self B _ (F.pure i)] at hx; exact hx
    change F.act s (zoom F r (F.coords B)) = zoom F r (F.act s (F.coords B))
    rw [F.act_coords, zoom_pure F r _ h, zoom_pure F r _ (show B∈_ from F.pure i), map_smul, F.act_coords]
  exact LinearMap.congr_fun H _

variable (B : Series C)

def dress (k N p : ℕ) : Mat C d :=
  (((C.labels.level d).scaled (ratio C (B.depth k) N p)⁻¹).comp
    (zoom _ (B.inversePitch k))).toContinuousLinearMap

def undress (k N p : ℕ) : Mat C d :=
  ((zoom (C.labels.level d) (B.inversePitch k)⁻¹).comp ((C.labels.level d).scaled (ratio C (B.depth k) N p))).toContinuousLinearMap

lemma is_desired (v : C.label d) (k N p) : dress B k N p v = Issue.desired B v k N p := by
  funext i
  let P := (C.labels.level d).grades i
  change (↑(((ratio C (B.depth k) N p)⁻¹)^P.2) : ℂ) * (↑(B.inversePitch k ^ P.1) * v i)=
    (↑(B.inversePitch k ^ P.1 * (θ C (B.depth k)/actualG C (B.depth k) N p)^P.2) : ℂ)* v i
  rw [ratio, inv_div, Complex.ofReal_mul]; ring

@[simp] lemma undress_dress (h : C.Makes) (hr : B.depth k ≤ N) (v : C.label d) :
    undress B k N p (dress B k N p v) = v := by
  let F := C.labels.level d
  let r := ratio C (B.depth k) N p
  have hv : F.scaled r (dress B k N p v) = zoom F (B.inversePitch k) v := F.scaled_inv (ratio_pos h p hr).ne' _
  change zoom F _ (F.scaled r (dress B k N p v)) = _
  rw [hv]; have he : 0 < B.inversePitch k := Zone.pointed ..
  ext i; simp only [zoom, LinearMap.coe_mk, AddHom.coe_mk]; simp [he.ne']

lemma dress_bijective (h : C.Makes) (hr : B.depth k ≤ N) : Bijective (dress (d:=d) B k N p) :=
  let L := (dress (d:=d) B k N p).toLinearMap
  have hi : Function.Injective L := (show LeftInverse (undress B k N p) L from undress_dress B h hr).injective
  ⟨hi,LinearMap.surjective_of_injective hi⟩

lemma dress_signature (d k N p) :
    dress B k N p (C.labels.level d).e0 = (C.labels.level d).e0 ∧
    Commuting (C.labels.level d) (dress B k N p) := by
  rw [is_desired]
  refine ⟨Issue.desired_unit B k N p, ?_⟩; constructor
  · intro s x
    let F := C.labels.level d
    let a := B.inversePitch k; let b := ratio C (B.depth k) N p
    change F.scaled b⁻¹ (zoom F a (F.act (Signed.inclusionO s) x))=F.act _ (F.scaled b⁻¹ (zoom F a x))
    rw [← zoom_turn, F.scaling]
  intro x; ext i; rw [is_desired]
  change _ = star (dress B k N p x i); rw [is_desired]
  simp [Issue.desired]



section Fees














end Fees
end YM.Further.CorrectedLift
