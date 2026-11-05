import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alphabet
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Ink
import YM.Push.FREE_RESOLVENT.JetWindows

/-!
# Compact shift for markings of genuine determinant

Reparameterizations also used for C^k *with tested positions*. Extensions
needn't meet the flag/mask tests along the arc; x fixed, shift varies freely.
No analytic branch/one-forms on eigenvector choices used. Non-Hermitian
`excess` calculation in separate file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Function Filter Set Matrix MeasureTheory FreeResolvent TestD Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Square ι} {W : ι→Set ι} {τ : Type*}

/-- `t` = attenuation. -/
def blend (A : Square ι) (t : ℝ) := 1+t • (A-1)

omit [Fintype ι] in
lemma blended (ha : A.PosDef) {t : ℝ} (ht : t∈Ink.interval) : (blend A t).PosDef := by
  rcases ht.1.eq_or_lt with h|h
  · rw [← h,blend,zero_smul,add_zero]; exact Matrix.PosDef.one
  rw [show blend A t=t • A + (1-t) • (1:Square ι) by unfold blend; rw [smul_sub,sub_smul,one_smul]; abel]
  exact (ha.smul h).add_posSemidef (Matrix.PosSemidef.one.smul (sub_nonneg.mpr ht.2))

lemma turned {u : ℝ} (h : A.PosDef) (hu : 0 ≤ u) : resolve A u = attenuation u • (blend A (attenuation u))⁻¹ := by
  let t := attenuation u
  let B := blend A t
  have ht : (1+u)*t=1 := mul_inv_cancel₀ (ne_of_gt (by positivity))
  have he : t • (A+u • 1)=B := by
    unfold B blend; rw [smul_add, smul_sub, smul_smul, show t*u=1-t by linarith only [ht], sub_smul, one_smul]; abel
  exact Matrix.inv_eq_right_inv (show (A+u • 1)*(t • B⁻¹)=1 from by rw [Matrix.mul_smul,← Matrix.smul_mul,he,
    Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ ((blended h ⟨(attenuation_pos hu).le,attenuation_le hu⟩).det_pos).ne')])

def manuscript (A : Square ι) (t : ℝ) := (A-1)*(blend A t)⁻¹
lemma scored (ha : A.PosDef) {u : ℝ} (hu : 0 ≤ u) : density A u = attenuation u^2 • manuscript A (attenuation u) := by
  let t := attenuation u; let B := blend A t
  have hh : B*B⁻¹=1 := Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (blended ha ⟨(attenuation_pos hu).le,attenuation_le hu⟩).det_pos.ne')
  have he : B⁻¹+t • ((A-1)*B⁻¹)=1 := by
    nth_rw 1 [show B=1+t • (A-1) from rfl, Matrix.add_mul, Matrix.one_mul,Matrix.smul_mul] at hh; exact hh
  rw [density,turned ha hu,← smul_sub]; change t • ((1:Square ι)-B⁻¹)=t^2 • ((A-1)*B⁻¹)
  rw [← show t • ((A-1)*B⁻¹)=1-B⁻¹ from eq_sub_of_add_eq' he, smul_smul, pow_two]

omit [Fintype ι] in
lemma adjusted (A : Square ι) (W : Set ι) (t : ℝ) : Next.SectorChange.Schur.principal (blend A t) W=blend (Next.SectorChange.Schur.principal A W) t := by
  unfold Next.SectorChange.Schur.principal blend; ext i j; simp [submatrix,Matrix.one_apply,Subtype.ext_iff]

def adjacent (W : ι → Set ι) (A : Square ι) (t : ℝ) := pie W (blend A t) 0
lemma adjusted_pie (W : ι→Set ι) (hw : ∀ i, i∈W i) {u : ℝ} (h : A.PosDef) (hu : 0 ≤ u) : pie W A u= attenuation u • adjacent W A (attenuation u) := by
  ext i j; by_cases he : i∈W j
  · rw [Matrix.smul_apply,pie_read _ _ u _ _ he (hw j),turned (A:=Next.SectorChange.Schur.principal A (W j)) (Matrix.PosDef.submatrix h Subtype.val_injective) hu]
    unfold adjacent; rw [pie_read _ _ _ _ _ he (hw j),adjusted, resolve, zero_smul, add_zero]; rfl
  unfold adjacent; rw [Matrix.smul_apply,pie_miss _ _ _ _ _ he,pie_miss _ _ _ _ _ he,smul_zero]

/-- E in manuscripts computed from adjacent via outside. No rerun of
precision tests, including at zero shift. -/
def afloat (hw : ∀ i, i∈W i) (A : Square ι) (t : ℝ) := (study W hw).outside (A*adjacent W A t)
lemma rises (hw : ∀ i, i∈W i) {u : ℝ} (h : A.PosDef) (hu : 0 ≤ u) : defect W A u = attenuation u • afloat hw A (attenuation u) := by
  let T := study W hw
  have hh := T.residual A u (fun j => IsUnit.mk0 _ (shift_posDef (h.submatrix Subtype.val_injective) hu).det_pos.ne')
  rw [defect_survey _ _ _ hw,hh]; unfold T at *
  rw [← pie_inspects,adjusted_pie W hw h hu,Matrix.mul_smul]; exact map_smul (outsideL (study W hw)) _ _

omit [DecidableEq ι] [Fintype ι] in
lemma all_saturated (A B : Square ι) (t : ℝ) (i j) {m : ℕ} (x : Fin m→ι) : road (t • A) (t • B) i j x=t^(m+1)*road A B i j x := by
  induction m generalizing A i with
  | zero => rw [road,road,pow_one]; rfl
  | succ m ih => rw [road,road,ih,Matrix.smul_apply,smul_eq_mul,pow_succ _ (m+1)]; ring

def fleece (hw : ∀ i, i∈W i) (A : Square ι) {n : ℕ} (i) (x : Fin (n+1)→ι) (t : ℝ) :=
  t^n * -road (adjacent W A t) (-afloat hw A t) i i x
lemma cloth (hw : ∀ i, i∈W i) (A : Square ι) (h : A.PosDef) {n : ℕ} (i) (x : Fin (n+1)→ι) (u : ℝ) (hu : 0 ≤ u) :
    scroll W A i x u=attenuation u^2 • fleece hw A i x (attenuation u) := by
  unfold scroll fleece; rw [adjusted_pie _ hw h hu,rises hw h hu, ← smul_neg, all_saturated,smul_eq_mul]; ring

section markings
variable {A : E → Square ι} {B : Square ι} {x : E} {s : ℝ} {k : ℕ}

omit [DecidableEq ι] in
lemma typed (h : ContDiffAt ℝ k A x) (i j : ι) : ContDiffAt ℝ k (fun y => A y i j) x := (evaluate i j).contDiff.contDiffAt.comp _ h
lemma reflected (h : ContDiffAt ℝ k A x) (he : IsUnit (A x).det) : ContDiffAt ℝ k (fun y => (A y)⁻¹) x := by
  rw [show (fun y => (A y)⁻¹)=action A 0 by unfold action resolve; simp]
  apply action_smooth _ h; unfold Neat; simpa only [zero_smul,add_zero]
lemma nested (h : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun p : E×ℝ => blend (A p.1) p.2) (x,s) :=
  contDiffAt_const.add (contDiffAt_snd.smul ((h.comp _ contDiffAt_fst).sub contDiffAt_const))
lemma embedded (h : ContDiffAt ℝ k A x) (he : (A x).PosDef) : Arc (fun p : E × ℝ => manuscript (A p.1) p.2) k x := fun _ ht =>
  prod_smooth ((h.comp _ contDiffAt_fst).sub contDiffAt_const) (reflected (nested h) (IsUnit.mk0 _ (blended he ht).det_pos.ne'))



omit [DecidableEq ι] in
lemma road_smooth {B : E → Square ι} (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x) {n : ℕ} (i j) (a : Fin n→ι) :
    ContDiffAt ℝ k (fun y => road (A y) (B y) i j a) x := by
  induction n generalizing i A with
  | zero => simp only [road]; exact typed hA i j
  | succ n ih => simp only [road]; exact (typed hA i (a 0)).mul (ih hB _ _)



variable [FiniteDimensional ℝ E] (v : τ → E)

lemma annotated_log (h : ContDiffAt ℝ k A x) (hw : ∀ᶠ y in 𝓝 x,(A y).PosDef) (i j : ι) :
    ContDiffAt ℝ k (fun y => logKernel (A y) i j) x ∧ ∀ l : List τ,l.length ≤ k →
      let g u := jet v (fun y=>density (A y) u i j) l x
      IntegrableOn g (Ioi 0) ∧ jet v (fun y=>logKernel (A y) i j) l x=∫ u in Ioi 0, g u :=
  panel_report (g:=fun p => manuscript (A p.1) p.2 i j) (fun _ hs => typed (embedded h hw.self_of_nhds _ hs) i j)
    (hw.mono fun y he u (hu : u∈Ioi 0) => show density (A y) u i j= _ from by rw [scored he hu.out.le]; rfl) v

lemma annotated_base (h : ContDiffAt ℝ k A x) (hw : ∀ᶠ y in 𝓝 x, (A y).PosDef) (hv : ∀ i, i∈W i) (i : ι) :
    ContDiffAt ℝ k (fun y => letterBase W (A y) i) x ∧ ∀ l : List τ,l.length ≤ k →
      let g u := jet v (fun y=> attenuation u - pie W (A y) u i i) l x
      IntegrableOn g (Ioi 0) ∧ jet v (fun y=> letterBase W (A y) i) l x = ∫ u in Ioi 0, g u := by
  let j : W i:= ⟨i,hv i⟩; let T : E → Square ↑(W i) := limitTo A Subtype.val
  have he := annotated_log (A:=T) v ((selectL (Subtype.val : W i→ι)).contDiff.contDiffAt.comp _ h)
    (hw.mono fun y he => he.submatrix Subtype.val_injective) j j
  have ht (y : E) (u : ℝ) : attenuation u - pie W (A y) u i i=density (T y) u j j := by
    unfold density; rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,smul_eq_mul,mul_one,pie_read _ _ _ _ _ (hv i) (hv i)]; rfl
  dsimp only; simp_rw [ht, show ∀ y : E, letterBase W (A y) i=logKernel (T y) j j from fun y => base_log hv _ i]; exact he

omit [FiniteDimensional ℝ E] in
lemma sculpted (h : ContDiffAt ℝ k A x) (he : (A x).PosDef) (hv : ∀ i,i∈W i) (u : ℝ) (hu : 0≤u) :
    ContDiffAt ℝ k (fun y=>pie W (A y) u) x := by
  apply rectangle_smooth; intro i j
  by_cases hx : i∈W j
  · simp_rw [pie_read _ _ _ _ _ hx (hv j)]
    let I:= W j
    let P := limitTo A (Subtype.val : I→ι)
    have hp : ContDiffAt ℝ k P x := (selectL (Subtype.val : W j→ι)).contDiff.contDiffAt.comp _ h
    exact typed (reflected (hp.add contDiffAt_const) (IsUnit.mk0 _ (shift_posDef (he.submatrix Subtype.val_injective) hu).det_pos.ne')) _ _
  simp_rw [pie_miss _ _ _ _ _ hx]; exact contDiffAt_const
omit [FiniteDimensional ℝ E] in
lemma bust (h : ContDiffAt ℝ k A x) (he : (A x).PosDef) (hv : ∀ i,i∈W i) (u : ℝ) (hu : 0≤u) : ContDiffAt ℝ k (fun y=>defect W (A y) u) x :=
  (prod_smooth (h.add contDiffAt_const) (sculpted h he hv u hu)).sub contDiffAt_const
omit [FiniteDimensional ℝ E] in
lemma lectern (h : ContDiffAt ℝ k A x) (he : (A x).PosDef) (hv : ∀ i,i∈W i) (u : ℝ) (hu : 0≤u) (i : ι) {n : ℕ} (a : Fin (n+1)→ι) :
    ContDiffAt ℝ k (fun y=>scroll W (A y) i a u) x := (road_smooth (sculpted h he hv u hu) (bust h he hv u hu).neg i i a).neg
end markings
end YM.AnalyticBridge.RelativeLogdet
