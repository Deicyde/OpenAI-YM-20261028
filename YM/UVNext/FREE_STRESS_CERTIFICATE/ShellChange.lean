import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Post
import YM.Work.A01.Conserve
import YM.Work.A01.Mirror

/-! Admissible changes to a Lighthouse under the *actual* delta side
condition. Not preservation assertions for an already-chosen weak comparison! -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Table Climb Work.A01 Work.A15 Next.UVStress Function Set MeasureTheory Filter Analysis
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} (HS : S.Hierarchy) {J : S.Stress}
variable {p : Climb.Parts S} {A : Ward.SpinRows S} (h : StressLaws S J p A)
include HS h

lemma scale_stress (c : ℝ) : StressLaws S (((c:ℝ):ℂ) • J) (c • p) (c • A) where
  translation := by
    intro n x hx q χ w b d B
    rw [← translationFlux_apply hx w HS.smooth q, map_smul, translationFlux_apply hx w HS.smooth q,h.translation hx q w, ← front_eval q x,← map_smul]
    rw [front_eval]; congr 3
  rotation := by
    intro n x hx q χ w g d B
    rw [← angularFlux_apply hx w HS.smooth q, map_smul, angularFlux_apply hx w HS.smooth q,h.rotation hx q w,← front_eval q x,← map_smul]
    rw [front_eval]; congr 3

omit h in
def pulsed (J : S.Stress) : S.Stress := fun a b => S.conj HS.spin _ (J a b)
omit h in
private lemma refl_tag (p : S.Tag) : realTag HS.spin (realTag HS.spin p) = p := by
  cases p; simp [realTag]; exact S.reflect_star ..

lemma reflected_law
    (hp : ∀ d b (v : S.Field d), S.conj HS.spin _ (p d b (S.conj HS.spin d v))=p d b v)
    (hA : ∀ d a (v : S.Field d), S.conj HS.spin _ (A d a (S.conj HS.spin d v))=A d a v) :
    StressLaws S (pulsed HS J) p A := by
  -- flux in *real*-reflected words (pairs of tag and position), no axis reflection
  have H1 {d n : ℕ} {x : Points (n+1)} (hx : x∈conf _) (q : Fin n → S.Tag) {χ} (hχ : Window x χ) (B : S.Field d) (V : E4→E4) :
      flux (pulsed HS J) χ V x q B = star (flux J χ V x (realTag HS.spin ∘ q) (S.conj HS.spin d B)) := by
    have he (a b : Axis) (y : E4) : term (pulsed HS J) χ V x q B a b y =
        star (term J χ V x (realTag HS.spin ∘ q) (S.conj HS.spin d B) a b y) := by
      by_cases ht : D (basis a) χ y=0
      · simp [term,ht]
      have hw := separated_of_D hx hχ ht
      unfold term; rw [star_mul', ← real_eval HS.laws.toSymmetric HS.spin hw, comp_cons, comp_cons,
        show realTag HS.spin ∘ realTag HS.spin ∘ q = q from funext fun i => refl_tag HS (q i)]
      simp only [realTag,pulsed,S.reflect_star,Complex.star_def,Complex.conj_ofReal]
    simp_rw [flux,he, star_neg,star_sum, Complex.star_def, integral_conj]
  have H2 {d n : ℕ} {x : Points (n+1)} (hx : x∈conf _) (q : Fin n → S.Tag) (B : S.Field d) :
      star (S.useAt S x (Fin.cons ⟨d,B⟩ (realTag HS.spin ∘ q))) = S.useAt S x (Fin.cons ⟨d,S.conj HS.spin d B⟩ q) := by
    rw [← real_eval HS.laws.toSymmetric HS.spin hx,comp_cons,show realTag HS.spin ∘ realTag HS.spin ∘ q=q from funext fun i => refl_tag HS (q i)]
    rfl
  constructor
  · intro n x hx q χ w b d B
    rw [← flux_translation,H1 hx q w,flux_translation,h.translation hx _ w,H2 hx q,hp]
  intro n x hx q χ w g d B
  rw [← flux_spin,H1 hx q w,flux_spin,h.rotation hx _ w,H2 hx q,hA]

omit h in
private def reflectC (d : ℕ) : S.Field d →L[ℝ] S.Field d := LinearMap.toContinuousLinearMap
    { toFun := S.conj HS.spin d
      map_add' := map_add _
      map_smul' t v := by simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ]; simp }

omit h in
lemma lie_real (W : DiffPlan S) (R : S.Rotation) (hR : R.Laws W HS.spin) (d a) (v : S.Field d) :
    S.conj HS.spin _ (R.lie d a (S.conj HS.spin d v))=R.lie d a v := by
  let L := reflectC HS d
  have he := L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hR.infinitesimal d a (L v))
  have ht := hR.infinitesimal d a v
  have hv (t : ℝ) : L (R.act d (Ortho.oneParameter a t) (L v)) = R.act d (Ortho.oneParameter a t) v := by
    change S.conj HS.spin _ _ = _; rw [hR.real, show S.conj HS.spin d (L v)=v from S.reflect_star ..]
  change HasDerivAt (L ∘ _) _ _ at he; simp_rw [Function.comp_def,hv] at he; exact he.unique ht

omit h in
def white (J : S.Stress) := (1/2:ℂ) • (J+pulsed HS J)

lemma averaged_white (W : DiffPlan S) (R : S.Rotation) (hR : R.Laws W HS.spin) (ho : W.Orientation HS.spin)
    (hv : W.deriv=p ∧ R.lie=A) : StressLaws S (white HS J) W.deriv R.lie := by
  obtain ⟨rfl,rfl⟩ := hv
  have hp := reflected_law HS h (fun d b v => by rw [ho.realDer,S.reflect_star]) (lie_real HS W R hR)
  constructor
  · intro n x hx q χ w b d B
    rw [white, ← translationFlux_apply hx w HS.smooth, map_smul, map_add]; simp_rw [translationFlux_apply]
    rw [h.translation hx q w,hp.translation hx q w,smul_eq_mul]; ring
  intro n x hx q χ w g d B
  rw [white, ← angularFlux_apply hx w HS.smooth,map_smul,map_add]; simp_rw [angularFlux_apply]
  rw [h.rotation hx q w,hp.rotation hx q w,smul_eq_mul]; ring

omit h in
lemma white_real (J : S.Stress) (a b : Axis) : S.conj HS.spin _ (white HS J a b) = white HS J a b := by
  unfold white pulsed
  simp only [Pi.smul_apply,Pi.add_apply,map_smulₛₗ,map_add,S.reflect_star,add_comm (S.conj _ _ _)]
  rw [show (starRingEnd ℂ) (1/2)= (1/2:ℂ) by rw [map_div₀,map_one,← one_add_one_eq_two,map_add,map_one]
     ]

omit h in
lemma plainTensor (W : DiffPlan S) (R : S.Rotation) (hR : R.Laws W HS.spin) (J : S.Stress) (he : Tensorial R J) : Tensorial R (white HS J) := by
  intro K a b
  unfold white pulsed
  simp only [Pi.smul_apply,Pi.add_apply,map_smul,map_add, ← hR.real,he K a b, map_sum, map_smulₛₗ, Finset.smul_sum,Finset.sum_add_distrib,smul_add]
  apply congr_arg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply Finset.sum_congr rfl <;> intro j _
  · rw [smul_comm]
  · rw [show (starRingEnd ℂ) ((↑(K.val i a * K.val j b)):ℂ) = (↑(K.val i a * K.val j b):ℂ) by simp, smul_comm]


omit h HS in
def fossil (t : Axis→Axis→ℂ) : S.Stress := fun a b => t a b • S.unit 4

omit h HS in
private lemma air_integral (χ : E4→ℝ) (w : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (c : Axis → Axis → ℂ) (hs : ∀ a b,c a b=c b a) (V : E4→E4) (hV : ∀ i : Axis, ContDiff ℝ ∞ fun y => V y i)
    (hv : killing V) :
    ∑ a : Axis, ∑ b : Axis, ∫ y : E4, D (basis a) χ y • (V y b • c a b) = 0 := by
  let f (a b : Axis) (y : E4) : ℂ := V y b • c a b
  have hf (a b) : ContDiff ℝ ∞ (f a b) := (hV b).smul contDiff_const
  have hg (a b : Axis) :
      (∫ y : E4, χ y • D (basis a) (f a b) y) = -(∫ y, D (basis a) χ y • f a b y) := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    · exact cutoff_integrable (hc.fderiv_apply ℝ _) (continuous_iff_continuousAt.mpr fun _ =>
        (dSmooth (m:=∞) w.contDiffAt _ (by simp)).continuousAt) fun _ _ => (hf _ _).continuous.continuousAt
    · exact cutoff_integrable hc w.continuous fun y _ => (dSmooth (m:=∞) (hf _ _).contDiffAt _ (by simp)).continuousAt
    · exact cutoff_integrable hc w.continuous fun _ _ => (hf _ _).continuous.continuousAt
    · exact fun _ _ => w.differentiable (by simp) _
    exact fun _ _ => (hf _ _).differentiable (by simp) _
  let Z (a b : Axis) := ∫ y, D (basis a) χ y • f a b y
  have ht (a b : Axis) : Z a b = - Z b a := by
    apply neg_injective
    unfold Z; rw [neg_neg,← hg a b,show (∫ y, D (basis b) χ y • f b a y)=-(∫ y, χ y • D (basis b) (f b a) y) by rw [hg b a, neg_neg], ← integral_neg]
    apply integral_congr_ae; filter_upwards with y
    have he (a b : Axis) : D (basis a) (f a b) y = (D (basis a) (fun y => V y b) y) • c a b := by
      let T := (ContinuousLinearMap.id ℝ ℝ).smulRight (c a b)
      change fderiv ℝ (T ∘ fun y => V y b) y (basis a) = _
      rw [fderiv_comp y T.differentiableAt ((hV b).differentiable (by simp) y), T.fderiv,ContinuousLinearMap.comp_apply]; rfl
    rw [he a b, hv a b y,neg_smul, hs a b,he, smul_neg]
  have hh : (∑ a, ∑ b, Z a b) = - (∑ a, ∑ b, Z a b) := by
    rw [← Finset.sum_neg_distrib,Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_); rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b _ => ht _ _)
  linear_combination (norm:=ring1) hh/2

omit h in
lemma unit_shell (t : Axis→Axis→ℂ) (he : ∀ a b,t a b=t b a) : StressLaws S (fossil (S:=S) t) 0 0 := by
  have H {d n : ℕ} {x : Points (n+1)} (hx : x∈conf _) (q : Fin n→S.Tag)
      (B : S.Field d) {χ} (hw : Window x χ) (V : E4→E4) (hV : ∀ i : Axis,ContDiff ℝ ∞ fun y => V y i)
      (hv : killing V) : flux (fossil t) χ V x q B = 0 := by
    let z := S.useAt S x (Fin.cons ⟨d,B⟩ q)
    have ht (a b) (y) : term (fossil t) χ V x q B a b y = D (basis a) χ y • (V y b • (t a b * z)) := by
      by_cases ha : D (basis a) χ y=0
      · simp [term,ha]
      have hsep := separated_of_D hx hw ha
      unfold term fossil
      rw [← front_eval _ _ 4 _, map_smul,front_eval,S.at_unit HS.laws hsep,show Points.tail (Points.cons y x)=x from PiLp.ext fun _ => rfl]
      simp [z,Complex.real_smul,mul_assoc]
    simp_rw [flux,ht,air_integral χ hw.1 hw.2.1 _ (fun a b => congr_arg (·*z) (he a b)) _ hV hv,neg_zero]
  constructor
  · intro n x hx q χ w b d B
    rw [← flux_translation,H hx q B w _ (fun _ => contDiff_const) (killing_const _)]
    exact (front_eval q x _ (0 : S.Field (d+1)) ▸ map_zero (frontRead q x (d+1))).symm
  intro n x hx q χ w g d B
  rw [← flux_spin]; change flux (fossil t) χ (orbital g (x 0)) x q B = _; rw [H hx q B w _ (smooth_orbital _ _) (killing_orbital _ _)]
  rw [← front_eval]; exact (map_zero (frontRead q x d)).symm

lemma add_unit (t : Axis→Axis→ℂ) (he : ∀ a b,t a b=t b a) : StressLaws S (J+fossil t) p A := by
  have hi := unit_shell HS t he
  constructor
  · intro n x hx q χ w b d B
    rw [← translationFlux_apply hx w HS.smooth, map_add]; simp_rw [translationFlux_apply]
    rw [h.translation hx q w,hi.translation hx q w, show ((0:Climb.Parts S) d b B)=0 from rfl, ← front_eval q x _ 0,map_zero,add_zero]
  intro n x hx q χ w g d B
  rw [← angularFlux_apply hx w HS.smooth,map_add]; simp_rw [angularFlux_apply]
  rw [h.rotation hx q w,hi.rotation hx q w, show (0:Ward.SpinRows S) d g B = 0 from rfl,← front_eval q x _ 0,map_zero,add_zero]

end YM.UVNext.FreeStress
