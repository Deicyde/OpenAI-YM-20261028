import YM.Work.A01.Support

/-!
# Local integration by parts

`current` and its divergence are used with the support of χ disjoint
from *all* inserts (after removal of the unit). Outside this good region,
we make no claim of regularity of `current` itself. The integration by
parts lemma used here only requires differentiability on the crossed
supports, and we pay all integrability hypotheses by compact support.
The result also applies with no inserts left at all.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A01
open Table Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {n d : ℕ}

def headDir (n : ℕ) : E4 →L[ℝ] Points (n+1) := LinearMap.toContinuousLinearMap
  { toFun y := Points.cons y (0:Points n)
    map_add' y z := by
      ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons]
    map_smul' c y := by
      ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons] }

theorem shifting_head (x : Points n) : (fun y => Points.cons y x) =
    fun y => headDir n y + Points.cons 0 x := by
  funext y; ext1 i; change _ = (Points.cons y (0:Points n) + Points.cons 0 x) i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons]

theorem smooth_cons (S : Table L) (h : S.Smooth) (v : S.Tag) {x : Points n} (q : Fin n → S.Tag)
    {y : E4} (hy : Points.cons y x ∈ conf _) :
    ContDiffAt ℝ ∞ (fun z => S.useAt S (Points.cons z x) (Fin.cons v q)) y := by
  have hu : ContDiff ℝ ∞ (fun p => Points.cons p x) := by
    rw [shifting_head]; exact (headDir n).contDiff.add contDiff_const
  exact (((S.class_smooth S h _ _ hy).contDiffAt ((conf_open _).mem_nhds hy))).comp y hu.contDiffAt

theorem D_cons (h : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S) (v : S.Field d)
    {x : Points n} (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) (a : Axis) :
    D (basis a) (fun p => S.useAt S (Points.cons p x) (Fin.cons ⟨d,v⟩ q)) y =
      S.useAt S (Points.cons y x) (Fin.cons ⟨d+1,W.deriv d a v⟩ q) := by
  let F := fun p : Points (n+1) => S.useAt S p (Fin.cons ⟨d,v⟩ q)
  let u := fun p => Points.cons p x
  have hu : HasFDerivAt u (headDir n) y := by
    unfold u; rw [shifting_head]
    exact (headDir n).hasFDerivAt.add_const _
  have he : DifferentiableAt ℝ F (u y) :=
    ((S.class_smooth S h _ _ hy).contDiffAt ((conf_open _).mem_nhds hy)).differentiableAt (by simp)
  rw [hd.kernels d a v hy]
  change fderiv ℝ (F ∘ u) y (basis a) = _
  rw [fderiv_comp y he hu.differentiableAt, hu.fderiv, ContinuousLinearMap.comp_apply,
    show headDir n (basis a) = Points.direction 0 a from ?_]
  · rfl
  · ext1 i; change Points.cons (basis a) 0 i = _
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, Points.direction]

/-- V contracts the second index. The fixed x,q are arbitrary (here used
for the actual exterior insertions after deleting the unit). -/
def current (J : S.Stress) (V : E4 → E4) (x : Points n) (q : Fin n → S.Tag) (a : Axis) (y : E4) :=
  ∑ b : Axis, V y b • S.useAt S (Points.cons y x) (Fin.cons ⟨4,J a b⟩ q)

def killing (V : E4 → E4) := ∀ (a b : Axis) (x : E4),
  D (basis a) (fun y => V y b) x = - D (basis b) (fun y => V y a) x

theorem killing_const (y : E4) : killing fun _ => y := by intro a b x; simp [D]

def orbital (u : Ortho.Skew) (x : E4) : E4 → E4 := fun y => M4.move u.val (y-x)

private def row (u : Ortho.Skew) (b : Axis) : E4 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun y := M4.move u.val y b
    map_add' y z := congr_arg (fun p : E4 => p b) (map_add (Matrix.toEuclideanLin u.val) y z)
    map_smul' c y := congr_arg (fun p : E4 => p b) (map_smul (Matrix.toEuclideanLin u.val) c y) }

theorem smooth_orbital (u : Ortho.Skew) (w : E4) (b : Axis) :
    ContDiff ℝ ∞ (fun x => orbital u w x b) := (row u b).contDiff.comp (contDiff_id.sub contDiff_const)

theorem killing_orbital (u : Ortho.Skew) (w : E4) : killing (orbital u w) := by
  intro a b x
  have he (i j : Axis) : D (basis i) (fun y => orbital u w y j) x = u.val j i := by
    rw [show (fun y => orbital u w y j) = fun y => row u j y - row u j w from funext fun y => map_sub (row u j) y w]
    unfold D
    rw [fderiv_fun_sub (row u j).differentiableAt (differentiableAt_const _), (row u j).fderiv]
    rw [(hasFDerivAt_const ((row u j) w) x).fderiv, sub_zero]
    exact M4.move_basis u.val j i
  rw [he,he]
  have ht := congr_arg (fun A : M4 => A a b) (show star u.val = -u.val from u.property)
  simpa using ht

theorem smooth_current (J : S.Stress) (V : E4 → E4) {x : Points n} (q : Fin n → S.Tag) (a : Axis)
    {y : E4} (hV : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hy : Points.cons y x ∈ conf _)
    (hs : S.Smooth) : ContDiffAt ℝ ∞ (current J V x q a) y := by
  change ContDiffAt ℝ ∞ (fun _ => ∑ _, _) _
  exact ContDiffAt.sum fun b _ => (hV b).contDiffAt.smul (smooth_cons S hs _ q hy)

theorem divergence (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S) {H : S.RealSpin}
    (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b))
    (hk : killing V) {x : Points n} (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current J V x q a) y = 0 := by
  let F (a b : Axis) (p : E4) := S.useAt S (Points.cons p x) (Fin.cons ⟨4,J a b⟩ q)
  let T a b := D (basis a) (fun z => V z b) y • F a b y
  let R (a b : Axis) := V y b • S.useAt S (Points.cons y x)
    (Fin.cons ⟨4+1,W.deriv 4 a (J a b)⟩ q)
  have hf (a b : Axis) : DifferentiableAt ℝ (F a b) y :=
    (smooth_cons S hs _ q hy).differentiableAt (by simp)
  have hp (b : Axis) : DifferentiableAt ℝ (fun z => V z b) y := (hv b).differentiable (by simp) y
  have he (a b : Axis) : D (basis a) (fun z => V z b • F a b z) y = T a b + R a b := by
    calc
      _ = D (basis a) (fun z => V z b) y • F a b y + V y b • D (basis a) (F a b) y := by
        unfold D; rw [fderiv_fun_smul (hp b) (hf a b)]; simp [add_comm]
      _ = _ := by
        change _ + V y b • D (basis a) (fun z => F a b z) y = _
        unfold F
        rw [D_cons hs W hd _ q hy a]
  have hi (a : Axis) : D (basis a) (current J V x q a) y = ∑ b : Axis, (T a b + R a b) := by
    change fderiv ℝ (fun z => ∑ b : Axis, V z b • F a b z) y _ = _
    rw [fderiv_fun_sum fun b _ => (show DifferentiableAt ℝ (fun z => V z b • F a b z) y from
        (hp b).smul (hf a b)), _root_.sum_apply]
    exact Finset.sum_congr rfl fun b _ => he a b
  simp_rw [hi, Finset.sum_add_distrib]
  have ht : ∑ a, ∑ b, R a b = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero
    intro b _
    simp_rw [R, ← front_eval, ← Finset.smul_sum, ← map_sum, hJ.divergence, map_zero, smul_zero]
  have ha : ∀ a b, T a b = -T b a := by
    intro a b; unfold T; rw [hk, neg_smul, show F a b y = F b a y from by unfold F; rw [hJ.symmetric a b]]
  let z := ∑ a, ∑ b, T a b
  have hh : z = -z := calc
    z = ∑ b, ∑ a, (-T a b) := by
      apply Finset.sum_congr rfl; intro a _
      exact Finset.sum_congr rfl fun b _ => ha a b
    _ = -(∑ b, ∑ a, T a b) := by simp_rw [Finset.sum_neg_distrib]
    _ = -z := by rw [Finset.sum_comm]
  have hh' : (2:ℂ)*z = 0 := by
    rw [two_mul]; conv_lhs => lhs; rw [hh]
    exact neg_add_cancel z
  rw [ht,add_zero]; exact (mul_eq_zero.mp hh').resolve_left (by norm_num)

/-- Integrability even if g has junk off the crossed support neighborhood. -/
theorem cutoff_integrable {f : E4 → ℝ} (hf : HasCompactSupport f) (hp : Continuous f) {g : E4 → ℂ}
    (hg : ∀ y ∈ tsupport f, ContinuousAt g y) : Integrable (fun y => f y • g y) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hf.smul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases he : x ∈ tsupport f
  · exact hp.continuousAt.smul (hg x he)
  · refine continuousAt_const.congr (show (fun _ : E4 => (0:ℂ)) =ᶠ[𝓝 x] (fun y => f y • g y) from ?_)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he] with y hy
    simp [hy]

/-- Integration by parts against the compactly supported cutoff χ, away
from the points of the word. No conditions at infinity on the readout. -/
theorem cutoff_zero (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S) {H : S.RealSpin}
    (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b))
    (hk : killing V) (x : Points n) (q : Fin n → S.Tag) (χ : E4 → ℝ) (hw : ContDiff ℝ ∞ χ)
    (hχ : HasCompactSupport χ) (hp : ∀ y ∈ tsupport χ, Points.cons y x ∈ conf _) :
    - (∑ a : Axis, ∫ y : E4, D (basis a) χ y • current J V x q a y) = 0 := by
  let F := current J V x q
  have hF (a : Axis) (y) (hy : y ∈ tsupport χ) : ContDiffAt ℝ ∞ (F a) y :=
    smooth_current J V q a hv (hp y hy) hs
  have h1 (a : Axis) : Integrable fun y => D (basis a) χ y • F a y := by
    refine cutoff_integrable (hχ.fderiv_apply ℝ (basis a)) ?_ ?_
    · exact continuous_iff_continuousAt.mpr (fun y =>
        (dSmooth (m:=∞) (hw.contDiffAt (x:=y)) (basis a) (by simp)).continuousAt)
    · exact fun y hy => (hF a y (tsupport_fderiv_apply_subset ℝ _ hy)).continuousAt
  have h2 (a : Axis) : Integrable fun y => χ y • D (basis a) (F a) y := cutoff_integrable hχ hw.continuous
    (fun y hy => (dSmooth (m:=∞) (hF a y hy) _ (by simp)).continuousAt)
  have he (a : Axis) : (∫ y, χ y • D (basis a) (F a) y) = -∫ y, D (basis a) χ y • F a y :=
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (h1 a) (h2 a)
      (cutoff_integrable hχ hw.continuous (fun y hy => (hF a y hy).continuousAt))
      (fun y _ => hw.differentiable (by simp) y) (fun y hy => (hF a y hy).differentiableAt (by simp))
  have ht (y : E4) : (∑ a, χ y • D (basis a) (F a) y) = 0 := by
    by_cases hx : y ∈ tsupport χ
    · rw [← Finset.smul_sum, divergence hs W hd J hJ V hv hk q (hp y hx), smul_zero]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  change -(∑ a, ∫ y, D (basis a) χ y • F a y) = 0
  rw [← Finset.sum_neg_distrib]
  simp_rw [← he]
  rw [← integral_finsetSum _ (fun a _ => h2 a)]
  simp_rw [ht]; simp

theorem flux_unit (h : S.Basic) (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S) {H : S.RealSpin}
    (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b))
    (hk : killing V) {x : Points (n+1)} (hx : x ∈ conf _) (q : Fin n → S.Tag) (χ : E4 → ℝ)
    (hw : Window x χ) (d : ℕ) : flux J χ V x q (S.unit d) = 0 := by
  have h0 (y : E4) (hy : y ∈ tsupport χ) : Points.cons y (Points.tail x) ∈ conf _ := by
    refine conf_cons (Points.tail_in hx) (fun i he => ?_)
    exact hw.2.2.2 i (he ▸ hy)
  have he (a b : Axis) (y : E4) : term J χ V x q (S.unit d) a b y = D (basis a) χ y •
      (V y b • S.useAt S (Points.cons y (Points.tail x)) (Fin.cons ⟨4,J a b⟩ q)) := by
    by_cases ht : D (basis a) χ y = 0
    · simp [term,ht]
    · unfold term
      have hy := separated_of_D hx hw ht
      rw [exchange_use h.toSymmetric hy, S.at_unit h (Points.rearrange_in _ hy), exchange_positions]
      simp [Complex.real_smul,mul_assoc]
  have hi (a : Axis) : (∑ b, (∫ y, term J χ V x q (S.unit d) a b y)) =
      ∫ y, D (basis a) χ y • current J V (Points.tail x) q a y := by
    rw [← integral_finsetSum _ (fun b _ => term_integrable J χ V x q (S.unit d) hs hx hw a b (hv b).continuous)]
    simp_rw [he, current, Finset.smul_sum]
  simp_rw [flux, hi]
  exact cutoff_zero hs W hd J hJ V hv hk (Points.tail x) q χ hw.1 hw.2.1 h0
end YM.Work.A01
