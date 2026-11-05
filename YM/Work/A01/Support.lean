import YM.Euclid.Window
import YM.Org.Input

/-!
# Shell comparisons on the all-spectator quotient (A01): tools

`flux` contracts J with a position-dependent vector, allowing us to treat
both the translation and the angular shell, always at the actual points. We
use it with smooth V. `term_integrable`: even for continuous multiplier,
with window support, these are genuine integrals. No comparison/regularity
of readouts off configuration space is needed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A01
open Table Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} {d n : ℕ}

theorem exists_window (x : Points (n+1)) (hx : x ∈ conf _) : ∃ χ, Window x χ := by
  let F : Fin n → E4 := fun i => x i.succ
  have hx' : x 0 ∈ (range F)ᶜ := by
    rintro ⟨i, he⟩
    exact Fin.succ_ne_zero i ((show Injective x.ofLp from hx) he)
  have hu := (finite_range F).isClosed.isOpen_compl.mem_nhds hx'
  obtain ⟨r, hr, hs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hu
  let B : ContDiffBump (x 0) := ⟨r/2,r,by positivity,by linarith⟩
  refine ⟨B, B.contDiff, B.hasCompactSupport, B.eventuallyEq_one, ?_⟩
  intro i
  rw [B.tsupport_eq]
  exact fun hi => hs hi ⟨i,rfl⟩

theorem conf_cons {x : Points n} (hx : x ∈ conf n) {y : E4} (h : ∀ i, y ≠ x i) :
    Points.cons y x ∈ conf _ := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) j
    simp [Points.cons,h]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Points.cons, Ne.symm (h i)]
    · simp only [Points.cons, points_apply, Fin.cons_succ]
      exact fun he => congr_arg Fin.succ ((show Injective x.ofLp from hx) he)

/-- The closed gradient-support also avoids all points, including the center. -/
theorem window_separated {x : Points (n+1)} (hx : x ∈ conf _) {χ : E4 → ℝ} (w : Window x χ)
    {y : E4} (hy : y ∈ tsupport (fderiv ℝ χ)) : Points.cons y x ∈ conf _ := by
  refine conf_cons hx fun i => Fin.cases ?_ (fun j => ?_) i
  · rintro rfl
    apply (show x 0 ∉ tsupport (fderiv ℝ χ) from ?_) hy
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [w.2.2.1.fderiv (𝕜 := ℝ)] with z hz
    simp [hz]
  · rintro rfl
    exact w.2.2.2 j (tsupport_fderiv_subset ℝ hy)

theorem separated_of_D {x : Points (n+1)} (hx : x ∈ conf _) {χ : E4 → ℝ} (w : Window x χ)
    {y : E4} {a : Axis} (h : D (basis a) χ y ≠ 0) : Points.cons y x ∈ conf _ := by
  apply window_separated hx w
  apply subset_closure
  change fderiv ℝ χ y ≠ 0
  exact fun he => h (by simp [D, he])

/-- First-slot quotient readout at fixed all-spectator word. -/
def frontRead (q : Fin n → S.Tag) (x : Points (n+1)) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  Ward.here (Fin.cons ⟨d,(0:S.Field d)⟩ q) x 0 d

theorem front_eval (q : Fin n → S.Tag) (x) (d) (p : S.Field d) :
    frontRead q x d p = S.useAt S x (Fin.cons ⟨d,p⟩ q) := by
  unfold frontRead
  rw [Ward.takes, Fin.update_cons_zero]; rfl

theorem comp_cons {I M : Type*} (f : I → M) (p : I) (q : Fin n → I) :
    f ∘ (Fin.cons (α := fun _ : Fin (n+1) => I) p q) = Fin.cons (f p) (f ∘ q) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

def exchangeFirst (n : ℕ) := Equiv.swap (0 : Fin (n+2)) (0 : Fin (n+1)).succ

theorem exchange_use {x : Points (n+2)} (hp : S.Symmetric) (hx : x ∈ conf _) (A B : S.Tag)
    (q : Fin n → S.Tag) : S.useAt S x (Fin.cons A (Fin.cons B q)) =
      S.useAt S (Points.rearrange (exchangeFirst n) x) (Fin.cons B (Fin.cons A q)) := by
  conv_lhs => rw [← S.class_perm S hp (exchangeFirst n) hx]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [exchangeFirst]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [exchangeFirst]
    · rw [Function.comp_apply, exchangeFirst, Equiv.swap_apply_of_ne_of_ne
        (Fin.succ_ne_zero k.succ) (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero k))]
      simp

theorem exchange_positions (x : Points (n+1)) (y : E4) :
    Points.tail (Points.rearrange (exchangeFirst n) (Points.cons y x)) = Points.cons y (Points.tail x) := by
  ext1 i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Points.tail, exchangeFirst, Points.cons]
  · simp only [Points.tail, points_apply, Points.rearrange_at]
    rw [exchangeFirst, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k.succ)
      (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero k))]
    simp [Points.cons]

section Flux
variable (J : S.Stress) (χ : E4 → ℝ) (V : E4 → E4) (x : Points (n+1))
variable (q : Fin n → S.Tag) (B : S.Field d)

def term (a b : Axis) (y : E4) :=
  ((D (basis a) χ y * V y b : ℝ) : ℂ) *
    S.useAt S (Points.cons y x) (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ q))

def flux := - ∑ a : Axis, ∑ b : Axis, ∫ y : E4, term J χ V x q B a b y

theorem term_integrable (h : S.Smooth) (hx : x ∈ conf _) (hw : Window x χ) (a b : Axis)
    (hV : Continuous fun y => V y b) : Integrable (term J χ V x q B a b) := by
  have hp : Continuous fun y => ((V y b : ℝ) : ℂ) := Complex.continuous_ofReal.comp hV
  change Integrable (fun y => term J χ V x q B a b y)
  simpa only [term, Complex.ofReal_mul] using integrableShell hx hw h
    (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ q)) a (fun y => ((V y b : ℝ) : ℂ)) hp

theorem flux_translation (c : Axis) :
    flux J χ (fun _ => basis c) x q B = shellGrad S J χ c x q B := by
  unfold flux shellGrad
  apply congr_arg Neg.neg
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · simp [term]
  · intro b _ hb; simp [term,basis_eq,hb]

theorem flux_spin (u : Ortho.Skew) :
    flux J χ (fun y => M4.move u.val (y - x 0)) x q B = shellSpin S J χ u x q B := rfl

theorem flux_scale (c : ℝ) :
    flux J χ (fun y => c • V y) x q B = (c:ℂ) * flux J χ V x q B := by
  have H (a b : Axis) (y : E4) : term J χ (fun y => c • V y) x q B a b y =
      (c:ℂ) * term J χ V x q B a b y := by
    simp only [term, Complex.ofReal_mul, PiLp.smul_apply, smul_eq_mul]
    ring
  simp_rw [flux, H, integral_const_mul, mul_neg, Finset.mul_sum]

end Flux

/-- Inclusion tested also below the stress slot; uses `useAt` only on Conf. -/
theorem flux_inclusion {x : Points (n+1)} (hp : S.Symmetric) (hx : x ∈ conf _) (W : DiffPlan S)
    (hi : W.Inclusions S) (J : S.Stress) {χ : E4 → ℝ} (hw : Window x χ) (V : E4 → E4)
    (B : S.Field d) (q : Fin n → S.Tag) {e : ℕ} (he : d ≤ e) :
    flux J χ V x q (W.rise he B) = flux J χ V x q B := by
  have ht (a b : Axis) (y : E4) : term J χ V x q (W.rise he B) a b y = term J χ V x q B a b y := by
    by_cases hz : D (basis a) χ y = 0
    · simp [term, hz]
    unfold term
    have hy := separated_of_D hx hw hz
    rw [exchange_use hp hy, hi.kernels he B (Points.rearrange_in _ hy), exchange_use hp hy]
  simp_rw [flux, ht]

end YM.Work.A01
