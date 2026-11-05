import YM.Extra.MULTISOURCE_TRAJECTORIES.Block
import YM.Next.FOUNDATIONS.LinkBounds
/-!
# Unnormalized complete marker coefficients on the actual blocking trajectory

Including the common scalar and physical dimension changes.

Argument `j` is
the CURRENT level, `N` is the fine cutoff.

Beyond N values are just padding.

Normalization before taking connected coefficients is by the common TOTAL
positive vacuum density at level j, not the partition function and never a
single K.

For numerical estimates this is a substantive choice of algorithm!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Function Lattice Wilson RG Overlay Marker Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

def readM (d : Step) (x : Site n) (A : Field G n) := if d.neg then star (A (d.used x)) else A (d.used x)

def along (A : Field G n) (x : Site n) : Walk → G.Mat
  | [] => 1
  | d::w => readM d x A * along A (x+d.vec) w

lemma readM_smooth (d : Step) (x : Site n) : ContDiff ℝ ∞ (readM (G:=G) d x) := by
  unfold readM; split
  · exact (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (contDiff_apply ℝ _ _)
  exact contDiff_apply ℝ _ _

lemma along_smooth (x : Site n) (w : Walk) : ContDiff ℝ ∞ (fun A : Field G n => along A x w) := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ih => exact (readM_smooth d x).mul (ih _)

lemma along_agrees (x : Site n) (w : Walk) (U : Config G n) : along (matrixField U) x w = G.mat (travel U x w) := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => simp only [along, travel,readM,Step.read,G.mat_mul,ih]; split <;> rfl

def thermal (β : ℝ) (A : Field G n) := Real.exp (-β * ∑ p : Face (Per n),mPrice G (along A p.1 (square p.2.val.1 p.2.val.2)))

lemma thermal_agrees (β : ℝ) (U : Config G n) : thermal β (matrixField U) = bare β U := by simp only [thermal,along_agrees]; rfl

lemma thermal_smooth (β : ℝ) : ContDiff ℝ ∞ (thermal (G:=G) (n:=n) β) :=
    Real.contDiff_exp.comp (contDiff_const.mul (ContDiff.sum fun _ _ => (price_smooth G).comp (along_smooth ..)))

variable {N p : ℕ} {H : RG.History G} {V : Type} [DecidableEq V] {R : Census V}
structure Insertions (H : RG.History G) (V : Type) (N p : ℕ) where
  load : V → ℕ
  field : V → Field G (H.S.side N p) → ℂ
  smooth i : ContDiff ℝ ∞ (field i)

namespace Insertions
variable (A : Insertions H V N p)

def uses (i : V) := A.field i ∘ matrixField

def Symmetric := ∀ i, GaugeInvariant (A.uses i)

def source (s : R.Mode) (x : Field G (H.S.side N p)) := Ride.bump (H.S.a N) s A.load *
    (thermal (H.β N p N) x:ℂ) * ∏ i∈s.val,A.field i x

lemma source_eq (s : R.Mode) (U : Config G (H.S.side N p)) :
    A.source s (matrixField U) = Ride.bump (H.S.a N) s A.load * (bare (H.β N p N) U:ℂ)*Ride.Product (H:=H) A.uses s U := by
  unfold source; rw [thermal_agrees]; rfl

lemma source_smooth (s : R.Mode) : ContDiff ℝ ∞ (A.source s) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (thermal_smooth _))).mul (smooth_prod _ _ fun i _ => A.smooth i)

def step (j : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Field G (H.S.side (j+1) p) → E) :=
    extended (H.levels.clock.op j p) (H.β N p (j+1)) (F ∘ matrixField)

lemma step_push (j : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Field G (H.S.side (j+1) p) → E} (hf : Continuous F) (U : Config G (H.S.side j p)) :
    step (H:=H) (p:=p) (N:=N) j F (matrixField U) = (H.levels.clock.op j p).push (H.β N p (j+1)) (F ∘ matrixField) U :=
  extended_push _ (H.levels.blocks j p).branches (hf.comp matrixField_cont) ..

def vacuum (H : History G) (N p j : ℕ) : Field G (H.S.side j p) → ℝ :=
    if h : j=N then by subst j; exact thermal (H.β N p N)
    else if j<N then step (H:=H) (p:=p) (N:=N) j (vacuum H N p (j+1)) else 1
termination_by N-j

@[simp] lemma vac_top : vacuum H N p N = thermal (H.β N p N) := by rw [vacuum]; simp
lemma vac_step (j : ℕ) (hj : j<N) : vacuum H N p j = step (H:=H) (N:=N) j (vacuum H N p (j+1)) := by rw [vacuum]; simp [hj,hj.ne]
lemma vac_smooth {j : ℕ} (hj : j ≤ N) : ContDiff ℝ ∞ (vacuum H N p j) := by
  induction hj using Nat.decreasingInduction with
  | self => rw [vac_top]; exact thermal_smooth ..
  | of_succ j hj ih => rw [vac_step j hj]; exact extended_smooth _ (H.levels.blocks ..).branches (ih.continuous.comp matrixField_cont) _
lemma vac_pos {j : ℕ} (hj : j ≤ N) (x) : 0 < vacuum H N p j x := by
  induction hj using Nat.decreasingInduction with
  | self => rw [vac_top]; exact Real.exp_pos _
  | of_succ j hj ih => rw [vac_step j hj]; exact extended_pos _ (H.levels.blocks ..).branches ((vac_smooth hj).continuous.comp matrixField_cont) (fun U => ih _) ..
lemma vac_eq (h : H.Selected) {j : ℕ} (hj : j ≤ N) : vacuum H N p j ∘ matrixField = (H.rep N p j).eval := by
  induction hj using Nat.decreasingInduction with
  | self => rw [vac_top,(h.starts ..).2]; exact funext (thermal_agrees _)
  | of_succ j hj ih =>
    funext U; rw [vac_step j hj,comp_apply, step_push j (vac_smooth hj).continuous U,ih]; exact congrFun (h.steps _ _ j hj).1.symm _

def total (s : R.Mode) (j : ℕ) : Field G (H.S.side j p) → ℂ :=
    if h : j=N then by subst j; exact A.source s
    else if j<N then Ride.bump (H.S.block j).val s A.load • step (H:=H) (p:=p) (N:=N) j (total s (j+1)) else 0
termination_by N-j

@[simp] lemma total_top (s : R.Mode) : A.total s N = A.source s := by rw [total]; simp
lemma total_step (s : R.Mode) (j : ℕ) (hj : j<N) : A.total s j = Ride.bump (H.S.block j).val s A.load •
    step (H:=H) (N:=N) j (A.total s (j+1)) := by rw [total]; simp [hj,hj.ne]
lemma smooth_total (s : R.Mode) {j : ℕ} (hj : j ≤ N) : ContDiff ℝ ∞ (A.total s j) := by
  induction hj using Nat.decreasingInduction with
  | self => rw [total_top]; exact source_smooth ..
  | of_succ j hj ih =>
    rw [total_step A s j hj]
    exact contDiff_const.smul (extended_smooth _ (H.levels.blocks ..).branches (ih.continuous.comp matrixField_cont) _)

lemma total_gauge (h : A.Symmetric) (s : R.Mode) {j : ℕ} (hj : j ≤ N) : GaugeInvariant (A.total s j ∘ matrixField) := by
  induction hj using Nat.decreasingInduction with
  | self => intro t U; simp [total_top, A.source_eq, Ride.Product,comp_apply, fun i => h i t U]
  | of_succ j hj ih =>
    have he := invariant_push (H.levels.clock.op j p) (β:=H.β N p (j+1)) (H.levels.transition_mass ..)
      (fun V U t => (H.levels.blocks j p).gauge _ U V t) ((A.smooth_total s hj).continuous.comp matrixField_cont) ih
    intro t U
    simp only [total_step A s j hj,comp_apply,Pi.smul_apply, step_push j (A.smooth_total s hj).continuous,he t U]

lemma quiet_eq {j : ℕ} (hj : j ≤ N) : A.total R.quiet j = fun x => (vacuum H N p j x:ℂ) := by
  induction hj using Nat.decreasingInduction with
  | self => funext x; simp [source,Ride.bump,Census.quiet]
  | of_succ j hj ih =>
    funext x
    rw [total_step A _ j hj, vac_step j hj, ih]
    simp only [Ride.bump,Census.quiet,prod_empty,one_smul]
    exact extended_real _ (H.levels.blocks j p).branches ((vac_smooth hj).continuous.comp matrixField_cont) ..

def ratios (R : Census V) (j : ℕ) (x : Field G (H.S.side j p)) :=
    Poly.inject fun s : R.Mode => A.total s j x * ((vacuum H N p j x)⁻¹ : ℝ)

lemma part_ratios (j : ℕ) (x) (s : R.Mode) : (A.ratios R j x).part s=A.total s j x * ((vacuum H N p j x)⁻¹ : ℝ) := rfl
lemma ratios_quiet {j : ℕ} (hj : j≤N) (x) : (A.ratios R j x).part R.quiet=1 := by
  rw [part_ratios,A.quiet_eq hj, ← Complex.ofReal_mul, mul_inv_cancel₀ (vac_pos hj x).ne', Complex.ofReal_one]

variable [Fintype V]

def cumulant (j : ℕ) (s : R.Mode) (x : Field G (H.S.side j p)) := (connected (A.ratios R j x)).part s

lemma compound_eq {j : ℕ} (hj : j ≤ N) (x) : Poly.pass (Poly.inject fun s : R.Mode => A.cumulant j s x) = A.ratios R j x :=
    pass_connected (A.ratios_quiet hj x)
lemma cumulant_quiet {j : ℕ} (hj : j ≤ N) (x) : A.cumulant j R.quiet x = 0 := connected_quiet (A.ratios_quiet hj x)

lemma cumulant_smooth {j : ℕ} (hj : j ≤ N) (s : R.Mode) : ContDiff ℝ ∞ (A.cumulant j s) := by
  refine contDiff_connected (F:=A.ratios R j) (fun l => (A.smooth_total l hj).mul ?_) s
  exact Complex.ofRealCLM.contDiff.comp ((vac_smooth hj).inv (fun x => (vac_pos hj x).ne'))

lemma cumulant_gauge (h : A.Symmetric) {j : ℕ} (hj : j ≤ N) (s : R.Mode) : GaugeInvariant (A.cumulant j s ∘ matrixField) := by
  intro t U
  have he (s : R.Mode) := A.total_gauge h s hj t U
  simp only [comp_apply] at he ⊢
  unfold cumulant ratios
  simp only [he]; rw [show vacuum H N p j (matrixField (gauge t U)) = vacuum H N p j (matrixField U) from ?_]
  apply Complex.ofReal_injective
  rw [← congrFun (A.quiet_eq (R:=R) hj) _, ← congrFun (A.quiet_eq (R:=R) hj) _]
  exact he _
end Insertions
end YM.Extra.Trajectories
