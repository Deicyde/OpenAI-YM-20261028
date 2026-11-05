import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Post
import YM.UVNext.FREE_STRESS_CERTIFICATE.Samples

/-!
# Inclusions and a sharp limitation on where degree-four style fullness applies

`Makes` calibration or changing frames cannot make the free quotient full on Ref
at arbitrary comparable weights. Stress comparisons use `filled_four`, not
its generalization to d=5 or farther ahead. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Table Climb Next.UVStress Function Set Tensor Analysis
open scoped RealInnerProductSpace
variable {G : Gauge} (F : Frames G) {d e n : ℕ}

lemma spectra_include (h : d ≤ e) (v : Label G d) :
    (freeTable F).spectra e (embed F e (raiseLabel G h v)) = (freeTable F).spectra d (embed F d v) := by
  funext x
  change (freeTable F).read x.point (Fin.cons (token F e _) x.letter) =
    (freeTable F).read x.point (Fin.cons (token F d _) x.letter)
  rw [first_label,first_label]; rfl
lemma null_include (h : d ≤ e) (v : Label G d) : embed F d v=0 ↔ embed F e (raiseLabel G h v)=0 := by
  have he : ∀ i (z : (freeTable F).Field i), z=0 ↔ (freeTable F).spectra i z=0 := fun i z =>
    ⟨fun hz => hz ▸ map_zero _,fun hv => (freeTable F).faithfully i (hv.trans (map_zero _).symm)⟩
  simp_rw [he,spectra_include]

-- true free inclusions with no dependency on station labels, every d.
def climb (h : d ≤ e) : (freeTable F).Field d →ₗ[ℂ] (freeTable F).Field e :=
  ((freeTable F).null d).liftQ ((embed F e).comp ((raiseLabel G h).comp (F.level d).coords.symm.toLinearMap)) (by
    intro x hx
    apply (null_include F h ((F.level d).coords.symm x)).mp
    change (freeTable F).project d ((F.level d).coords ((F.level d).coords.symm x)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx)

lemma climbed (h : d ≤ e) (v : Label G d) : climb F h (embed F d v) = embed F e (raiseLabel G h v) := by
  change embed F e (raiseLabel G h ((F.level d).coords.symm ((F.level d).coords v))) = _
  rw [LinearEquiv.symm_apply_apply]
lemma keeps (h : d ≤ e) (v : (freeTable F).Field d) : (freeTable F).spectra e (climb F h v)=(freeTable F).spectra d v := by
  obtain ⟨v,rfl⟩ := covers F v; rw [climbed,spectra_include]

-- Doesn't *define* a DiffPlan to thereby claim a Derivatives hypothesis. The rise
-- part is fully separate: lets the assembler pay literal edges without null theorem at
-- high weight.
lemma true_inc (W : DiffPlan (freeTable F)) (hW : ∀ d e (h : d≤e), W.rise h=climb F h) : W.Inclusions (freeTable F) := by
  constructor; intro d e h v n x hx w
  choose k hk using fun i => (covered_word F (w i))
  rw [show w=(freeTable F).classTokens ∘ k from funext fun i => (hk i).symm]
  rw [Table.through _ (table_sym F) _ _ hx,Table.through _ (table_sym F) _ _ hx,hW,keeps]
where
  covered_word (F : Frames G) (u : (freeTable F).Tag) : ∃ t : (standard F).Token, (freeTable F).classTokens t=u := by
    obtain ⟨d,p⟩ := u; obtain ⟨t,rfl⟩ := (freeTable F).onto d p
    exact ⟨⟨d,t⟩, rfl⟩


open Work.D06

-- with compat gives the `hers` antecedent directly on such inputs




-- explicit off-shell label detected on radial closed coefficients; on the actual
-- free quotient vanishes identically. Use potential equivalence (Bianchi only).
private def spot {Y : Type*} [AddCommGroup Y] (x : Y) (a b : Axis) :=
  if a=0 ∧ b=1 then x else if a=1 ∧ b=0 then -x else 0
private lemma spot_odd {Y : Type*} [AddCommGroup Y] (x : Y) (a b : Axis) : spot x a b= -spot x b a := by
  unfold spot; split_ifs <;> simp_all [and_comm]

private def coreZero (x : G.Color) : Tensor.T E4 G.Color 0 := ContinuousMultilinearMap.constOfIsEmpty ℝ _ x
private def coreOne (x : G.Color) : Tensor.T E4 G.Color 1 :=
  ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1) (tint (G:=G) x ∘L compAxis 0)


private lemma opened_zero (x : G.Color) : ClosedJet (spot (coreZero x)) := by
  constructor
  · intro i l v r; exact congr_arg _ (Subsingleton.elim ..)
  · exact spot_odd _
  intro a b c z
  have h (A : Tensor.T E4 G.Color 0) (a) : grad a (Tensor.diagonal A) z=0 := by
    rw [show Tensor.diagonal A = fun _ => A (fun _ => 0) from funext fun t => congr_arg A (Subsingleton.elim (fun _ : Fin 0 => t) _)]
    simp [grad,D]
  simp [h]

private lemma opened_one (x : G.Color) : ClosedJet (spot (coreOne x)) := by
  have he : Tensor.diagonal (coreOne x) = (fun y : E4 => y 0 • x) := rfl
  have h (a b : Axis) : Tensor.diagonal (spot (coreOne x) a b) = fun z => spot (z 0 • x) a b := by
    funext z; unfold spot; split_ifs <;> rfl
  constructor
  · intro i l v s; exact congr_arg (fun z : Fin 1 → E4 => spot (coreOne x) i l z) (funext fun j => congr_arg v (Subsingleton.elim (s j) j))
  · exact spot_odd _
  intro a b c z
  have hw (c a b : Axis) : grad c (Tensor.diagonal (spot (coreOne x) a b)) z = spot ((YM.basis c 0) • x) a b := by
    let L := tint (G:=G) x ∘L compAxis 0
    have ht : (fun z : E4 => z 0 • x) = L := rfl
    rw [h]; unfold spot; split_ifs
    · rw [ht]; exact congr_arg (fun p : E4 →L[ℝ] G.Color => p (YM.basis c)) (L.fderiv : fderiv ℝ L z = L)
    · change fderiv ℝ (fun t => -(L t)) z _ = _
      rw [fderiv_fun_neg,L.fderiv]; rfl
    simp [grad,D]
  rw [hw,hw,hw]; unfold spot; split_ifs <;> simp_all [basis_eq] <;> grind

def short (x : G.Color) : Labels.Jet G :=
  Pi.single 0 (contracted (opened_zero x)) + Pi.single 1 (contracted (opened_one x))










end YM.UVNext.FreeStress
