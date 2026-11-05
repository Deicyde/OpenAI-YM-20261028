import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Next.FREE_KERNELS.Lifts
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

/-!
# Directional reproduction: nonprincipal aliases

Show for B70's free stationary one-form column, any *nonprincipal* alias
has all the required vanishing, at the exact analytic zero (not recovery
from ignoring a harmonic mode). No estimates depend on a finite torus side. No Jordan pole division in this extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Filter Function Set Lattice Laurent Bloch Exterior RG Next.Free Next.Free.Flight
open scoped Topology BigOperators ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {j t : ℕ}

private abbrev Silva (f : Momentum → ℂ) := ContDiffAt ℂ ω f 0

private lemma fromBudget {ι : Type*} {w : ι → ℝ} {f : ι → Momentum → ℂ}
    (h : Moderate w f) (i : ι) : Silva (f i) := by
  obtain ⟨σ,C,hσ,hC,h⟩ := h
  apply (PolyDisc.formOf ?_).contDiffAt -- parameters
  filter_upwards [(cube_open σ).mem_nhds (cube_zero σ hσ)] with p hp; exact (h i).hol p hp

private abbrev Panel {m n : Type*} (F : Momentum → Matrix m n ℂ) := ∀ i j, Silva (fun p => F p i j)
lemma pilot_silva (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4 ≤ t) (l : Site P.L) :
    ∀ i a, ContDiffAt ℂ ω (fun p => pilot k P p l i a) 0 := fun i a => fromBudget ((secure_both k hk P.legal ht).1.pay.tap i a) ⟨P,l⟩

private lemma joint_mask (v : Momentum → Axis → ℂ) (h : ∀ i, Silva fun p => v p i) : Panel fun p => mask 1 (v p) := by
  intro i j; simp_rw [mask_value]; by_cases he : i=j <;> simp_rw [he]; exact h _; exact contDiffAt_const

private lemma panel_mul {m n k : Type*} [Fintype n] {F : Momentum → Matrix m n ℂ} {G : Momentum → Matrix n k ℂ}
    (hF : Panel F) (hG : Panel G) : Panel fun i => F i*G i := fun i j => by
  simp_rw [Matrix.mul_apply]; exact ContDiffAt.sum fun b _ => (hF i b).mul (hG b j)

private lemma roots_zero : (0:Momentum) ∈ realCube zone := ⟨star_zero _,fun _ => by simp; positivity [zone_pos]⟩

/-- Peel precisely the alias polynomial vanishing part, leaving a regular
analytic germ. No assumed diagonalization of the *measured* kernels. -/
lemma pilot_components (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4≤t) (l : Site P.L) (hl : l≠0) (i b : TypeFace 1) :
    let z := fun p => area P.L (-aliasAt p l)
    z 0=0 ∧ ContDiffAt ℂ ω z 0 ∧ ∃ f : Momentum → ℂ, ContDiffAt ℂ ω f 0 ∧
      ∀ p, pilot k P p l i b=z p ^ j * f p := by
  classical
  intro z
  let q p := aliasAt p l
  have hZ := P.vanishing_box (show -l≠0 from neg_ne_zero.mpr hl)
  have hQ : aliasAt 0 (-l) = -q 0 := by simpa only [neg_zero] using alias_reverse 0 P.odd l
  rw [hQ] at hZ
  refine ⟨?_,?_,?_⟩
  · by_contra! hx
    exact (pow_ne_zero j hx) hZ
  · have hd : Differentiable ℂ z := Train.area_diff _ |>.comp (by unfold aliasAt; fun_prop)
    exact (PolyDisc.formOf (Eventually.of_forall fun p : Momentum => hd p)).contDiffAt
  let v p a := portD k P p l a
  let w p a := rail P.L (-q p a)
  let y p a := rail P.L (q p a)
  let u p (a : Axis) := (∑ b,v p b)/(abide k P p)-v p a*(y p a*w p a)/(Train.bulb k P.land p a)
  let B p : Frequency 1 1 := mask 1 (v p)*mask 1 (w p)*priorG k P p
  let X p : Frequency 1 1 := mask 1 (u p)*signal P.L 0 (q p)*sluice k P p
  refine ⟨fun p => Flight.span P p * B p i b + X p i b, ?_, ?_⟩
  · let g : Unit→Flight j t := fun _=>P
    let s : ∀ i:Unit, Site (g i).L := fun _ => l
    have hV (a) : Silva fun p => v p a := fromBudget (portD_budget k P.legal g s (fun _ => hl) fun _ => a) ()
    have hY (a) : Silva fun p => y p a := fromBudget (rails g s (fun _=>a)) ()
    have hW (a) : Silva fun p => w p a := fromBudget (reverse_rails g s (fun _=>a)) ()
    have hU (a : Axis) : Silva fun p => u p a := by
      have hh : Silva (abide k P) := fromBudget (abide_budget k P.legal g) ()
      have hg : Silva (fun p => Train.bulb k P.land p a) := fromBudget (Train.bulb_budget k ht (fun _ : Unit => P.land) (fun _ => a)) ()
      have he : Silva (fun p => ∑ b,v p b) := ContDiffAt.sum fun b _ => hV b
      exact (he.div hh (abide_live k hk P roots_zero)).sub (((hV a).mul ((hY a).mul (hW a))).div hg (by simp))
    have hG : Panel (priorG k P) := fun a b => fromBudget ((prior_cost k hk ht g).tap a b) ()
    have hB := panel_mul (panel_mul (joint_mask v hV) (joint_mask w hW)) hG
    have hs : Panel fun p => signal P.L 0 (q p) := fun a b => fromBudget ((sig_budget g s 0).tap a b) ()
    have hm : Panel (sluice k P) := fun a b => fromBudget ((sluice_cost k hk ht g).tap a b) ()
    have hH : Silva (Flight.span P) := fromBudget (divisor_control (fun _ : Unit => P.land.mass)) ()
    exact (hH.mul (hB i b)).add (panel_mul (panel_mul (joint_mask _ hU) hs) hm i b)
  intro p
  have hy : flux P 1 (q p)=(z p^j) • mask 1 (w p) := by
    unfold flux hinges; rw [Matrix.transpose_smul,mask_trans]; rfl
  have hu : gains k P p l = fun a => z p^j * u p a := by
    unfold gains; rw [if_neg hl]; rfl
  unfold pilot ahead; rw [if_neg hl,show flux P 1 (aliasAt p l)=_ from hy,hu,mask1_scale]
  simp only [Matrix.mul_smul, Matrix.smul_mul,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]; unfold B X
  change Flight.span P p * (z p^j* (_: Frequency 1 1) i b) + (z p^j)*_ = _
  unfold v q; ring

private lemma empty_velocity (z g : ℝ → ℂ) (hz : ContDiffAt ℝ ω z 0) (hg : ContDiffAt ℝ ω g 0) (hc : z 0=0)
    (n h : ℕ) (hn : h<n) : iteratedDeriv h (fun t => z t^n*g t) 0=0 := by
  classical
  induction n generalizing h with
  | zero => omega
  | succ n ih =>
    let v t := z t^n*g t
    have hv : ContDiffAt ℝ ω v 0 := (hz.pow n).mul hg
    rw [show (fun t => z t^(n+1)*g t) = fun t => v t*z t from funext fun t=>by unfold v; ring]
    rw [iteratedDeriv_fun_mul (hv.of_le le_top) (hz.of_le le_top)]; apply Finset.sum_eq_zero; intro i hi
    -- value z for i=h always; lower terms earlier
    have hi := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases he : i=h
    · subst i; simp [hc]
    simp only [show iteratedDeriv i v 0=0 from ih i (by omega)]; simp

lemma pilot_vanish (k : ℝ) (hk : 0<k) (P : Flight j t) (ht : 4 ≤ t) (l : Site P.L) (hl : l≠0)
    (i b : TypeFace 1) {r : ℝ→Momentum} (hr : r 0=0) (hR : ContDiffAt ℝ ω r 0) (n : ℕ) (h : n<j) :
    iteratedDeriv n (fun t => pilot k P (r t) l i b) 0=0 := by
  obtain ⟨hz,hz',f,hf,H⟩ := pilot_components k hk P ht l hl i b
  let z p := area P.L (-aliasAt p l)
  simp_rw [H]
  have he {F : Momentum → ℂ} (h : ContDiffAt ℂ ω F 0) : ContDiffAt ℝ ω (fun t : ℝ => F (r t)) 0 :=
    (show ContDiffAt ℝ ω F (r 0) from hr.symm ▸ (h.analyticAt.restrictScalars).contDiffAt).comp 0 hR
  apply empty_velocity (fun x => z (r x)) (fun x => f (r x)) (he hz') (he hf) _ j n h
  rw [hr]; exact hz

end YM.Planned.PrimaryIntegral295.Carrier
