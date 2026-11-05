import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.MvPolynomial
import YM.Analysis.Symmetric
import YM.Complex.Columns
import YM.Overlay.Bill


/-!
# Complete exponential estimates propagate along the ACTUAL transfer

IG cutoffs all positive measure. Allows different weights within a marker
family. Test even singleton & subwords explicitly. No reserve compatibility
inferred across transformations. Specialize in `Supplier` later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Overlay
open Lattice Wilson RG Marker
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Census V} {H : RG.History G}

lemma beta_positive (h : H.Selected) {m N p} (hm : m≤N) : 0<H.β N p m :=
  lt_of_lt_of_le (div_pos (lt_trans zero_lt_one (H.levels.fits.delayed m)) (by norm_num)) (h.represents N p m hm).band.1

namespace Ride

def bump (a : ℝ) (T : R.Mode) (k : V → ℕ) : ℂ := ∏ i∈ T.val, (a : ℂ)^(k i)

variable {N p : ℕ}
def Product (u : V → Config G (H.S.side N p) → ℂ) (T : R.Mode) (U : Config G (H.S.side N p)) := ∏ i∈ T.val,u i U
end Ride

/-- A full family for a marker set, any permitted. Clients may require
more from singleton/restrictions. Not defining propagation itself to generate
a Lane -- require proofs on every step for the active path/query scope.
-/
structure Lane (H : RG.History G) (R : Census V) (N p : ℕ) where
  sites (m : ℕ) : Overlay.Bands R (H.rep N p m)
  load (v : V) : ℕ
  uses (v : V) : Config G (H.S.side N p) → ℂ

namespace Lane
open Ride
variable {N p : ℕ} (L : Lane H R N p)

def signal (m : ℕ) (s : R.Mode) : Config G (H.S.side m p) → ℂ := fun U => ((L.sites m).density U).part s

structure Works (r : ℕ) : Prop where
  admits : r ≤ N
  meaningful (m : ℕ) : r ≤ m → m ≤ N →
    (L.sites m).Active ∧ ∃ w u c d b, (L.sites m).Radial w u c d b
  origin (m : ℕ) (i : V) : r≤m → m < N → (H.levels.clock.op m p).ratio.parent ((L.sites (m+1)).origins i)=(L.sites m).origins i
  reads (s : R.Mode) : Integrable (Ride.Product L.uses s) (law G _ (H.β N p N))
  first (s : R.Mode) (U) : L.signal N s U = bump (H.S.a N) s L.load * (bare (H.β N p N) U : ℂ)*Product L.uses s U
  step (m) : r ≤ m → m < N → ∀ s, L.signal m s = (bump (H.S.block m).val s L.load) •
    (H.levels.clock.op m p).push (H.β N p (m+1)) (L.signal (m+1) s)

lemma from_ (h : H.Selected) {r} (z : L.Works r) (s : R.Mode) (m) (hr : r≤m) (hm : m≤N) :
    (∫ U, L.signal m s U ∂prior G (H.S.side m p)) =
      bump (H.S.a m) s L.load * (partition G (H.S.side N p) (H.β N p N) : ℂ) * moment (H.β N p N) (Product L.uses s) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [moment_formula _ _ (z.reads s)]
    simp_rw [z.first s,mul_assoc, integral_const_mul]
    rw [mul_inv_cancel_left₀]; exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  | of_succ k hk ih =>
    simp_rw [z.step k hr hk s, Pi.smul_apply,smul_eq_mul,integral_const_mul]
    have he := z.meaningful (k+1) (hr.trans (Nat.le_succ _)) hk
    obtain ⟨hh,w,u,c,d,b,ht⟩ := he
    have hv : Integrable (L.signal (k+1) s) (prior G _) := ((L.sites _).material hh ht (h.represents _ _ _ hk).good (beta_positive h hk).le s).1
    rw [StepData.push_integral (H.levels.transition_mass ..) _ hv, ih (hr.trans (Nat.le_succ _)), ← mul_assoc,←mul_assoc,bump,bump, ← Finset.prod_mul_distrib,H.S.a_step]
    have ht : ∀ i : V, ((↑(↑(H.S.block k):ℝ):ℂ)^L.load i)*((↑(H.S.a k / (H.S.block k).val):ℂ)^L.load i) = (H.S.a k:ℂ)^L.load i := by
      intro i; rw [← mul_pow, Complex.ofReal_div]; have h1 : ((H.S.block k).val:ℂ) ≠ 0 := by exact_mod_cast (H.S.block k).property.ne'
      push_cast; field_simp
    simp_rw [ht]; rfl


lemma pays {r : ℕ} (h : H.Selected) (e : L.Works r) {w : V → ℝ} {u c d b : ℝ} (t : (L.sites r).Radial w u c d b) (s : R.Mode) :
    let F := H.levels.clock
    ‖bump (H.S.a r) s L.load‖ * ‖moment (H.β N p N) (Product L.uses s)‖ * Poly.toll w s ≤ Real.exp
      (Bands.finalBill (Fintype.card V) (H.rep N p r) (F.hatCoupling r) u c d b (F.params r).paths (F.loopCap r) (F.allowance r) (F.forcedAllowance r)) := by
  intro F
  have he := h.represents N p r e.admits
  have hh : 0 < F.hatCoupling r := inv_pos.mpr (Real.sqrt_pos.2 (lt_trans zero_lt_one (H.levels.fits.delayed r)))
  have hv : F.hatCoupling r ≤ (H.rep N p r).p.threshold := by
    rw [he.vac]; change _ ≤ F.hatCoupling r * Real.exp _
    exact le_mul_of_one_le_right hh.le (Real.one_le_exp (sq_nonneg _))
  have ht := (L.sites r).total ((e.meaningful _ le_rfl e.admits).1) t he.good (beta_positive h e.admits).le _ hh hv
    (H.nonnegative h N p r e.admits) s
  have hZ := H.partition_eq h N p r e.admits
  rw [show (∫ U, ((L.sites r).density U).part s∂prior G _) = _ from L.from_ h e s r le_rfl e.admits, hZ, norm_mul,norm_mul] at ht
  rw [Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le, mul_right_comm _ (partition G _ _), mul_div_cancel_right₀ _ (partition_pos _).ne'] at ht
  exact ht
end Lane
end YM.Overlay
