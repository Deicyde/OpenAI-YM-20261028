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
import YM.Next.FREE_KERNELS.Differences
import YM.Next.FREE_KERNELS.Switch
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


/-!
# Releasing Ψ for a retained horizon

Optional strengthened export for downstream iteration. The quotient rows and
the cost promise don't use new choices of H or towers. They read exact fields
of the retained horizon and hold even at degenerate sides by true periodic
actions. Weighted preimage estimate per residue with full support, before any
L. Neither sup estimates on complex paths nor `Kin` assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {j t : ℕ}
namespace Flight

def psi (k : ℝ) (P : Flight j t) := meshBook (alloy k) 2 [] P

def groundPsi (k : ℝ) (P : Flight j t) (u : List Axis) := proceeds (advanceC P.L (psi k P) u) u

variable (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (ht : 4 ≤ t)
include hk hj ht
lemma paid_path_stock {u : List Axis} (h : u.length≤j-2) :
    let C := fun P : Flight j t => advanceC P.L (psi k P) u
    Transaction (2+u.length) C := by
  intro C
  obtain ⟨σ,D,hσ,hD,H⟩ := (status_quote k hk hj ht).honored hj 2
  refine ⟨fun i => by unfold fee; positivity,σ,D,hσ,hD,fun i => ?_⟩
  simpa only [div_eq_mul_inv,fee,C,psi] using H i u h
lemma path_stock {u : List Axis} (h : u.length≤j-2) :
    Transaction (2+u.length) (fun P : Flight j t => groundPsi k P u) := by
  have hp := paid_path_stock k hk hj ht h
  exact proceeds_stock hp u

lemma stockroom : ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ P : Flight j t, ∀ l : List Axis, l.length≤j-2 →
    (groundPsi k P l).strip σ (C/(P.L.val:ℝ)^(2+l.length)) := by
  letI : Fintype {l : List Axis // l.length≤j-2} := (Secured.limited_lengths (j-2)).fintype
  obtain ⟨σ,C,hσ,hC,H⟩ := staple (κ:={l : List Axis // l.length≤j-2})
    (fun x σ C => ∀ P : Flight j t, (groundPsi k P x.val).strip σ (C*fee (2+x.val.length) P))
    (fun x => (path_stock k hk hj ht x.property).uniform)
    (fun x σ C τ D h hτ _ hD P => strip_mono (h P) hτ (mul_le_mul_of_nonneg_right hD (by unfold fee; positivity)))
  exact ⟨σ,C,hσ,hC,fun P l hl => by simpa only [div_eq_mul_inv,fee] using H ⟨l,hl⟩ P⟩

variable (P : Flight j t)
omit hj
lemma refund (u : List Axis) (hu : u.length≤j-2) :
    let A := advanceC P.L (psi k P) u
    ∃ g : Momentum → Matrix (Co P.L (TypeFace 2)) (TypeFace 2) ℂ,
      (∀ p∈baseCube, ContinuousAt g p) ∧ ∀ p∈baseCube,A.read p=listChip p u • g p := by
  intro A
  classical
  have hx := cable_exists k hk ht P u (le_trans hu (Nat.sub_le j _))
  choose w hW hw using hx
  let fg (r : Site P.L) (p) := ∑ i : Site P.L, mode (aliasAt p i) (lift r) • (toll P.L 2 • w i p)
  have he (r : Site P.L) {p : Momentum} (hp : p∈baseCube) : ContinuousAt (fg r) p := by
    apply tendsto_finsetSum (f:=fun i p => mode (aliasAt p i) (lift r) • (toll P.L 2 • w i p))
    intro i _; have hc : ContinuousAt (fun p => mode (aliasAt p i) (lift r)) p := by unfold mode aliasAt; fun_prop
    exact hc.smul (ContinuousAt.const_smul (hW i p hp) (toll P.L 2))
  let g (p : Momentum) := Matrix.of fun (i : Co P.L (TypeFace 2)) (j : TypeFace 2) => fg i.1 p i.2 j
  refine ⟨g,fun p hp => ?_,fun p hp => ?_⟩
  · change ContinuousAt (fun p (i : Co P.L _) j => fg i.1 p i.2 j) p
    apply continuousAt_pi.mpr; intro i; apply continuousAt_pi.mpr; intro j
    exact continuousAt_pi.mp (continuousAt_pi.mp (he _ hp) _) _
  let J := status_quote k hk P.legal ht
  have hh (r : Site P.L) : spread (alloy k) 2 u P r p=listChip p u • fg r p := by
    unfold spread fg; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_smul, hw i p hp]; simp only [smul_smul]
    congr 1; ring
  ext ⟨i,j⟩ b
  unfold A psi; rw [Secured.traverse J P.legal 2 hu, J.bankRead P.legal 2 hu _ _ hp, hh i]; rfl

variable {c f : Side} (hc : f.val=c.val*P.L.val)
lemma psi_bridge : installed (P.visitRatio hc) (psi k P)=(blue k P.wing).acts f*installed (P.visitRatio hc) (duo k P).T*(pink k P.land).acts c := by
  have ht' := sail_run P hc (status_quote k hk P.legal ht) P.legal 2
  have hP := (heart_true k hk ht P.land).1.coarse c
  have hb := P.sail_run hc (agility k hk P.legal ht) P.legal 2
  have hh := hb.product hP; unfold solo at hh; rw [fiber_mult] at hh
  have hm (p : Momentum) : P.fromBank (agile k) 2 p * pulse k P.land p=P.fromBank (alloy k) 2 p := by
    unfold fromBank alloy; rw [alias_then]; congr! 2 with l; rw [Matrix.smul_mul]
  simp_rw [hm] at hh
  rw [← P.buckle_physical k hk ht hc]; exact ht'.lands hh (rotations_crew c _)
lemma refund_period (u : List Axis) (hu : u.length≤j-2) :
    motion (TypeFace 2) f u * installed (P.visitRatio hc) (psi k P)=installed (P.visitRatio hc) (groundPsi k P u)*motion (TypeFace 2) c u := by
  let A := advanceC P.L (psi k P) u
  obtain ⟨g,hg,H⟩ := refund k hk ht P u hu
  have hw u (hu : List.length u ≤ j-2) : Whole (advanceC P.L (psi k P) u) := (paid_path_stock k hk P.legal ht hu).whole P
  have hp := real_divides u (hw u hu) hg H
  let R := groundPsi k P u; let X := pathJet (TypeFace 2) u
  have hh := jet_whole (TypeFace 2) u
  have hB : Whole R := proceeds_whole (hw u hu) _
  have he : A.acts c=(composeRows R X).acts c := (hw u hu).eq_on (hB.prod hh) (fun p ha => by
    rw [H p ha,hB.read hh ha.1,jet_read (TypeFace 2) u ha.1, show R.read p=g p from hp _ ha]; rw [Matrix.mul_smul,Matrix.mul_one]) c
  rw [← flow_movement (P.visitRatio hc) _ _ P.odd (fun v hv => hw v (hv.trans hu))]
  change installed (P.visitRatio hc) A=installed (P.visitRatio hc) R*(pathJet (TypeFace 2) u).acts c
  rw [← Whole.from_coarse (P.visitRatio hc) hB hh]
  unfold installed; rw [he]
end Flight
end YM.Next.Free

namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate


end YM.Next.Free
