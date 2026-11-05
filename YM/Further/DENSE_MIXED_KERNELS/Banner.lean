import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.SECTOR_MEASURE.Oriented


/-!
# One way to buy full-volume mixed components after their flag test

High cost × **literal number of Sites**, for use with dense packets.
Didn't throw away long paths, use all channels and families. Estimates here
on unmarked scalar part evaluated along with these mixed contributions;
no K expansion included here. Needs matching actual Fit incl β etc.

Pathwise cuff cost uses only width in actual fine/coarse units, even on
huge wrapping supports with row truncation. Suffices for this per-volume
calculation; won't buy a general vacuum decomposition/matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {n : Side} {G : Gauge} {R : PathData G} {a : Clip} {σ C Λ : ℝ} {U : Config G n}
    {d r : ℕ}

namespace Streamer
-- parameter unit d positive

def tide (σ : ℝ) (r d : ℕ) := Real.exp (-σ*(r:ℝ)/d)


lemma drop_tail (H : R.Bounds a σ C Λ) (x : Cell n) (r d : ℕ) (hd : 0<d) :
    ‖R.ell U x - shorten R r d U x‖ ≤ 2*C*tide σ r d ∧ ‖R.ell U x‖ ≤ 2*C ∧ ‖shorten R r d U x‖ ≤ 2*C := by
  let D := fun i : ℕ => |(R.row x.2 i).1| *Real.exp (σ*((R.row x.2 i).2.length:ℝ))
  have h : SumBudget D C := H.rows x.2
  let E i := D i*2
  have hi : Summable E := h.2.1.mul_right _
  let e i := R.ellTerms x i U; let z i := shortenTerm R r d U x i
  have hx (i) : ‖e i‖ ≤ |(R.row x.2 i).1| *2 := by
    unfold e PathData.ellTerms; rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
  have hp i : ‖e i‖ ≤ E i := (hx i).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _)
    (Real.one_le_exp (mul_nonneg H.width.le (Nat.cast_nonneg _)))) (by norm_num))
  have hz i : ‖z i‖ ≤ E i := by
    unfold z shortenTerm; split
    · exact hp i
    rw [norm_zero]; exact (norm_nonneg _).trans (hp i)
  have h₁ := hi.of_nonneg_of_le (fun i => norm_nonneg (e i)) hp
  have h₂ := hi.of_nonneg_of_le (fun i => norm_nonneg (z i)) hz
  have he : ∑' i, E i ≤ 2*C := by unfold E; rw [tsum_mul_right,mul_comm 2]; exact mul_le_mul_of_nonneg_right h.2.2 (by norm_num)
  refine ⟨?_, (norm_tsum_le_tsum_norm h₁).trans ((h₁.tsum_le_tsum hp hi).trans he),
    (norm_tsum_le_tsum_norm h₂).trans ((h₂.tsum_le_tsum hz hi).trans he)⟩
  let t := tide σ r d
  have hr : 0<t := Real.exp_pos _
  have hZ i : ‖e i - z i‖ ≤ E i*t := by
    unfold z shortenTerm; split
    · rw [show R.ellTerms x i U=e i from rfl,sub_self,norm_zero]; exact mul_nonneg ((norm_nonneg _).trans (hp i)) hr.le
    next he =>
      unfold E; rw [sub_zero,mul_right_comm]; apply (hx i).trans
      refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
      let X := ((R.row x.2 i).2.length:ℝ)
      unfold D t tide; rw [mul_assoc,← Real.exp_add]; apply le_mul_of_one_le_right (abs_nonneg _)
      apply Real.one_le_exp; have hg : 0<(d:ℝ) := by exact_mod_cast hd
      have hh : (r:ℝ)/d ≤ X := (div_le_iff₀ hg).mpr (by unfold X; exact_mod_cast (le_of_lt <| lt_of_not_ge he))
      change 0 ≤ σ*X+ -σ*r/d; rw [neg_mul,neg_div,mul_div_assoc];
      linarith only [mul_le_mul_of_nonneg_left hh H.width.le]
  change ‖(∑' i,e i)-∑' i,z i‖ ≤ _
  rw [← h₁.of_norm.tsum_sub h₂.of_norm]
  have hE := (hi.mul_right t).of_nonneg_of_le (fun i => norm_nonneg (e i-z i)) hZ
  apply (norm_tsum_le_tsum_norm hE).trans ((hE.tsum_le_tsum hZ (hi.mul_right t)).trans ?_)
  rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right he hr.le

lemma gap_cost (H : R.Bounds a σ C Λ) (x : Cell n) (hd : 0<d) (P : BudgetPoint) :
    |R.baseTerm a P U x - crown R a r d P.threshold U x| ≤ 4*C^2*tide σ r d := by
  obtain ⟨h₁,h₂,h₃⟩ := drop_tail (U:=U) H x r d hd
  let b := shorten R r d U x; let e := R.ell U x
  unfold PathData.baseTerm crown trunk; split_ifs
  · change |_+ ‖e‖^2/2 - (‖b‖^2/2+_)| ≤ _
    rw [add_comm (b:=‖e‖^2/2),add_sub_add_right_eq_sub]
    have hv := (abs_norm_sub_norm_le e b).trans h₁
    calc
      _ = |‖e‖-‖b‖| * (‖e‖+‖b‖) /2 := by
        rw [show ‖e‖^2/2 - ‖b‖^2/2=(‖e‖-‖b‖)*(‖e‖+‖b‖)/2 by ring, abs_div, abs_mul, abs_of_nonneg (by positivity : 0≤‖e‖+‖b‖), abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ (2*C*tide σ r d)*(2*C+2*C) /2 := div_le_div_of_nonneg_right
        (mul_le_mul hv (add_le_add h₂ h₃) (by positivity) ((abs_nonneg _).trans hv)) (by norm_num)
      _ = _ := by ring
  rw [add_zero,zero_add,sub_self,abs_zero]; exact mul_nonneg (by positivity) (Real.exp_pos _).le

-- Pre volume: includes raw vacuum exponential; no absorbing activation across sectors
-- OUT goes through Wick base term. Orbit signs at actual orientation, price per site.
def per (σ C : ℝ) (r d : ℕ) := (Fintype.card PlaqAxes:ℝ)* (4*C^2*tide σ r d)
def frames (R : Rep G n) (U : Config G n) : ℝ := Oriented.averaged fun s => ∑ x : Face (Per n), R.path.baseTerm R.clip R.p (pull s 0 U) x
def cut (R : Rep G n) (r d : ℕ) (U : Config G n) : ℝ := Oriented.averaged fun s => ∑ x, crown R.path R.clip r d R.p.threshold (pull s 0 U) x
lemma paid_per : 0 ≤ per σ C r d := mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.exp_pos _).le)

variable {L : Rep G n} {δ w : ℝ} (h : L.Lawful σ C Λ δ w)
include h

open Oriented
-- even value of actual tails (not approximating U by any truncated representative)
lemma sways (hd : 0<d) : |frames L U-cut L r d U| ≤ Fintype.card (Site n)*per σ C r d := by
  unfold frames cut; rw [← av_sub]
  let q (y : Config G n) := (∑ p : Cell n, L.path.baseTerm L.clip L.p y p) - ∑ p : Cell n,crown L.path L.clip r d L.p.threshold y p
  let b := Fintype.card (Site n)*per σ C r d
  have hv y : |q y| ≤ b := by
    unfold q; rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    apply (Finset.sum_le_sum (f:=fun p => |L.path.baseTerm L.clip L.p y p - crown L.path L.clip r d L.p.threshold y p|) (s:=Finset.univ)
      (fun i _ => gap_cost h.paths (d:=d) (r:=r) i hd _)).trans_eq
    simp only [Finset.sum_const,card_univ, show Fintype.card (Cell n)= Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod ..,
      nsmul_eq_mul,Nat.cast_mul,b,per,mul_assoc]
  change |averaged (fun i => q (pull i 0 U))| ≤ b; rw [abs_le]
  exact ⟨(av_const (-b)).symm.le.trans (av_mono (H:=fun i => q (pull i 0 U)) fun i => (abs_le.mp (hv _)).1),
    (av_mono (F:=fun i=>q (pull i 0 U)) fun i => (abs_le.mp (hv _)).2).trans (av_const b).le⟩

lemma departure (U : Config G n) (hb : 0≤ L.beta) :
    |L.path.inChannels L.clip L.p L.beta U - L.beta*frames L U| ≤
      Fintype.card (Site n) * PathData.loopsPrice L.p L.beta C Λ := by
  let Q (y:Config G n) := L.path.principal L.clip L.p L.beta y - L.beta * ∑ x : Cell n, L.path.baseTerm L.clip L.p y x
  let q := Q ∘ (fun i => pull i 0 U)
  let D := Fintype.card (Site n)*PathData.loopsPrice L.p L.beta C Λ
  have hh : averaged q = L.path.inChannels L.clip L.p L.beta U-L.beta*frames L U := by
    unfold q Q averaged PathData.inChannels frames; simp only [comp_apply, Finset.sum_sub_distrib, ← Finset.mul_sum,averaged]; ring
  have hv i : |q i| ≤ D := PathData.volume_price _ _ _ _ hb _ h.paths
  rw [← hh,abs_le]
  exact ⟨(av_const (-D)).symm.le.trans (av_mono (H:=q) fun i => (abs_le.mp (hv i)).1),
    (av_mono (F:=q) fun i => (abs_le.mp (hv i)).2).trans (av_const D).le⟩

omit h in
def total (σ C Λ δ : ℝ) (r : ℕ) (P : BudgetPoint) (β : ℝ) :=
    PathData.loopsPrice P β C Λ + β*per σ C r 1 + δ

-- use *regardless* chosen nonzero marked part of L.density
lemma receipt (hb : 0≤L.beta) :
    L.exponent U - L.v*Fintype.card (Site n) + L.beta*cut L r 1 U ≤ Fintype.card (Site n)*total σ C Λ δ r L.p L.beta := by
  have hv := (abs_le.mp (departure h U hb)).1
  have hx := mul_le_mul_of_nonneg_left (abs_le.mp (sways (r:=r) (U:=U) h (Nat.zero_lt_one))).1 hb
  have hh := (abs_le.mp (RG.volumeE _ h.labels U)).1
  unfold total Rep.exponent; linarith only [hh,hx,hv]

omit h in
lemma total_pos (n : Side) {L : Rep G n} (h : L.Lawful σ C Λ δ w) (hb : 0≤L.beta) (r : ℕ) :
    0≤ total σ C Λ δ r L.p L.beta := by
  obtain ⟨b,hb',hi⟩ := h.labels.boundE
  have hz := hi (0: Site n); have he : 0≤δ := (tsum_nonneg hz.1).trans hz.2.2
  have hC : 0 ≤ C := (tsum_nonneg h.paths.three.1).trans h.paths.three.2.2
  have hL : 0 ≤ Λ := (tsum_nonneg h.paths.two.1).trans h.paths.two.2.2
  refine add_nonneg (add_nonneg ?_ (mul_nonneg hb paid_per)) he
  have hx := L.p.threshold_pos; unfold PathData.loopsPrice; positivity

end Streamer
end YM.Further.DenseMixedKernels
