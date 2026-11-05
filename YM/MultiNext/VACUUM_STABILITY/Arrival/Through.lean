import YM.MultiNext.VACUUM_STABILITY.Arrival.InputLaw
import YM.Next.MULTISOURCE.Enclosure
import YM.Push.SECTOR_MEASURE.Output



set_option warningAsError false

/-!
# Input work with actual tagged kernel

Every occurrence reaches a single SectorMeasure family. No cancellations in the
decomposition budget. Polynomials BEFORE any changing of frames. Does not commute
a cutoff limit through the decomposition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff Tree YM.Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n p : Side}

private lemma sum_at {ι : Type} [Countable ι] (X : ι → Config G n → ℂ) (Y : Config G n→ℂ)
    (h : Dominated X) (hh : ∀ i,Measurable (X i)) (he : ∀ x,Y x=∑' i,X i x) (S : StepData p n)
    {β : ℝ} (hv : S.IsKernel β G) (V : Config G p) :
    Envelope Y ∧ (∀ i, Envelope (X i)) ∧ HasSum (fun i => S.push β (X i) V) (S.push β Y V) := by
  have hY : Envelope Y := by rw [funext he]; exact ⟨Measurable.tsum hh,h.bound⟩
  obtain ⟨f,hf,hF⟩:=h; have hX (i) : Envelope (X i) := ⟨hh _, f i, hF i⟩
  let μ := prior G n
  refine ⟨hY,hX,?_⟩; unfold StepData.push
  let z i U := S.density β U V • X i U
  have hg : ∀ i, Integrable (z i) μ := fun i => StepData.push_slice hv _ _
    (Integrable.of_bound (hh i).aestronglyMeasurable (f i) (Eventually.of_forall (hF i)))
  obtain ⟨k,hk⟩:=hv.bound
  have ht : Summable fun i => ∫ U, ‖z i U‖ ∂μ := by
    refine (hf.mul_left k).of_nonneg_of_le (fun i => integral_nonneg fun U => norm_nonneg _) fun i => le_trans ?_
        (show (∫ _ : Config G n, k*f i ∂μ) ≤ k*f i by simp [μ])
    refine integral_mono (hg i).norm (by unfold μ; apply integrable_const) fun U => ?_
    unfold z; rw [norm_smul_of_nonneg (hv.positive U V)]; exact mul_le_mul (hk U V) (hF i _) (norm_nonneg _)
      ((hv.positive U V).trans (hk U V))
  have h (U) : S.density β U V • Y U=∑' i,z i U := by rw [he]; apply (((hf.of_nonneg_of_le (fun i => norm_nonneg _) fun i => hF i U).of_norm.hasSum.const_smul (S.density β U V)).tsum_eq).symm
  simp_rw [h]; exact hasSum_integral_of_summable_integral_norm hg ht

namespace Flock
variable (F : Flock V G n) (P : Rep G n)

def signature (s : Voucher F) := (∑ i∈s.1,(F.scrip P i).name) + (∑ i∈s.2,(penny F i).name)

variable [Fintype V]

def peelRow (s : Voucher F) (U : Config G n) := (Real.exp (P.exponent U):ℂ) * F.plain P s 1 U

def payFee (z : V→ℂ) := Complex.exp (Brush.launch (fun i => (F i).fiat) z)

private lemma unpriced (q : Grade V) : beat q 1=1 := by simp [beat]

lemma linearized (s : Voucher F) (z : V→ℂ) : F.carried P s z = (payFee F z * beat (signature F P s) z) • peelRow F P s := by
  funext U
  have ht : ∀ i,F.optional P i z U=beat (penny F i).name z * F.optional P i 1 U := fun i => by
    unfold optional; by_cases H : Healthy P.p.threshold (pennyZone F i) U <;> simp [H,unpriced]
  have he : F.attends P z s.1 U=beat (∑ i∈s.1,(F.scrip P i).name) z * F.attends P 1 s.1 U := by
    unfold attends; split
    · simp_rw [Stamp.tells,Stamp.beat_pile,unpriced,one_mul,Finset.prod_mul_distrib]
    rw [mul_zero]
  have hg : F.draw P s.2 z U=beat (∑ i∈s.2,(penny F i).name) z * F.draw P s.2 1 U := by
    unfold draw; split
    · simp_rw [Stamp.beat_pile]; rw [←Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => ht i
    rw [mul_zero]
  unfold carried plain peelRow
  rw [he,hg,signature,Stamp.beat_add,Pi.smul_apply]; unfold weight payFee plain; rw [smul_eq_mul]; ring

namespace Attended
variable {F} {o : V → Site n} {k : V → ℝ} {κ η : ℝ} {D : V → Pulse G n}
variable (h : Attended F P.p D o k κ)
variable {σ c Λ δ b : ℝ} (H : P.Lawful σ c Λ δ b) (hp : 0 < κ)
include h H hp

lemma investments (hx : GaugeInvariant P.exponent) : ∀ i, Envelope (peelRow F P i) ∧ GaugeInvariant (peelRow F P i) := by
  obtain ⟨r,hr,hR⟩:=Desk.permits o k 1 (fun i => (h.authorizations _).ok) (by norm_num)
  let z (_ : V) := (r:ℂ)
  have hz : z ∈ allot o k 1 := hR fun i => by change ‖(r:ℂ)‖≤r; simp [abs_of_pos hr]
  obtain ⟨⟨f,hf,hF⟩,H,-⟩:=held P h H hz le_rfl hp
  intro i
  let a := payFee F z * beat (signature F P i) z
  have ha : a≠0 := mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun j _ =>
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne'))
  have he : peelRow F P i = a⁻¹ • F.carried P i z := by rw [linearized,show _ * _=a from rfl,inv_smul_smul₀ ha]
  rw [he]; refine ⟨⟨measurable_const.smul (H _).1, ‖a⁻¹‖ * f i,fun v => ?_⟩,fun k U => congrArg (a⁻¹ • ·) ((H i).2 hx k U)⟩
  rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hF _ _) (norm_nonneg _)

/-- Per V. Every choice passes the same D.bill Allocation (already shares the kernel choices).
    Includes true absolute integrability at this volume, unweighted individual input components,
    physical push. Uniform rate on resulting components NOT provided here. -/
lemma delivered (S : StepData p n) (hs : S.patch.Branches S.kernel G) (hx : GaugeInvariant P.exponent) {W t : ℝ}
    (D' : Allocation G S t W) (Y : Forest S.ratio) {z : V→ℂ} (hz : z∈allot o k η) (he : η ≤ 1) (q : Config G p) :
    Envelope (perturbs P D z) ∧
    HasSum (fun i : Voucher F => (payFee F z * beat (signature F P i) z)*∑ A, output D' Y P.beta (peelRow F P i) A q)
      (S.push P.beta (perturbs P D z) q) := by
  obtain ⟨hd,hM,hI⟩:=held P h H hz he hp
  have hm := S.isKernel hs P.beta
  obtain ⟨hG,-,hg⟩:=sum_at (fun s => F.carried P s z) (perturbs P D z) hd (fun i => (hM i).1) hI S hm q
  refine ⟨hG,?_⟩
  have ht (i : Voucher F) : S.push P.beta (F.carried P i z) q =
      (payFee F z * beat (signature F P i) z)*∑ A, output D' Y P.beta (peelRow F P i) A q := by
    obtain ⟨⟨ht,e,he⟩,hu⟩:=h.investments P H hp hx i
    have hv := Integrable.of_bound (μ:=prior G n) ht.aestronglyMeasurable e (Eventually.of_forall he)
    rw [linearized,StepData.push_smul _ _ _ _ hv,push_columns D' Y _ _ hs hv hu]; rfl
  simp_rw [ht] at hg; exact hg
end Attended
end Flock
end YM.Multi.Vacuum.Arrival
