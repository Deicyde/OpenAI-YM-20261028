import YM.MultiNext.VACUUM_STABILITY.Arrival.KWick
import YM.MultiNext.VACUUM_STABILITY.Arrival.Letters

set_option warningAsError false

/-!
# Actual pre-RG expression for any simultaneous small perturbation

Full-label sum, exponent/powers kept. Tie tag and forest still unmarked vacuum in kernel.
No choice of log at this stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival.Flock
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n : Side} (F : Flock V G n) (Q : Rep G n)
variable [Fintype V]

-- as letters, with the actual masks even away from the eventual chart

def optional (i : Power V) (z : V → ℂ) : Config G n → ℂ :=
    masked Q.p.threshold (pennyZone F i) ((penny F i).tell z)

def draw (s : Finset (Power V)) (z : V → ℂ) (U : Config G n) :=
    if Set.InjOn (Prod.fst : Power V → Bulk V) (s : Set (Power V)) then ∏ i∈s, F.optional Q i z U else 0

abbrev Voucher (F : Flock V G n) := Finset (Cases F) × Finset (Power V)

def weight (z : V → ℂ) (U : Config G n) := Complex.exp (Brush.launch (fun i => (F i).fiat) z) *
      (Real.exp (Q.exponent U):ℂ)

def plain (s : Voucher F) (z : V → ℂ) (U : Config G n) := F.attends Q z s.1 U * F.draw Q s.2 z U

def carried (s : Voucher F) (z : V → ℂ) (U : Config G n) := F.weight Q z U * F.plain Q s z U

-- full occurrence at fixed z, dominates before integration, TRUE on all inputs

namespace Attended
variable {F} {o : V → Site n} {k : V → ℝ} {κ η : ℝ} {D : V → Pulse G n} {z : V → ℂ}
variable (h : Attended F Q.p D o k κ)
variable {σ c Λ δ b : ℝ} (H : Q.Lawful σ c Λ δ b)

private lemma masked_fee (P : BudgetPoint) (X : Support n) {f : Config G n → ℂ} {o : Site n} {c : ℝ} (h : P.supBounds o X f c) (U) :
    ‖masked P.threshold X f U‖ ≤ c := by
  by_cases he : Healthy P.threshold X U
  · rw [masked_eq _ _ _ _ he]; exact h.2 U he [] (by simp) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact h.1

include h in
lemma raisins (hz : z∈allot o k η) (he : η ≤ 1) :
    Dominated (fun i U => F.optional Q i z U) ∧
      ∀ i, Measurable (F.optional Q i z) ∧ GaugeInvariant (F.optional Q i z) := by
  obtain ⟨hf,hF⟩:= h.pepper z hz he
  have hg i := hF i |>.2.2
  constructor
  · exact ⟨_, hf.imposed fun i => (hg i).1, fun i => masked_fee Q.p _ (hg i)⟩
  intro i; have hk := Spanned.regular (path_scaled (Stamp.beat (penny F i).name z) (hF i).2.1)
  exact ⟨hk.meas,hk.gauge⟩

include h in
lemma converts (hz : z∈allot o k η) (he : η ≤ 1) (U : Config G n) :
    Complex.exp (∑ i,z i * (D i).1 U)=Complex.exp (Brush.launch (fun i => (F i).fiat) z) *
      ∑' b,F.draw Q b z U := by
  obtain ⟨hf,hF⟩:= h.issued_bulk z hz
  let X i := masked Q.p.threshold (bulkZone F i) ((stimulant F i).tell z) U
  have ht : Summable X := ((hf.imposed fun i => (hF i).2.2.1).of_nonneg_of_le (fun i => norm_nonneg _) fun i =>
    masked_fee Q.p _ (hF i).2.2 U).of_norm
  have hx : Summable (fun i => ‖heat X i‖) := by
    unfold X; rw [heated]; exact ((h.raisins Q hz he).1.absolute U)
  have hv i : z i*(D i).1 U=z i*(F i).fiat + ∑' j, X (i,j) := by
    rw [← h.fact]; dsimp only [Stroke.pulse]; rw [mul_add,← tsum_mul_left]; congr 1
    apply tsum_congr; intro j; unfold X bulkZone stimulant
    by_cases hh : Healthy Q.p.threshold ((F i).letter j) U <;> simp [hh,Stamp.beat_spike]
  rw [sum_congr rfl (fun i _ => hv i),Finset.sum_add_distrib,Complex.exp_add]
  congr 1
  have hb := grouped X ht hx
  rw [ht.tsum_prod] at hb; nth_rw 1 [tsum_fintype] at hb
  rw [hb]; unfold draw; apply tsum_congr; intro s; split; rename_i hs
  · apply prod_congr rfl; intro j hj; exact congrFun (heated F Q.p z U) j
  exact rfl

private lemma lattice_products {I : Type} {q : I → Config G n → ℂ} (h : Dominated q) :
    Dominated fun s : Finset I => fun U => ∏ i∈s,q i U := by
  obtain ⟨v,hs,hv⟩:=h
  have hp i : 0 ≤ v i := (norm_nonneg _).trans (hv i 1)
  exact ⟨fun s => ∏ i∈s, v i, summable_finsetProd_of_summable_nonneg hp hs,fun i U => (norm_prod ..).trans_le
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hv i U)⟩

include h H in
lemma packs_pay {z : V→ℂ} (hz : z∈allot o k η) (he : η ≤ 1) (hc : 0 < κ) :
    Dominated (F.attends Q z) ∧ Dominated (fun s => F.draw Q s z) := by
  have hdK : Dominated (fun i U => (scrip F Q i).tell z U) := by
    obtain ⟨a,b,hx,hf,-⟩:= hard_budget Q h H z hz hc; exact ⟨a,hf.imposed fun i => (hx i).2.1,fun i => (hx i).2.2⟩
  obtain ⟨f,hf,hF⟩:= lattice_products hdK; obtain ⟨g,hg,hG⟩:= lattice_products (h.raisins Q hz he).1
  refine ⟨⟨f,hf, fun i U => ?_⟩,g,hg,fun i U => ?_⟩
  · unfold attends; split; exact hF i U; exact norm_zero.le.trans ((norm_nonneg _).trans (hF i U))
  dsimp only [draw]; split; exact hG i U; exact norm_zero.le.trans ((norm_nonneg _).trans (hG i U))

private lemma draw_read {z : V→ℂ} (s : Finset (Power V)) (h : ∀ i, Measurable (F.optional Q i z) ∧ GaugeInvariant (F.optional Q i z)) :
    Measurable (F.draw Q s z) ∧ GaugeInvariant (F.draw Q s z) := by
  by_cases hw : Set.InjOn (Prod.fst : Power V → Bulk V) (s:Set (Power V))
  · have he : F.draw Q s z = (fun U => ∏ i∈s,F.optional Q i z U) := funext fun i => if_pos hw
    rw [he]; refine ⟨?_,?_⟩
    · exact Finset.measurable_fun_prod _ fun i _ => (h i).1
    intro k U; exact prod_congr rfl fun i _ => (h i).2 k U
  rw [show F.draw Q s z = (fun _ => 0) from funext fun _ => if_neg hw]
  exact ⟨measurable_const,fun _ _ => rfl⟩

include h H in
lemma row_read {z : V → ℂ} (hz : z∈allot o k η) (he : η ≤ 1) (s : Voucher F) :
    Measurable (F.plain Q s z) ∧ GaugeInvariant (F.plain Q s z) := by
  obtain ⟨hv,hV⟩:= partner Q h H s.1 z
  obtain ⟨ht,hD⟩:= draw_read Q s.2 (h.raisins Q hz he).2
  exact ⟨hv.mul ht,fun k U => congrArg₂ (· * ·) (hV k U) (hD k U)⟩

include h H in
lemma rowed {z : V→ℂ} (hz : z∈allot o k η) (he : η ≤ 1) (hc : 0 < κ) :
    Dominated (fun s => F.plain Q s z) ∧ ∀ s, Measurable (F.plain Q s z) ∧ GaugeInvariant (F.plain Q s z) := by
  obtain ⟨⟨f,hf,hF⟩,g,hg,hG⟩:= packs_pay Q h H hz he hc
  constructor
  · have he := summable_mul_of_summable_norm hf.norm hg.norm
    refine ⟨fun x => f x.1 * g x.2,he,fun i U => ?_⟩
    dsimp only [plain]; rw [norm_mul]
    exact mul_le_mul (hF i.1 U) (hG i.2 U) (norm_nonneg _) ((norm_nonneg _).trans (hF _ U))
  exact row_read Q h H hz he

include h H in
lemma held {z : V→ℂ} (hz : z∈allot o k η) (he : η ≤ 1) (hc : 0 < κ) :
    Dominated (fun s => F.carried Q s z) ∧ (∀ s,Measurable (F.carried Q s z) ∧
      (GaugeInvariant Q.exponent → GaugeInvariant (F.carried Q s z))) ∧
    ∀ U, perturbs Q D z U = ∑' s,F.carried Q s z U := by
  obtain ⟨hf,hF⟩:=rowed Q h H hz he hc
  obtain ⟨hm,u,hu⟩:= (Q.exponentEnv H).exp; let p := Complex.exp (Brush.launch (fun i => (F i).fiat) z)
  have hp : Measurable (F.weight Q z) := measurable_const.mul (Complex.continuous_ofReal.measurable.comp hm)
  constructor
  · obtain ⟨q,hq,g⟩:=hf
    have ht U : ‖F.weight Q z U‖ ≤ ‖p‖*u := by unfold weight; rw [norm_mul, Complex.norm_real]; exact mul_le_mul_of_nonneg_left (hu U) (norm_nonneg _)
    exact ⟨fun i => (‖p‖*u)*q i,hq.mul_left _, fun i U => (norm_mul ..).trans_le (mul_le_mul (ht U) (g i U) (norm_nonneg _)
      ((norm_nonneg _).trans (ht U)))⟩
  refine ⟨fun i => ⟨hp.mul (hF i).1, fun hh k U => ?_⟩,fun U => ?_⟩
  · unfold carried weight; rw [(hF i).2 k U,hh k U]
  obtain ⟨hx,hy⟩:=packs_pay Q h H hz he hc
  unfold perturbs progeny baseJoint carried
  rw [converts Q h hz he U,←runs Q h H z hz hc U,tsum_mul_left]; unfold weight
  let f s := F.attends Q z s U; let g s := F.draw Q s z U
  have hv : (∑' i,f i)*(∑' i,g i)=∑' i,F.plain Q i z U := tsum_mul_tsum_of_summable_norm (hx.absolute U) (hy.absolute U)
  rw [←hv]; unfold f g; ring
end Attended
end YM.Multi.Vacuum.Arrival.Flock
