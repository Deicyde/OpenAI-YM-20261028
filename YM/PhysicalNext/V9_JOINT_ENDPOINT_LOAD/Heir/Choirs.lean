import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Fusion
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Script

/-! # Assembling anchored clause for the E singleton part

No crossing between possibly many mixture choices at a given index, count
only their legitimately bought coefficients and keep the OLD multiplicity
before and after reallocating by parent. Label address sites/supports provided,
bulk consuming system still needs lattice sym tests (ValuesE etc), tag law
identities/prerequisites and local costs for ALL other operands. This clause
does not pay Local on its own, nor vanishing of the correlations/gradients of
the integral. Interacting path-history control still required. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Filter Function Set Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian Push.AbsoluteSums Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {S : StepData c f} {L : Side} {P B : BudgetPoint} {x u A t E τ : ℝ} {n p r : ℕ} {C : Libretto G n} {D : Record} {Pt : Teller G} {T : Tube G S}
    {q : Chi} {d : ℝ}
namespace Release

structure Quotation (C : Libretto G n) (p r : ℕ) (A t E : ℝ) : Prop where
  nonneg : 1≤E
  prices {c f : Side} (S : StepData c f) (D : Record) (P B : BudgetPoint) (X : Support f) (Y : Support c) (u x : ℝ) :
    P.power=p → B.supportExponent=A → accepts r A t S.patch.L → Walled S X Y x r → P.B=radiusB x → B.B≤2*P.B → P.threshold≤2*B.threshold →
      0≤u → Lute.Plented C D P B S.patch.L r x u → ∀ τ : ℝ, 0≤τ → Real.exp (t*coverNumber P.B Y)*(τ*Lute.returnFee C D P B S.patch.L X r x u) ≤ E*((S.patch.L.val:ℝ)⁻¹)^5 * B.mass X τ
lemma quoting (C : Libretto G n) (p r : ℕ) {A t : ℝ} (hA : 0<A) (ht : 0≤t) : ∃ E, Quotation C p r A t E := by
  obtain ⟨E,h,H⟩ := preprices C p r hA ht; exact ⟨E,h,H⟩

lemma spread {ι : Type*} (q : Ratio c f) (a : ι → Site f) (b u : ι → ℝ) (ht : ∀ i, 0 ≤ u i) (hh : ∀ z : Site f,SumBudget (fun i => if a i=z then b i else 0) τ) (hE : 0≤E)
    (he : ∀ i, u i ≤ E*((q.count.val:ℝ)⁻¹)^5 * b i) (y : Site c) : SumBudget (fun i => if q.parent (a i)=y then u i else 0) (E/(q.count.val:ℝ)*τ) := by
  let L : ℝ := q.count.val; have hL : 0<L := Nat.cast_pos.mpr q.count.property
  let C (z : Site q.count) := E*L⁻¹^5 * τ
  let h z (i : ι) := if a i=q.assemble (y,z) then u i else 0
  have hb z : SumBudget (h z) (C z) := budget_mono (budget_scale (mul_nonneg hE (show 0≤(L⁻¹)^5 by positivity)) (hh (q.assemble (y,z)))) (fun i => by unfold h; split <;> first | exact ht i | exact le_rfl) (fun i => by unfold h; split; exact he i; rw [mul_zero])
  rw [show E/L*τ=∑ z,C z by simp only [C,Finset.sum_const,Finset.card_univ,site_card,nsmul_eq_mul,Nat.cast_pow]; change _=L^4*_; field_simp]
  refine budget_mono (budget_over Finset.univ h C (fun z _ => hb z)) (fun i => by split; exact ht i; rfl) fun i => ?_
  split
  next hi => exact le_trans (b:=h (q.residue (a i)) i) ((if_pos (show a i = q.assemble (y, q.residue (a i)) from hi ▸ (by rw [q.unpack]; exact (q.splitSites.symm_apply_apply _).symm))).symm.le) (Finset.single_le_sum (f:=fun z => h z i) (fun z _ => (hb z).1 _) (Finset.mem_univ _))
  exact Finset.sum_nonneg fun z _ => (hb z).1 _

variable {C : Libretto G n}
theorem chorus {a : Activities G f} {labels : ℕ → RegularAddress c} (σ : ∀ i, Script G S (a.reg i).support (labels i).support r x) (hs : ∀ i, (labels i).site=S.ratio.parent (a.reg i).site)
    (hg : G.Simple) (hq : Quotation C P.power r B.supportExponent t E) (h : Plays C D P B Pt T x) (hA : accepts r B.supportExponent t S.patch.L) (hP : P.B=radiusB x) (hu : 0≤u)
    (hC : Lute.Plented C D P B S.patch.L r x u) (hh : ∀ i,(σ i).Played n u (D.ε*B.threshold)) (hE : a.RegularFamily B) (hτ : a.EBound B τ) :
    ∃ v : ℕ→ℝ, (∀ i, let f := (σ i).tuning u q d (a.E i) T; P.Regular (labels i).support f ∧ P.supBounds (labels i).site (labels i).support f (v i)) ∧
      Footprint.Anchored (fun i => (labels i).site) v (fun i => coverNumber P.B (labels i).support) t (E/(S.patch.L.val:ℝ)*τ) := by
  obtain ⟨w,hw,H⟩ := hτ
  let v i := w i * Lute.returnFee C D P B S.patch.L (a.reg i).support r x u
  have hc i := (σ i).choirs (q:=q) (d:=d) hg h (Seed.family hE i) (hw i) hu (hh i)
  have he i := hq.prices S D P B _ _ u x rfl rfl hA (σ i).fields hP (by rw [hP]; exact h.rehearsed.weft.cover) (by rw [h.rehearsed.temp_eq]; exact h.rehearsed.tensions.coarse) hu hC (w i) (hw i).1
  refine ⟨v,fun i => hs i ▸ hc i,fun y => ?_⟩
  simp_rw [hs]
  exact spread S.ratio _ _ _ (fun i => mul_nonneg (hc i).2.1 (Real.exp_pos _).le) H (by linarith only [hq.nonneg]) (fun i => (mul_comm ..).le.trans (he i)) y
end Release
end YM.PhysicalNext.JointLoad.Heir
