import YM.Next.FOUNDATIONS.SU2
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Hit
import YM.Push.GRID_APPROXIMATION.Joint
import YM.Push.GRID_APPROXIMATION.Nil

/-!
# Supply `Launch` budgets from precise upstream inputs

Price **before** merging. Need `a` with origins and rooted-mark budget
at one higher exponent after budgeting per-K sampling and a
vacuum hit budget at one higher exponent too. Prove origin-to-hit cost,
κ division conventions and estimates for actual old polynomials. Needed
alongside the unready physics. Does not claim it follows from `CellHyp`,
`Metered` etc (they don't give these estimates). Overlap receives old
K cost even when markers existed before F birth. Sufficient constants shown,
independent of volume.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Attach
open RG Lattice Wilson Cells MeasureTheory Measure Function Filter Finset Ac Marker Overlay Nil
open scoped Topology BigOperators
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}
    {P : Rep G n} {a : Bands R P}

/-- Cost port at birth. Tuning realizations still required. `κ0`
desired incoming hit budget at exp `[A+1]`, `κ1` desired marked forced
root budget (with its additional exponential of reserve and w markers).
Use actual entries prior to merging, needs true hit reserve from that
vacuum too. Doesn't force `extraTest` to have names reserved for spares.
-/
structure Before (a : Bands R P) (w : V → ℝ) (κ0 κ1 : ℝ) : Prop where
  positions : Injective a.origins
  markBound : 0 ≤ κ1
  hold : ∃ v : ℕ → ℝ, (∀ i,0≤v i ∧ ∀ U, ‖P.activities.K i U‖ ≤ v i) ∧
    Hit (fun i => (P.activities.forced i).support) P.p.B v (P.p.supportExponent+1) κ0
  bills : ∃ g : ℕ×ℕ → ℝ, (∀ i j, 0≤g (i,j) ∧ (∀ U, ‖a.entries i j U‖ ≤ g (i,j)) ∧ (0<g (i,j) → a.entries i j≠0)) ∧
    ∀ i : V, SumBudget (fun j : ℕ × ℕ => if i∈ (a.marks j.1 j.2).val then
        (Poly.toll w (a.marks j.1 j.2)*g j)*Real.exp
          ((P.p.supportExponent+1+1)*coverNumber P.p.B (P.activities.forced j.1).support) else 0) κ1

/-- Disjoint appended supports (sufficient for far copy application) or
an arbitrary site hit guarantee could also be used; use disjoint here to
keep cost explicit. Inputs separate masked/exponential and complement
uses. May derive from genuine norm-factorial tests in applications with
conversions. -/
structure Adds (I : Plan a) (w : V → ℝ) (u c ε : ℝ) : Prop where
  sparse : Pairwise (fun i j => Disjoint (I.Y i) (I.Y j))
  nonnegative : 0 ≤ ε
  unitBudget i : w i * ‖I.c i‖ ≤ u
  localBudget i : ∃ r : ℝ, P.p.supBounds (a.origins i) (I.Y i) (I.F i) r ∧
      w i * P.p.mass (I.Y i) r ≤ c
  fineBudget i : ∃ d : ℝ, 0≤d ∧ (∀ U, ‖I.F i U‖ ≤ d) ∧
      (w i*d) * Real.exp ((P.p.supportExponent+1)*coverNumber P.p.B (I.Y i)) ≤ ε

section old
variable {w : V → ℝ} {ρ γ κ0 κ1 δ κ u c d b : ℝ} (hr : P.activities.Valid P.p δ κ) (ha : a.Active) (ht : a.Radial w u c d b)

include ha ht hr in
lemma Before.accounts (H : Before a w κ0 κ1) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ f : ℕ → ℝ, (∀ i,0≤f i) ∧ Hit (fun i => (P.activities.forced i).support)
      P.p.B f (P.p.supportExponent+1) ((κ0+hitConstant P.p.B*κ1)/ρ) ∧
      ∀ i, ∃ A : Nil.Sheet R, 0≤A ∧ wordsPrice w A ≤ ρ*f i ∧ ∀ U j, ‖(a.each i U).part j‖ ≤ A j := by
  obtain ⟨v,hv,hR⟩ := H.hold
  obtain ⟨g,hg,hB⟩ := H.bills
  let C (i : ℕ) := (P.activities.forced i).support
  let W (x : ℕ × ℕ) := Poly.toll w (a.marks x.1 x.2)*g x
  let M := P.p.B
  let A := P.p.supportExponent+1
  have hw (i : R.Mode) := Poly.worth ht.pure i
  have hn (x : ℕ×ℕ) : 0 ≤ W x := mul_nonneg (hw _).le (hg x.1 x.2).1
  let f (i : ℕ) := (v i + ∑' j,W (i,j))/ρ
  have he : Hit (C ∘ Prod.fst) M W A (hitConstant M*κ1) := by
    apply root_to_hit _ _ a.origins H.positions _ hn (fun j => (a.marks j.1 j.2).val) _ _ H.markBound _ hB
    intro i hi
    obtain ⟨x,hx⟩ := ha.occurs i.1 i.2
    refine ⟨x,hx, ha.retained i.1 i.2 ((hg i.1 i.2).2.2 ?_) x hx⟩
    exact pos_of_mul_pos_right hi (hw _).le
  let X (x : Site n) (i : ℕ) := if x∈C i then Real.exp (A*coverNumber M (C i)) else 0
  have hf (x : Site n) :
      SumBudget (fun i:ℕ => v i*X x i) κ0 ∧ SumBudget (fun i:ℕ×ℕ => W i*X x i.1) (hitConstant M*κ1) := by
    simpa only [X,C,M,A,mul_ite,mul_zero,Function.comp_def]
      using And.intro (hR x) (he x)
  have hL (i : ℕ) : Summable fun j => W (i,j) := by
    have hx : (C i).Nonempty := (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup
    obtain ⟨x,hx⟩ := hx
    have hh (j) : 0≤W j*X x j.1 := (hf x).2.1 j
    have hz := ((summable_prod_of_nonneg (f:=fun i:ℕ×ℕ => W i*X x i.1) hh).mp ((hf x).2.2.1)).1 i
    exact hz.of_nonneg_of_le (fun j => hn (i,j)) (fun j => le_mul_of_one_le_right (hn (i,j)) (by
      unfold X; dsimp only; rw [if_pos hx]; have hA : 0≤A := add_nonneg P.p.exponent_pos.le zero_le_one
      exact Real.one_le_exp (mul_nonneg hA (by positivity))))
  let B (i : ℕ) (j : R.Mode) (l : ℕ) : ℝ := if j=a.marks i l then g (i,l) else 0
  have hN i j l : 0 ≤ B i j l := by unfold B; split; exacts [(hg _ _).1,le_rfl]
  have hT (i j) : Summable (B i j) := by
    apply Summable.of_nonneg_of_le (hN i j) (g:=_)
    · intro l; unfold B; split
      next he => exact le_of_eq (show g (i,l)=W (i,l)*(Poly.toll w j)⁻¹ by
        rw [he]; unfold W; have h := (hw (a.marks i l)).ne'; field_simp)
      next he => exact mul_nonneg (hn (i,l)) (inv_nonneg.mpr (hw j).le)
    exact (hL i).mul_right _
  refine ⟨f,fun i => div_nonneg (add_nonneg (hv i).1 (tsum_nonneg fun j => hn (i,j))) hρ.le,?_,?_⟩
  · intro x
    let p (i : ℕ) := if x∈ C i then f i*Real.exp (A*coverNumber M (C i)) else 0
    have hy i : p i=(v i*X x i + (∑' j, W (i,j) * X x i)) * ρ⁻¹ := by
      unfold p f; rw [tsum_mul_right]; unfold X; split <;> simp [div_eq_mul_inv,add_mul]; ring
    let Q : ℕ × ℕ → ℝ := fun i => W i * X x i.1
    obtain ⟨⟨h1,h2,h3⟩,⟨hz,hs,h5⟩⟩ := hf x
    have h4 := ((summable_prod_of_nonneg (show 0 ≤ Q from hz)).mp hs).2
    have hX := h2.add h4
    change SumBudget p _
    have hp : p = fun i => (v i*X x i + (∑' j, Q (i,j))) * ρ⁻¹ := funext hy
    rw [hp]; refine ⟨fun i => mul_nonneg (add_nonneg (h1 _) (tsum_nonneg fun j => hz (i,j))) (inv_nonneg.mpr hρ.le), hX.mul_right _,?_⟩
    have hh : Summable Q := hs
    rw [tsum_mul_right, Summable.tsum_add h2 h4, ← hh.tsum_prod, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right
      (add_le_add h3 h5) (inv_nonneg.mpr hρ.le)
  intro i
  let Q (j : R.Mode) := (if j=R.quiet then v i else 0)+(∑' l, B i j l)
  refine ⟨Q,fun j => ?_,?_, fun U j => ?_⟩
  · change 0≤Q j; unfold Q; apply add_nonneg _ (tsum_nonneg (hN i j)); split; exacts [(hv _).1,le_rfl]
  · have he (l : ℕ) : ∑ j, Poly.toll w j * B i j l = W (i,l) := by
      unfold B; rw [Finset.sum_eq_single (a.marks i l)]
      · simp [W]
      · intro j _ hj; rw [if_neg hj,mul_zero]
      simp
    unfold wordsPrice Q
    simp_rw [mul_add,Finset.sum_add_distrib,← tsum_mul_left,mul_ite,mul_zero]
    rw [← Summable.tsum_finsetSum (fun j _ => (hT i j).mul_left _)]; simp_rw [he]
    simp only [Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte, Poly.quiet_toll,one_mul]
    unfold f; exact le_of_eq (by field_simp)
  · have hp (l : ℕ) : ‖(a.tagged i l U).part j‖ ≤ B i j l := by
      unfold Bands.tagged B; rw [Poly.part_send]; split
      next he => exact (hg i l).2.1 U
      next he => simp
    have hS := a.baseBound ha ht hr U |>.1 i
    have hQ := (hT i j).of_nonneg_of_le (fun l => norm_nonneg _) hp
    unfold Bands.each Q; rw [Poly.part_plus,Poly.share hS,Poly.part_send]
    apply (norm_add_le ..).trans; apply add_le_add _ ((norm_tsum_le_tsum_norm hQ).trans (hQ.tsum_le_tsum hp (hT i j)))
    split; next he => simpa only [Complex.norm_real] using (hv i).2 U
    simp
end old




end YM.Push.GridApprox.Attach
