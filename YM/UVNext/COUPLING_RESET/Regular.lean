import YM.UVNext.COUPLING_RESET.Precision


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Pre-reset estimates on all-good configurations

`Prereset` specifies the representation identity and the bounds needed to estimate the scalar contribution after subtraction. The lemmas in this module take those estimates as hypotheses and derive the corresponding bounds on `Income`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.PriceCompiler Push.BetaTransport Lattice Wilson RG RG.Activities RG.Supply Input Precision Function Set Filter
open scoped Matrix.Norms.Frobenius Topology BigOperators

variable {G : Gauge} {n : Side}

/-- Like `RG.volumeE` but assuming only the numerical estimate on a
preparatory family. Use at the unforced probes in `Prereset`. -/
lemma preBound {P : BudgetPoint} {S : Activities G n} {δ : ℝ} (h : S.EBound P δ)
    {V : Config G n} (hV : flags P.threshold V = ∅) : |S.additive P V| ≤ sites n * δ := by
  obtain ⟨b,hb,hx⟩ := h
  let q (x : Site n) i := if (S.reg i).site = x then P.mass (S.reg i).support (b i) else 0
  have hq x : Summable (q x) := (hx x).2.1
  have hs := summable_sum (s:=Finset.univ) (fun x _ => hq x)
  have he i : ‖S.regularOccurrence P i V‖ ≤ ∑ x, q x i := by
    have hh : Healthy P.threshold (S.reg i).support V := by simp [Healthy,hV]
    simp only [q, Finset.sum_ite_eq, Finset.mem_univ, if_true, regularOccurrence,masked_eq _ _ _ _ hh]
    exact ((hb i).2 _ hh [] (Nat.zero_le _) (by simp)).trans (P.loMass _ _ (hb i).1)
  have ht := hs.of_nonneg_of_le (fun i => norm_nonneg _) he
  refine (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum he hs).trans ?_)
  rw [Summable.tsum_finsetSum fun x _ => hq x]; simpa [sites] using Finset.sum_le_sum (s:=Finset.univ) fun x _ => (hx x).2.2

lemma second_one (D : PathData G) (A : Clip) : secondTerm A D (1 : Config G n) = 0 := by
  have he (s : Signed) : pull s 0 (1:Config G n) = 1 := by funext e; unfold pull Step.read; split <;> simp
  have hu (b : Face (Per n)) : faceValue (1:Config G n) b = 1 := by simp [faceValue,travel,square]
  have ht (x : Site n) (l : Slot) : l.atSite (1:Config G n) x = 0 := by rw [Work.F03.atSite_path, hu, G.curvature_unit,map_zero]
  simp [secondTerm,Patch.average,quadratic,he,hu,PathData.ell,PathData.ellTerms,ht]

variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {q : ResetPrices}
    {s : Set ℝ} {N m p : ℕ} {Q : In B.a m p}

/-- One sufficient unforced value-income regime at the actual return.

Algebra of components on a different history wouldn't show it. -/
structure Prereset (B : Directed G I Z K P) (q : ResetPrices) (s : Set ℝ) (N m p : ℕ) (Q : In B.a m p)
    (u : ℝ → ℝ) (S : ℝ → Activities G (B.a.S.side m p)) : Prop where
  early x : x ∈ s → (S x).EBound (B.a.budget m) (funds B.a m q / 4)
  emit x : x∈s → ∀ V, flags (B.a.budget m).threshold V = ∅ →
    let R := B.kin.path N m; let A := (B.a.params m).clip
    target Q x V = Real.exp (u x * sites (B.a.S.side m p) - ((Q x).beta * mainTerm A R V + B.kin.alpha N m * secondTerm A R V + loop R V) -
      (S x).additive (B.a.budget m) V)

variable {u : ℝ → ℝ} {S : ℝ → Activities G (B.a.S.side m p)} {V : Config G (B.a.S.side m p)}

lemma Prereset.flat (h : Prereset B q s N m p Q u S) {x : ℝ} (hx : x ∈ s) :
    Real.log (target Q x 1) = u x * sites (B.a.S.side m p) - (S x).additive (B.a.budget m) 1 := by
  let R := B.kin.path N m; let A := (B.a.params m).clip
  have h0 : flags (B.a.budget m).threshold (1:Config G (B.a.S.side m p)) = ∅ := flags_one _
  obtain ⟨h₁,h₂,-⟩ := unmasked_precision R A h0
  rw [kinetic_one] at h₁
  rw [loop_one] at h₂
  rw [h.emit x hx _ h0, Real.log_exp]
  rw [← h₁, ← h₂, second_one]; ring

lemma Prereset.value_income (h : Prereset B q s N m p Q u S) (hV : flags (B.a.budget m).threshold V = ∅)
    {x : ℝ} (hx : x∈s) :
    (0 < target Q x 1 ∧ 0 < target Q x V) ∧ |scalar (target Q) x - u x| ≤ funds B.a m q / 4 ∧
      |vacuumError B N Q V x| ≤ sites (B.a.S.side m p) * (funds B.a m q / 2) := by
  have h₀ := preBound (h.early x hx) (flags_one _)
  have hh := preBound (h.early x hx) hV
  constructor
  · exact ⟨(Real.exp_pos _).trans_eq (h.emit x hx 1 (flags_one _)).symm,(Real.exp_pos _).trans_eq (h.emit x hx V hV).symm⟩
  constructor
  · let n := B.a.S.side m p
    have hn : sites n ≠ 0 := (sites_pos n).ne'
    rw [scalar,h.flat hx,sub_div,mul_div_cancel_right₀ _ hn,sub_sub_cancel_left,abs_neg, abs_div,abs_of_pos (sites_pos n)]
    apply (div_le_iff₀ (sites_pos n)).mpr; rw [mul_comm]; exact h₀
  unfold vacuumError contrast; rw [h.flat hx,h.emit x hx _ hV,Real.log_exp]
  obtain ⟨h1,h2⟩ := abs_le.mp h₀; obtain ⟨h3,h4⟩ := abs_le.mp hh; exact abs_le.mpr ⟨by linarith,by linarith⟩

variable {F : Terms B.a m p}

lemma Prereset.income (h : Prereset B q s N m p Q u S) (hV : flags (B.a.budget m).threshold V = ∅)
    (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x) (hm : m < N)
    (hc : Catalog (board B N F) s (window B.a m q) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m))
    (he : ∀ x∈s, ∀ a∈window B.a m q, ∀ b∈window B.a m q, (board B N F).varies V (funds B.a m q) x a b) : Income B N m p q s Q V F :=
  ⟨hc,fun _ hx => (h.value_income hV hx).1,fun _ hx => pays_surplus hg hm hV (h.value_income hV hx).2.2,
    fun x hx a ha b hb => Template.motion hV (hc.valid x hx a ha) (hc.valid x hx b hb) (he x hx a ha b hb)⟩
end YM.UVNext.CouplingReset
