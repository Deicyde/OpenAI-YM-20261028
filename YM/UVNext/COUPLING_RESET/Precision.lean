import YM.UVNext.COUPLING_RESET.Advance


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# A precision-to-response currency conversion specific to B70

For obtaining `surplus`, if doing pre-reset calculations on the unmasked
`mainTerm`, `loop`, and with **only the quadratic** `secondTerm` at α price,
the two actual output test arguments need no clipping/tail replacements or
sector predicates. (The FINE integration of course still uses all of them.)
Handle the discrepancy here using the bought widths/monetary delays. This is
a value estimate, not a bound on masked E derivatives beyond reset. Exposes
where additional nonperturbative log-contrast estimates on the two vacuum
probes are required **beyond** jet matching and a bound on α relative to the leading log.
No identifying the interacting log with `thermal`!
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open MeasureTheory Push.PriceCompiler Push.BetaTransport Lattice Wilson RG RG.Shoot RG.Supply Input Precision Filter Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side}

lemma chord_le {P : BudgetPoint} {U : Config G n} (hu : flags P.threshold U = ∅) (p : Face (Per n)) :
    G.chord (faceValue U p) ≤ P.threshold := by
  by_contra! ht
  have h := (flags_spec P.threshold U p.1).mpr ⟨p,List.mem_toFinset.mpr (List.mem_cons_self),ht⟩
  simp [hu] at h

lemma unmasked_precision {P : BudgetPoint} (D : PathData G) (A : Clip) {V : Config G n} (hV : flags P.threshold V = ∅) :
    kinetic D A P V = mainTerm A D V ∧ D.inChannels A P 0 V = loop D V ∧ ∀ s : Signed,
      quadratic A D (pull s 0 V) = ∑ f, D.baseTerm A P (pull s 0 V) f := by
  have hh (s : Signed) p : G.chord (faceValue (pull s 0 V) p) ≤ P.threshold :=
    (Face.send_price V _ _ _ G.chord G.chord_inv (fun k g => G.chord_conj g k)).trans_le (chord_le hV _)
  have hk (s : Signed) (p : Face (Per n)) : PathData.kept A P.threshold p.1 (pull s 0 V) := fun f =>
    (hh s f).trans <| le_mul_of_one_le_right P.threshold_pos.le <| Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) A.radius_pos.le)
  have hb (s : Signed) : quadratic A D (pull s 0 V) = ∑ f, D.baseTerm A P (pull s 0 V) f := by
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [PathData.baseTerm,PathData.clipped,if_pos (hh ..),if_pos (hk s f), G.chord_price]; ring
  have hs {k : ℕ} (s : Signed) (F : ℕ → Atom G k) : ∑ x : Site n, PathData.atomSeries F P (pull s 0 V) x = uncut F (pull s 0 V) := by
    refine Finset.sum_congr rfl fun x _ => tsum_congr fun i => masked_eq _ _ _ _ ?_
    simp [Healthy,flags_empty (hh s)]
  simp [kinetic,mainTerm,loop, Patch.average,Finset.sum_add_distrib,PathData.inChannels,PathData.principal,← hb,hs,add_assoc]

lemma higher_estimate {P : BudgetPoint} {D : PathData G} {A : Clip} {σ C Λ : ℝ} (hD : D.Bounds A σ C Λ)
    {V : Config G n} (hV : flags P.threshold V = ∅) :
    |kinetic D A P V - secondTerm A D V| ≤ sites n * (2*C*P.threshold^3) := by
  obtain ⟨-, -, hb⟩ := unmasked_precision D A hV
  have hC : 0 ≤ C := (tsum_nonneg hD.three.1).trans hD.three.2.2
  have he (s : Signed) (x : Site n) :
      |PathData.atomSeries D.cubic P (pull s 0 V) x + PathData.atomSeries D.quartic P (pull s 0 V) x| ≤ 2*C*P.threshold^3 := by
    refine (abs_add_le ..).trans ((add_le_add (atomVolume _ _ _ _ hD.width hD.three)
      (atomVolume _ _ _ _ hD.width hD.four)).trans ?_)
    have ht := pow_le_pow_of_le_one P.threshold_pos.le P.threshold_le (by norm_num : (3:ℕ) ≤ 4)
    linarith only [mul_le_mul_of_nonneg_left ht hC]
  simp only [kinetic,secondTerm,Patch.average,hb]
  rw [← mul_sub]; change |(Fintype.card Signed : ℝ)⁻¹ * _| ≤ _
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),inv_mul_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos),
    Finset.sum_add_distrib,add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum fun s (_ : s∈Finset.univ) =>
    (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun x _ => he s x)).trans_eq ?_)
  simp [sites]

lemma late_cubic (C : ℝ) : ∀ᶠ x : ℝ in atTop, C * (Vac.Numbers.theta x)^3 ≤ (Vac.Numbers.Hat x) ^ ((11:ℝ)/5) := by
  filter_upwards [Vac.Numbers.cost 3 (1/5) (by norm_num), (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5)).eventually_ge_atTop C,
    eventually_gt_atTop (0:ℝ)] with x he h hx
  change C ≤ x ^ ((1:ℝ)/5) at h
  have hP : (mon x)^ (3:ℕ) ≤ x^((1:ℝ)/5) := by simpa using (show _ ≤ _ from he : Vac.Numbers.P x ^ ((3:ℕ):ℝ) ≤ x^((1:ℝ)/5))
  have ht : Vac.Numbers.Hat x = x^(-(1/2:ℝ)) := by rw [Vac.Numbers.Hat,Real.sqrt_eq_rpow,Real.rpow_neg hx.le]
  unfold Vac.Numbers.theta; rw [ht, mul_pow, ← Real.rpow_natCast (x^(-(1/2:ℝ))) 3, ← Real.rpow_mul hx.le,
    ← Real.rpow_mul hx.le]
  calc
    _ ≤ x^((1:ℝ)/5) * (x^(-(1/2:ℝ)*((3:ℕ):ℝ)) * x^((1:ℝ)/5)) := by have := mon_pos x; unfold mon at this; gcongr
    _ = _ := by rw [← Real.rpow_add hx,← Real.rpow_add hx]; norm_num

variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {η : ℕ → ℝ} {q : ResetPrices}
    {s : Set ℝ} {N m p : ℕ} {F : Terms B.a m p} {Q : In B.a m p} {V : Config G (B.a.S.side m p)}

def alphaBound (D : Rolls c) (j : ℕ) := (c.profile j).drift + |G.slopeConstant * Real.log (D.L j).val|

lemma within_alpha (hm : m < N) : |B.kin.alpha N m| ≤ alphaBound D (B.a.clock.J (m+1)) := by
  have he := B.support.kinetic N m hm
  rw [params_eq B.valid, block_eq B.valid] at he
  unfold alphaBound; have h := abs_sub ((B.kin.alpha N m)+G.slopeConstant*Real.log (D.L (B.a.clock.J (m+1))).val)
    (G.slopeConstant*Real.log (D.L (B.a.clock.J (m+1))).val)
  rw [add_sub_cancel_right] at h; linarith

def CubicGate (D : Rolls c) (q : ResetPrices) (j i : ℕ) (x : ℝ) :=
    alphaBound D j * (2 * (c.profile i).paths * (Vac.Numbers.theta x)^3) ≤
        q.cost j i / 2 * Vac.Numbers.Hat x ^ ((11:ℝ)/5)

theorem delay_cubic (D : Rolls c) (q : ResetPrices) (e : ℕ → ℝ) :
    ∃ f, Monotone f ∧ e ≤ f ∧ ∀ j x, f j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x := by
  refine collect_upper e _ fun j => eventually_transitions _ _ _ fun i _ => ?_
  have hp : 0 < q.cost j i := q.cost_pos ..
  filter_upwards [late_cubic (4 * alphaBound D j * (c.profile i).paths / q.cost j i)] with x hx
  unfold CubicGate
  rw [div_mul_eq_mul_div, div_le_iff₀ hp] at hx; linarith

theorem pays_cubic (B : Directed G I Z K P) (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x)
    (hm : m < N) :
    |B.kin.alpha N m| * (2 * (B.a.params m).paths * (B.a.budget m).threshold^3) ≤ funds B.a m q / 2 := by
  have hp := hg _ _ (B.valid.pays m) _ (step_paid B.a m)
  have h := (within_alpha (B:=B) hm)
  have he := (B.a.budget m).threshold_pos; have hc := (B.a.params m).paths_pos
  refine (mul_le_mul_of_nonneg_right h (by positivity)).trans ?_
  rw [params_eq B.valid, funds, mul_div_right_comm]
  exact hp

/-- Output test using *unmasked* (kinematic + one-loop) price prior to
higher-atom reset. Simplifications valid on THIS argument only. -/
def vacuumError (B : Directed G I Z K P) (N : ℕ) {m p : ℕ} (Q : In B.a m p) (V : Config G (B.a.S.side m p)) x :=
    let R := B.kin.path N m; let γ := (B.a.params m).clip
    ((Q x).beta * mainTerm γ R V + B.kin.alpha N m * secondTerm γ R V + loop R V) - contrast (target Q) V x

lemma pays_surplus (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x) {x : ℝ}
    (hm : m < N) (hV : flags (B.a.budget m).threshold V = ∅)
    (h : |vacuumError B N Q V x| ≤ sites (B.a.S.side m p) * (funds B.a m q / 2)) : let A := board B N F
    |predictor B N Q x * A.leg V + A.background V - contrast (target Q) V x| ≤ sites (B.a.S.side m p) * funds B.a m q := by
  intro A; change |predictor B N Q x * kinetic (B.bake.path N m) _ _ V + (B.bake.path N m).inChannels _ _ _ V - contrast (target Q) V x| ≤ _
  rw [B.bases]; have hD := B.support.cap N m hm.le
  let R := B.kin.path N m; let γ := (B.a.params m).clip
  let E := kinetic R γ (B.a.budget m) V
  obtain ⟨h1,h2,-⟩ := unmasked_precision R γ hV
  have hf := higher_estimate hD hV
  have hc := pays_cubic B hg hm
  let n := B.a.S.side m p
  have H : |B.kin.alpha N m * (E-secondTerm γ R V)| ≤ sites n * (funds B.a m q / 2) := by
    rw [abs_mul]; have hh := mul_le_mul_of_nonneg_left hf (abs_nonneg (B.kin.alpha N m)); exact hh.trans (by
      linarith only [mul_le_mul_of_nonneg_left hc (sites_pos n).le])
  unfold vacuumError at h
  change |predictor B N Q x * kinetic R γ (B.a.budget m) V + R.inChannels γ (B.a.budget m) 0 V - contrast (target Q) V x| ≤ _
  rw [h1,h2,predictor]; dsimp only [E] at H; rw [h1] at H
  have ⟨hu,hv⟩ := abs_le.mp h; have ⟨hw,hW⟩ := abs_le.mp H
  exact abs_le.mpr ⟨by dsimp only [R,γ,n] at *; linarith only [hu,hw],by dsimp only [R,γ,n] at *; linarith only [hv,hW]⟩
end YM.UVNext.CouplingReset
