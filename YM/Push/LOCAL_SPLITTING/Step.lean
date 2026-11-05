import YM.Push.LOCAL_SPLITTING.Comparison
import YM.Push.LOCAL_SPLITTING.Funding
import YM.Push.LOCAL_SPLITTING.Leading


/-!
# A one-block source conversion and its upstream estimates

Same `C.op m p` (shared-choice kernel on physical links), history and Rep
on both sides.

`Output` asks for an exact *pre-readout*
local-component expansion at output level, including its non-primary terms
*not yet projection-null*, with regular & forced income, leading-model and
identity log-jet estimates.

It concerns the stated actual unnormalized
pushforward, not the kernel after dividing by its separate measure in a sector.

We do **not** assume the residual bound on an insertion after readout; below
we produce that insertion and an `owns` estimate.

All losses for this
conversion in the weighted coordinates are before the side and independent
of L after the stated delay, including support costs.

No availability of
`Output` on all inputs without further estimates is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations Work.G08 Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {d N p m : ℕ} {F : Labels.Frame G d} {H : RG.History G} {A : Hol G} {T : SectionData F}

abbrev kappa (H : RG.History G) (m : ℕ) := Real.sqrt (H.levels.clock.forcedAllowance m)

private theorem barunit_pos (L : Side) : 0 < barunit L := by have h : 0 < L.val := L.property; unfold barunit puffs; positivity

def nextCash (H : RG.History G) (F : Labels.Frame G d) (m : ℕ) (W : Worth) (v : F.Coeff) (t : ℝ) :=
  W.K (H.levels.clock.J (m+1)) * F.coeffSize (F.core (vowel F (H.S.block m) v)) + barunit (H.S.block m) * t

def rawLimit (H : RG.History G) (F : Labels.Frame G d) (m : ℕ) (D q : ℝ) (v : F.Coeff) (t : ℝ) :=
  D*F.coeffSize (F.core (vowel F (H.S.block m) v)) + q*t

structure Prices (A : Hol G) (T : SectionData F) (H : RG.History G) (m : ℕ) (W : Worth) (w σ D q ε : ℝ) : Prop where
  upper : 0 ≤ D
  nonneg : 0 ≤ q
  perturbation : 0 ≤ ε
  matrices : triangularPrice F σ ≤ W.K (H.levels.clock.J (m+1))
  principal : (2*factor A T (H.levels.params m).supportExponent w + 1)*D ≤ W.K (H.levels.clock.J (m+1))
  shrinks : (2*factor A T (H.levels.params m).supportExponent w + 1)*q ≤ barunit (H.S.block m)
  errs : errorPrice A F*ε ≤ barunit (H.S.block m)

structure Output (A : Hol G) (T : SectionData F) (H : RG.History G) (N p m : ℕ) (o : Site (H.S.side (m+1) p))
    (P : Coefficient F (H.S.side (m+1) p)) (t : ℝ) (X : ℕ → Support (H.S.side m p)) (M : Raw F (H.S.side m p)) (σ D q ε : ℝ) : Prop where
  raw : M.Format ((H.levels.clock.op m p).ratio.parent o) X (H.rep N p m)
  bulk : let R := H.rep N p m
    ∃ e, M.cost ((H.levels.clock.op m p).ratio.parent o) X R.p e ∧ SumBudget (fun i => reservedMass R.p (X i) (e i)) (rawLimit H F m D q P.x t)
  packets : let R := H.rep N p m
    ForceCost R.p R.activities M.forced (kappa H m * rawLimit H F m D q P.x t)
  identity : ∃ (B : F.Coeff →ₗ[ℂ] F.Coeff) (g : ℕ → Directions G (H.S.side m p) → ℂ),
    Leading B σ ∧ Models A ((H.levels.clock.op m p).ratio.parent o) X (H.rep N p m).p M (B (vowel F (H.S.block m) P.x)) (ε*(F.coeffSize (F.core P.x)+t)) g
  integrates : M.eval ((H.levels.clock.op m p).ratio.parent o) X T (H.rep N p m) = ((H.S.block m).val : ℂ)^d • (H.levels.clock.op m p).push (H.β N p (m+1)) (P.density o T (H.rep N p (m+1)))

variable {w t σ D q ε : ℝ} {W : Worth} {o : Site (H.S.side (m+1) p)} {P : Coefficient F (H.S.side (m+1) p)}
    {X : ℕ → Support (H.S.side m p)} {M : Raw F (H.S.side m p)}

theorem Output.income (he : Output A T H N p m o P t X M σ D q ε) (hcash : Prices A T H m W w σ D q ε) (ht : 0 ≤ t)
    (hconv : H.Conv N p m) (hy : Readable A T (H.rep N p m).p (H.S.side m p) w) (hW : hitWidth (H.levels.budget m)*kappa H m ≤ 1) :
    Raw.Income M ((H.levels.clock.op m p).ratio.parent o) X A T (H.rep N p m) w (H.levels.clock.forcedAllowance m) (kappa H m) (nextCash H F m W P.x t) := by
  have ha : 0 ≤ rawLimit H F m D q P.x t := add_nonneg (mul_nonneg hcash.upper (size_nonneg ..)) (mul_nonneg hcash.nonneg ht)
  obtain ⟨e,h1,h2⟩ := he.bulk
  refine income_of_reserved hy.sound he.raw.origin h1 h2 he.packets ha ha (Real.exp_pos _).le hy.nonneg (by rwa [hconv.vac]) ?_
  rw [hconv.vac]; let z := F.coeffSize (F.core (vowel F (H.S.block m) P.x))
  have hz : 0 ≤ z := size_nonneg ..
  have hb := mul_le_mul_of_nonneg_right hcash.principal hz
  have he := mul_le_mul_of_nonneg_right hcash.shrinks ht
  dsimp only [Levels.budget]; unfold rawLimit nextCash; change 2*_* (D*z+q*t)+(D*z+q*t) ≤ _
  linarith

def localOwns (H : RG.History G) (m : ℕ) (W : Worth) (F : Labels.Frame G d) (u v : F.Coeff) (t : ℝ) :=
    direction H W m F u v (nextCash H F m W v t) t ∧ (v = unitVec F H (m+1) → t=0 → u=unitVec F H m ∧ nextCash H F m W v t = 0)

private theorem vowel_unit (H : RG.History G) (F : Labels.Frame G d) (m : ℕ) : vowel F (H.S.block m) (unitVec F H (m+1)) = unitVec F H m := by
  funext i
  by_cases h : i=0
  · subst i; have he := (H.S.block m).property.ne'
    simp [vowel,H.S.a_step,unitVec,F.zero_degree,Frame.e0, ← mul_pow,mul_div_cancel₀ _ (show ((H.S.block m).val:ℂ) ≠ 0 by exact_mod_cast he)]
  simp [vowel, unitVec, Frame.e0,h]

theorem Output.owns (he : Output A T H N p m o P t X M σ D q ε) (hcash : Prices A T H m W w σ D q ε) (ht : 0 ≤ t)
    (S : Slots (H.rep N p m).activities (fun i => joint T ((H.levels.clock.op m p).ratio.parent o) (X i)))
    (hy : Readable A T (H.rep N p m).p (H.S.side m p) w) (hs : Summable (M.row ((H.levels.clock.op m p).ratio.parent o) X A (H.rep N p m).p.threshold)) :
    let Q := M.build ((H.levels.clock.op m p).ratio.parent o) X A T (H.rep N p m) S
    localOwns H m W F Q.x P.x t := by
  intro Q
  let y := vowel F (H.S.block m) P.x
  have hcore := size_nonneg F (F.core P.x)
  obtain ⟨B,g,hB,hg⟩ := he.identity
  have hd : F.coeffSize (Q.x-B y) ≤ barunit (H.S.block m)*(F.coeffSize (F.core P.x)+t) := (compareModels S hy he.raw hs
    (mul_nonneg hcash.perturbation (add_nonneg hcore ht)) hg).trans ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hcash.errs (add_nonneg hcore ht)))
  let Z := H.levels.clock.J (m+1)
  have hnext : 0 ≤ nextCash H F m W P.x t := add_nonneg (mul_nonneg (zero_le_one.trans (W.prices Z)) (size_nonneg ..)) (mul_nonneg (barunit_pos _).le ht)
  constructor
  · let b := LinearEquiv.ofBijective B hB.bijective
    refine ⟨hnext,ht,b,fun x => ?_, hd,le_rfl⟩
    have hx : B (b.symm x) = x := b.apply_symm_apply x
    obtain ⟨_,hb⟩ := hB.cost (b.symm x)
    rw [hx] at hb
    exact ⟨((hB.cost x).1.trans (mul_le_mul_of_nonneg_right hcash.matrices (size_nonneg ..))),hb.trans (mul_le_mul_of_nonneg_right hcash.matrices (size_nonneg ..)),hB.core x⟩
  intro hv hr
  have h0 (j : ℕ) : F.coeffSize (F.core (unitVec F H j)) = 0 := by
    unfold unitVec; rw [map_smul,show F.core F.e0 = 0 from funext fun i => by by_cases h : i=0 <;> simp [Frame.e0,Frame.core,Function.update,h], smul_zero]; simp [Frame.coeffSize]
  have he : Q.x = B y := sub_eq_zero.mp (size_separates F _ (by rw [hv,hr,h0] at hd; simpa using hd))
  rw [he, nextCash, show y = vowel F (H.S.block m) P.x from rfl, hv, vowel_unit H F, hr, h0]; simp [unitVec,hB.unit]

/-- One-step exact marked conversion in an actual Conv history, with explicit
missing component producer estimates. No `m+1 ≤ N` used in the algebra; need
fine density integrability separately when making estimates for `Output` or
using the identity in integrals. Output `S`, not an existential refit. -/
theorem one_step (he : Output A T H N p m o P t X M σ D q ε) (hcash : Prices A T H m W w σ D q ε) (ht : 0 ≤ t)
    (S : Slots (H.rep N p m).activities (fun i => joint T ((H.levels.clock.op m p).ratio.parent o) (X i))) (hconv : H.Conv N p m)
    (hy : Readable A T (H.rep N p m).p (H.S.side m p) w) (hW : hitWidth (H.levels.budget m)*kappa H m ≤ 1) :
    let c := H.levels.clock.op m p
    let R := H.rep N p m
    let Q := M.build (c.ratio.parent o) X A T R S
    Q.Format (c.ratio.parent o) A R ∧ Q.remBound (c.ratio.parent o) R (kappa H m) (nextCash H F m W P.x t) ∧
      Q.density (c.ratio.parent o) T R = ((H.S.block m).val : ℂ)^d • c.push (H.β N p (m+1)) (P.density o T (H.rep N p (m+1))) ∧ localOwns H m W F Q.x P.x t := by
  dsimp only
  have hf := hconv.good
  have hu := he.income hcash ht hconv hy hW
  have hκ : 0 < kappa H m := Real.sqrt_pos.mpr (Real.exp_pos _)
  exact ⟨Raw.build_format S hf.labels.forced hy he.raw,Raw.build_remBound S hf.labels.boundK hy he.raw hu hκ,
    (Raw.build_density S hf hy he.raw hu hκ).trans he.integrates,
    he.owns hcash ht S hy ((Raw.dominated_pieces _ hy he.raw hu).1.of_norm)⟩
end YM.Push.Local
