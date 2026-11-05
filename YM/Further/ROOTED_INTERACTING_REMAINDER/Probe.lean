import YM.Next.FREE_KERNELS.Lifts
import YM.Push.CORRECTED_COLUMNS.Tree
import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped


/-!
# Exact weighted leftOver queries (intact)

Positive and signed probes with arbitrary Store/tag/position dependence
(structurally explicit bounds, for other use glue sector/LF integrands
**before** invoking estimate). Keep every profile. Nothing charged for log
branches or smoothness at switches. `cargo` allows support/pay bills varying
per share; interest rates chosen in `Station`. Sampling always on the SAME
joint array and probability measures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Lattice RG Wilson Filter Function Set Tree Finset MeasureTheory Precision
open SectorNext.Vacuum Pressure Pressure.Stores Push.SectorMeasure
open Next.Fluctuations.Sector Oriented Presented
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
  (F : Forest S.ratio) (T : Tube G S) (R : Rep G f) {x W : ℝ} (D : Allocation G S x W)

/-- An ALL-store/tag probe. Functions themselves, not just prior ae values;
may test every input dependency/status. Measurable domination for true
cost below. -/
abbrev GaugeProbe (G : Gauge) {c f : Side} (S : StepData c f) (F : Forest S.ratio) (X : Type*) :=
    Stores S→S.Choices→ F.Slice G × Config G c → X

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (g : GaugeProbe G S F X)

def carrier (A : Stores S) (i : S.Choices) (V : Config G c) (a : F.Slice G) :=
    ‖Real.exp (-R.scalar)*exposed R (till x) (F.drape a)‖ *
      ‖g A i (a,V)‖ * leaves A T R.beta x i V (F.drape a) -- x omitted by lean because curly?

def cargo (A : Stores S) (V : Config G c) :=
    sieve T R.beta x V * D.column A F V (fun i a => carrier (x:=x) F T R g A i V a)

/-- The literal RHS remainders, including complement queries. Set `g=1` for
scalar-stripped `leftOver`. -/
def itinerary (κ : ℝ) (Y : Finset (Stores S)) (V : Config G c) :=
    ∑ A∈Y, earn S G x κ R.beta A.shares * cargo F T R D g A V

/-- Same expression on LHS of the flight. Includes true signed/vector
coefficients, requires legitimate integrability for applying.
Keep CompleteSpace or use no application claim. -/
def inspectAt (A : Stores S) (i : S.Choices) (V : Config G c) :=
    ∫ a : F.Slice G, ((D.bill A i (F.drape a) V *
      taggedKernel S R.beta i (F.drape a) V * stripped R (F.drape a)) • g A i (a,V)) ∂F.order G

def repaid (Y : Finset (Stores S)) (V : Config G c) :=
    ∑ A∈Y, ∑ i : S.Choices, ‖inspectAt F R D g A i V‖

section payment
-- Envelopes even for integrating RHS. Integrands permitting L^p
-- growth on slice instead can relax these separately. All estimates actual
-- whenever queries are Envelopes (finite per period, no payment of
-- their `cost` on uniform conclusions). Allocation complement enlargements
-- could break that as well; check first. -

variable {T} {P : Teller G} (hT : P.Funds S T)
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w)
    (A : Stores S) (i : S.Choices)
include hR hT
set_option linter.unusedSectionVars false
lemma actual (he : Envelope (g A i)) : Envelope
    (fun p : F.Slice G × Config G c => D.bill A i (F.drape p.1) p.2 *
      carrier (x:=x) F T R g A i p.2 p.1) ∧ Envelope
    (fun p : F.Slice G × Config G c => (D.bill A i (F.drape p.1) p.2 *
      taggedKernel S R.beta i (F.drape p.1) p.2 * stripped R (F.drape p.1)) • g A i p) := by
  have hf : Measurable (fun p : F.Slice G × Config G c => F.drape p.1) := F.continuous_drape.measurable.comp measurable_fst
  let U := fun p : F.Slice G × Config G c => F.drape p.1
  have hB : S.patch.Branches S.kernel G := funds_branch hT
  have hE : Envelope (fun p => Real.exp (-R.scalar)*exposed R (till x) (U p)) :=
    (Envelope.const _).mul (Env.along (env_exposed R hR _) hf)
  have hN : Envelope (fun p => ‖Real.exp (-R.scalar)*exposed R (till x) (U p)‖) := by
    obtain ⟨b,hb⟩ := hE.cost; exact ⟨hE.meas.norm,b,fun i => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hb i)⟩
  have h₁ := D.envelope (U:=U) (V:=Prod.snd) hB hf measurable_snd A i
  have h₂ : Envelope (fun p => ‖g A i p‖) := by
    obtain ⟨b,hb⟩ := he.cost; exact ⟨he.meas.norm,b,fun j => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hb j)⟩
  have h₃ := env_leaves (V:=Prod.snd) hT A R.beta x i hf measurable_snd
  refine ⟨h₁.mul ((hN.mul h₂).mul h₃),?_⟩
  exact Env.scale ((h₁.mul (env_tagged (V:=Prod.snd) R.beta i hB hf measurable_snd)).mul
    ((Envelope.const _).mul (Env.along (R.envelope hR) hf))) he

lemma cargo_portable (he : ∀ i, Envelope (g A i)) : Envelope (cargo F T R D g A) := by
  apply (sieve_env R.beta x hT).mul
  unfold Allocation.column tagTotal
  apply Envelope.sum; intro i
  -- real smul, defeq
  exact Env.marginal (actual F R D g hT hR A i (he i)).1 _

lemma inspect_portable (he : Envelope (g A i)) : Envelope (inspectAt F R D g A i) :=
  Env.marginal (actual F R D g hT hR A i he).2 _

lemma itinerary_portable (κ : ℝ) (Y : Finset (Stores S)) (he : ∀ A i, Envelope (g A i)) :
    Envelope (itinerary F T R D g κ Y) := by
  unfold itinerary; apply Envelope.sum; intro i; exact (Envelope.const _).mul (cargo_portable F R D g hT hR i (he i))

lemma repaid_portable (Y : Finset (Stores S)) (he : ∀ A i, Envelope (g A i)) : Envelope (repaid F R D g Y) := by
  unfold repaid; apply Envelope.sum; intro A; apply Envelope.sum; intro i
  have h := inspect_portable F R D g hT hR A i (he A i)
  obtain ⟨b,hb⟩ := h.cost; exact ⟨h.meas.norm,b,fun j => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hb j)⟩

lemma individual [CompleteSpace X] {κ : ℝ} (he : Envelope (g A i)) (hp : PointCharge T x W κ) (hh : Fits T R x) (hβ : 0 ≤ R.beta)
    (V : Config G c) : ‖inspectAt F R D g A i V‖ ≤
      earn S G x κ R.beta A.shares * sieve T R.beta x V *
        ∫ a : F.Slice G,D.bill A i (F.drape a) V * carrier (x:=x) F T R g A i V a ∂F.order G := by
  let Y := F.Slice G × Config G c
  let M (p : Y) := D.bill A i (F.drape p.1) p.2 * carrier (x:=x) F T R g A i p.2 p.1
  let N (p : Y) := (D.bill A i (F.drape p.1) p.2 * taggedKernel S R.beta i (F.drape p.1) p.2 *
    stripped R (F.drape p.1)) • g A i p
  obtain ⟨hM,hN⟩ : Envelope M ∧ Envelope N := actual F R D g hT hR A i he
  let u (p : F.Slice G) := (p,V)
  have hU : Measurable u := measurable_id.prodMk measurable_const
  unfold inspectAt; rw [←integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans; apply integral_mono
    (Env.integrableX (Env.along hN hU) _).norm ((Env.integrableX (Env.along hM hU) _).const_mul _)
  intro a
  let y := F.drape a
  change ‖(_ : ℝ) • _‖ ≤ _ * (D.bill A i y V * carrier (x:=x) F T R g A i V a)
  by_cases h0 : D.bill A i y V = 0
  · change ‖(D.bill A i y V*_*_) • _‖ ≤ _*_
    simp [h0]
  by_cases hy : Alive S y i
  swap
  · change ‖(D.bill A i y V*(S.likelihood y i*_)*_) • _‖ ≤ _*(D.bill A i y V*(‖_‖ * _ *(S.likelihood y i*_)))
    simp [dead hy]
  have hb := funds_branch hT
  have hk : taggedKernel S R.beta i y V*R.eval y = _ := use_gap hh y i V
  rw [enters_eq hb A] at hk
  let C := earn S G x κ R.beta A.shares
  have hC : prefactor S G R.beta * Real.exp (-R.beta * meanEnergy A T x y i V) ≤ C :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (mean_pays F A x W y i V hb (fun j hj => F.on_tree a ⟨j,hj⟩) (D.actual _ _ _ _ h0) hy hp) (neg_nonpos.mpr hβ)))
        (prefactor_pos R.beta).le
  let s := sieve T R.beta x V
  let l := leaves A T R.beta x i V y
  have hl : 0≤l := mul_nonneg (S.likelihood_pos ..) (Real.exp_pos _).le
  have hs : 0≤s := (Real.exp_pos _).le
  rw [norm_smul]
  change ‖D.bill A i y V*taggedKernel S R.beta i y V*(Real.exp (-R.scalar)*R.eval y)‖ * ‖g A i (a,V)‖ ≤ C*s*(D.bill A i y V*(_*_*l))
  rw [show D.bill A i y V*taggedKernel S R.beta i y V*(Real.exp (-R.scalar)*R.eval y)=
      D.bill A i y V*Real.exp (-R.scalar)*(taggedKernel S R.beta i y V*R.eval y) by ring,hk]
  change ‖D.bill A i y V*Real.exp (-R.scalar)*(s*(exposed R _ y*(prefactor S G R.beta*_*l)))‖ * _ ≤ C*s*(D.bill A i y V*(‖Real.exp (-R.scalar)*exposed R (till x) y‖*_*l))
  simp only [norm_mul,Real.norm_of_nonneg hs,Real.norm_of_nonneg hl,Real.norm_of_nonneg (D.nonneg ..),
    Real.norm_of_nonneg (prefactor_pos R.beta).le,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_trans ?_ (le_of_eq (show D.bill A i y V*Real.exp (-R.scalar)*(s*(‖exposed R _ y‖*(C*l)))*‖g A i (a,V)‖=
    C*s*(D.bill _ _ _ _*(Real.exp (-R.scalar)*‖exposed R _ _‖*_*l)) by ring))
  gcongr
  · exact mul_nonneg (D.nonneg ..) (Real.exp_pos _).le
  all_goals first| exact D.nonneg .. | exact hs | exact hl | exact hC

lemma authorized [CompleteSpace X] {κ : ℝ} (Y : Finset (Stores S)) (he : ∀ A i,Envelope (g A i))
    (hp : PointCharge T x W κ) (hh : Fits T R x) (hβ : 0≤R.beta) (V : Config G c) :
    repaid F R D g Y V ≤ itinerary F T R D g κ Y V := by
  unfold repaid itinerary
  refine sum_le_sum fun A _ => ?_
  unfold cargo Allocation.column tagTotal Allocation.portion
  change _ ≤ _*(sieve T _ _ V*∑ i,∫ a : F.Slice G, D.bill A i (F.drape a) V * carrier (x:=x) F T R g A i V a ∂_)
  rw [←mul_assoc,Finset.mul_sum]; exact sum_le_sum fun i _ => individual F R D g hT hR A i (he _ _) hp hh hβ V
end payment

section bare_uses
omit [NormedSpace ℝ X]


lemma sees_flags {A : Stores S} {V : Config G c} (h : RG.flags (temp x) V≠ A.flags) : cargo F T R D g A V=0 := by
  unfold cargo Allocation.column tagTotal Allocation.portion
  have h0 (i) (a : F.Slice G) : D.bill A i (F.drape a) V = 0 := by
    by_contra he
    exact h (D.actual _ _ _ _ he).exactFlags.symm
  simp [h0]




end bare_uses

end YM.Further.RootedInteractingRemainder
