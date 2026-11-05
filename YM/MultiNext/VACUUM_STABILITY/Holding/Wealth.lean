import YM.MultiNext.VACUUM_STABILITY.Holding.Affinity
import YM.MultiNext.VACUUM_STABILITY.Holding.Patterns

set_option warningAsError false

/-!
# Price from unmarked scores uniformly on arbitrary lists

The raw E terms themselves can be held through the kernel score when only requesting the
absolute price. Denote them using the REAL thermal expansion and K source terms themselves
at the fine configs. Allows separate construction of operator score bounds using every
integration chart, tags, seeds, shields and background sector derivatives only. Does not
require any derivative bound at all on K at post-integration perturb presentations. Does
require that the literal-factor and orientation decompositions agree with THESE supports even
on wrapping or away from any healthy patch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Holding
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture Puff Stamp
open Arrival Arrival.Flock Tune Gauss
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I V : Type} {G : Gauge} {n p : Side} {Q : Rep G n} {F : Flock V G n} {B : Brush V G p}
variable {P : BudgetPoint} {A : Component.Pasture (Station I F) B}

/-- One background operator allocation at certain held support sites. All core letters are
arguments of the same T search coordinates. Even if their indexing is statistically
independent to one order, NEVER assume their contributions are independent. Their local
link values and all stored tests carried evaluated from these (must include the query
addresses in A). -/
structure Jobs (F : Flock V G n) (I : Type) (M : Theater) where
  positions (i : Station I F) : M.place → Config G n
  taking : M.place → Prop

namespace Jobs
variable {M : Theater} (B : Jobs F I M) (Q : Rep G n)

def basis (s : Finset (Station I F)) (X : M.place) := ∏ i∈s, reads Q F i (B.positions i X)

variable [Fintype V]

def effect (s : Finset (Station I F)) (z : V→ℂ) (X : M.place) := ∏ i∈s, assay Q F i z (B.positions i X)

lemma expand (s : Finset (Station I F)) (z : V → ℂ) (X : M.place) : B.effect Q s z X=
    beat (∑ i∈s,codon Q F i) z * B.basis Q s X := by
  simp only [beat_pile,effect, assay,Pi.smul_apply,smul_eq_mul,basis,prod_mul_distrib]
end Jobs

variable (Q) (A)

-- Soft unit at post-Vac
structure Hire (T : Charts B P) where
  indoors (i U) (h : Healthy P.threshold (B.u i).zone U) : Jobs F I (T.soft i U h).stage
  flier i U : Jobs F I (T.packet i U).stage
  kernel (i U) (h : Healthy P.threshold (B.u i).zone U) : (T.soft i U h).stage.place → Config G p → ℂ
  kernelHard i U : (T.packet i U).stage.place → ℂ

-- Q implicit? used? Hire variables A not in fields, Lean

variable [Fintype V]

namespace Hire
variable {T : Charts B P}
-- earlier hypothesis on actual integrals. `Approved` commit with the chart
-- evaluation *actually produced in Flow*. Estimates without any input at z.
structure Approved (H : Hire (F:=F) (I:=I) T) (K J C κ : ℝ) (k l : ℕ) (tax : Station I F → ℝ) : Prop where
  liftH (i : Fruit) : calls B i = ∑ j∈A.bud i,codon Q F j
  secure (i U) (h : Healthy P.threshold (B.u i).zone U) :
    let M := T.soft i U h; let Y := H.indoors i U h
    let L := A.bud (.inl i)
    (∀ x, Y.basis Q L x≠0 → Y.taking x) ∧
    (∀ x, M.core x =ᶠ[𝓝 U] Y.basis Q L x • H.kernel i U h x) ∧
    ∀ v : List (Directions G p), v.length ≤ P.order → (∀ a∈v,P.dirBound (B.u i).anchor a) →
      Heat M.stage Y.taking (fun j => leftDerivs (H.kernel i U h j) v U) K J (Gauss.Live.bill A P.B (.inl i))
        (C*A.feast tax k P.B (.inl i)) l ∧ Priced M.stage (fun j => leftDerivs (M.core j) v U)
  freeze (i U) : let M := T.packet i U; let Y := H.flier i U
    let L := A.bud (.inr i)
    (∀ x,Y.basis Q L x≠0 → Y.taking x) ∧
    (∀ x, M.core x = Y.basis Q L x * H.kernelHard i U x) ∧
      Heat M.stage Y.taking (H.kernelHard i U) K J (Gauss.Live.bill A P.B (.inr i))
        (κ*(C*A.feast tax k P.B (.inr i))) l ∧ Priced M.stage M.core

-- per-occurrence literal estimate, not yet hit
lemma cut (H : Hire (F:=F) (I:=I) T) (K J C κ : ℝ) (k l : ℕ) (tax : Station I F → ℝ) {u : Station I F → ℝ}
    (h : Approved Q A H K J C κ k l tax) (z : V→ℂ) (he : ∀ i U, ‖assay Q F i z U‖ ≤ u i) :
    Charts.Covered A P T z K J C κ k l (fun i => u i * tax i) := by
  have hn (i) : 0 ≤ u i := (norm_nonneg _).trans (he i 1)
  let t (i) := ∏ j∈A.bud i,u j
  have ht i : 0≤t i := prod_nonneg fun i _ => hn i
  have hz (i : Fruit) : C*feast A (fun i => u i * tax i) k P.B i = t i*(C*feast A tax k P.B i) := by
    unfold feast t; rw [prod_mul_distrib]; ring
  have hg (i : Fruit) {M : Theater} (b : Jobs F I M) x : b.effect Q (A.bud i) z x=beat (calls B i) z * b.basis Q (A.bud i) x := by
    rw [Jobs.expand,h.liftH i]
  have hx (i) {M : Theater} (b : Jobs F I M) x : ‖b.effect Q (A.bud i) z x‖ ≤ t i := by
    unfold Jobs.effect; rw [norm_prod]; exact prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => he _ _
  constructor
  · intro i U hU v hv hw; dsimp only
    let M := T.soft i U hU; let Y := H.indoors i U hU; let y := Y.effect Q (A.bud (.inl i)) z
    obtain ⟨hp,hEq,hI⟩:=h.secure i U hU; obtain ⟨hI,hq⟩:=hI v hv hw
    rw [hz]; refine respond _ hI (f:=y) ?_ (fun i hi=>hp i ?_) (ht _) (hx _ _ ) (billable _ _ hq _)
    · intro j; change beat _ z * leftDerivs (M.core j) v U = _
      unfold y; rw [Jets.agrees (hEq j) v, scaled_left,hg]; exact (mul_assoc ..).symm
    unfold y at hi; rw [hg] at hi; exact right_ne_zero_of_mul hi
  intro i U; dsimp only
  let M := T.packet i U; let Y:=H.flier i U
  obtain ⟨hp,hb,hI,hq⟩:=h.freeze i U
  rw [hz,mul_left_comm]
  refine respond _ hI (f:=Y.effect Q (A.bud (.inr i)) z) ?_ (fun i hi => hp _ ?_) (ht _) (hx _ _ ) (billable _ _ hq _)
  · intro j; change beat _ z * (T.packet i U).core _ = _
    rw [hb,hg]; exact (mul_assoc ..).symm
  rw [hg] at hi; exact right_ne_zero_of_mul hi
end Hire

-- sufficient explicit parameter bill (`η` from actual step). Will need pre-stage
-- purchases in uniform request. no station exponent loss used between *different*
-- calls.
def crossingPrice (A : Currency G n p) (m : ℕ) (e c b κ η : ℝ) :=
    c + (e*(A.scaleCost m*(Sugar.powerFee A.P.order * η)) + e*(A.scaleCost m*(b+κ*η)))

variable {T : Charts B P}

theorem filled (H : Hire (F:=F) (I:=I) T) (K J C κ : ℝ) (k l : ℕ) (tax : Station I F → ℝ)
    (hK : 0≤K) (hJ : 1 ≤ J) (hC : 0≤C) (h : Hire.Approved Q A H K J C κ k l tax)
    (R : Currency G n p) (hR : R.Live) (hr : R.M=P.B) (hP : R.P=Q.p) (m : ℕ) (e c : ℝ) (he : 0 ≤ e)
    (hh : Table Q F R A) (hT : Passable Q F R A tax m e c)
    (t a u : ℝ) (ht : 0≤t) (ha : 0≤a) (hk : a+2 ≤ R.strong) (hβ : siteUnit P.B*t ≤ 1)
    (hz : coat K J l*C*(sizeTax (l+k)*(Real.exp t-1))≤u)
    {β η σ d Λ δ b : ℝ} (hη : 0≤η) (ηh : η≤1) (hp : 0 < β) (hB : Q.Lawful σ d Λ δ b) (hb : 0≤b)
    (hy : crossingPrice R m e c b β η ≤ t)
    (o : V→Site p) (z : V→ℂ) (fee : V→ℝ) (D : V→ Pulse G n) (hD : Attended F Q.p D (fun i=>R.ratio.embed (o i)) fee β)
    (hZ : z∈allot o fee η) : A.ProductCost P z u a κ := by
  have hf := Attended.crosses R hR hP hD hη hZ ηh hp hB hb
  obtain ⟨⟨hl,hL⟩,f,hy',hx⟩:=hf
  let g := F.raiseE Q.p z
  have hv i : 0≤g i := (hL i).2.2.1
  have hg i : 0≤f i := (hx i).1
  let d := priceAt F tax g f
  have hj : Ac.Hit A.sites P.B d (a+2) t := by
    have hf := Passable.buys (f:=g) Q hT hh he hl hy' hv hg
    rw [hr] at hf; refine Absolute.relax hf (by unfold crossingPrice at hy; rwa [hP] at hy) (fun j=>?_) (fun _ => le_rfl) hk
    apply mul_nonneg _ (hT.nonneg _)
    obtain i|i|i:= j; exact zero_le_one; exact hv _; exact hg _
  apply Charts.transfers A P T z hK hJ hC _ ha ht hβ hj hz
  refine Hire.cut Q A H _ _ _ _ _ _ tax (u:=fit F g f) h z ?_
  rintro (i|i|i) U
  · simp [codon,fit,reads,assay]
  · rw [at_pressure]
    let L := pennyZone F i.1
    let W := penny F i.1; obtain ⟨hb,-,he⟩:=hL i.1
    unfold Flock.optional
    by_cases h : Healthy Q.p.threshold L U
    · rw [masked_eq _ _ _ _ h]; exact he.2 U h [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ h,norm_zero]; exact hv _
  exact (hx i.1).2 U
end YM.Multi.Vacuum.Holding
