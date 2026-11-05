import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Aisles
import YM.Next.BOUNDARY.Coordinates
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression

set_option warningAsError false

/-!
# Calibration in the middle

These columns are always readings of the actual Factory. NEVER another
placement-offset basis. Use even on a trial for which there is no terminal
calibration in C (e.g. Wdff), when needing to *match* in a different weight.

Two extra finite-step accuracy estimates `Chorus` & `Mute` (below). We'll
address how to get them and their schedules later; neither follows from
`.Makes` alone as far as we know. No hypothesis about a multi-step signed-source
continuation or attenuation in these tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source Bid
open Push.RelayDifference
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {N i p e : ℕ} {C : Family G}

-- a few local names; keep N,p specified (same orders)
abbrev Inks (C : Family G) (e i p : ℕ) := Body (C.labels.level e) (C.side i p)
def inherited (C : Family G) (e N p i : ℕ) : GridU (C.side i p) := ((C.factory e N p).entries i 0).support
def library (C : Family G) (e N p i : ℕ) (v : C.label e) : Inks C e i p := Body.unpack ((C.factory e N p).entries i v)
abbrev count (x : C.label e) := (C.labels.level e).coeffSize x
abbrev nonunit (x : C.label e) := (C.labels.level e).core x
abbrev columns (C : Family G) (i) := (C.path.levels.params i).columns
abbrev silver (C : Family G) (i) := Real.sqrt (C.path.levels.clock.forcedAllowance i)
abbrev grow (C : Family G) (e i : ℕ) := ((C.S.block i).val:ℂ)^e
abbrev Boots (N) (D : Inks C e i p) := Body.Ok 0 C.params (C.path.rep N p i) (inherited C e N p i) D
abbrev Shod (N) (D : Inks C e i p) (r : ℝ) := Body.cap 0 (C.path.rep N p i) (inherited C e N p i) D (silver C i) r
/-- One-scale *unnormalized* identity in the same weight separating coefficient
price from derivative bills. Beta and centered step held fixed. -/
abbrev weighs (N) (D : Inks C e i p) := Body.density D 0 (C.localSection e) (C.path.rep N p i) (inherited C e N p i)
def carries (N) (D : Inks C e (i+1) p) (D' : Inks C e i p) :=
  weighs N D'=grow C e i • (C.path.levels.clock.op i p).push (C.path.β N p (i+1)) (weighs N D)

open Body
variable (H : C.Makes) (h : C.ref e ≤ i) (he : i ≤ N)
include H h he



def matrices (p : ℕ) : C.label e ≃ₗ[ℂ] C.label e := by
  have hb := H.calibrated _ N p (h.trans he)
  let M (j) v := coord (library C e N p j v)
  let T : C.label e →ₗ[ℂ] C.label e := ((hb.linear i h he).1).mk' _
  have hX : Injective T := by
    apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    have hh (j) (hg : i ≤ j) (hr : j ≤ N) : M j u=0 := by
      induction j,hg using Nat.le_induction with
      | base => exact hu
      | succ j hJ ih =>
        have hf := hb.back j (h.trans hJ) hr u
        change count (M (j+1) u) ≤ _* count (M j u) at hf
        rw [ih (j.le_succ.trans hr)] at hf
        apply Work.G08.size_separates _ _
        simpa [count,Labels.Frame.coeffSize] using hf
    have ht := hh N he le_rfl
    exact (hb.bare_coord u).symm.trans ht
  exact LinearEquiv.ofBijective T ⟨hX,LinearMap.injective_iff_surjective.mp hX⟩


/-- Fit a new vector into the old coordinates at any stage. -/
def fits (p : ℕ) (x : C.label e) : C.label e := (matrices H h he p).symm x






omit h in
lemma integral {D : Inks C e i p} {u : ℝ} (hh : Boots N D) (hq : Shod N D u) :
    Integrable (weighs N D) (prior G _) := by
  obtain ⟨hM,t,ht⟩ := Coefficient.envelope (C.localSection e) (H.wilson.represents N p i he).good hq hh
  exact Integrable.of_bound hM.aestronglyMeasurable _ (Filter.Eventually.of_forall ht)
omit H h he in
lemma push_pair (i : ℕ) {X Y : Config G (C.side (i+1) p) → ℂ} (β : ℝ)
    (hX : Integrable X (prior G _)) (hY : Integrable Y (prior G _)) :
    let L := C.path.levels.clock.op i p
    L.push β (X+Y)=L.push β X+L.push β Y := by
  intro L; have h := C.path.levels.transition_mass i p β
  funext V; simp only [Pi.add_apply,StepData.push,smul_add]
  exact integral_add (StepData.push_slice h V X hX) (StepData.push_slice h V Y hY)
omit h in
lemma carry_plus (hf : i < N) {D E : Inks C e (i+1) p} {D' E' : Inks C e i p} {a b c d : ℝ}
    (hd : Boots N D) (hd' : Shod N D a) (hj : Boots N E) (hj' : Shod N E b)
    (hx : Shod N D' c) (hy : Shod N E' d) (H1 : carries N D D') (H2 : carries N E E') : carries N (D+E) (D'+E') := by
  have hD := integral H hf hd hd'
  have hE := integral H hf hj hj'
  unfold carries weighs at *
  rw [Body.density_add hx hy _ ((H.wilson.represents N p i he).good), Body.density_add hd' hj' _
    ((H.wilson.represents N p _ hf).good), push_pair i _ hD hE,smul_add, H1,H2]

section Admissions
omit H h he
variable (C) (e N p i : ℕ)

def softer (C : Family G) (i : ℕ) := Bid.barunit (C.S.block i)/(4*(1+columns C (i+1)))



/-- Approximation estimates on the *actual calibrated primary columns* at a
step. Stage Worth (pre-L); can choose W. Anticipate the factor 4 eps margin
(and the factor 2 in paying coarse remainder), buy such Worth & calendar
when fitting the Family initially. This is stronger than Based. No assumption
how to match a trial to these columns, nor on their environment in different
multisource calls. E.g., use Paper.Clocks with sharpened local PSREC margins.
For these calls B needn't be uniform in x, though expected leading income rule
is. -/
def Chorus (W : Worth) := ∀ x : C.label e, let Q := C.labels.level e
    let L := C.S.block i; let K := W.K (C.path.levels.clock.J (i+1))
    let u := library C e N p i x; let v := coord (library C e N p (i+1) x); let y := vowel Q L v
    ∃ B : C.label e ≃ₗ[ℂ] C.label e, (∀ v,count (C:=C) (e:=e) (B v) ≤ K*count (C:=C) v ∧
      count (C:=C) (e:=e) (B.symm v) ≤ K*count (C:=C) v ∧ nonunit (C:=C) (e:=e) (B v)=B (nonunit (C:=C) v)) ∧
      count (C:=C) (e:=e) (coord u-B y) ≤ barunit L/4*count (C:=C) (e:=e) (nonunit (C:=C) v) ∧
      Shod N u (K/2*count (C:=C) (e:=e) (nonunit (C:=C) y))

/-- Only PURE remainder transfer.

At one step.

With masks, label
eligibility, full push, derivative and exponent weights already bought on
this history.

In particular, no assumption has to be made
about signed budgets or about a common *linear* transformation on comparison
data evolving separately and then chosen to match the primary at reference. -/
def Mute := ∀ D : Inks C e (i+1) p, coord D=0 → Boots N D → (∃ c,Shod N D c) →
    ∃ P : Inks C e i p, Boots N P ∧ carries N D P ∧ ∀ c : ℝ, Shod N D c →
      count (C:=C) (e:=e) (coord P) ≤ softer C i*c ∧ Shod N P (softer C i*c)

/-- The prices here are local calls not depending on cutoffs or chosen field
vectors when setting the reserve constants. But do require them at the same
family already meeting Shop (so actual scheduled betaBands etc). Can also ask
at every N,p≥...; f.fuse later is enough. -/
structure Passage (W : Worth) : Prop where
  aisles : ∀ j, C.ref e ≤ j → j ≤ N → Bays (inherited C e N p j) 0
  prim : ∀ j, C.ref e ≤ j → j < N → Chorus C e N p j W
  pureR : ∀ j, C.ref e ≤ j → j < N → Mute C e N p j
end Admissions
end YM.MultiNext.SignedSource
