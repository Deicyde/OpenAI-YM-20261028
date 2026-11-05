import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Vivid

/-!
# Words, actual sector/product weights

One common F and tagged V,Y everywhere. `body` takes reference X and
prices variation in Y along slices (for integrations); colors and triggers
read that single configuration. Eligibility/present Seeds from occurrences
retained elsewhere ALSO required for selecting words. Here quota can work
without enforcing most beyond Pack checks and structural packet count.
Don't assume relative-sign tests except where built into those factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Coat
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type*}

lemma cumulate {M : Type*} [CommMonoid M] (v : Finset (ι⊕κ)) (Y : ι⊕κ→M) :
    ∏ i∈v,Y i=(∏ i∈v.toLeft,Y (.inl i))* ∏ i∈v.toRight,Y (.inr i) := by
  rw [← Finset.prod_disjSum, show Finset.disjSum v.toLeft v.toRight=v from by ext i; cases i <;> simp]

abbrev Head (S : StepData c f) := Mixed.Alphabet S (YM.ConnectedActivityE6.Alphabet c f)
abbrev Molecule (S : StepData c f) := Finset (Head S)

def blaze (p : Molecule S) : Finset (WarningAt c f) := p.toRight.toRight.toRight


namespace Coat
variable {x μ W α r C : ℝ} {L : Side} {R : Rep G f} {Ñ : ChartRatio G}
variable {G' : ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F)

/-- Structural s, reading K coverage from the calling context. Packets
not repriced in distinct neighboring log components. -/
def vertex (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ) (z : Air f G) (p : Head S) :=
    let u := X.liftA R.beta z
    p.elim (fun A => if Packets.connected S m X.B A then X.Pack R Ñ l W a A u else 0)
      (Sum.elim (X.bag R a u) (Sum.elim (X.raiseAir R a Ñ z) (X.detect u W a R l)))

def term (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ) (z : Air f G) (p : Molecule S) :=
    ∏ i∈p, X.vertex R Ñ W a l m z i

def body (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ) (p : Molecule S)
    (i : F.Slice G × Air f G) := (X.wrapY i.1).term R Ñ W a l m i.2 p

lemma vertex_b (hk : LocalRatio Ñ) (h : Intake P T X.x R) (he : ShellAccess S G X.x W X.width C) (a : ℝ) (l : Finset ℕ)
    (m : ℕ) (p : Head S) {i : Type*} [MeasurableSpace i] {Z : i → F.Slice G} {z : i → Air f G} (hz : Measurable Z) (hp : Measurable z) :
    Measurable (fun t=> (X.wrapY (Z t)).vertex R Ñ W a l m (z t) p) := by
  have hh := (X.airwards (v:=z) he h.ready hz).2.2 R.beta hp
  rcases p with p|p|p|p
  · let u t := X.wrapY (Z t)
    let f i := (u i).liftA R.beta (z i)
    change Measurable (fun t=> if Packets.connected S m X.B p then (u t).Pack R Ñ l W a p (f t) else 0)
    split_ifs
    · change Measurable (fun t => if X.existSeeds p 300 then (u t).steam R Ñ l W a p (f t) else 0)
      split_ifs
      · exact X.vapor_b hz he h.ready R hk a l p hh
      exact measurable_const
    exact measurable_const
  · exact X.paidK hz hh p h a
  · exact (Real.measurable_exp.comp (X.log_b hz he a h hk hp p)).sub measurable_const
  exact X.det_b hz hh p l R W a h.ready

lemma body_b (hk : LocalRatio Ñ) (h : Intake P T X.x R) (he : ShellAccess S G X.x W X.width C) (a : ℝ)
    (l : Finset ℕ) (m : ℕ) (p : Molecule S) : Measurable (X.body R Ñ W a l m p) :=
    Finset.measurable_fun_prod _ fun i _=> X.vertex_b hk h he a l m i measurable_fst measurable_snd

end Coat
open Target

/-- Prepared numbers backed by proofs; state explicitly on global periods
and support. Future means/cov local need additional geometry tests. -/
def steamP (S : StepData c f) (b : Mixed.Costs) (A : Stores S) := Packets.income b.cap b.spendSeed b.gain A.shares

/-- Key index field names for downstream use at a period. -/
structure Cash (W x μ : ℝ) (L : Side) (R : YM.ConnectedActivityE6.Target G P) (o : Target.Order G W) (C : ℝ)
    (T : Tube G S) (I : Rep G f) where
  alarms : ℝ
  laws : Target.Invoices W x μ L R o C T I
  v : ℕ→ℝ
  w : LogIndex c f→ℝ
  fares : let X := rates v w (alarms*topStorm S.patch)
    Sales (radiusB x) R.relative R.ε (footprints T I R.halo (radiusB x)) X
      (Sum.elim (Raw.forcedExtra I) (Sum.elim (exCharge T I) fun _ => 0)) (R.goal L x)
  pos : 0 ≤ alarms
  quotes : ∀ (F : Forest S.ratio) (Y : Coat T F), Y.x=x → Y.width=o.K → Y.manifest →
    (∀ i U, |Y.bag I o.a U i| ≤ v i) ∧ (∀ p z,|Y.farLog I o.a R.table z p| ≤ w p ∧
      |Y.raiseAir I o.a R.table z p| ≤ w p) ∧
      (∀ u l A, |Y.Pack I R.table l W o.a A u| ≤ steamP S (R.costs L μ I.beta x C) A) ∧
        ∀ p : Finset (WarningAt c f), Y.dice.real (Y.catastrophe o.ξ I.beta p) ≤ alarms^p.card ∧
          ∀ l z,(∀ i∈p,Y.detect (Y.liftA I.beta z) W o.a I l i≠0) → z∈Y.catastrophe o.ξ I.beta p

lemma circulates {W x μ C : ℝ} {L : Side} {I : Rep G f} {R : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    (h : Target.Invoices W x μ L R o C T I) : Nonempty (Cash W x μ L R o C T I) := by
  obtain ⟨u,v,H,hH,hp,hq⟩ := h.vapors
  exact ⟨⟨H,h,u,v,hp,hH,hq⟩⟩
end YM.ConnectedActivityE6
