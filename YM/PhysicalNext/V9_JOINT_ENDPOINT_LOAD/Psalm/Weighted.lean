import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Album

/-!
# Full support-hit budget of the double-marked singleton

At its original-projected anchor with every argument/path test backed in Y
(if enlarged after this calculation, MUST pay again). Unlike the linear E
anchored result, can hit anywhere before coupling delay even for lambda-derivative
values. Doesn't price additional calls needed to supply a broad/K/ordinary
partner or if taking differences where THESE data weren't fixed (other
labels under the expectation are not supported). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Solo
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
   Push.SectorMeasure Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian Heir
   Push.AbsoluteSums
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {V : Config G c} {P B : BudgetPoint} {u t r₀ δ θ x E : ℝ} {n r : ℕ} {o : Site f}
    {k : S.Choices} {Pt : Teller G} {C : Libretto G n} {Bt : Baton G} {D : Record} {d : ℝ} {q : Chi}

variable {a : Activities G f} {labels : ℕ → RegularAddress c} (σ : ∀ i, Script G S (a.reg i).support (labels i).support r x) (hs : ∀ i, (labels i).site=S.ratio.parent (a.reg i).site)
    (I : Instrument B.order) (hg : G.Simple) (hq : Release.Quotation C P.power r B.supportExponent (t+2) E) (ht : 0 ≤ t) (h : Plays C D P B Pt T x) (hA : Release.accepts r B.supportExponent (t+2) S.patch.L)
    (hP : P.B=radiusB x) (hu : 0≤u) (hC : Lute.Plented C D P B S.patch.L r x u) (hh : ∀ i,(σ i).Played n u (D.ε*B.threshold)) (hE : a.RegularFamily B) (hτ : a.EBound B δ) (hδ : δ ≤ 1)

structure Income (P : BudgetPoint) (I : Instrument B.order) (T : Tube G S) (labels : ℕ→RegularAddress c) (σ : ∀ i, Script G S (a.reg i).support (labels i).support r x) (u t E : ℝ) (w : ℕ → ℝ) : Prop where
  earns (q : Chi) (d : ℝ) (H) (he : Marked H B.order I.bid) (j) : let f := album T u q d (a.E j) H (σ j)
    P.Regular (labels j).support f ∧ P.supBounds (labels j).site (labels j).support f (w j)
  hits : Ac.Hit (fun i => (labels i).support) P.B w t E

abbrev hitFare (M : ℕ) := Footprint.payment 1 (4*M+2) 0 1 1 1 0 0


include σ hs I hg hq h ht hA hP hu hC hh hE hτ hδ

end YM.PhysicalNext.JointLoad.Psalm.Solo
