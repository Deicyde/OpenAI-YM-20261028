import YM.FullVolume.Profiles
import YM.Independent.Core
import YM.OPE.Nesting.Endpoint
import YM.Contacts.Solstice.Result
import YM.Pert.Position.Four

/-! Public mathematical specification checked against the Wilson construction.
The family precedes the extraction order. Every conclusion inside a refinement
refers to its one table, reconstruction, choice of fields and reader. -/
set_option autoImplicit false
noncomputable section
namespace YM.Nonperturbative.Headline

open Function Set Filter Metric MeasureTheory Spec Boundary Mink TraceExtension
open TraceExtension.Photons OPE OPE.Orbits
open scoped Topology BigOperators InnerProductSpace

universe u v
variable {G : Gauge} {C : Family G} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- The single-center expansion for each fixed grade, on the unselected table
and in every character. The same coefficients serve every grade and spectator. -/
structure SeparatedOPE : Prop where
  coefficient (I : Type) [Fintype I] (d : I → ℕ) (a : Labels S d) (M η ε : ℝ) :
    0 ≤ M → 0 < η → 0 < ε → ∀ (j : ℕ) (i : Q.channels j), ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (x : I → E4) (o : E4), WithinRoom r M η x o →
        ‖Q.coef j i x a o‖ ≤ r ^ ((j : ℝ) - weight d - ε)
  remainder {I J : Type} [Fintype I] [Fintype J] {d : I → ℕ} {e : J → ℕ}
      (a : Labels S d) (b : Labels S e) {M η c ε : ℝ}
      (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) (D : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4) (y : J → E4),
      WithinRoom r M η x o → ClearOf o y c → ∀ s : Viewers F,
      ‖whole (spectator F s) x a y b -
        ∑ j : Fin (D + 1), ∑ i : Q.channels j.val, Q.coef j.val i x a o *
          whole (spectator F s) (sole o)
            (sole (Q.actor j.val i) : Labels S (fun _ : Unit => j.val)) y b‖
        ≤ r ^ ((D : ℝ) + 1 - weight d - ε)

  profiles (I J : Type) [Fintype I] [Fintype J] (d : I → ℕ) (e : J → ℕ)
      (a : Labels S d) (b : Labels S e) (M η c ε : ℝ) :
    0 ≤ M → 0 < η → 0 < c → 0 < ε → ∀ (D : ℕ) (K : Type) [MeasurableSpace K] (B : ℝ),
      ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (μ : Measure K) (w : K → ℂ) (z : K → Loc I J),
        AEMeasurable z μ → Integrable w μ → (∫ i, ‖w i‖ ∂μ) ≤ B →
        (∀ᵐ i ∂μ, w i ≠ 0 → z i ∈ FitsOn I J M η c r) →
        (∀ χ : K → F.α.space.X, AEMeasurable χ μ →
          JointEstimate F Q D a b (B * r ^ ((D : ℝ) + 1 - weight d - ε)) μ w z (some ∘ χ)) ∧
        JointEstimate F Q D a b (B * r ^ ((D : ℝ) + 1 - weight d - ε)) μ w z (fun _ => none)

/-- Hilbert-space and distributional requirements for one phase of the table.
The representation acts on the same Hilbert space as the fields and momentum. -/
structure WightmanAxioms (A : Wightman S) (W : Surface S) : Prop where
  norm : ‖A.operators.vacuum‖ = 1
  dense : Dense (A.operators.domain : Set A.operators.H)
  cyclic : A.operators.domain = Submodule.span ℂ (Set.range A.operators.vector)
  tempered (x : S.Union) (v : A.operators.domain) :
    Continuous (fun f => (A.operators.field x f v).val)
  adjoints (x : S.Union) (f : Test4) (v w : A.operators.domain) :
    inner ℂ (A.operators.field x f v).val w.val =
      inner ℂ v.val (A.operators.field (A.J x) (Probe.bar f) w).val
  moments (b : Sentence S) : inner ℂ A.operators.vacuum (A.operators.vector b) = W.expect b
  positive : W.wordsPositive A.J
  localFields (x y : S.Union) (f g : Test4) (spacelike : Fields.causal f g)
      (v : A.operators.domain) :
    A.operators.field x f (A.operators.field y g v) = A.operators.field y g (A.operators.field x f v)
  symmetries : Symmetries A.spin A.action
  strong (v : A.operators.H) : Continuous (fun g => A.action.V g v)
  spectral : A.action.orbit.Spectrum A.momentum
  forward : A.momentum.region Mink.coneᶜ = 0
  unique (v : A.operators.H) : (∀ x, A.action.orbit.translation x v = v) →
    ∃ z : ℂ, z • A.operators.vacuum = v

/-- The selected phase and all characters are reconstructed from this table.
Integrating the character correlations recovers the unselected boundary distributions. -/
structure Reconstruction (L : EveryPhase.Almanac F) : Prop where
  unselected : F.B.From S
  selected : F.A.From (F.α.ensemble F.α.atPoint)
  chosen : WightmanAxioms F.action F.A.world
  characters (i : F.α.space.X) : WightmanAxioms (L.actors i) (L.contours i).world
  average (n : ℕ) (v : Fin n → S.Union) (g : Joint n) :
    (∫ i, (L.contours i).world.W n v g ∂F.α.space.μ) = F.B.world.W n v g

/-- Tests of the physical centered trace in the selected reconstruction. -/
structure TraceExclusions : Prop where
  centered (f : Test4) :
    inner ℂ F.action.operators.vacuum (excitation F.action.operators (pinned F) f) = 0
  identified (f : Test4) :
    F.action.operators.field (pinned F) f =
      F.action.operators.field (S.pin 4 (stressTrace F.sector.energy)) f -
        (euclideanVEV S (selected F) (stressTrace F.sector.energy) * ∫ x, f x) •
          LinearMap.id (R := ℂ)
  shortDistance :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) • euclidean F s)
      (𝓝[>] 0) (𝓝 (Trace.Verse.award G : ℂ))
  positive : 0 < Trace.Verse.award G
  wick (Color : Type u) (palette : Wick.Palette Color) (left right : Wick.PolyField Color) :
    ∃ x y : Probe E4, HasCompactSupport ⇑(waveTest (productTest x y)) ∧
      F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest x y) ≠
        palette.wicks left right (waveTest (productTest x y))
  maxwell (n : ℕ) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient n)
      (physical : ∀ w, PhysicalWave (U w)) (unit : U F.action.operators.vacuum = vacuum n)
      (translations : ∀ w (b : E4), ∀ᵐ x ∂sumMeasure n,
        U (F.action.action.orbit.translation b w) x = Probe.plane (forward x) b * U w x) :
    ∃ (f : Test4) (h : TestList n), HasCompactSupport ⇑f ∧
      (∀ i, HasCompactSupport ⇑(h i)) ∧ (∀ i, Probe.bar (h i) = h i) ∧
      (∀ i, Fields.causal f (h i)) ∧ inner ℂ (coherent (-h)) (signal F U f) ≠
        inner ℂ (signal F U (Probe.bar f)) (coherent h)
  invariant (n : ℕ) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient n)
      (hU : Comparison F U) (I : Type v) [MeasurableSpace I]
      (μ : Measure I) [IsProbabilityMeasure μ] (P : I → Ambient n → Ambient n)
      (preserves : ∀ z x y, PhysicalWave x → PhysicalWave y →
        inner ℂ (P z x) (P z y) = inner ℂ x y) (fixes : ∀ z x, P z (U x) = U x)
      (r : ℝ) (hr : 0 < r) :
    ∃ (A B : Set E4), IsOpen A ∧ IsOpen B ∧ closure A ⊆ ball 0 r ∧
      (∀ x ∈ closure A, ∀ y ∈ closure B, x-y ∈ spacelike) ∧
      ∃ (f : Test4) (h : TestList n), tsupport f ⊆ A ∧ HasCompactSupport ⇑f ∧
        (∀ i, tsupport (h i) ⊆ B) ∧ (∀ i, HasCompactSupport ⇑(h i)) ∧
        (∀ i, Probe.bar (h i) = h i) ∧
        (∫ z, inner ℂ (P z (coherent (-h))) (signal F U f) ∂μ) ≠
          ∫ z, inner ℂ (signal F U (Probe.bar f)) (P z (coherent h)) ∂μ

section trees
open OPE.Nesting OPE.Orbits.Reader OPE.Nesting.Measures OPE.Nesting.Menu OPE.Nesting.Atom Function Table
open OPE.Nesting.Tree
variable (U : Final C p S) (R : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)

/-- Estimates over admissible finite trees, with truncations and rates at their nodes. -/
structure NestedOPE : Prop where
    direct(n:ℕ)(f:Fin n→Tree)(v:(fork n f).Leaf→S.Tag)(m:ℕ)(c:R.channels m)(D:(fork n f).Inner→ℕ)(M η ε:ℝ)(_ :0≤M)(_ :0<η)(_ :0<ε):
      ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:(fork n f|>.Plot)), Accept r M η s z → orbitMargin R.port m (Tree.profile z) (anchor z) ∧ z∈Kernel.aperture U R (fork n f) m D ∧ ‖Kernel.output U R z v c‖ ≤ toll (wages v) ε m s ∧ ‖Kernel.output U R z v c - Kernel.chord U R z v c D‖ ≤ bothToll (wages v) ε m D s
    tested(n:ℕ)(f:Fin n→Tree)(J:Type)[Fintype J](v:(fork n f).Leaf→S.Tag) (w:J→S.Tag)(m:ℕ)(M η ε δ:ℝ)(_ :0≤M)(_ :0<η)(_ :0<ε)(_ :0<δ):
      ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:(fork n f).Plot) (y:J→E4),Accept r M η s z → Buffer z y δ→
    Kernel.cardPanel z y ∈ Orbits.guardZone U R m ∧ ‖Kernel.normData U R z v m y w‖ ≤ toll (wages v) ε (m+1:ℝ) s ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q m y w‖ ≤ toll (wages v) ε (m+1:ℝ) s
    joint(n:ℕ)(p:Fin n→Tree)(v:(fork n p).Leaf→S.Tag)(m:ℕ)(c:R.channels m)(D:(fork n p).Inner→ℕ)(M η ε:ℝ)(_ :0≤M)(_ :0<η)(_ :0<ε)(K:Type)[MeasurableSpace K]:
      ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (s:(fork n p|>.Inner)→ℝ),Tapered _ r 1 s → ∀ (μ:Measure K)(B:ℝ)(q:K→ℂ)(z:Envelope K (fork n p)), Integrable q μ→ (∫ i, ‖q i‖ ∂μ) ≤ B→ AEMeasurable z μ→ (∀ᵐ i ∂μ, q i≠0→Accept r M η s (z i)) → CoefIntegral U R v m c D B ε s z q μ
    jointLaw(n:ℕ)(f:Fin n→Tree)(J:Type)[Fintype J](v:(fork n f).Leaf→S.Tag) (w:J→S.Tag)(m:ℕ)(M η ε δ:ℝ)(_ :0≤M)(_ :0<η)(_ :0<ε)(_ :0<δ)(K:Type)[MeasurableSpace K]:
      ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:((fork n f).Inner→ℝ))(μ:Measure K)(B:ℝ)(u:K→ℂ), Tapered (fork n f) r 1 s → Integrable u μ → (∫ i, ‖u i‖ ∂μ) ≤ B → ∀ (z:Tree.Envelope K (fork n f))(y:K→J→E4), AEMeasurable z μ→ AEMeasurable y μ → (∀ᵐ i ∂μ,u i≠0→Accept r M η s (z i) ∧ Buffer (z i) (y i) δ) →
      let estimate:=JointEstimate U R m (voices v) (voices w) (B*(Tree.toll (wages v) ε (m+1:ℝ) s)) μ u (TestedProfile (fork n f) z y); (∀ t:K→U.α.space.X, AEMeasurable t μ → estimate (.some ∘ t)) ∧ estimate (fun _=>none)
end trees

/-- A single Wilson existence claim, including reconstruction, OPE, trace
countertests, contact extensions and the leading position comparison. -/
def WilsonExistence (G : Gauge) (hG : G.Simple) (b : ℝ) : Prop :=
  ∃ C : Family G, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
    ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
      (F : Final C (p.refine q) S) (L : EveryPhase.Almanac F)
      (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (M : Contacts.Devices F.sector.derivatives) (X : Climb.Scaling S),
      (Extraction.Order.mk Extraction.Sequence.full (p.refine q).per).Ordered C S ∧
      FullVolume.PositionsUV C Extraction.Sequence.full ∧
      Spec.Calibrated C ∧ Independent.Core.{u,v} hG F L Q ∧ Reconstruction F L ∧
      SeparatedOPE F Q ∧ NestedOPE F Q ∧
      TraceExclusions.{u,v} F ∧ M.basis = Q.port ∧ Contacts.Solstice.MultipleLight F M ∧
      Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Contacts.Solstice.Thresholds M) ∧
      Pert.FirstExtension F X ∧ Pert.Position.FourMeters F X

end YM.Nonperturbative.Headline
