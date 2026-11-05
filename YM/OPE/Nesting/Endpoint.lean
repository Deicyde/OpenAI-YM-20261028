import YM.OPE.Nesting.Motions

/-!
# Finite nested operator products
`Uniform` controls a tree of shrinking clusters with a fixed outer grade and specified intermediate grades. `Accept` describes the separation and scale conditions. `Kernel.output` is the direct coefficient and `Kernel.chord` sums over intermediate channels. The difference is bounded by `bothToll`. The weighted estimates also allow the test geometry and character to vary.
`rooted` supplies a single Wilson hierarchy and reader for the ordinary and nested expansions. The estimates take the short-distance limit with the grades fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Tree
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)

structure Uniform : Prop where
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

variable (h:Services C F S)
include h
lemma uniform : Uniform U R :=by
    constructor
    · intro n f v m c D M η ε hM hη hε; exact Limits.coe_power U R h hM hη hε v m c D
    · intro n f J h_J v w m M η ε δ hM hη hε hδ; exact Limits.tested_power U R h hM hη hδ hε v w m
    · intro n f v m c D M η ε hM hη hε K hK; exact coefficient_joint U R h hM hη hε v m c D
    intro n f J h_J v w m M η ε δ hM hη hε hδ K hK; exact all_weighted U R h hM hη hε hδ v w m

omit h in
/-- Endpoint for all power-with-positive-loss claims. Existence and these
estimates on **one** fully calibrated final hierarchy + Reader. -/
theorem rooted (G:Gauge)(hG:G.Simple)(F:Extraction.Order) : ∃(C:Family G) (g:Extraction.Order) (S:Table C.book), Services C (F.refine g) S ∧ ∃ (U:Spec.Final C (F.refine g) S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin),Uniform U R ∧ Foundation U R := by
    obtain ⟨C,g,S,hC,U,R,hF⟩:=Orbits.foundation G hG F
    exact ⟨C,g,S,hC,U,R, uniform U R hC,hF⟩
end YM.OPE.Nesting
