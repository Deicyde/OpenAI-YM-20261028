import YM.TraceExtension.Made.World
import YM.TraceExtension.Atlas.Last
import YM.TraceExtension.Atlas.Crash
import YM.TraceExtension.Verse.Cape
import YM.TraceExtension.Wick.Refute
import YM.TraceExtension.Fock.Conclude
set_option autoImplicit false
noncomputable section
namespace YM.Trace
open Set Function Filter MeasureTheory Analysis Measure Extraction Mink OS Spec MergeProof TraceExtension
open Ward Climb Cells Boundary Spin Over Verse
open Terrace Pilot
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {G : Gauge} {C : Family G}{p:Extraction.Order}{S:Table C.book}
-- current precision. Through first nonzero EVEN power looping, in formal parity convention through cap4 X. Parsed normalization.W
structure Crest (F:Spec.Final C p S)(h:G.Simple):Prop where
    optics : Gallery C p
    reward : d2 G= -b0 G/2 ∧ 0 < award G
    zero_alpha : ∀ v:Probe E4, inner ℂ F.action.operators.vacuum (excitation F.action.operators (pinned F) v)=0
    charts : ∀ (𝓛:Ultrafilter (ℕ×ℕ))(Z:Arch C)(H:(Bel C.book).Hierarchy), Bliss F 𝓛 Z H →
       Coupling G (wilson Z)∧(∃ P:ℝ→ change S 4, PlotX F H 𝓛 h P∧∀ m:ℕ, ∀ᶠ r in Pilot.trail, chores r (P r) m) ∧
       (∀ (P :ℝ→ change S 4), PlotX F H 𝓛 h P → ∃ d:ℝ→ ℝ,TendC F P d ∧ Through (wilson Z) d (![0,d2 G]:Pilot.Jet))
    at_length : EuclideanAsymptotic F (award G)
    spectrum : ∃ μ: Measure E4, TraceSpectrum F μ ∧
        (∀ φ:E4→ℂ, Continuous φ→ HasCompactSupport φ→
          Tendsto (fun r=> Zlog r • ∫ p: E4,φ (r⁻¹ • p)∂μ) atTop (𝓝 ((award G/(1536*Real.pi)) • ∫ p:E4 in cone,m p^ (2:ℕ) • φ p)))∧
        (∀ φ:Probe E4,Tendsto (fun r=> Zlog r • ∫ p:E4, φ (r⁻¹ • p)∂μ) atTop (𝓝 ((award G/(1536*Real.pi)) • ∫ p:E4 in cone,m p^ (2:ℕ) • φ p))) ∧
        (∀ φ:Joint 2,Tendsto (fun r=> Zlog r • F.A.world.W 2 (pairV F.action.J (pinned F)) (condense r φ)) atTop (𝓝 (∫ p:E4,waveTest φ p ∂coneMeasure (award G))))
    polynomial : ∀ W:TraceExtension.Wick.Collection, ¬ ∀ f g :Probe E4, HasCompactSupport ⇑(waveTest (productTest f g)) → F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest f g)= TraceExtension.Wick.tests W (waveTest (productTest f g))
    nfock : ∀ (n : ℕ) (U:F.action.operators.H →ₗᵢ[ℂ] Photons.Ambient n), Photons.Comparison F U →¬ Photons.Nfl F U
lemma crest_ready (F:Spec.Final C p S)(h:G.Simple)(hx:Gallery C p) : Crest F h:= by
   have he:= Verse.outside F h hx
   obtain ⟨μ,hμ,-⟩:= traceSpectrum_exists F
   have hh:= award_pos h
   refine ⟨hx,⟨force_b G,hh⟩,pinned_centered F,?_,he,⟨μ,hμ,compact_limit hh.le hμ he, spectral_limit hh.le hμ he,joint_limit hh.le hμ he⟩, Wick.polynomial_excludes he hh,fun _ _ A=> Photons.excludes hh he A⟩
   intro b Z H hp; have hv:= wilson_link F h hp.budgets hp.keen hp.lies
   refine ⟨hv, glenned F h hp,?_⟩; intro P hP; obtain ⟨d,hD⟩:= margaret F h hp _ hP; refine ⟨d,hD,?_⟩; change Tendsto (fun i=> (d i-0)/_) _ (𝓝 (d2 G)) ; simp only [sub_zero]; rw [force_b]; exact hD.measures _ hv
/-- Current assembly. depending Penalty choices. -/
lemma belfry(h:G.Simple)(x:ℝ) (hx:0<x)(p:Extraction.Order): ∃ (C:Family G) (g:Extraction.Order) (S:Table C.book) (F:Spec.Final C (p.refine g) S), C.path.levels.clock.kernel.penalty=x ∧ Crest F h:=by
   obtain ⟨C,-,-,hP,-,g,S,-,-,hL, ⟨F⟩⟩:=MergeProof.Acme.northBay h x hx p
   exact ⟨C,g,S,F,hP,crest_ready F h hL⟩
end YM.Trace
#print axioms YM.Trace.belfry
