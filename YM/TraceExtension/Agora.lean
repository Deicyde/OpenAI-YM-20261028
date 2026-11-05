import YM.TraceExtension.Belfry
import YM.TraceExtension.Sundial.Grand
import YM.TraceExtension.Sundial.Hours
import YM.TraceExtension.Sundial.ScalePos
import YM.TraceExtension.Wick.Palette
import YM.TraceExtension.Fock.Occult

/-! Lower-level assembly (see `Endpoint` for public surface). -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 MeasureTheory Measure Maxwell UVNext.FreeStress Spin
open Spec Over Terrace Pilot Pith Sundial Verse TraceExtension TraceExtension.Wick
open Analysis Mink OS Spec MergeProof Boundary
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F: Final C X S) (h:G.Simple)
structure Zenith(P: ℝ→change S 4)(H:(Bel C.book).Hierarchy)(Z:Arch C) : Prop where
    centered : ∃ (d κ e:ℝ→ℝ), TendC F P d ∧
       (∀ᶠ r in Pilot.trail, Pith.Measures F r (P r) (κ r) (d r) (e r))∧Tendsto κ Pilot.trail (𝓝 1)∧
       Through (wilson Z) d (![0,d2 G]:Pilot.Jet) ∧ ∀ (χ:E4→ℝ), Window sail χ →
         LiveP P κ d χ∧ Easel.Verified (limitE C χ) P χ (wilson Z)∧ Easel.System (limitE C χ) 1 (![0,d2 G]:Pilot.Jet)∧∀ a d,Easel.System (limitE C χ) a d → a=1 ∧ (4:ℝ) • d.toSigned= ![0,0,-2*b0 G,0]
    zenith (φ:E4→ℝ)(he:Window sail φ) : ∃ (P':ℝ→change S 4)(x y:ℝ→ℝ), Posed H h P P' x y∧ ShellNorm P' φ
    moves (φ:E4→ℝ)(P':ℝ→change S 4)(x y:ℝ→ℝ) : Posed H h P P' x y→ShellNorm P' φ → Another F (H:=H) P' P ∧
          (∀ m:ℕ, ∀ᶠ r in Pilot.trail, chores r (P' r) m) ∧
          Tendsto (fun i=> glo P' i / wilson Z i) Pilot.trail (𝓝 1)∧ Coupling G (glo P') ∧ ∃ a d e:ℝ→ℝ,TendC F P' d ∧ Tendsto a Pilot.trail (𝓝 1)∧ (∀ᶠ i in Pilot.trail, Pith.Measures F i (P' i) (a i) (d i) (e i)) ∧
          (fun i=> d i-d2 G * (glo P' i)^(2:ℕ)) =O[Pilot.trail] fun i=> glo P' i^ (4:ℕ)
lemma sign_d (G:Gauge): (4:ℝ) • Pilot.Jet.toSigned (![0,d2 G])= ![0,0,-2*b0 G,0]:=by ext i;fin_cases i<;> simp [force_b G,Pilot.Jet.toSigned];ring
lemma zenithReady(H:(Bel C.book).Hierarchy)(Z:Arch C)(l:Ultrafilter (ℕ×ℕ))(u:Bliss F l Z H)(P:ℝ→change S 4)(p:PlotX F H l h P)(hc:∀ m:ℕ,∀ᶠ r in Pilot.trail, chores r (P r) m): Zenith F h P H Z:=by
    obtain ⟨d,hD⟩:= margaret F h u _ p
    have hg:= wilson_link F h u.budgets u.keen u.lies
    obtain ⟨κ,e,hE,hK,hX,hS⟩:= formed H F h hg hD p hc
    refine ⟨⟨d,κ,e,hD,hE,hK,hX,?_⟩, fun φ he=>spectrum_s F H h u p hc he,?_⟩
    · intro v hv; refine ⟨(hS v hv).1,(hS v hv).2,limit_sol _,fun a s hs=>?_⟩
      obtain ⟨h₁,h₂⟩:= normalized_sol H h _ _ _ hs;exact ⟨h₁,h₂ ▸ sign_d _⟩
    intro v P' x y hx hv
    obtain ⟨-,hG,hA⟩:= glow F H h u p hc hx hv hg
    exact ⟨avatar F H h u p hc hv.valid hx hv,(meadow F H h u p hc hx hv).1,hG,hA,meterQ F H h u p hc hx hv hg⟩

structure Lantern (H:(Bel C.book).Hierarchy)(Z:Arch C)(l:Ultrafilter (ℕ×ℕ)) : Prop where
    past : Bliss F l Z H
    slope : Coupling G (wilson Z)
    height : ∃ P: ℝ→change S 4, PlotX F H l h P ∧∀ m:ℕ,∀ᶠ r in Pilot.trail, chores r (P r) m
    sees (P:ℝ→change S 4): PlotX F H l h P→ (∀ m:ℕ,∀ᶠ r in Pilot.trail, chores r (P r) m) → Zenith F h P H Z
    leading (P:ℝ→change S 4): Month (𝓛:=l) F H P → ∃ d:ℝ→ℝ,(∀ᶠ i in Pilot.trail,∃ a e,Pith.Measures F i (P i) a (d i) e)∧∀ g:ℝ→ℝ,Coupling G g→Through g d (![0,d2 G]:Pilot.Jet)

structure Starry(μ:Measure E4):(Prop) where
    measure : TraceSpectrum F μ
    leader : 0 ≤ award G
    compact (φ:E4→ℂ)(hc : Continuous φ)(he: HasCompactSupport φ):
        (∀ r:ℝ,0 < r→ Integrable (fun p:E4=>φ (r⁻¹ • p)) μ) ∧ IntegrableOn (fun p:E4=>m p^ (2:ℕ) • φ p) cone volume∧
        Tendsto (fun r=> Zlog r • ∫ p:E4,φ (r⁻¹ • p)∂μ) atTop (𝓝 ((award G/(1536*Real.pi)) • ∫ p:E4 in cone,m p^ (2:ℕ) • φ p))
    schwartz (φ:Probe E4): (∀ r:ℝ,0< r→Integrable (fun p:E4=> φ (r⁻¹ • p)) μ)∧ IntegrableOn (fun p:E4=>m p^ (2:ℕ) • φ p) cone volume∧ Tendsto (fun r=> Zlog r • ∫ p:E4,φ (r⁻¹ • p)∂μ) atTop (𝓝 ((award G/(1536*Real.pi)) • ∫ p:E4 in cone,m p^ (2:ℕ) • φ p))
    relative (φ:Probe E4):
        letI := measure.upper
        letI := cone_temperate leader
        Tendsto (fun r=> Zlog r • TraceExtension.relative μ (condense r φ)) atTop (𝓝 (TraceExtension.relative (coneMeasure (award G)) φ))
    wight (φ:Joint 2): Tendsto (fun r=> Zlog r • F.A.world.W 2 (pairV F.action.J (pinned F)) (condense r φ)) atTop (𝓝 (∫ p:E4,waveTest φ p ∂coneMeasure (award G)))

universe u
-- measure, coefficient and sharp asymptotics, nonfree at scope
structure Arena : Prop where
    crest : Crest F h
    trace_nonzero : pinned F ≠ 0
    stage : ∃ H Z l,Lantern F h H Z l
    strong : ∃! μ:Measure E4, Starry F μ
    exclude (Flavor:Type u)(P:Palette Flavor)(q w:PolyField Flavor): ¬ ∀ x y:Probe E4,HasCompactSupport ⇑(waveTest (productTest x y))→ F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest x y)=P.wicks q w (waveTest (productTest x y))
    projected (n:ℕ)(U:F.action.operators.H →ₗᵢ[ℂ] Photons.Ambient n)(r:ℝ): 0 < r → Photons.Comparison F U→ ¬ Photons.Regions r F U

lemma arenaT (he:Crest F h): Arena.{u} F h:=by
    have ht:= he.at_length; have hh:= award_pos h
    obtain ⟨l,Z,H,hg⟩:= bliss F he.optics
    obtain ⟨μ,hμ,-⟩:= traceSpectrum_exists F
    refine ⟨he,nonzero_strength F hh ht,⟨H,Z,l, hg, wilson_link F h hg.budgets hg.keen hg.lies, glenned F h hg, zenithReady F h H Z l hg, fun _ hw=> december_move F H h hg hw⟩,⟨μ,?_,fun y hy=> hy.measure.unique hμ⟩,fun _ _ _ _=> wick_excludes ht hh _ _ _, fun _ _ _ hr X=> Photons.regions_excludes hr hh ht X⟩
    refine ⟨hμ,hh.le,?_,fun p=> ⟨fun r hr=> amp_s _ hμ _ hr, cone_int_s p,spectral_limit hh.le hμ ht p⟩,relative_limit hh.le hμ ht,joint_limit hh.le hμ ht⟩; intro x hc hp; exact ⟨fun r hr=> amp_compact hc hp hμ r hr,cone_int_c hc hp,compact_limit hh.le hμ ht _ hc hp⟩

lemma agora (b:ℝ) (hb:0<b)(f:Extraction.Order) : ∀ h:G.Simple, ∃ (C:Family G), C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ ∃ (g:Extraction.Order) (S:Table C.book), Nonempty (Spec.Final C (f.refine g) S) ∧ ∀ (S:Table C.book)(F:Spec.Final C (f.refine g) S), Arena.{u} F h:=by
    intro h; obtain ⟨C,hC,hK,hB,hW,g,S,-,-,hF,hs⟩:= MergeProof.Acme.northBay h b hb f; exact ⟨C,hC,hK,hB,hW,g,S,hs,fun S F=> arenaT _ _ (crest_ready F h hF)⟩
end YM.Trace
#print axioms YM.Trace.agora
