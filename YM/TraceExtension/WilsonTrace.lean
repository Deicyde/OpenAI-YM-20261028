import YM.TraceExtension.Centered
import YM.Next.BOUNDARY.Stage

/-! Assemble on the constructed Final. Pin to actual covariance, fields and
vacuum throughout. In `euclidean` argument is relative positive distance
on the time axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral Table
open scoped Topology Matrix.Norms.Frobenius NNReal ENNReal BigOperators InnerProductSpace

section continuation
variable {G : Gauge} {L : Register G} {S T : Table L}

lemma vev_boundary (X : Boundary.Wightman S) {R : Rotation S} {rs : S.RealSpin}
    (H : T.Hierarchy) (hs : T.respects S) {A : Contour S} (hw : A.From T)
    (hr : X.Realizes (W := A.world) R rs) {d : ℕ} (v : S.Field d) (f : Probe E4) :
    inner ℂ X.operators.vacuum (excitation X.operators (S.pin d (centerIn S T v)) f) = 0 := by
    let b := centerIn S T v
    let w : Fin 1 → S.Union := fun _ => S.pin d b
    have ht : euclideanVEV S T b = 0 := centerIn_vac hs H v
    have he (x : SpacePoints 1) : EqOn (fun z => A.waves.F 1 z x w) 0 (strict 1) := by
        apply Next.BOUNDARY.ordered_eq _ _ (hw.heat.hol _ _ _)
          (show DifferentiableOn ℂ (fun _ : Times 1 => (0:ℂ)) _ from differentiableOn_const _)
        intro y hy
        let Z : Fin 1 → S.Tag := fun _ => ⟨d,b⟩
        exact (hw.heat.roots 1 Z x y hy).trans ((vev_coordinates H.translations ..).trans ht)
    let s := [(S.pin d b,f)]
    change inner ℂ _ (X.operators.vector s)=_
    rw [hr.meets]; unfold Surface.expect
    let q : Fin 1 → Probe E4 := fun i => (s.get i).2; let t := Joint.materialize 1 q
    change A.world.W 1 (fun i => (s.get i).1) t=_
    rw [show (fun i : Fin 1 => (s.get i).1)=w by funext i; rw [Subsingleton.elim i 0]; rfl]
    have hh : (0:Heights 1) ∈ east 1 := fun i j hj => False.elim (ne_of_lt hj (Subsingleton.elim i j))
    refine tendsto_nhds_unique (hw.emerges.profile 1 w _ hh t) (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    unfold Waves.atSlopes
    have hz (x : Points 1) : A.waves.restricted w (ε • 0) x=0 :=
        he (trace x) (on_profile x _ ε hε hh)
    simp only [hz,zero_mul,integral_zero]
end continuation

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C f S)

abbrev selected := F.α.ensemble F.α.atPoint
def center := theta (selected F) F.sector.energy
def pinned := S.pin 4 (center F)

def opposed (r : ℝ) : Points 2 := place (0:SpacePoints 2) (pairH (r/2))
/-- Euclidean two-point at positive separation. Translation-normalized stress in F. -/
def euclidean (r : ℝ) := S.useAt (selected F) (opposed r) fun _ => ⟨4,center F⟩

lemma selected_respects : (selected F).respects S := fun d => (F.phase.phase.retains _ d).symm.le
lemma selected_hierarchy : (selected F).Hierarchy := F.phase.phase.states _

lemma self_adjoint : F.action.J (pinned F) = pinned F := by
    rw [pinned, F.realization.qt.induced]; rw [center,trace_adj F.phase.transport.conserved F.phase.transport.spin F.phase.transport.spots (selected_respects F) (selected_hierarchy F)]

lemma pinned_scalar (g : Lorentz) : F.action.spin.rail g (pinned F)=pinned F :=
    scalar_rail F.realization.qt.letters F.phase.transport.spots
      (trace_turn F.phase.transport.spin F.phase.transport.spots) g

lemma pinned_centered (φ : Probe E4) : inner ℂ F.action.operators.vacuum
    (excitation F.action.operators (pinned F) φ) = 0 :=
    vev_boundary F.action (selected_hierarchy F) (selected_respects F) F.realization.chosen F.realization.qt _ φ

lemma continuation {s : ℝ≥0} (h : 0<s) : euclidean F (2*(s:ℝ))=
    F.A.waves.restricted (pairV F.action.J (pinned F)) (pairH s) 0 := by
    let z : S.Tag := ⟨4,center F⟩
    have he := F.realization.chosen.heat.roots 2 (fun _ => z) 0 (pairH s) (east_pairH h)
    have hp : trace (0:Points 2)=0 := by funext i; simp [trace]
    have ht : pairV F.action.J (pinned F)=fun _ => pinned F := by funext i; fin_cases i <;> simp [self_adjoint]
    rw [ht]; unfold euclidean opposed Waves.restricted
    rw [show (2*(s:ℝ))/2 = s by ring,hp,show shift (0:Points 2) (pairH s)=(fun i => (↑(pairH s i):ℂ)*I) by
        funext i; simp [shift]]
    exact he.symm

/-- The spectral measure properties with the fixed convention; `core` pins
the normalization on field wave tests. `absolute` compares with W as a
tempered distribution, not only as an off-diagonal kernel. -/
structure TraceSpectrum (μ : Measure E4) : Prop where
    upper : μ.HasTemperateGrowth
    slab : ∃ (A : ℝ) (k : ℕ), 0 ≤ A ∧ energyBudget μ A k
    localcone : μ coneᶜ=0
    boost (g : Lorentz) : μ.map g.act=μ
    damped_mass (s : ℝ) (h : 0<s) : IsFiniteMeasure (OS.Semigroup.transform timeAxis s μ)
    laplace (s : ℝ) (h : 0<s) : euclidean F s = (((OS.Semigroup.transform timeAxis s μ).real univ:ℝ):ℂ)
    core (φ : Probe E4) : F.action.momentum.diagonal (excitation F.action.operators (pinned F) φ) =
        μ.withDensity fun p => (probeWeight φ p : ℝ≥0∞)
    norm (φ ψ : Probe E4) : inner ℂ (excitation F.action.operators (pinned F) φ) (excitation F.action.operators (pinned F) ψ) =
        ∫ p, star (testPlus φ p)*testPlus ψ p ∂μ
    absolute (φ : Joint 2) : F.A.world.W 2 (pairV F.action.J (pinned F)) φ = ∫ p, waveTest φ p ∂μ

lemma TraceSpectrum.unique {F : Spec.Final C f S} {μ ν : Measure E4} (h : TraceSpectrum F μ) (hp : TraceSpectrum F ν) : μ=ν :=
    weights_injective μ ν fun φ => (h.core φ).symm.trans (hp.core φ)

lemma traceSpectrum_exists : ∃! μ, TraceSpectrum F μ := by
    let P := F.realization.qt
    obtain ⟨Y,hY,h⟩ := ((Next.BOUNDARY.both (s:=F.room) F.phase P.letters F.realization.allWorld F.realization.chosen).2).reveals
    have he := (h F.action.J P.induced).2
    rw [hY] at he
    let v := pinned F
    let B := Y.bits
    let μ := spectralMeasure B v
    have hm : F.A.waves.Breathes := by rw [← hY]; exact Y.power.1
    have ht (s : ℝ) (hp : 0<s) : ∃ k:ℝ≥0, 0<k ∧ 2*(k:ℝ)=s :=
        ⟨⟨s/2,by positivity⟩,half_pos hp,by change 2*(s/2)=s; ring⟩
    have hμ : TraceSpectrum F μ := by
        refine ⟨spectral_temperate he hm _, energy_bounded he hm _, spectral_forward he hm F.realization.chosen.emerges P _, fun g => ?_, fun s hs=> ?_, fun s hs => ?_,
            mass_read he hm F.realization.chosen.emerges P _, norm_read he hm F.realization.chosen.emerges P _, surface_integral he hm F.realization.chosen.emerges _⟩
        · have hh := spectral_placed he hm F.realization.chosen.emerges P v g.dual
          unfold v at hh; rw [pinned_scalar,Lorentz.dual_involution] at hh; exact hh.symm
        · obtain ⟨k,hk,rfl⟩ := ht s hs
          unfold μ B; rw [damp he _ k hk]; infer_instance
        obtain ⟨k,hk,rfl⟩ := ht s hs
        unfold μ B; rw [continuation F hk,pair_restricted he _ k hk,damp he _ k hk]; simp [v]
    exact ⟨μ,hμ,fun ν h => h.unique hμ⟩
end YM.TraceExtension
