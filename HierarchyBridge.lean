import ChallengeSpec
import PublicView
import WilsonBridge
import YM.Nonperturbative.HeadlineSpec
import YM.Pert.Asymptotics.RawAxis

set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
open Function Set MeasureTheory Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius NNReal
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem regular (C : Family g.core) (hg : g.IsSimple) (h : C.Makes) : WilsonRegularity (wilsonFamily C) := by
  refine ⟨?_,fun N p v x => C.continuousO N p v.1 v.2 x, fun N p v x => C.invariant h N p v.1 v.2 x, ?_⟩
  · refine ⟨2*Pert.Asymptotics.b0 g.core, ?_, fun ε hε => ?_⟩
    · have hc := YM.Gauge.casimir_pos (GaugeGroup.coreSimple hg)
      unfold Pert.Asymptotics.b0
      positivity
    · filter_upwards [Pert.Asymptotics.zeroUp_bound C h hε] with N hN
      exact fun p => hN N p le_rfl
  intro v
  exact ⟨(C.localSection v.1).stencil,fun N p x => C.localO N p v.1 v.2 x⟩

def hierarchy : Hierarchy (wilsonFamily C) where
  H := stateSpace F.action
  labels := labelsOf S
  theory := view F.action
  Field := S.Field
  toLabel := S.pin
  project := S.classTokens
  Character := F.α.space.X
  phaseMeasure := F.α.space.μ
  selected := F.α.atPoint
  correlation s v x := S.useAt (spectator F s) x v
  continuation v z x := F.A.waves.F _ z x (fun i => S.pin (v i).1 (v i).2)
  Channel := Q.channels
  actor := Q.actor
  coefficient a j i x := Q.coef j i x (fun k => (a k).2)
  centeredTrace := TraceExtension.center F

theorem wilsonLimit {s : Extraction.Sequence} (h : (Extraction.Order.mk .full s).Ordered C S) :
    (wilsonFamily C).Converges s (fun v => (hierarchy F Q).correlation none ((hierarchy F Q).project ∘ v)) := by
  intro n v t
  obtain ⟨hv,row,hr,hl⟩ := fromWilson C h n v t
  refine ⟨hv,row,hr,?_⟩
  convert hl using 2
  congr 1
  funext x
  change t x * S.useAt S x (S.classTokens ∘ v) = t x * S.read x v
  by_cases hx : x ∈ conf n
  · rw [S.at_project S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) hx]
  · have hz : t x = 0 := notMem_support.mp (fun h => hx (t.tsupport_subset (subset_closure h)))
    simp [hz]

private theorem grouped_eq {I J : Type} [Fintype I] [Fintype J] (s : Viewers F)
    (a : I → S.Tag) (x : I → E4) (b : J → S.Tag) (y : J → E4) :
    (hierarchy F Q).grouped s a x b y =
      whole (spectator F s) x (fun i => (a i).2) y (fun j => (b j).2) := by
  apply congrArg (S.useAt (spectator F s) _)
  funext k
  change (Sum.elim a b) (YM.OPE.runNames (I ⊕ J) k) = _
  generalize YM.OPE.runNames (I ⊕ J) k = e
  cases e <;> rfl

theorem publicOPE (h : Headline.SeparatedOPE F Q) : (hierarchy F Q).OperatorProductExpansion := by
  constructor
  · intro I _ a M η ε hM hη hε j i
    filter_upwards [h.coefficient I (fun k => (a k).1) (fun k => (a k).2) M η ε hM hη hε j i] with r hr
    exact fun x o hx => hr x o ⟨hx.1,hx.2⟩
  · intro I J _ _ a b M η c ε hM hη hc hε D
    filter_upwards [h.remainder (fun k => (a k).2) (fun k => (b k).2) hM hη hc hε D] with r hr
    intro x o y hx hy s
    simp_rw [grouped_eq]
    exact hr x o y ⟨hx.1,hx.2⟩ ⟨hy.1,hy.2⟩ s

theorem publicReconstruction (L : EveryPhase.Almanac F) (h : EveryPhase.Completed F L) :
    (hierarchy F Q).Reconstructed := by
  refine ⟨view_axioms _ F.realization.qt, F.realization.qt.faithful, S.pin_inj, ?_, ?_, ?_,
    F.phase.phase.decomposition.normalized, F.phase.phase.decomposition.support,
    fun s _ a x hx π => S.class_perm _ (spectate F s).laws.toSymmetric π hx a,
    fun s _ a => S.class_smooth _ (spectate F s).smooth a, ?_, ?_, ?_, ?_, ?_⟩
  · let a : S.Tag := ⟨0,S.unit 0⟩
    have ne : S.pin 0 (S.unit 0) ≠ 0 := fun e => S.alive 0 F.room.kernel.laws ((S.pin_inj 0) (e.trans (map_zero _).symm))
    obtain ⟨f,hf⟩ := F.realization.qt.faithful _ ne
    exact ⟨a,f,hf⟩
  · intro u
    obtain ⟨d,v,e⟩ := F.sector.derivatives.covered F.room.kernel.laws.toSymmetric F.phase.transport.injection u
    exact ⟨⟨d,v⟩,e⟩
  · intro a
    refine ⟨⟨a.1,S.representative _ a.2⟩,?_⟩
    change Sigma.mk a.1 (S.project _ (S.representative _ a.2)) = a
    rw [S.rep]
  · intro n a x hx
    let w := Word.realize (fun i => quoteTag (a i)) x
    have hd : Word.distinct w := (Word.realized ..).mpr hx
    obtain ⟨z,d,hs⟩ := OS.Spread.Resolution.place_exists hd
    have he i : (hierarchy F Q).correlation (some i) a x = (F.α.ensemble i).expect w := by
      rw [show w = Word.realize (fun i => quoteTag (a i)) x from rfl, Table.readAt]
      rfl
    simp_rw [he, fun i => F.phase.phase.chosen i w hd z d hs]
    exact F.phase.phase.decomposition.weak _
  · intro n a x hx
    let w := Word.realize (fun i => quoteTag (a i)) x
    have hd : Word.distinct w := (Word.realized ..).mpr hx
    have he i : (hierarchy F Q).correlation (some i) a x = (F.α.ensemble i).expect w := by
      rw [show w = Word.realize (fun i => quoteTag (a i)) x from rfl, Table.readAt]
      rfl
    simp_rw [he]
    exact (h.at_words w hd).trans (S.readAt _ _)
  · intro n v x
    exact F.realization.chosen.heat.hol n _ x
  · intro n a x h
    have eqx : YM.Boundary.place (Hierarchy.spatialPoints x) (fun i => time (x i)) = x := by
      apply PiLp.ext
      intro i
      exact YM.position_eta (x i)
    have root := F.realization.chosen.heat.roots n a (Hierarchy.spatialPoints x) (fun i => time (x i)) h
    rw [eqx] at root
    exact root
  · intro n a h hh tests
    have edge := F.realization.chosen.emerges.profile n
      (fun i => S.pin (a i).1 (a i).2) h hh (YM.Boundary.Joint.materialize n tests)
    change Tendsto _ _ (𝓝 ((view F.action).fields.vacuumExpectation _ tests))
    rw [publicMoment _ F.realization.qt.meets]
    have eqShift (r : ℝ) (x : Points n) : Hierarchy.complexShift r h x = YM.Boundary.shift x (r • h) := by
      funext i; simp [Hierarchy.complexShift,YM.Boundary.shift,Pi.smul_apply,YangMills.time,YM.time]
    have eqSpace (x : Points n) : Hierarchy.spatialPoints x = YM.Boundary.trace x := rfl
    simp only [hierarchy, Hierarchy.tensorTest, eqShift, eqSpace,
      YM.Boundary.Waves.atSlopes, YM.Boundary.Waves.restricted, YM.Boundary.Joint.material_at] at edge ⊢
    exact edge
end YangMills
