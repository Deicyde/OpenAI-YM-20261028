import YM.Next.BOUNDARY.Heights
import YM.Work.C01
import YM.Work.C25



/-!
# Field cores consuming the same heat vectors

* `FieldCore` will be produced even for the *unselected* hierarchy; literally
Wightman.Realizes sans invariant-vector uniqueness. Reserve uniqueness for
with-Heat ports. Do not substitute this predicate at `Spec.Final`.
* Obtain an actual isometry between field and OS data (into, not claiming
onto). Its restrictions read the true word vectors as limits. Don't prepare
unique ground in a different chamber. Works even attaching an independently
constructed field realization. Attachment is independent of all small-width
recipes **on that Chamber**, intertwining translations and even actual
momentum projections. Use the full field-word domain in these conclusions.
* An additional continuous-linear compatibility with full joint Schwartz
smearing: including in the Hilbert norm. We do **not** put the image of an
arbitrary non-factorized test into the field domain.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function MeasureTheory Measure
open Boundary OS
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ContDiff FourierTransform

variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber T timeAxis}

structure FieldCore (W : Surface S) (R : S.Rotation) (h : S.RealSpin) (F : Wightman S) : Prop where
  induced : starRead F.J h
  letters : F.spin.Descends R h
  total : F.operators.Total
  adj : F.operators.sharpPair F.J
  meets : F.operators.realizes W
  localPairs : F.operators.commutes
  faithful : F.operators.notLost
  covariance : Symmetries F.spin F.action
  spectral : F.action.orbit.Spectrum F.momentum
  forward : F.momentum.region Mink.coneᶜ=0

variable {n m : ℕ} {B : Small S V} {A : Spread V} {Y : Waves S} {W : Surface S}
variable {R : S.Rotation} {h : S.RealSpin} {F : Wightman S} {U : F.operators.H →L[ℂ] V.H}





/-- Store no additional completion. From any field realization (even on a
space not originally built with `Kernel.host`) use the actual domain span,
not assuming density of one-letter vectors. -/
abbrev FieldCore.soil (H : FieldCore W R h F) : Soil W F.J where
  H := F.operators.H
  plant := F.operators.vector
  dense := H.total.cyclic ▸ H.total.everywhere
  measure := F.operators.general W H.meets F.J H.adj

theorem FieldCore.covariant (H : FieldCore W R h F) (p : Mink.Poincare) (b : Sentence S) :
    F.action.V p (F.operators.vector b)=F.operators.vector (F.spin.po p b) := by
  induction b with
  | nil => exact H.covariance.vacuum p
  | cons i b ih =>
    cases i with
    | mk x f =>
      change F.action.V p (F.operators.field x f (F.operators.evaluates b)).val = _
      rw [H.covariance.covariance]
      change (F.operators.field _ _ _).val = (F.operators.field _ _ _).val
      congr 2
      exact Subtype.ext ih

/-- Uniqueness of the hot insertions to be used in the attachment.
Requires a common chamber; `Spread.reads` determines the positive-width
operators on valid words. -/
theorem bar_eq {D : Small S V} {C : Spread V} (hb : B.concretized A) (hd : D.concretized C)
    (P : DiffPlan S) (hs : S.Symmetric) (hP : P.Inclusions S) (p : ℝ≥0) (hp : 0<p) :
    B.bar p=D.bar p := by
  ext1 i
  obtain ⟨d, u, rfl⟩ := P.covered hs hP i
  rw [hb d u p hp, hd d u p hp]
  apply V.GNS.by_bud
  intro q
  have hv : Slab timeAxis (p+p) [(position 0 p, (⟨d, S.representative d u⟩ : L.Token))] :=
    Work.C01.centeredSlab _ _ hp
  exact (A.reads hv q).trans (C.reads hv q).symm

private theorem train_eq {D : Small S V} {p : ℝ≥0} (hh : B.bar p=D.bar p) (n : ℕ) (x y v Z X) :
    B.trainB p n x y v Z X=D.trainB p n x y v Z X := by
  induction n generalizing Z X with
  | zero => rfl
  | succ n ih => rw [Small.trainB, Small.trainB, hh, ih]

theorem hot_eq {D : Small S V} {p : ℝ≥0} (hh : B.bar p=D.bar p) (n : ℕ) (v : Fin n → S.Union)
    (y : Heights n) (f : Joint n) : hot B v f (p, y)=hot D v f (p, y) := by
  cases n with
  | zero => rfl
  | succ n => unfold hot; simp only [Small.shot, hh, train_eq hh]

theorem FieldCore.coupling (H : FieldCore W R h F) (lamp : B.Lamp W F.J F.spin) :
    ∃ U : F.operators.H →L[ℂ] V.H, F.action.Intervenes (C:=V) U F.operators.vacuum ∧
      ∀ b, Tendsto (B.heatCup b) till (𝓝 (U (F.operators.vector b))) := by
  let Z := (B.bowls lamp).out
  obtain ⟨U, -, hU, hu⟩ := Soil.universal_embed H.soil (M:=V.H) Z.toFun Z.at_pair
  have hv (b : Sentence S) : U (F.operators.vector b)=Z.toFun b := hU b
  refine ⟨U, ⟨hu, fun p => Kernel.Gram.by_bud H.soil ?_, (hU _).trans Z.vacuum⟩, ?_⟩
  · intro b
    change U (F.action.V (Mink.Poincare.translation p) (F.operators.vector b)) =
      V.flow.unit.translation p (U (F.operators.vector b))
    rw [H.covariant, hv, hv, Z.volume]
  intro b
  rw [hv]
  exact (B.bowls lamp).chase b

/-- Criterion for a joint field test map. -/
def ExtendsTensor (F : Fields S) (v : Fin n → S.Union) (Ψ : Joint n →L[ℂ] F.H) : Prop :=
  ∀ z : Fin n → Test4, Ψ (Joint.materialize n z)=F.vector (tensorWord v z)

theorem tensor_determines {E : Hilbert} (A B : Joint n →L[ℂ] E) (h : ∀ f : Fin n → Test4,
    A (Joint.materialize n f)=B (Joint.materialize n f)) : A=B := by
  apply ContinuousLinearMap.ext_on (R₁:=ℂ)
    (s:=Set.range (Joint.materialize n))
  · intro x
    change x∈(Submodule.span ℂ (Set.range (Joint.materialize n))).topologicalClosure
    rw [Work.C25.answer n]
    exact Submodule.mem_top
  rintro _ ⟨f, rfl⟩
  exact h f



private theorem joints {Q : Fields S} {Z : Q.H →L[ℂ] V.H}
    {B : Small S V} (hu : ∀ i, ‖Z i‖=‖i‖) (hh : ∀ b, Tendsto (B.heatCup b) till (𝓝 (Z (Q.vector b))))
    (int : Y.NonTangentialFree W) (J : StarOp S) (hw : Bid.Hull B Y J) (v : Fin n → S.Union) :
    ∃ Ψ : Joint n →L[ℂ] Q.H, ExtendsTensor Q v Ψ ∧ ∀ f : Joint n,
      Tendsto (hot B v f) (edgeFilter n) (𝓝 (Z (Ψ f))) := by
  obtain ⟨M, hM, -⟩ := heated hw int v
  have ht (f : Fin n → Test4) : M (Joint.materialize n f)=Z (Q.vector (tensorWord v f)) := by
    refine tendsto_nhds_unique_of_eventuallyEq
      ((hM (Joint.materialize n f)).comp (profile_edge n)) (hh (tensorWord v f)) ?_
    exact Eventually.of_forall fun t => hot_profile B v f t
  let L := Z.adjoint.comp M
  have hz (x : Q.H) : Z.adjoint (Z x)=x := DFunLike.congr_fun ((Z.norm_map_iff_adjoint_comp_self).mp hu) x
  have hl : ExtendsTensor Q v L := by
    intro f
    change Z.adjoint (M (Joint.materialize n f)) = _
    rw [ht, hz]
  have he : Z.comp L=M := tensor_determines _ _ (fun i => by
    rw [ContinuousLinearMap.comp_apply, hl i, ht])
  exact ⟨L, hl, fun f => by rw [← ContinuousLinearMap.comp_apply, he]; exact hM f⟩

/-- Coherent attachment even across independently chosen (but concretized)
hot probes. Time signs fixed as in `Cups`, `V.flow`; use `volume` on Points. -/
structure Attachment (F : Wightman S) (V : Chamber T timeAxis) (U : F.operators.H →L[ℂ] V.H) : Prop where
  acts : F.action.Intervenes (C:=V) U F.operators.vacuum
  linked : ∃ (A : Spread V) (B : Small S V), B.concretized A
  smears (n : ℕ) (v : Fin n → S.Union) : ∃ Ψ : Joint n →L[ℂ] F.operators.H,
    ExtendsTensor F.operators v Ψ ∧ ∀ (A : Spread V) (B : Small S V), B.concretized A →
      ∀ f : Joint n, Tendsto (hot B v f) (edgeFilter n) (𝓝 (U (Ψ f)))

/-- This in particular retains the actual field words on the common domain. -/
theorem Attachment.traces (u : Attachment F V U) (w : B.concretized A) (b : Sentence S) :
    Tendsto (B.heatCup b) till (𝓝 (U (F.operators.vector b))) := by
  let v := fun i => (b.get i).1
  let f := fun i => (b.get i).2
  obtain ⟨Ψ, hΨ, hw⟩ := u.smears _ v
  have he := hw _ B w (Joint.materialize _ f)
  rw [hΨ f] at he
  have hh : tensorWord v f=b := by simp [tensorWord, v, f]
  have hz := he.comp (profile_edge b.length)
  rw [hh] at hz
  refine hz.congr' ?_
  exact Eventually.of_forall fun t => (hot_profile B v f t).trans (congr_arg (fun g => B.heatCup g t) hh)

/-- For every candidate FieldCore, not just ones made using Cups. -/
theorem FieldCore.attach (H : FieldCore W R h F) (P : DiffPlan S) (hs : S.Symmetric) (hP : P.Inclusions S)
    (w : B.concretized A) (int : Y.NonTangentialFree W)
    (hw : Bid.Hull B Y F.J) (lamp : B.Lamp W F.J F.spin) :
    ∃! U : F.operators.H →L[ℂ] V.H, Attachment F V U := by
  obtain ⟨U, hU, hθ⟩ := H.coupling lamp
  refine ⟨U, ⟨hU, ⟨A, B, w⟩, fun n v => ?_⟩, fun L k => Kernel.Gram.by_bud H.soil
    (fun b => tendsto_nhds_unique (k.traces w b) (hθ b))⟩
  obtain ⟨Ψ, hΨ, hW⟩ := joints hU.scale hθ int F.J hw v
  refine ⟨Ψ, hΨ, fun A₁ B₁ hb f => ?_⟩
  apply (hW f).congr'
  filter_upwards [heights_valid n] with i hi
  exact hot_eq (bar_eq w hb P hs hP i.1 hi.2.1.1) n v i.2 f

theorem Attachment.with_heat (u : Attachment F V U) (H : FieldCore W R h F) (q : V.UniqueHeat) :
    F.Realizes (W:=W) R h :=
  ⟨H.induced, H.letters, H.total, H.adj, H.meets, H.localPairs, H.faithful, H.covariance,
    H.spectral, H.forward, F.action.only u.acts q⟩



theorem Attachment.measures (u : Attachment F V U) (H : FieldCore W R h F) (x : F.operators.H) :
    F.momentum.diagonal x = V.flow.ℚmeasure.diagonal (U x) := by
  apply Measure.ext_of_charFun
  ext1 b
  rw [H.spectral, V.flow.joint, ← ContinuousLinearMap.comp_apply _ U, ← u.acts.across b]
  exact (LinearIsometry.inner_map_map
    (⟨U.toLinearMap, u.acts.scale⟩ : F.operators.H →ₗᵢ[ℂ] V.H) _ _).symm

/-- Equality on Borel spectral projections, not just time characters. -/
theorem Attachment.projections (u : Attachment F V U) (H : FieldCore W R h F)
    (s : Set E4) (hs : MeasurableSet s) (x : F.operators.H) :
    U (F.momentum.region s x) = V.flow.ℚmeasure.region s (U x) := by
  let P := F.momentum.region s
  let Q := V.flow.ℚmeasure.region s
  have hA (x : F.operators.H) : inner ℂ x (P x)=inner ℂ (U x) (Q (U x)) := by
    dsimp only [P, Q]
    rw [← F.momentum.at_pair hs, ← V.flow.ℚmeasure.at_pair hs, u.measures H x]
  have hp : P.toLinearMap=(U.adjoint.comp (Q.comp U)).toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro v
    apply (starRingEnd ℂ).injective
    rw [inner_conj_symm, inner_conj_symm]
    change inner ℂ v (P v) = inner ℂ v (U.adjoint (Q (U v)))
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact hA v
  let y := U (P x)
  let z := Q (U x)
  have hp' (x) : P x = U.adjoint (Q (U x)) := LinearMap.congr_fun hp x
  have hii : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
    nth_rw 1 [show P x=P.adjoint x from DFunLike.congr_fun (F.momentum.real hs).symm x]
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact congr_arg _ (F.momentum.idempotent hs _)
  have hyy : inner ℂ y y = inner ℂ (P x) (P x) := (LinearIsometry.inner_map_map
    (⟨U.toLinearMap, u.acts.scale⟩ : F.operators.H →ₗᵢ[ℂ] V.H) _ _)
  have hzz : inner ℂ z z = inner ℂ (P x) (P x) := by
    nth_rw 1 [show z=Q.adjoint (U x) from DFunLike.congr_fun (V.flow.ℚmeasure.real hs).symm _]
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (U x) (Q (Q (U x)))=_
    rw [show Q (Q (U x))=Q (U x) from V.flow.ℚmeasure.idempotent hs _, ← hA x, hii]
  have hzy : inner ℂ z y=inner ℂ (P x) (P x) := by
    change inner ℂ z (U (P x))=_
    rw [← ContinuousLinearMap.adjoint_inner_left U, show U.adjoint z=P x from (hp' x).symm]
  have hyz : inner ℂ y z=inner ℂ (P x) (P x) := by
    change inner ℂ (U (P x)) z=_
    rw [← ContinuousLinearMap.adjoint_inner_right U, show U.adjoint z=P x from (hp' x).symm]
  apply sub_eq_zero.mp
  change y-z=0
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hyy, hzy, hyz, hzz]; ring
end YM.Next.BOUNDARY
