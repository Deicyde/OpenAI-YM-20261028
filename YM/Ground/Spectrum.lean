import YM.Ground.Permute




/-!
# Compact probability with faithful characters on ground algebra. Requires
separability of generators (separate continuity proof). Not direct integral claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Ground
open Function Set Filter MeasureTheory Measure Spectral TopologicalSpace WeakDual
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators

-- test at generic R then specialization; avoids diamonds
variable {X : Type*} [CommCStarAlgebra X]
abbrev Theta := ↥(characterSpace ℂ X)

def view (x : Theta (X := X)) : X →⋆ₐ[ℂ] ℂ :=
    (ContinuousMap.evalStarAlgHom ℂ ℂ x).comp (gelfandStarTransform X : X→⋆ₐ[ℂ] C(Theta,ℂ))
lemma sees (x : Theta (X := X)) (p : X) : view x p=x p := rfl
lemma bij : Bijective (view (X := X)) := by
  constructor
  · intro i j hi
    apply CharacterSpace.equivAlgHom.injective
    exact DFunLike.ext _ _ (fun a => congr_arg (fun f : X →⋆ₐ[ℂ] ℂ => f a) hi)
  intro w
  obtain ⟨i,hi⟩ := CharacterSpace.equivAlgHom.surjective w.toAlgHom
  exact ⟨i, DFunLike.ext _ _ fun a => congr_arg (fun f : X →ₐ[ℂ] ℂ => f a) hi⟩
lemma view_cont (x : Theta (X := X)) : Continuous (view x) := (toStrongDual (x.val)).continuous
lemma mark_cont (a : X) : Continuous (fun x : Theta => view x a) := (gelfandStarTransform X a).continuous

theorem tiny (y : ℕ → X) (hy : DenseRange y) : MetrizableSpace (Theta (X := X)) := by
  let f (p : Theta) (i : ℕ) := view p (y i)
  have he : Continuous f := continuous_pi fun i => mark_cont _
  have hf : Injective f := by
    intro p q hh
    apply bij.1; apply DFunLike.coe_injective
    exact hy.equalizer (view_cont p) (view_cont q) hh
  exact (he.isClosedEmbedding hf).isEmbedding.metrizableSpace

lemma supports {D : Type*} [MetricSpace D] [T2Space D] [CompactSpace D] [MeasurableSpace D] [BorelSpace D]
    (H : Hilbert) (V : Rep.CC D →⋆ₐ[ℂ] H.Op) (v : H)
    (hv : ∀ x : Rep.CC D, V x v=0 → x=0) : IsOpenPosMeasure (Rep.sees V v) := by
  classical
  constructor
  intro U hU he h
  obtain ⟨x,hx⟩ := he
  obtain ⟨r,hr,hy⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let f : C(D,ℂ) := ⟨fun i => (↑(max 0 (r-dist i x)):ℂ),by fun_prop⟩
  let μ := Rep.sees V v
  have hm : ∀ᵐ i ∂μ, f i=0 := by
    have h' : ∀ᵐ i ∂μ,i∉U := mem_ae_iff.mpr (by change μ (Uᶜ)ᶜ=0;rw [compl_compl];exact h)
    filter_upwards [h'] with i hi
    change (↑(max 0 (r-dist i x)):ℂ) = 0
    simp [(show r-dist i x≤0 from by
      have ht : i ∉ Metric.ball x r := fun j => hi (hy j)
      simp at ht; linarith)]
  have ht : Rep.name μ f=0 := by
    apply Lp.ext; exact (ContinuousMap.coeFn_toLp ..).trans (EventuallyEq.trans (show ⇑f =ᵐ[μ] (0:D→ℂ) from hm) (EventuallyEq.symm (Lp.coeFn_zero ..)))
  have hE : f x=0 := by
    rw [hv f]
    · simp
    rw [← Rep.reads V v,ht]; exact map_zero _
  simp [f] at hE; linarith


section
variable {A : Type} [Semiring A] [StarRing A] [Algebra ℂ A]
structure Panes (A : Type) [Semiring A] [StarRing A] [Algebra ℂ A] where
  X : Type
  [m : MetricSpace X]
  [b : MeasurableSpace X]
  [borel : BorelSpace X]
  [compact : CompactSpace X]
  μ : Measure X
  character : X → A →⋆ₐ[ℂ] ℂ
attribute [instance] Panes.m Panes.b Panes.borel Panes.compact

structure Panes.Shines [TopologicalSpace A] (H : Hilbert) (p : A →⋆ₐ[ℂ] H.Op) (w : H) (R : Panes A) : Prop where
  normalized : IsProbabilityMeasure R.μ
  support : R.μ.IsOpenPosMeasure
  onto : Function.Bijective R.character
  values (x) : Continuous (R.character x)
  weak (i : A) : Continuous (fun x => R.character x i)
  ground (i : A) : (∫ x, R.character x i ∂R.μ) = inner ℂ w (p i w)
end

private lemma receives_ {A : Type} [CommCStarAlgebra A] (H : Hilbert) (p : A →⋆ₐ[ℂ] H.Op) (w : H) (hw : ‖w‖=1)
    (u : ℕ → A) (hu : DenseRange u) (ht : ∀ i : A, p i w=0 → i=0) : ∃ R : Panes A, R.Shines H p w := by
  classical
  let X := Theta (X := A)
  letI : MetrizableSpace X := tiny u hu
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MeasurableSpace X := borel _; letI : BorelSpace X := ⟨rfl⟩
  let P : Rep.CC X →⋆ₐ[ℂ] H.Op := p.comp ((gelfandStarTransform A).symm : _ →⋆ₐ[ℂ] _)
  let V : Panes A := { X := X, μ := Rep.sees P w, character := view }
  have hp i : P (gelfandStarTransform A i)=p i := congr_arg p ((gelfandStarTransform A).symm_apply_apply _)
  refine ⟨V,?_,?_,bij,view_cont,mark_cont,?_⟩
  · apply isProbabilityMeasure_iff_real.mpr
    change (Rep.sees P w).real _=1
    rw [Rep.size,hw,one_pow]
  · refine supports H P w ?_
    intro x hx
    obtain ⟨i,rfl⟩ := (gelfandStarTransform A).surjective x
    change P (gelfandStarTransform A i) w=0 at hx; rw [hp] at hx
    change (gelfandStarTransform A i)=0; rw [ht i hx,map_zero]
  intro i
  have h := Rep.pairings P w (gelfandStarTransform A i)
  rw [hp] at h; exact h

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

lemma attains (ab : ∀ x y : P.algebra, x*y=y*x) (H : Steady V) : ∀ p : P.algebra, p.val V.omega0=0 → p=0 := by
  intro p hp
  apply Subtype.ext
  apply DFunLike.coe_injective
  apply (full P H).equalizer p.val.continuous continuous_const
  funext x
  change p.val (x.val V.omega0)=0
  change (p*x).val V.omega0=0
  rw [ab];change x.val (p.val V.omega0)=_
  rw [hp,map_zero]

set_option maxHeartbeats 800000 in
theorem resolution (R : Table.Rotation S) (h : R.Oriented S) (s : S.Hierarchy)
    (u : ℕ→ P.algebra) (hu : DenseRange u) : ∃ W : P.Resolution, W.Out := by
  classical
  have H : Steady V := fun x i => inert V s R h _ _
  have ab := adjunction P H s R h
  haveI : IsClosed (P.algebra : Set V.VacuumOp) := isClosed_closure
  letI : CommCStarAlgebra P.algebra := {
    (StarSubalgebra.cstarAlgebra P.algebra) with mul_comm := ab }
  let D : Hilbert := { space := V.D }
  obtain ⟨A,t⟩ := receives_ D (show P.algebra →⋆ₐ[ℂ] D.Op from P.algebra.subtype) V.omega0 (nil_norm V.GNS s.laws) u hu
    (fun i => attains P ab H i)
  let U : P.Resolution := { X := A.X, metric := A.m, sets := A.b, borel := A.borel, compact := A.compact, μ := A.μ,
                            character := A.character }
  exact ⟨U, ab, t.normalized,t.support,t.onto,t.values,t.weak,t.ground⟩
end YM.OS.Ground
