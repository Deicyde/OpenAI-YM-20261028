import YM.Next.BOUNDARY.Stage

/-!
Bridge lemmas restored from the accepted original proof for the every-phase
extension. Their proof bodies are unchanged; keeping them here leaves the
pruned existence proof and its import graph intact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY
open Boundary OS Spec

section
variable {G : Gauge} {L : Register G} {S : Table L}
variable {W : Surface S} {R : S.Rotation} {h : S.RealSpin} {F : Wightman S}

theorem FieldCore.of_realizes (H : F.Realizes (W:=W) R h) : FieldCore W R h F :=
  ⟨H.induced, H.letters, H.total, H.adj, H.meets, H.localPairs, H.faithful, H.covariance, H.spectral, H.forward⟩
end

section
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- For ANY already produced Final, not just instances from
`after_materializes`. -/
theorem onFinal (F : Final C f S) :
    Compatible S F.α.unselected F.sector F.action.spin F.room.kernel.spin F.B ∧
    Compatible S F.α.slabs F.sector F.action.spin F.room.kernel.spin F.A :=
  both (s:=F.room) F.phase F.realization.qt.letters F.realization.allWorld F.realization.chosen
end
end YM.Next.BOUNDARY

-- Original Core helpers needed by the full joint-test attachment argument.
namespace YM.Next.BOUNDARY
open Set Filter Function MeasureTheory Measure Boundary OS
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ContDiff FourierTransform
variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber T timeAxis}
variable {n m : ℕ} {B : Small S V} {A : Spread V} {Y : Waves S} {W : Surface S}
variable {F : Wightman S} {U : F.operators.H →L[ℂ] V.H}
theorem extends_unique (v : Fin n → S.Union) {K O : Joint n →L[ℂ] F.operators.H}
    (hK : ExtendsTensor F.operators v K) (hO : ExtendsTensor F.operators v O) : K=O :=
  tensor_determines K O (fun i => (hK i).trans (hO i).symm)

theorem Attachment.inner_eq (u : Attachment F V U) (w : B.concretized A)
    (hw : Bid.Hull B Y F.J) (int : Y.NonTangentialFree W) {P : Joint n →L[ℂ] F.operators.H}
    {Q : Joint m →L[ℂ] F.operators.H} {v : Fin n → S.Union} {z : Fin m → S.Union}
    (hP : ExtendsTensor F.operators v P) (hQ : ExtendsTensor F.operators z Q) (f : Joint n) (g : Joint m) :
    inner ℂ (P f) (Q g)=W.W (n+m) (Bid.bothT v z F.J) (joinedTest f g) := by
  obtain ⟨Ψ, hΨ, hu⟩ := u.smears n v
  obtain ⟨Φ, hΦ, hv⟩ := u.smears m z
  rw [extends_unique v hP hΨ, extends_unique z hQ hΦ]
  refine Eq.trans ?_ (limiting_pair hw int _ _ _ _ _ _ (hu A B w f) (hv A B w g))
  exact (LinearIsometry.inner_map_map
    (⟨U.toLinearMap, u.acts.scale⟩ : F.operators.H →ₗᵢ[ℂ] V.H) _ _).symm
end YM.Next.BOUNDARY

namespace YM.Boundary
open Filter Set Distribution Probe MeasureTheory Mink Mink.Poincare
open scoped Topology InnerProductSpace BigOperators Matrix.Norms.Frobenius
lemma solid_fields (n) : IsClosed (shores n) := isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => closed_cone.preimage (by fun_prop)
end YM.Boundary
