import YM.Climb.Beams
import YM.Fields.Spectrum


/-!
# Transport descent to actual labels.

Given free Lorentz label action (needs proving, not a spectral assumption).
Push via the *same* polar morph returned from Beams. d-equivalences obtained
independently; need show they generate SAME action across caps via Lie
intertwining and spatial agreement. `same` tested. -/
set_option autoImplicit false
noncomputable section
namespace YM.Spin
open Function Set Complex Filter MeasureTheory Analysis Extraction Boundary Climb Mink Ward
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}

/-- Shell sewing callback -- sufficient compatibility for building C_M.
Used after Hplus with Lie actual; doesn't assert boost conj continuity at Union. -/
def run (U : ∀ d,Spin.change S d) (X : Spins (Bel L)) (d : ℕ) (p : Lorentz) : S.Field d≃ₗ[ℂ] S.Field d :=
    (U d).symm.trans ((X.shell d p).trans (U d))

def wand (W : DiffPlan S) (U : ∀ d,Spin.change S d) (X : Spins (Bel L)) :=
    ∀ d e (hp : d ≤ e) p v,run U X e p (W.rise hp v)=W.rise hp (run U X d p v)

def intercedes (U : ∀ d,Spin.change S d) (Y : Table.Rotation S) (K : Table.Rotation (Bel L)) :=
    ∀ d g k,Y.lie d g (U d k)=U d (K.lie d g k)

lemma transmits (U : ∀ d,Spin.change S d) (T : Lighthouse L) {a : Table.RealSpin (Bel L)} {H}
    (h : T.Goes L a) (p : SpinRows S) (hx : Port (morph T.K p U) H) : intercedes U (morph T.K p U) T.K := by
  intro d g k
  let M := (U d).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have he := hx.spinAt d g (U d k)
  have hp := M.hasFDerivAt.comp_hasDerivAt 0 (h.turns.infinitesimal d g k)
  apply he.unique
  simpa only [morph,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using! hp

lemma reach (W : DiffPlan S) (T : Lighthouse L) {a : Table.RealSpin (Bel L)} {H : Table.RealSpin S}
    (U : ∀ d,Spin.change S d) (p : SpinRows S) (ht : ∀ d,realH H a (U d)) (he : intercedes U (morph T.K p U) T.K)
    (hx : W.Inclusions S) (hy : S.Symmetric) (X : Spins (Bel L)) (h : X.Descends T.K a)
    (hh : wand W U X) : ∃ Y : Spins S,Y.Descends (morph T.K p U) H := by
  have hg k : ∃! T:S.Union→ₗ[ℂ] S.Union, ∀ d v,T (S.pin d v)=S.pin d (run U X d k v) :=
    W.uniqueLift hy hx (fun d => (S.pin d).comp (run U X d k).toLinearMap) (by
      intro d e hD t
      change S.pin e (run U X e k (W.rise hD t))= S.pin d (run U X d k t); rw [hh,W.stays hy hx])
  choose B hB using fun p => (hg p).exists
  have hi i v : B 1 (S.pin i v)=S.pin i v := by
    have he (x : (Bel L).Field i) : X.shell i 1 x=x := (Bel L).pin_inj _ ((h.ties 1 i x).symm.trans (h.identity _))
    simp [hB,he,run]
  have hr d k t (a : (Bel L).Field d) : X.shell d (k*t) a=X.shell d k (X.shell d t a) := (Bel L).pin_inj _ (by rw [← h.ties,← h.ties,← h.ties,h.representation])
  have hF v : B 1 v=v := by obtain ⟨i,v,rfl⟩ := W.covered hy hx v; rw [hi]
  have hZ k t v : B (k*t) v=B k (B t v) := by
    obtain ⟨d,x,rfl⟩ := W.covered hy hx v
    simp [hB,run,hr]
  let Y : Spins S := {
    shell := run U X
    rail k := LinearEquiv.ofBijective (B k) ⟨fun i j hb => by
      calc i=B k⁻¹ (B k i) := by rw [← hZ]; simp [hF]
           _=B k⁻¹ (B k j) := by rw [hb]
           _=j := by rw [← hZ];simp [hF], fun j => ⟨B k⁻¹ j,by rw [← hZ];simp [hF]⟩⟩ }
  have hrt (i k v) : Y.shell i k (U i v)=U i (X.shell i k v) := by simp [Y,run]
  refine ⟨Y,hB,hF,hZ,fun d v => ?_,fun n i q => ?_,fun K H v p => ?_,fun g d v => ?_⟩
  · obtain ⟨x,rfl⟩ := (U d).surjective v; simp_rw [hrt]
    exact (U d).toLinearMap.continuous_of_finiteDimensional.comp (h.spin d x)
  · obtain ⟨u,rfl⟩ := (U n).surjective q; simp_rw [hrt, he _ _ _]
    let A := ((U n).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
    have hp : A (((-I):ℂ) • (T.K.lie n _ u))=(-I:ℂ) • U n (T.K.lie n (Ortho.plane timeAxis i.castSucc) u) := (U n).map_smul (-I) _
    rw [←hp]; exact A.hasFDerivAt.comp_hasDerivAt 0 (h.boosts n i u)
  · obtain ⟨j,rfl⟩ := (U v).surjective p; rw [hrt,h.spatial K H]; simp [morph]
  obtain ⟨x,rfl⟩ := (U d).surjective v
  have ht' (i) : S.adj H d timeAxis (U d i) = U d ((Bel L).adj a d timeAxis i) := by
    unfold Table.adj; simp only [LinearMap.comp_apply, (ht d).2,(ht d).1]
  rw [hrt,ht', h.commutes,ht',hrt]
end YM.Spin
