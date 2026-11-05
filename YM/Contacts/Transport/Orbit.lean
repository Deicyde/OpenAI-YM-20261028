import YM.Contacts.Transport.Pier
/-!
# Full isometry cases

Arbitrary change of orthogonal coordinates also at the evaluation of all the Reader integrals
consumes the preceding point identities with transformed tests. Running length metadata & basis
grades are preserved in this statement. Use on the joint stage or any transformed orthogonal
Jacobi tester with its centers appropriately transformed. Provides also the all-points transform
as a `Ribbon`, to use covariance simply on full position tests. Isometries here exact, e.g. when
just changing spectator order. Typography `orbit_cost` is integration, not a pushforward of
one root test onto coincident exterior supports.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Transport
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal OPE Harvest Route Solstice Ordered WithLp
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace MeasureTheory
variable {E F : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F]
variable {k n : ℕ} {G:Gauge}{C:Family G}{O:Extraction.Order}{S:Table C.book}{Z:Final C O S}{d : Fin k→ℕ}{d':Fin n→ℕ}
variable {U:E≃ₗᵢ[ℝ] F} {c:F} [MeasurableSpace E][MeasurableSpace F][BorelSpace E][BorelSpace F]
variable {t:Fin k↪Fin n}{P:E→ₗᵢ[ℝ] Points k}{T:F→ₗᵢ[ℝ] Points n} {o:Points k}{o' : Points n}{s : Ortho}{w:E4}{b : Bool}{a : ℝ}{g : Normal.Group k}
lemma orbit_cost (R : Ribbon t P T U.toLinearIsometry c o o' s w g) (Q : Pieces g) {M : Devices Z.sector.derivatives} {z : Cells S d}{z' : Cells S d'} (hM : M.rotation=Z.sector.turns) (h : Ribbon.Forms M s b t g z z') (α : Viewers Z) {ψ: SmoothTests E}{ψ':SmoothTests F}(hh : Transport.follows b (fun x=>U x+c) ψ ψ') :
    (∫ x,readExpr M.basis (spectator Z α) (localImage M T (flow t g Q) o' a z' ψ' x))= realChange b (∫ x,readExpr M.basis (spectator Z α) (localImage M P Q o a z ψ x)):= by
    let p:= U.toHomeomorph.trans (Homeomorph.addRight c); let F(x : E):= readExpr M.basis (spectator Z α) (localImage M P Q o a z ψ x); let Y:= readExpr M.basis (spectator Z α) ∘ localImage M T (flow t g Q) o' a z' ψ';
    have ht : MeasurePreserving p := (measurePreserving_add_right volume c).comp (LinearIsometryEquiv.measurePreserving U)
    change (∫ x,Y x)=realChange b (∫ x,F x); rw [← ht.integral_comp p.measurableEmbedding Y, show (fun x=> Y (p x))= (fun x=> realChange b (F x)) from funext fun x=> R.aperture_travels h hM a Q α hh x]; suffices he: ∀ b, (∫ x,realChange b (F x))=realChange b (∫ x,F x) by exact he b
    intro b; cases b with
    | false=> rfl
    | true=> exact ContinuousLinearEquiv.integral_comp_comm Complex.conjCLE _

variable (e : Fin k≃ Fin n) (s : Ortho) (v : E4)
abbrev total (k:ℕ):= LinearIsometry.id (R:=ℝ) (E:=Points k)
def rotateStage : Points k ≃ₗᵢ[ℝ] Points n:= (LinearIsometryEquiv.piLpCongrLeft 2 ℝ E4 e).trans (LinearIsometryEquiv.piLpCongrRight 2 fun _=> s.motion)
lemma symmetry : Ribbon e.toEmbedding (total k) (total n) (rotateStage e s).toLinearIsometry (points (fun _=>v)) 0 0 s v g := by
    constructor
    · exact fun x _=> ⟨x,rfl⟩
    · exact fun x _=> ⟨x,rfl⟩
    · exact fun i hi=> (map_zero _).symm
    · exact fun i hi=> (map_zero _).symm
    intro i hi x; change ((rotateStage e s x+_) +0) (e i)= _; simp only [total,LinearIsometry.id_apply,add_zero,PiLp.add_apply]; change Ortho.motion s (x (e.symm (e i))) + v=_; rw [e.symm_apply_apply]
end YM.Contacts.Transport
