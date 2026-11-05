import YM.Contacts.Transport.Joined
import YM.Contacts.Solstice.Venue
/-!
# Poller-the-world. Transport of contact fields.

Rotational, scalar orientation, translations, cluster index and padding/parametric placement.
System witnesses fixed. Moves in the complex field quotients (orientation through each grade).
Particles with fewer slots to any cluster of the ambient, Taylor prescription in every group
using its own J coordinates, averts any duplication of data on overlaps. No orientation hypotheses
on the basis used internally to split Motion into channels (except the coherent covariant field
projections). Results are equalities on integrands without requiring costs. Apply to genuine
readers e.g. with cleared supports & patched integrals as shown. The formula is explicitly 4-dim.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Transport
open Function Filter Set Normal Submodule Table Spec OPE Harvest Route Solstice Ordered MultipleContact
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace
variable {E F : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F]
variable {k n : ℕ}{U:E→ₗᵢ[ℝ] F}{P : E→ₗᵢ[ℝ] Points k}{T : F→ₗᵢ[ℝ] Points n}
 {f g : Normal.Group k}{t:Fin k↪ Fin n}{o:Points k}{o' : Points n}{c:F}{s : Ortho}{w : E4}
variable {G:Gauge}{C:Family G}{O:Extraction.Order}{S:Table C.book}{Z:Final C O S}
variable {b : Bool} {M : Devices Z.sector.derivatives}
local notation "E!"=> Expression Z.sector.derivatives

namespace Ribbon
open Devices
variable (R : Ribbon t P T U c o o' s w g)
-- R removed where unneeded; fields transform if b=true also real conjugation, then rotate and translate.
omit R
def glaze (M: Devices Z.sector.derivatives)(b : Bool)(n : ℕ)(y : S.Field n) := if b then S.conj M.hierarchy.spin n y else y
def truth (M : Devices Z.sector.derivatives)(b : Bool) : Expression Z.sector.derivatives→+* Expression Z.sector.derivatives := if b then realExpr M.basis M.hierarchy.spin else RingHom.id _
def press (M : Devices Z.sector.derivatives)(s : Ortho)(w : E4)(b : Bool) : Expression Z.sector.derivatives→+* Expression Z.sector.derivatives := (shiftExpr w).toRingHom.comp ((turnExpr M.basis M.rotation s).toRingHom.comp (truth M b))
lemma pressing (x:E!) : press M s w b x= shiftExpr w (turnExpr M.basis M.rotation s (truth M b x)):= rfl
def laid (M : Devices Z.sector.derivatives)(s : Ortho)(b:Bool) (f:S.Tag) : S.Tag:= ⟨f.1,M.rotation.act _ s (glaze M b _ f.2)⟩
lemma confers : Conforms b (press M s w b):= by
   intro c t; simp_rw [pressing]; rw [show truth M b (c • t)=(realChange b c) • truth M b t from (by cases b; exact (_root_.Eq.refl _); exact real_coeff ..),map_smul,map_smul]

lemma fixed_glaze (n) (x:E4)(f) : truth M b (insertField M.basis x n f)= insertField M.basis x n (glaze M b n f):= by cases b; rfl; exact real_field M.basis M.hierarchy.laws.toSymmetric M.incl M.orientation M.coherent x n f
lemma truth_row (x:E4)(i:ℕ)(f:E!) : M.row x i (truth M b f)= glaze M b i (M.row x i f):=by cases b; rfl; exact (M.row_real ..).symm
lemma sharp (x:E4)(n:ℕ)(f) : press M s w b (insertField M.basis x n f)= insertField M.basis (Ortho.motion s x+w) n (M.rotation.act n s (glaze M b n f)):= by
   rw [pressing,fixed_glaze,turn_field M.basis M.rotation M.laws M.hierarchy.laws.toSymmetric M.incl M.coherent,shift_field]; rfl
lemma sharper (x:E4)(f:S.Tag) : press M s w b (insertField M.basis x _ f.2)= insertField M.basis (Ortho.motion s x+w) _ (laid M s b f).2:= sharp ..
lemma turned_row (x:E4)(n:ℕ)(e:E!) : M.row (Ortho.motion s x+w) n (press M s w b e)= M.rotation.act _ s (glaze M b n (M.row x n e)):= by rw [pressing,M.row_moves n, Ortho.motion_at, ← M.row_spin, truth_row]
lemma pressure (x:E4)(i:ℕ)(e:E!) : press M s w b (M.insertRow x i e) = M.insertRow (Ortho.motion s x+w) i (press M s w b e):= by
   rw [insertRow, insertRow,LinearMap.comp_apply,LinearMap.comp_apply,sharp,turned_row]
lemma any_turn (h : M.rotation=Z.sector.turns)(α:Viewers Z): M.rotation.Oriented (spectator Z α):= by
    cases α with
    | none=> exact M.turns
    | some i=> rw [h]; exact Z.phase.phase.sym i
lemma shift_reading (e:E!) (h : M.rotation= Z.sector.turns)(v:Viewers Z) : readExpr M.basis (spectator Z v) (press M s w b e)= realChange b (readExpr M.basis (spectator Z v) e):= by
   have he:=(spectate Z v); have hh:=spectate_respects Z v; have hm:=spectate_ready Z v
   rw [pressing,shift_read M.basis (spectator Z v) he, turn_read M.basis M.rotation M.laws M.hierarchy.laws.toSymmetric M.incl M.coherent (spectator Z v) he hh hm (any_turn h v)]; cases b; rfl; exact real_read M.basis M.hierarchy.laws.toSymmetric M.incl M.orientation M.coherent _ he hh hm _

local notation "q" => current t g
variable {d : Fin k→ℕ}{d':Fin n→ℕ}{z:Cells S d}{y:Cells S d'}
-- occurrence of rotation and conjugation with same real conventions. Basis equality by assigned Tag.

def Forms (M:Devices Z.sector.derivatives) (s:Ortho)(b:Bool)(t : Fin k↪Fin n)(g : Normal.Group k)(z:Cells S d)(y:Cells S d') := ∀ j∈g,(⟨d' (t j), y (t j)⟩: S.Tag)=laid M s b ⟨d j,z j⟩

variable (h : Forms M s b t g z y)
include R h
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma branch_joint : Joint t b (press M s w b) (fun x=> U x+c) g (waySystem P M o d z) (waySystem T M o' d' y) := by
    constructor; exact fun i hi=> congr_arg Sigma.fst (h i hi)
    · intro i hi x; change insertField M.basis _ _ (y (t i)) = press M s w b (insertField M.basis _ _ (z i)); rw [R.lie i hi]
      have hf:=sharper (M:=M) (s:=s) (b:=b) (w:=w) ((P x+o) i) ⟨d i,z i⟩; rw [← h i hi] at hf; exact hf.symm
    intro f hf hl k x e; change press M s w b (M.insertRow (centroid f _) k e) = M.insertRow (centroid (current t f) _) k _; rw [(R.smaller hf).centroid_move x hl]; exact pressure ..
lemma transports (a:ℝ)(Q:Pieces g) {ψ:SmoothTests E}{ψ':SmoothTests F}(hp:Transport.follows b (fun x=> U x+c) ψ ψ')(x:E) : press M s w b (localImage M P Q o a z ψ x) = localImage M T (flow t g Q) o' a y ψ' (U x+c) := (R.bank_flow (branch_joint R h) a Q).fin confers hp x
lemma aperture_travels (hM : M.rotation=Z.sector.turns) (a:ℝ)(Q:Pieces g)(v:Viewers Z) {ψ:SmoothTests E}{ψ':SmoothTests F}(hp:Transport.follows b (fun x=> U x+c) ψ ψ')(x:E) :
    readExpr M.basis (spectator Z v) (localImage M T (flow t g Q) o' a y ψ' (U x+c))= realChange b (readExpr M.basis (spectator Z v) (localImage M P Q o a z ψ x)):= by rw [← R.transports h a Q hp x, shift_reading _ hM]
lemma whole_travels (hM: M.rotation=Z.sector.turns)(hv:g.Nonempty)(a:ℝ)(v:Viewers Z){ψ:SmoothTests E}{ψ':SmoothTests F}(hp:Transport.follows b (fun x=> U x+c) ψ ψ')(x:E): kernel T q M y v o' a ψ' (U x+c)= realChange b (kernel P g M z v o a ψ x):= by have he:= aperture_travels R h hM a (root g) v hp x; rw [show flow t g (root g)=root q from summit t hv] at he; exact he
end Ribbon
end YM.Contacts.Transport
