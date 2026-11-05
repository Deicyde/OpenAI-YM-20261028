import YM.Next.RANK.Cadence
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Cadence for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value Finset MeasureTheory Edition Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {B : Side}
variable {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q D N d n a : ℕ}
variable {c r s ε e v : ℝ}

-- Geometry estimates. May use orders and supports only on comparison arcs.
structure ReadyShSky (s : ℝ) (X : AtlasData G A.S p) (d q k : ℕ) (R : Lead G A.S p) : Prop where
  canvas : roomTestSky A s k p d q
  withers i : middleSky A s k ≤ i → i<k → Mote (A:=A) R i
  gauge i : middleSky A s k ≤ i → i<k → Voice R i

variable {Y : AtlasData G C.S p} {F : Lead G C.S p}
variable (x : Points n) (P : Fin n→ C.label d)

-- h per stamp; same H and W clipping parameters for Gauge
section
variable {Q : Rep G (C.side k p)}
variable (M : StampDuty C k N p d D Q q Y) (R : ReadyShSky (A:=C.path.levels) s Y a q k F)

-- strong for all pennants, not just Cozy
include R

-- Initial W payload costs transferred unchanged, path transformations from Truth

omit R in
private lemma signet_hereSky {n : Side} (o : Site n) (j : ℝ) (P : Normal.poly (slotC G k)) (U : Config G n) : signet o j P U=signet 0 j P (pull 1 o U):= by
  unfold signet Spindle.curl registered; rw [s_translation]
lemma journeySky (hN : k≤N) (j : Fin n) (v : (Ship.yardSky C s hN p).Cell) (g : ℝ) (U : Config G (C.side k p)) :
    let A:= C.path.levels
    glorySky (C:=C) x s p hN le_rfl (beforeSky A s k) v (.inl j) g (jacketPol (s:=s) (F:=F) x P M le_rfl (.inl j)) U= dot ((Ship.yardSky C s hN p).hand v)
      (signet 0 g (M.W (P j)) (pull ((Ship.yardSky C s hN p).omega v) (seatsSky C s x hN p (v,j)) U)):= by
  intro A; simp only [glorySky, Function.comp_apply,jacketPol,polygon,oneRoot,center_shelf]
  let T:=Ship.yardSky C s hN p; let l:middleSky A s k≤k:=beforeSky ..; let a:= (Station.widerSky A s k).trans l; let u:= wrap (C.side k p) (Station.choose A s k x j)
  have hx : seatsSky C s x hN p (v,j)= affine (T.omega v) (spreadCSky C s p a v) u:= by
    let y:=core A x s p (k:=k) le_rfl j
    have hv:y=u:=homeHere ..; rw [← hv]; exact fillsSky C x s p hN le_rfl a _
  have hp : 8 ≤ q:= by linarith only [R.canvas.radius]
  unfold prefaced; rw [show core C.path.levels x s p le_rfl (headMark (Sum.inl j))=u from homeHere .., caseK Y _ k _ M.r g _ ?_, signet_hereSky u, watchesSky,pull_pull,mul_one,hx]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hp) _)) (R.canvas.suite k l le_rfl)
end

section
variable {n : Side} {V ι κ : Type} [Fintype V] [DecidableEq V]

end
-- Stamp

end YM.Next.Rank.Tapes
