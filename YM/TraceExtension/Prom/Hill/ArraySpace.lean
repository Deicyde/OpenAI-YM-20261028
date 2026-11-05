import YM.Next.RANK.ArraySpace
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.ArraySpace for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {V : Type}
variable {N k p v : ℕ} {b : ℝ}
variable (C : Family G) (X : Points v)

-- normalized separations uniform at arbitrary charged comparison stamps

lemma lengthTagSky (h : FitSky C.path.levels b k X) (p : ℕ) (i j):
    let A:=C.path.levels
    let s:= A.S.toDepth (beforeSky A b k) p
    8*(Station.choose A b k X i j).natAbs ≤ s.count.val := by
  -- physical tag deep
  intro A v
  let z:= Station.choose A b k X i j
  have hi := h.deep i j
  change |A.S.a k * (z:ℝ)|≤ _ at hi
  rw [abs_mul,abs_of_pos (A.S.a_pos k),← A.S.embeds_scale v] at hi
  have hh : A.S.a k*(8*|(z:ℝ)|) ≤ A.S.a k*v.count.val := by linarith only [hi]
  have ht := le_of_mul_le_mul_left hh (A.S.a_pos k)
  rw [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] at ht; exact_mod_cast ht

lemma at_depthSky (X : Points v) (b : ℝ) (hN : k≤N) (p : ℕ) (i : ListensSky C b (v:=v) hN p) :
    let A:= C.path.levels; let T:= Cells.center C.S p ((widerSky A b k).trans (beforeSky A b k)) 0; let x:= wrap (C.side k p) (Station.choose A b k X i.2)
    seatsSky C b X hN p i = affine (T.omega i.1) (T.translateBy i.1) x:= by
  intro A T x; unfold seatsSky Peak.readersSky; rw [exact_campSky]; exact (C.S.toDepth hN p).embed_parent _

end YM.Next.Rank.Edition
