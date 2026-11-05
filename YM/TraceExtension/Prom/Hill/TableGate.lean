import YM.Next.RANK.TableGate
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.TableGate for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Wilson RG Value Perch Marker Glyph Cells Market Read Dock Camp Filter Station Extraction
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {m p k N v : ℕ}
variable {c : Demand} {z : ℝ} (A : Levels G) {i : ℕ}

-- s length cap consumed uniformly at same fixed stage.

-- At the station take an unweighted W estimate, signed compensation from
-- negatively connected value. Use Cube locally through all gauges.
section
variable {b : ℝ} {hN : k ≤ N} {A}
variable {D : Rep G (A.S.side (middleSky A b k) p)}
variable (u : Shelf c m (A.clock.hatBeta k) (A.clock.hatBeta (middleSky A b k))) (ho : D.p.B=walls (A.clock.hatBeta (middleSky A b k)))
variable {F : Points v}

lemma warmingSky {ζ : Site (A.S.side (widthSky A b k) p) × Fin v → Site (A.S.side (middleSky A b k) p)}
    {W : Site (A.S.side (widthSky A b k) p) × flame (Fin v) → SourceAt G ζ}
    {C : Site (A.S.side (widthSky A b k) p) × flame (Fin v) → ℂ}
    (hv : v ≤ m) (hw : ∀ i,(W i).extent=Peak.routeSky A b k p c.Q D.p.B i.1)
    (hp : ∀ i,(W i).fires=sectionAt i)
    (hU : ∀ i U, Healthy D.p.threshold (Peak.routeSky A b k p c.Q D.p.B i.1) U →
      ‖(W i).value U+C i‖ ≤ bill (-31/32) (A.clock.hatBeta k))
    (hV : ∀ i, ‖C i‖ ≤ bill (1/4) (A.clock.hatBeta k)) : Wells (Meter A ho u) W C (Peak.routeSky A b k p c.Q D.p.B) := by
  let e := c.e; let s := A.clock.hatBeta k; let g := c.Q; let Y := Meter A ho u
  have he (i : Site (A.S.side (widthSky A b k) p) × flame (Fin v)) {e : ℝ} (he : 0≤e) : charge D.p e (Peak.routeSky A b k p g D.p.B i.1) * Poly.toll (fun _ => Y.radius) (sectionAt i) ≤
      Real.exp (e*((g+g+1:ℕ):ℝ)^4)*bill (1/8) s := mul_le_mul (charged_cube g he _) (aperture _ ho u i (by simpa using hv))
        (Poly.worth (fun _ => Y.pos_r) _).le (Real.exp_pos _).le
  have hz (e : ℝ) : 0 ≤ Real.exp (e*((g+g+1:ℕ):ℝ)^4)*bill (1/8) s := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  refine ⟨hp,hw, fun i U hh => (mul_le_mul (he i Y.base) (hU i U hh) (norm_nonneg _) (hz _)).trans u.wakes, ?_⟩
  intro i; exact (mul_le_mul (he i (add_nonneg Y.base zero_le_one)) (hV i) (norm_nonneg _) (hz _)).trans u.tree
end

variable {C : Family G} {X : Points v}

/-- D prices bounded uniformly on planned generic rounding. -/
def sufficientlySky (C : Family G) (B : Fin v→(standard C).Tag) (b : ℝ) (X : Points v) (k : ℕ) :=
    ∀ h : FitSky C.path.levels b k X, ∀ p N (hi : k ≤ N) i,
      ‖view (Ship.yardSky C b hi p) (Ship.targetsSky C B h) i‖≤ bill (1/4) (C.path.levels.clock.hatBeta k)

end YM.Next.Rank.Peak
