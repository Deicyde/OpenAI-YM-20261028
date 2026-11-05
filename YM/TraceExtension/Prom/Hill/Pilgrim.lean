import YM.Next.RANK.Pilgrim
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.Pilgrim for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Labels Price Prayer Glimmer Rise Perch  Beamer Cells Common Normal Filter Marker Glyph Exponential Read Configuration Particle
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ} (v : Fin n→ C.label d)

-- pins are gathered ON a real coarse-lattice endpoint input. It fits inside near-test ranges.
section
variable (P : Levels G) (X : AtlasData G P.S p)
variable {w : Fin n → Cover} {l : ℕ} {hi : l≤ k}

-- gauge amplitude permitted at l. `Bell` expects every such Y (and closure can be required on full torus through wrapping), reuse same m for all local subsets.

/-- Finite miscompare gates on kernels. Supports are true native l/k levels. At A k root require universal over Wind (on each pulled orientation inquiry). -/
structure BellSky {b : ℝ} (d : ℕ) {x : Points n} (deg : ℕ) (hx : FitSky P b k x) : Prop where
  validQ i j :
    let Q := Qmarks X (Station.choose P b k x) (beforeSky P b k)
    ((Q.cov i j).re:ℂ)=Q.cov i j
  validM (m : Chamber G P.S (middleSky P b k) p→ℝ) : Wind P m (fraction n deg (clim P k)) → ∀ i,
    let u:= noise X (Station.choose P b k x) (beforeSky P b k) (fun x => (m x:ℂ)) i
    (u.re:ℂ)=u
  verdict (m : Chamber G P.S (middleSky P b k) p → ℝ) (h : Wind P m (fraction n deg (clim P k))) :
    let f := Station.choose P b k x
    Reads d (Ship.fittingSky hx) (mag P b k) (Γre P.S X f (beforeSky P b k))
      (μre P.S X f (beforeSky P b k) (fun x => (m x:ℂ))) (lengthW (clim P k)) (fraction n deg (clim P k)) (bill (-3) (clim P k))
end

variable {Y : AtlasData G C.S p}

variable {x : Points n} {b : ℝ} (g : FitSky C.path.levels b k x) (degree : ℕ)
variable {Z : Heater C k d} {T : C.label d→ₗ[ℂ] C.label d}

end YM.Next.Rank.Atlas
