import YM.MergeProof.West.Mooncake
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Pilgrim
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Labels Price Prayer Glimmer Rise Perch  Beamer Cells Common Normal Filter Marker Glyph Exponential Read Configuration Particle
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ}

variable {d0:Fin n→ℕ} (v:(i:Fin n)→ C.label (d0 i))

variable {Y : AtlasData G C.S p}

variable {x : Points n} {b : ℝ} (g : FitSky C.path.levels b k x) (degree : ℕ)
variable {Z : (i:Fin n)→ Heater C k (d0 i)} {T : (i:Fin n)→ Module.End ℂ (C.label (d0 i))}

theorem sizesXSky (hY:∀ i,d0 i ≤ d) (hN : k≤N) (D : ∀ i, Heating C k N p (d0 i) degree (Z i) (T i)) (h : BellSky C.path.levels Y d degree g)
    (m : Chamber G C.S (middleSky C.path.levels b k) p→ℝ) (hm : Wind C.path.levels m (fraction n degree (clim C.path.levels k)))
    (H : passingX hY v k degree b) (u : (i:Fin n)→ C.label (d0 i)) (hU : ∀ i,Price.Solves C (mag C.path.levels b k) (d0 i) k N p (T i) (v i) (u i))
    (hs :
      let s:=clim C.path.levels k
      Meridian d (Ship.fittingSky g) (G:=G) (fraction n degree s) (fraction n degree s) (bill (-3) s) (bill (fuel degree n) s)
        (bill (-2) s) (Station.mag C.path.levels b k) (lengthW s)) (q : Glyph.modes (Fin n)) :
    let A:= C.path.levels
    let w:= Station.choose A b k x
    ‖(Answer Y w (beforeSky A b k) (fun i => Z i (u i)) (fun x => (m x:ℂ))).part q-(Read.maxProfile C (Station.tested A b k x) (jointX v)).part q‖ ≤ bill (-3/2) (clim A k) := by
  intro A w
  obtain ⟨U,hB,hc,hF,h₁⟩ := H N p hN Z T D u hU
  let M₀ := lengthW (clim A k)
  let l := Station.middleSky A b k
  let g₀ := (Subtype.val : trimV M₀ G → _)
  let Γ:= Γre A.S Y w (beforeSky A b k)
  let μ:= μre A.S Y w (beforeSky A b k) (fun x => (m x:ℂ))
  let K:= Γs A Y w (beforeSky A b k)
  let r:= mag A b k
  let Q := Qmarks Y w (beforeSky A b k); let U' := noise Y w (beforeSky A b k) (fun x => (m x:ℂ))
  let f := fun i : Fin n × trimV M₀ G => (i.1,i.2.val)
  let S := primary d g₀ r Γ K
  let V := Beamer.seen d g₀ r μ
  let L := Normal.perSlot (fun _ : Fin n => features d g₀ r)
  have hT : Normal.scope (fun i => Finsupp.single (f i) 1) Q=Normal.scope L S := by
    have ht : Normal.scope L S=prize g₀ Γ K := shaped d g₀ r Γ K (zero_lt_one.trans_le h₁.radius)
    rw [ht]; apply Normal.Symmetric.ext; funext i j; rw [Normal.match_name f]; exact (h.validQ ..).symm
  have hv : U' ∘ f= Normal.reads L V := by
    funext i; rw [show Normal.reads L V i= _ from scanned d g₀ r μ i (zero_lt_one.trans_le h₁.radius)]
    exact (h.validM m hm _).symm
  let X' := Prayer.Reads d (Ship.fittingSky g) r Γ μ
  have hh := Prayer.resolution d (Ship.fittingSky g) r _ hs g₀ (fun i => (tracing ..).1 i.property) Γ μ K (h.verdict m hm)
  rw [Answer_part, stagesX _ hY _ (Ship.fittingSky g),← hF]
  exact Particle.acuity h₁ (Ship.fittingSky g) S V q _ _ hT hv (hB ▸ hh.1) (hB ▸ hc ▸ hh.2)
end YM.Next.Rank.Atlas
