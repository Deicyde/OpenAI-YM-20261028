import YM.Next.RANK.Memorandum
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.Memorandum for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Wilson RG MeasureTheory Marker Glyph Exponential Cells Station Value Camp Dock Read Finset Filter
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V]

-- independent of curvature prediction. oriented D in Wells already has this sign.

section
variable {C : Family G} {k i N p m v : ℕ} {b : ℝ}
variable {d : widthSky C.path.levels b k ≤ N} {T : Tiling (C.side N p)} (Y : Course C N p k)

-- fixed stencil cube at stop. current ancestors always included.

def routeSky (A : Levels G) (b : ℝ) (k p : ℕ) (Q B : ℕ) (j : Site (A.S.side (widthSky A b k) p)) := halo (Q*B) {(A.S.toDepth (widerSky A b k) p).embed j}

def readersSky (x : Points v) (hN : k ≤ N) (hi : i ≤ N) : (Ship.yardSky C b hN p).Cell × Fin v → Site (C.side i p) :=
    fun z => ancestor C.S p i hi (stampSiteSky C b x hN p z)

lemma alignedSky (A : Levels G) (p : ℕ) {k B Q : ℕ} (H : AllowedSky A b k)
    (hP : B^2+2*(Q*B) ≤ (A.clock.coverSize k)^10) i j (hi : i ≠ j) : ∀ x ∈ routeSky A b k p Q B i,
      ∀ y∈routeSky A b k p Q B j, B^2 ≤ separation x y := by
  let S := A.S.toDepth (widerSky A b k) p
  intro x hx y hy
  obtain ⟨s,h1,h2⟩ := halo_spec.mp hx
  obtain ⟨t,h3,h4⟩ := halo_spec.mp hy
  rw [mem_singleton] at h1 h3; change s=S.embed i at h1; change t=S.embed j at h3; rw [← separation_comm] at h4
  have he : S.count.val ≤ separation s t := h1 ▸ h3 ▸ by
    rw [both]; exact Nat.le_mul_of_pos_right _ (separation_pos i j hi)
  have hv := separation_triangle s x t; have hb := separation_triangle x y t
  have hg : B^2+2*(Q*B) ≤ S.count.val := hP.trans (H.surplusage p); omega

lemma alignmentSky (_Y : Course C N p k) {x : Points v} (hN : k ≤ N) (hA : AllowedSky C.path.levels b k) (hx : FitSky C.path.levels b k x)
    {B Q : ℕ} (hb : 8≤B)
    (hh : B^2+2*(Q*B) ≤ (C.path.levels.clock.coverSize k)^10) :
    rearranged (readersSky (C:=C) (b:=b) (p:=p) x hN ((beforeSky _ b k).trans hN)) (routeSky C.path.levels b k p Q B) B := by
  refine ⟨fun i => ?_,hb,fun i j hp => alignedSky C.path.levels p hA hh i j hp.symm⟩
  unfold readersSky; rw [hx.stop]; exact halo_spec.mpr ⟨_,mem_singleton_self _,by simp⟩

variable {D : Rep G (C.side (middleSky C.path.levels b k) p)} (J : Change D.p m)

/-- Contributions at middle chamber cut. Inputs are still *uncorrected*. -/
def AuroraSky {x : Points v} (Q : ℕ) (Y : Course C N p k) (hN : k ≤ N) (t : Fin v→ C.book.Token)
    (B : Fin v → (standard C).Tag) (hx : FitSky C.path.levels b k x) : Prop :=
    let T := Ship.yardSky C b hN p
    let A := C.path.levels
    let P := routeSky A b k p Q D.p.B
    let read := Ship.clients C t b k N p x
    let F := Ship.targetsSky C B hx
    let HI : middleSky A b k ≤ N := (beforeSky A b k).trans hN
    let u := readersSky (C:=C) (b:=b) (p:=p) x hN HI
    ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ), ∃ (H : ι → SourceAt G u)
      (K : κ → Lifted G u D.p.threshold) (W : T.Cell × flame (Fin v) → SourceAt G u),
      Wells J W (view T F) P ∧ Reception J H K ∧ Background D K ∧
        Y.flow (Array.stamp T (C.beta N p) (bareP read)) _ HI = dust D (Sum.elim H W) K

theorem launchedSky {x : Points v} (Q : ℕ) (Y : Course C N p k) (hN : k ≤ N) (t : Fin v → C.book.Token)
    (B : Fin v → (standard C).Tag) (hx : FitSky C.path.levels b k x) (ha : AllowedSky C.path.levels b k)
    (hm : v ≤ m) (hu : AuroraSky J Q Y hN t B hx)
    (hb : 8≤D.p.B) (hh : D.p.B^2+2*(Q*D.p.B)≤(C.path.levels.clock.coverSize k)^10) :
    let A := C.path.levels
    let T := Ship.yardSky C b hN p
    let l := middleSky A b k
    let HI : l ≤ N := (beforeSky A b k).trans hN
    let X := Array.stamp T (C.beta N p) (Ship.invoiceSky B t hx N p)
    Notice D (readersSky (C:=C) (b:=b) (p:=p) x hN HI) (Y.flow X l HI) (fun _ => J.radius) J.e J.output J.hail := by
  intro A T l HI X
  obtain ⟨ι,κ,hι,hκ,H,K,W,hW,h,hB,hD⟩ := hu
  let F := Ship.targetsSky C B hx
  let u := bareP (Ship.clients C t b k N p x)
  have hz : F.part (quiet _)=0 := (Read.cumulative C (Station.tested C.path.levels b k x) B _).1
  have hc : ∀ i : modes (Fin v),Continuous fun U => (u U).part i := raw_cont _ (fun i => Read.probes_cont i)
  have hv : Y.flow X l HI= fun U => Poly.pass (Array.tilt T F)*dust D (Sum.elim H W) K U := by
    change Y.flow (Array.stamp T (C.beta N p) (fun z => Poly.pass (-F)*u z)) l HI=_
    rw [Array.flow_corr _ _ T hc F hz]; exact funext fun U => congr_arg (Poly.pass _ * ·) (congr_fun hD U)
  rw [hv,catches T F hz]; have hy (i : T.Cell × flame (Fin v)) : sectionAt i = (W i).fires := (hW.lit i).symm
  simp_rw [hy]; exact Dock.grant J (by simpa only [Fintype.card_fin] using hm) (alignmentSky Y hN ha hx hb hh) hW h hB
end
end YM.Next.Rank.Peak
