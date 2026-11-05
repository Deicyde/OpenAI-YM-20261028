import YM.Bid.Loan
import YM.Next.RANK.Allowance
import YM.Next.RANK.Dock


/-!
# Middle-output uses actual ancestors

$B=M_l^2$ used as actual current cover radius for Rep budget on the restarted
run; no identifications with a different ancestor site. Relate W to oriented
minus target in `tilt` using every local mode. Geometric equality is by Fit.stop,
no assumption about independent offsets on reflected copies. Price W closeness
on good cube implies Wells with explicit expenditures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Wilson RG MeasureTheory Marker Glyph Exponential Cells Station Value Camp Dock Read Finset Filter
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V]

lemma parts (C : veil V) (h : C.part (quiet _)=0) :
    C=∑ i : flame V, Poly.send i.val (C.part i.val) := by
  -- vacuum term is zero
  have he := sum_image (g:=Subtype.val) (s:=(univ : Finset (flame V))) Subtype.val_injective.injOn
    (f:=fun i : modes V => Poly.send i (C.part i))
  refine (Poly.studs C).symm.trans ((_root_.Eq.trans ?_ he))
  symm; apply sum_subset (subset_univ _); intro i hi hp
  by_cases hq : i.val.Nonempty
  · exact False.elim (hp (mem_image.mpr ⟨⟨i,hq⟩,mem_univ _,rfl⟩))
  have hz : i=quiet _ := Subtype.ext (not_nonempty_iff_eq_empty.mp hq); subst i; rw [h,Poly.send_zero]

-- independent of curvature prediction. oriented D in Wells already has this sign.

def view (T : Tiling n) (C : veil V) : T.Cell × flame V → ℂ := fun i => (Array.reorient T i.1 (-C)).part i.2.val

lemma catches (T : Tiling n) (C : veil V) (h : C.part (quiet _)=0) :
    Array.tilt T C=∑ i : T.Cell × flame V, Poly.send (sectionAt i) (view T C i) := by
  rw [Fintype.sum_prod_type]; unfold Array.tilt; apply sum_congr rfl; intro i _
  have he : (Array.reorient T i (-C)).part (quiet _) = 0 := by unfold Array.reorient; split <;> simp [h]
  refine (congr_arg (Glyph.insertAt i) (parts (Array.reorient T i (-C)) he)).trans ?_
  rw [map_sum]; simp_rw [insert_send]; rfl

section
variable {C : Family G} {k i N p m v : ℕ} {b : ℝ}
variable {d : width C.path.levels b k ≤ N} {T : Tiling (C.side N p)} (Y : Course C N p k)

-- fixed stencil cube at stop. current ancestors always included.

def route (A : Levels G) (b : ℝ) (k p : ℕ) (Q B : ℕ) (j : Site (A.S.side (width A b k) p)) := halo (Q*B) {(A.S.toDepth (wider A b k) p).embed j}

def readers (x : Points v) (hN : k ≤ N) (hi : i ≤ N) : (Ship.yard C b hN p).Cell × Fin v → Site (C.side i p) :=
    fun z => ancestor C.S p i hi (stampSite C b x hN p z)

lemma aligned (A : Levels G) (p : ℕ) {k B Q : ℕ} (H : Allowed A b k)
    (hP : B^2+2*(Q*B) ≤ (A.clock.coverSize k)^10) i j (hi : i ≠ j) : ∀ x ∈ route A b k p Q B i,
      ∀ y∈route A b k p Q B j, B^2 ≤ separation x y := by
  let S := A.S.toDepth (wider A b k) p
  intro x hx y hy
  obtain ⟨s,h1,h2⟩ := halo_spec.mp hx
  obtain ⟨t,h3,h4⟩ := halo_spec.mp hy
  rw [mem_singleton] at h1 h3; change s=S.embed i at h1; change t=S.embed j at h3; rw [← separation_comm] at h4
  have he : S.count.val ≤ separation s t := h1 ▸ h3 ▸ by
    rw [both]; exact Nat.le_mul_of_pos_right _ (separation_pos i j hi)
  have hv := separation_triangle s x t; have hb := separation_triangle x y t
  have hg : B^2+2*(Q*B) ≤ S.count.val := hP.trans (H.surplusage p); omega

lemma alignment (_Y : Course C N p k) {x : Points v} (hN : k ≤ N) (hA : Allowed C.path.levels b k) (hx : Fit C.path.levels b k x)
    {B Q : ℕ} (hb : 8≤B)
    (hh : B^2+2*(Q*B) ≤ (C.path.levels.clock.coverSize k)^10) :
    rearranged (readers (C:=C) (b:=b) (p:=p) x hN ((before _ b k).trans hN)) (route C.path.levels b k p Q B) B := by
  refine ⟨fun i => ?_,hb,fun i j hp => aligned C.path.levels p hA hh i j hp.symm⟩
  unfold readers; rw [hx.stop]; exact halo_spec.mpr ⟨_,mem_singleton_self _,by simp⟩

variable {D : Rep G (C.side (middle C.path.levels b k) p)} (J : Change D.p m)

/-- Contributions at middle chamber cut. Inputs are still *uncorrected*. -/
def Aurora {x : Points v} (Q : ℕ) (Y : Course C N p k) (hN : k ≤ N) (t : Fin v→ C.book.Token)
    (B : Fin v → (standard C).Tag) (hx : Fit C.path.levels b k x) : Prop :=
    let T := Ship.yard C b hN p
    let A := C.path.levels
    let P := route A b k p Q D.p.B
    let read := Ship.clients C t b k N p x
    let F := Ship.targets C B hx
    let HI : middle A b k ≤ N := (before A b k).trans hN
    let u := readers (C:=C) (b:=b) (p:=p) x hN HI
    ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ), ∃ (H : ι → SourceAt G u)
      (K : κ → Lifted G u D.p.threshold) (W : T.Cell × flame (Fin v) → SourceAt G u),
      Wells J W (view T F) P ∧ Reception J H K ∧ Background D K ∧
        Y.flow (Array.stamp T (C.beta N p) (bareP read)) _ HI = dust D (Sum.elim H W) K

theorem launched {x : Points v} (Q : ℕ) (Y : Course C N p k) (hN : k ≤ N) (t : Fin v → C.book.Token)
    (B : Fin v → (standard C).Tag) (hx : Fit C.path.levels b k x) (ha : Allowed C.path.levels b k)
    (hm : v ≤ m) (hu : Aurora J Q Y hN t B hx)
    (hb : 8≤D.p.B) (hh : D.p.B^2+2*(Q*D.p.B)≤(C.path.levels.clock.coverSize k)^10) :
    let A := C.path.levels
    let T := Ship.yard C b hN p
    let l := middle A b k
    let HI : l ≤ N := (before A b k).trans hN
    let X := Array.stamp T (C.beta N p) (Ship.invoice B t hx N p)
    Notice D (readers (C:=C) (b:=b) (p:=p) x hN HI) (Y.flow X l HI) (fun _ => J.radius) J.e J.output J.hail := by
  intro A T l HI X
  obtain ⟨ι,κ,hι,hκ,H,K,W,hW,h,hB,hD⟩ := hu
  let F := Ship.targets C B hx
  let u := bareP (Ship.clients C t b k N p x)
  have hz : F.part (quiet _)=0 := (Read.cumulative C (Station.tested C.path.levels b k x) B _).1
  have hc : ∀ i : modes (Fin v),Continuous fun U => (u U).part i := raw_cont _ (fun i => Read.probes_cont i)
  have hv : Y.flow X l HI= fun U => Poly.pass (Array.tilt T F)*dust D (Sum.elim H W) K U := by
    change Y.flow (Array.stamp T (C.beta N p) (fun z => Poly.pass (-F)*u z)) l HI=_
    rw [Array.flow_corr _ _ T hc F hz]; exact funext fun U => congr_arg (Poly.pass _ * ·) (congr_fun hD U)
  rw [hv,catches T F hz]; have hy (i : T.Cell × flame (Fin v)) : sectionAt i = (W i).fires := (hW.lit i).symm
  simp_rw [hy]; exact Dock.grant J (by simpa only [Fintype.card_fin] using hm) (alignment Y hN ha hx hb hh) hW h hB
end
end YM.Next.Rank.Peak
