import YM.Next.RANK.TableGate
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Wilson RG Value Perch Marker Glyph Cells Market Read Dock Camp Filter Station Extraction
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {m p k N v : ℕ}
variable {c : Demand} {z : ℝ} (A : Levels G) {i : ℕ}


variable {C : Family G}
lemma coughX (h : G.Simple) {b : ℝ} (hb : 0<b) (X : Points v) (hx : X∈conf _) (B : Fin v→ (standard C).Tag)(κ:ℕ→ℕ)(px:ℕ→ Points v) (hκ:Tendsto κ atTop atTop)(HP:Tendsto (fun i=> Station.tested C.path.levels b (κ i) (px i)) atTop (𝓝 X)) :
    ∀ᶠ k in atTop, sufficiently C B b (px k) (κ k) := by
  let Y := C.path.levels; let H := fun x : Points v => Read.maxProfile C x B
  let D := fun x => Exponential.roll (H x) (Fintype.card (Fin v))
  have ht : Tendsto (fun k => D (Station.tested Y b (κ k) (px k))) atTop (𝓝 (D X)) := by
    apply (Exponential.roll_cont _).continuousAt.tendsto.comp
      (profile_tends _ _ (Maxwell.table_smooth C.labels) (hx) HP)
  have he i : ∀ᶠ k : ℕ in atTop, ‖(D (Station.tested Y b (κ k) (px k))).part i‖ ≤ bill (1/4) (Y.clock.hatBeta (κ k)) := by
    have hx := ((tendsto_pi_nhds.1 ht i).norm).eventually (ge_mem_nhds (lt_add_one (‖(D X).part i‖)))
    filter_upwards [hx, ((bill_lo (a:=1/4) (by norm_num)).comp ((hat_rate Y h).comp hκ)).eventually_ge_atTop (‖(D X).part i‖+1)] with k hp hq
    exact le_trans hp hq
  filter_upwards [eventually_all.mpr he] with k hf hh p N hi j
  let T := Ship.yard C b hi p
  have hv := Read.cumulative C (tested Y b (κ k) (px k)) B (Ship.fitting hh)
  have hp : Ship.targets C B hh=D (tested Y b (κ k) (px k)) := Exponential.Expands.uniq hv (Exponential.rolls _ (Read.profile_vac _ (Maxwell.table_regular C.labels) _ (Ship.fitting hh) B))
  rw [hp,view]; unfold Array.reorient; split_ifs <;> simpa only [shade_part, Poly.part_neg,norm_star,norm_neg] using! hf j.2.val
end YM.Next.Rank.Peak
