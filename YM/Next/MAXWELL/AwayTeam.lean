import YM.Next.MAXWELL.Beacon
import YM.Next.MAXWELL.Depth
import YM.Next.MAXWELL.Quarters


/-!
# Internal finite Ward test on Bel

At degree 4 commute a few actual signed axis motions using the exact
metric at all directions and the House matrix. Force the low defect,
then use the local angular flux to propagate across the full bounded
weights. No compact gauges secretly acting as spatial rotations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open Ortho Org Climb
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} (F : Labels.Frames G) {d n : ℕ}

lemma circle_ode (v : Ortho.Skew) (x : (Model F).Field d) (t : ℝ) : HasDerivAt
    (fun s => (gear F).act d (oneParameter v s) x) ((gear F).lie d v ((gear F).act d (oneParameter v t) x)) t := by
  have hd := (gear_port F).spinAt d v ((gear F).act d (oneParameter v t) x)
  have hi : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const _
  simpa only [Function.comp_def,one_smul, ← (gear_port F).sends, ← Corners.fact, sub_add_cancel] using
    hd.scomp_of_eq t hi (by simp)

lemma complete_turn {T : Module.End ℂ ((Model F).Field d)}
    (h : ∀ u p,(gear F).lie d u (T p)=T ((gear F).lie d u p))
    (i j : Axis) (he : i≠j) (p : (Model F).Field d) :
    (gear F).act d (Corners.quarter i j).ortho (T p) = T ((gear F).act d (Corners.quarter i j).ortho p) := by
  let u := Ortho.plane i j
  let f := fun s => (gear F).act d (oneParameter u s)
  let A t := f t (T p)
  let C t := T (f t p)
  let M := ((gear F).lie d u).toContinuousLinearMap
  let L := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  have hp (s) : HasDerivAt A (M (A s)) s := circle_ode F u _ _
  have ht (s : ℝ) : HasDerivAt C (M (C s)) s := by
    change HasDerivAt C ((gear F).lie d u (T _)) s
    rw [h]; exact L.hasFDerivAt.comp_hasDerivAt s (circle_ode F u p s)
  rw [Corners.sendsTime i j he]
  exact congr_fun (ODE_solution_unique_univ (s := fun _ => Set.univ) (fun (_ : ℝ) => M.lipschitz.lipschitzOnWith)
    (fun t => ⟨hp t, mem_univ _⟩) (fun t => ⟨ht t,mem_univ _⟩) (show A 0=C 0 from by
      simp [A,C,f,Work.A13.oneParameter_zero,(gear_port F).fixes])) _

theorem erasing (h : G.Simple) : erases (hierarchy F).spin (scheme F) := by
  refine ⟨4,?_⟩
  intro d hd T H W
  let P u v := brand F (d:=d) (T u v)
  let R := (scheme F).rise hd
  have hw u v : silence G d (P u v) := (branded F _).mp (fun n w x hx => W n x hx u v w)
  have ht (u v) (p : (Model F).Field 4) : T u v (R p)∈LinearMap.range R := H.rises _ hd u v p
  have hs u v : ∀ p∈ shellSector G 4, P u v p∈shellSector G 4 := by
    intro p hp
    let x := wrap F hp
    obtain ⟨y,hy⟩ := ht u v x
    have heq : address F d (R x)=p := by rw [show address F d (R x)= _ from address_rise ..,shed F hp]
    rw [← heq,show P u v (address F d (R x)) = _ from brand_eval ..,← hy]
    rw [show address F d (R y)=_ from address_rise ..]; exact address_in F _ _
  have hr (p : (Model F).Field 4) (u v) (i j : Axis) (he : i≠j) :
      let k := Corners.quarter i j
      (gear F).act d k.ortho (T u v (R p)) = T u v ((gear F).act d k.ortho (R p)) := by
    intro k; apply address_inj F d
    let x := basis i + basis j
    have hX : 0 < ‖x‖ := norm_pos_iff.mpr (show x≠0 from fun hh => by
      have hy := congr_arg (fun u : E4 => u i) hh; simp [x,he] at hy)
    have hp : address F d (R p) ∈ shellSector G 4 := by rw [address_rise]; exact address_in ..
    have h := low_motion h hd (hw u v) (hs u v) i hX (v:=x) rfl hp
    have hb : house (-‖x‖ • basis i)*house x=k.ortho := Corners.quarter_house i j he _ hX
    dsimp only at h; rw [hb,show P u v (address F d (R p)) = _ from brand_eval ..,
      ← paints_gear, ← paints_gear,show P u v (address F d ((gear F).act d k.ortho (R p)))=_ from brand_eval ..] at h; exact h
  have hi (u v) (i j : Axis) (he : i ≠ j) (p : (Model F).Field d) :
      let k := Corners.quarter i j
      (gear F).act d k.ortho (T u v p)=T (orients k u) (orients k v) ((gear F).act d k.ortho p) := by
    intro k; rw [(gear_port F).signed,(gear_port F).signed]; exact H.polar k (Corners.proper i j he) u v p
  have ha x u v : T u v (R x)=0 := by
    let L : Ortho.Skew →ₗ[ℝ] Ortho.Skew →ₗ[ℝ] (Model F).Field d :=
      { toFun s :=
          { toFun t := T s t (R x)
            map_add' h k := by rw [map_add]; rfl
            map_smul' t k := by simp only [map_smul]; rfl }
        map_add' s t := by ext1 u; rw [map_add]; rfl
        map_smul' k t := by ext1 u; rw [map_smul]; rfl }
    have he : L=0 := by
      refine Corners.none L (fun a => LinearMap.congr_fun (H.alt a) _) ?_
      intro i j u v he
      let k := Corners.quarter i j
      obtain ⟨p,hx⟩ := ((gear F).act 4 k.ortho).surjective x
      have hh := hi u v i j he (R p)
      have ht : (gear F).act d k.ortho (R p)=R x := by rw [(gear_laws F).filtered,hx]
      change _= T (orients k u) (orients k v) ((gear F).act d k.ortho (R p)) at hh
      rw [ht,show (gear F).act d k.ortho _ = _ from hr p u v i j he, ht] at hh
      exact hh.symm
    change L u v = _; rw [he]; rfl
  have hp u v a b : P u v (polStress G a b)=0 := by
    calc
      _ = address F d (T u v (R (original F a b))) := by rw [← brand_eval,address_rise,inertia]
      _ = _ := by rw [ha,map_zero]
  apply Corners.none T H.alt
  intro a b u v hb; apply LinearMap.ext; intro p
  let k := Corners.quarter a b
  obtain ⟨p,rfl⟩ := ((gear F).act d k.ortho).surjective p
  rw [← show (gear F).act d k.ortho _=_ from (hi u v a b hb p)]
  refine complete_turn F ?_ a b hb p
  intro s p
  let f := address F d p
  have hg := address_in F d p
  have hS (n) (x : Points (n+1)) (hx : x∈ conf _) :
      ∃ χ V,Table.Window x χ ∧ Motion (x:=x 0) (l:=0) V (wheel G s) χ := by
    obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx; exact ⟨χ,_,hχ,rotational_motion hχ.1 hχ.2.1 hχ.2.2.1 s⟩
  have he := sub_eq_zero.mp (ghosts_out (Submodule.sub_mem _ (wheel_holds s (brand_fit F (T u v) f)) (brand_fit F (T u v) _))
    (commute_ghost hd (hw u v) (hp u v) hS f hg (wheel_holds _ hg)))
  apply address_inj F d
  change address F d (scopeRise F d s _)=address F d (T u v (scopeRise F d s p))
  rw [scopeRewrite,← brand_eval,← brand_eval,scopeRewrite]
  exact he
end YM.Maxwell.Free
