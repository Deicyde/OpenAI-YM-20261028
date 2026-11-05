import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Enamel
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Pitch
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.RoofTile


/-! # Doing the local comparison itself

Not from any periodic analyticity/wave/currents assumptions. Paid functions and cylinders
are shared including auxiliary Lift of external sources. Intertwined motions
and test, not just scalar equality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Enrobe
open Jacobi Macrame Macrame.Lace Polytrace Withdrawal  Enamel Function Lattice Gauge RG Tree Matrix Finset Precision Filter Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch
open scoped Topology ContDiff BigOperators Classical
variable {c C f F : Side} {P : Patch} (Q : KernelChoices)
  {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {M : ℕ} {G : Gauge} (hC : C.val=c.val*M) (he : 2 ≤ c.val)
variable (T : Forest (decreed h))
local notation "L" => Macrame.Lace.project (h:=h) (H:=H) hC he
local notation "BU" => circuit (H:=H) hC he T
local notation "CB" => crown (H:=H) hC he T
local notation "Ψ" => Macrame.Lace.Fitted.narrow L (G:=G)

-- period script fully covariant
lemma assesses (p : Clip) (R : PathData G) :
    Shelter Ψ ((CB).track)
      (Uniform.priced (S:=stepped Q h) T (plain Q (h:=h)) p R)
      (Uniform.priced (S:=stepped Q H) BU (plain Q (h:=H)) p R) (M^4) := by
  let Y := L; let X := BU
  have hm {α β : Type} [Fintype β] [Fintype α] (e : β → α) (hF : Fold e 1) : Injective e := by
    have hs : Surjective e := by
      intro i; obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (parcel e i).card from (by rw [hF i]; norm_num)); exact ⟨j,(posted _ _ _).mp hj⟩
    exact ((Fintype.bijective_iff_surjective_and_card e).mpr ⟨hs,by simpa using received e hF⟩).1
  refine ⟨(CB).tree_keys _, ?_,?_⟩
  · intro x; exact Fitted.appraisal Q CB x (plain Q (h:=h)) p R
  intro x y h
  obtain ⟨w,hw,hs⟩ := rim hC he T x y h
  let E := Macrame.Lace.edge (H:=H) hC he w
  let S := fibers (H:=H) hC he T hw
  refine ⟨Macrame.Lace.Fitted.narrow E,S.track, hm _ (S.tree_keys _),hs,flange (H:=H) hC he T hw,?_⟩
  intro u; have ht := S.appraisal Q u (Macrame.Lace.plain Q (h:=H)) p R; erw [Macrame.Lace.plain_binding] at ht
  rw [Nat.cast_one,one_mul] at ht; exact ht

lemma analytic_ground {g : Gauge} {n m : Side} {X : StepData m n} {t : X.Choices} {F : Forest X.ratio} {p : Clip} {R : PathData g}
    {u : In g m → AxisChart g F} (h : Critical F p R u) : ContDiffAt ℝ ω (Uniform.priced F t p R) 0 :=
    (show ContDiffAt ℝ ω (uncurry (tested F t p R)) (paint F g 0) from by rw [map_zero]; exact (h.2.2 t).1).comp (f:=paint F g) 0 (paint F g).contDiff.contDiffAt

-- all service asks at large; smaller need only Critical (inc originating from OnShell)
local notation "X" => Positions (Primary c G)
local notation "Y'" => Positions (Primary C G)
variable {R : PathData G} {μ B Λ : ℝ} {j n : ℕ} {p : Clip} {A : Push.Uniform.Before G μ B j Q n}
    {u : In G c → AxisChart G T} {U : Forest (decreed H)} {v : In G C → AxisChart G U} (cb : (Macrame.Lace.project (h:=h) (H:=H) hC he).Fitted T U)
    (hu : Critical (S:=stepped Q h) T p R u) (hv : A.Service (S:=stepped Q H) U p R v)
include cb hu hv hC he T

lemma cover_germ (hx : Shelter (Macrame.Lace.Fitted.narrow (Macrame.Lace.project (h:=h) (H:=H) hC he) (G:=G)) cb.track (Uniform.priced (S:=stepped Q h) T (plain Q) p R) (Uniform.priced (S:=stepped Q H) U (plain Q) p R) (M^4)) :
    let g := @Uniform.station G c _ (stepped Q h) T u; let g' := @Uniform.station G C _ (stepped Q H) U v; let t := Lace.plain Q (h:=H)
    ∀ᶠ x : Positions (Primary c G) in 𝓝 0,
      let y := onpass (Macrame.Lace.Fitted.narrow (Macrame.Lace.project (h:=h) (H:=H) hC he) (G:=G)) x
      g' y = onpass cb.track (g x) ∧ Every cb.track (trend (S:=stepped Q H) U t p R v y) (trend (S:=stepped Q h) T (plain Q (h:=h)) p R u x) := by
  let K := cb.track (G:=G); let d := onpass (Macrame.Lace.Fitted.narrow (Macrame.Lace.project (h:=h) (H:=H) hC he) (G:=G))
  let t := plain Q (h:=h)
  intro g g' t'
  have hT : 0<M^4 := pow_pos (Nat.pos_of_mul_pos_left (show 0<c.val*M from hC ▸ C.property)) _
  let f := Uniform.priced (S:=stepped Q h) T t p R -- shadows f side? close
  let F₀ := Uniform.priced (S:=stepped Q H) U t' p R
  change Shelter Ψ K f F₀ (M^4) at hx
  let Y := A.tables p P; let b := onpass K
  let Z := (curve g); let Z' (x:Positions (Primary c G)) := meetVar (d x) (b (g x))
  let Lx := tint G (Body 1 c); let Ly := tint G (Body 1 C); let Lz := tint G (U).Free
  have ht : Tendsto Lx (𝓝 0) (𝓝 0) := map_zero Lx ▸ Lx.continuous.continuousAt.tendsto
  have hZ : Tendsto g (𝓝 0) (𝓝 0) := by
    let Lv := (tint G T.Free).symm
    have hg : Tendsto Lv (𝓝 0) (𝓝 0) := map_zero Lv ▸ Lv.continuous.continuousAt.tendsto
    have he : Tendsto u (𝓝 0) (𝓝 0) := hu.1 ▸ hu.2.1.continuousAt.tendsto
    exact hg.comp (he.comp ht)
  have hs : Tendsto Z (𝓝 0) (𝓝 0) := by
    let l := (partSpace (Primary c G) (Key T G)).symm
    have hr : Tendsto l (𝓝 0) (𝓝 0) := map_zero l ▸ l.continuous.continuousAt.tendsto
    exact hr.comp (tendsto_id.prodMk_nhds hZ)
  have hb : Tendsto d (𝓝 0) (𝓝 0) := map_zero d ▸ d.continuous.continuousAt.tendsto
  have hg : Tendsto (b ∘ g) (𝓝 0) (𝓝 0) := (show Tendsto b (𝓝 0) (𝓝 0) from map_zero b ▸ b.continuous.continuousAt.tendsto).comp hZ
  have hs' : Tendsto Z' (𝓝 0) (𝓝 0) := by
    let l := (partSpace (Primary C G) (Key U G)).symm
    exact (show Tendsto l (𝓝 0) (𝓝 0) from map_zero l ▸ l.continuous.continuousAt.tendsto).comp (hb.prodMk_nhds hg)
  have hf := analytic_ground (t:=t) hu
  have hF := analytic_ground (t:=t') hv.critical
  change ContDiffAt ℝ ω F₀ 0 at hF
  filter_upwards [hs.eventually (hf.eventually (by simp)), hs'.eventually (hF.eventually (by simp)),
    ht.eventually ((hu.2.2 t).2), hb.eventually (Metric.ball_mem_nhds _ hv.x_pos), hg.eventually (Metric.ball_mem_nhds _ hv.zone_pos)] with x hxF hxG heU hx' hy'
  let y := d x
  have hl := hx.intensity hT x (g x) hxG hxF
  have he₁ : HasFDerivAt (𝕜:=ℝ) (f ∘ meetVar x) 0 (g x) := by
    refine (@Uniform.view_exact G _ _ (stepped Q h) T t R p x (g x)).2 ?_
    change HasFDerivAt (𝕜:=ℝ) (tested T t p R _) 0 ((tint G T.Free) ((tint G T.Free).symm (u (Lx x))))
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact heU
  have hS : Slope f (Z x)=0 := (slope_zero_test hxF).2 he₁
  have he : Slope F₀ (Z' x)=0 := funext fun j => (hx.rollers hT x (g x) hxG hxF j).trans (congr_fun hS (K j))
  have hp := (@Uniform.view_exact G _ _ (stepped Q H) U t' R p y (b (g x))).1 ((slope_zero_test hxG).1 he)
  -- Service uniqueness
  have hC' : Ly.symm (Ly y) ∈ ball 0 Y.horizon := by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hx'
  have hD := (hv.2.2.2.2.2.2 _ hC').2.2 t' (Lz (b (g x))) (show Lz.symm (Lz _) ∈ closedBall 0 Y.zone from by rw [ContinuousLinearEquiv.symm_apply_apply]; exact ball_subset_closedBall hy')
  have hJ : g' y=b (g x) := by
    change Lz.symm (v (Ly y)) = _
    rw [show v (Ly y)=_ from (hD.1 hp).symm, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨hJ,?_⟩
  change Every K (block F₀ (meetVar y (g' y))) (block f (Z x)); rw [hJ]; exact hl
end YM.Further.PhysicalPeriodLimitF933.Enrobe
