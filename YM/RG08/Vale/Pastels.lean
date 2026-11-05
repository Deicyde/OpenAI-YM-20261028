import YM.RG08.Vale.Movie
/-!
# Radial projections always real on real tests, genuine color invariance
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {m : Side} {d i j n r : ℕ} (H:Hol G) {V W: Shale (Loc G 1) r}
-- color-stained film mathematically line for any allowed probe law
include H in
lemma filmL (s:G.El)(m : Side) : (studio G d m) ∘ Film.colorIn G d s =ᶠ[𝓝 0] (stain s) ∘ studio G d m := by
  have he (x : Co m (Loc G 1)) := Film.light H (d:=d) s (heap (lift x.1,x.2))
  filter_upwards [eventually_all.mpr he] with t ht
  funext p
  rcases p with ⟨u,i,j⟩
  dsimp only [Function.comp_apply]; rw [← arm_apply G m 1 (stain s _) u i j, stain]; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,(arm G m 1).apply_symm_apply]
  let k:Fare G:= (lift u,i,j)
  let Q:= heap k
  have hi : arm G m 1 (studio G d m t) (u,i)=Film.lane (Place.seat Q.1) Q.2 t := by ext1 j; rw [arm_apply]; rfl
  change scent j (Film.lane (Place.seat Q.1) Q.2 _)=(G.adjoint s (arm _ _ _ (studio G d m t) (u,i))) j
  rw [ht (u,i,j), hi]; rfl
structure Dappled (V: Shale (Loc G 1) r) : Prop extends Tidy V where
  shy : ∀ m:Side,Stained G (rootSong V m 0)
include H in
lemma showed (hu : Dappled V)(hp : Polished V) (v:Fin j → Snap G d)(s:G.El) : amount V d j ((Film.colorIn G d s) ∘ v) = amount V d j v := by
  let A:= Film.colorIn G d s
  refine tendsto_nhds_unique_of_eventuallyEq (movie hu.toTidy hp _) (movie hu.toTidy hp _) (Eventually.of_forall fun i=>?_)
  let m:= boards i; let F:= rootSong V m 0 ∘ studio G d m
  have he: Tendsto (studio G d m) (𝓝 0) (𝓝 0) := (begins G d m) ▸ (begins_sm G d m).continuousAt.tendsto
  have hz : F ∘ A=ᶠ[𝓝 0] F := by
    filter_upwards [filmL H s (d:=d) m, he.eventually (hu.shy m s)] with x hx hX; change rootSong V _ _ (studio G d m (A x))= _; rw [show studio G d m (A x)=_ from hx]; exact hX
  have hf : ContDiffAt ℝ j F 0 := (((Tensor.diag_smooth ..).contDiffAt).comp _ (begins_sm ..)).of_le le_top
  exact (DFunLike.congr_fun (Next.Foundations.jets_linear A hf).symm v).trans (DFunLike.congr_fun ((hz.iteratedFDeriv ℝ j).eq_of_nhds) v)
lemma dappled_zero (G:Gauge) (r:ℕ) : Dappled (0:Shale (Loc G 1) r) := ⟨Tidy.zero ..,fun m k=> by simp only [root_zero]; exact Eventually.of_forall fun _=> rfl⟩
lemma dappled_more (h : Dappled V) (g : Dappled W) : Dappled (V+W) := by
  refine ⟨h.toTidy.plus g.toTidy,fun m i=>?_⟩
  rw [rootSong,st_plus h.pens.of_norm g.pens.of_norm]; exact EventuallyEq.add (h.shy m i) (g.shy m i)
lemma dappled_less (h : Dappled V)(g : Dappled W) : Dappled (V-W) := by
  refine ⟨h.toTidy.less g.toTidy,fun m i=>?_⟩
  rw [rootSong,st_sub h.pens.of_norm g.pens.of_norm]; exact EventuallyEq.sub (h.shy m i) (g.shy m i)
lemma dappled_sm (h : Dappled V)(k:ℝ) : Dappled (k•V) := by
  refine ⟨h.toTidy.scale k, fun m i=>?_⟩
  rw [rootSong,st_scale k h.pens.of_norm]; exact (h.shy m i).mono fun _ hx=>congr_arg (k•·) hx
open Loom
variable {U : Screed ℝ (Loc G 1)} {τ : ℕ}
lemma shy_useful (he : Tidy V) {X : Config G m→ℝ}(hs : Shell G m X)(ht : stitch V m 0=Tensor.coeff (X ∘ input G m) r 0): Stained G (rootSong V m 0) := by
  intro s
  let F:= X ∘ input G m; let S:= stain (m:=m) s
  have ha : Tendsto S (𝓝 0) (𝓝 0) := by simpa only [map_zero] using S.continuous.tendsto 0
  have hv : Tendsto (input G m) (𝓝 0) (𝓝 1) := by simpa using (input_cont.tendsto (0: Link G m))
  have hb : F ∘ S=ᶠ[𝓝 0] F := hs.coast (input G m) (input G m ∘ S) (fun _ _=>s) _ hv (hv.comp ha) (Eventually.of_forall fun i=> (stain_cons ..).symm)
  apply Eventually.of_forall; intro v; unfold Function.comp rootSong Tensor.diagonal; rw [ht]
  exact congr_arg ((r.factorial:ℝ)⁻¹ • · : ℝ→ℝ) ((DFunLike.congr_fun (Next.Foundations.jets_linear S (show ContDiffAt ℝ r F 0 from hs.hol.of_le le_top)).symm (fun _=>v)).trans (DFunLike.congr_fun ((hb.iteratedFDeriv ℝ r).eq_of_nhds) (fun _=>v)))
lemma strand_dapple (hu : ∀ i r,Tidy (U i r))(hv : ∀ m:Side, Shore (0:Site m) τ U) : Dappled (Loom.strand τ i U r) := by
  refine ⟨strand_tid hu,fun m=>?_⟩
  obtain ⟨X,hX⟩:= shelved (n:=τ+r) (p:=i) (hv m) (by omega) hu
  exact shy_useful (strand_tid hu) hX.toShell (hX.scores_at r (by omega)).symm
lemma costed_dapple (he: ∀ i j,Tidy (U i j))(hp: ∀ m:Side, Shore (0:Site m) τ U)(hU : Fits τ U) : Dappled (U i j) := by
  by_cases hx : j≤τ+i
  · let n:=τ+i-j; have ht : Loom.strand τ n U j=U i j := by unfold Loom.strand; rw [if_pos (by unfold n; omega),show n+j-τ=i by unfold n; omega]
    rw [←ht]; exact strand_dapple he hp
  rw [not_ne_iff.mp (mt (hU i j) hx)]; exact dappled_zero ..
end YM.RG08.Vale
