import YM.RG08.Shade.Reach
import YM.RG08.Loom.Silk
/-!
# Cutoff-independent mark identities catch all fixed m including the tilted collars
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent Profiles
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}{c f m : Side}{D n k j h τ e r : ℕ}{R : ℝ} {S : Patch}

private lemma song_cost {α:Type} [Fintype α](i : Site c) {f : Shale α r} {A:ℝ} (h : Quire.Lit f 0 A) : ‖stitch f c i‖≤A := by
  apply ContinuousMultilinearMap.opNorm_le_bound h.nonneg; intro v
  unfold Quire.Lit Quire.Ink at h; simp only [ling,zero_mul,Real.exp_zero,one_mul] at h
  have he : Summable f := h.2.1.of_norm; have hv := bead_summable f v he i
  rw [stitch_apply he]
  apply (norm_tsum_le_tsum_norm hv.norm).trans
  let C:=∏ j, ‖v j‖; have hc:0≤C:= by unfold C; positivity
  apply (Summable.tsum_le_tsum (g:=fun i=> ‖f i‖ * C) ?_ hv.norm (h.2.1.mul_right C)).trans
  · rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hc
  intro j; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (rosary_bill ..) (norm_nonneg _)
lemma pens_tuft {α : Type}[Fintype α]{F : ℕ→Shale α r} {S : Shale α r} (h : Hurled F S) (m)(i : Site m) : Tendsto (fun j=>stitch (F j) m i) atTop (𝓝 (stitch S m i)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  obtain ⟨δ,hδ,H⟩:= h.moment.thus
  refine squeeze_zero (fun i=> norm_nonneg _) (g:=δ) (fun j=>?_) hδ
  rw [← st_sub (h.ever j|>.of_norm) h.old.of_norm]; exact song_cost _ (H j)
section tiling
variable (U : Screed ℝ (Loc G 1))(g : Ratio c f)(i : Site f)
lemma slate_t {F : Shale (Loc G 1) r} (h : Pens F)(u : Link G g.count): rootSong F f i (tiltCopy g G u)=rootSong F g.count (g.residue i) u := by
  unfold rootSong Tensor.diagonal; rw [stitch_apply h.of_norm,stitch_apply h.of_norm]; refine tsum_congr fun b=>?_ ; congr 1; refine prod_congr rfl fun j _=>?_ ; unfold silks; change u (g.residue (i+wrap _ _),_)=u _; rw [map_add,g.residue_wrap]
lemma slate_arc (h : ∀ i j,Pens (U i j))(n k : ℕ)(v : ℝ→Link G g.count)(t : ℝ) : arco f (fun e=> large i (n+e) (U e)) (tiltCopy g G ∘ v) k t= arco g.count (fun e=>large (g.residue i) (n+e) (U e)) v k t := by unfold arco year; apply sum_congr rfl; intro j _; unfold large; dsimp only; rw [Finset.sum_apply,Finset.sum_apply]; congr 1; exact sum_congr rfl fun i' _=> slate_t _ i (h j i') (v t)
lemma shore_travel (hU : ∀ i j,Pens (U i j))(h : Shore i τ U) : Shore (g.residue i) τ U := by
  intro v w hv hw hz k; dsimp only
  obtain ⟨q,x,hq,H⟩:=hz
  have hu u : suitify (tiltCopy g G ∘ u)= (tiltCopy g G ∘ suitify u) := funext fun t=> Eq.symm (map_smul ..)
  have hm : GaugeNear (suitify (tiltCopy g G∘v)) (suitify (tiltCopy g G ∘ w)) := by
    rw [hu,hu]; refine ⟨fun t=> q t ∘ g.residue,x,tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mp hq (g.residue i),?_⟩; filter_upwards [H] with i hi
    simp only [Function.comp_apply, tilt_yes, hi]; exact tilt_g ..
  have he:=h _ _ ((tiltCopy g G|>.analyticAt _).comp hv) ((tiltCopy g G|>.analyticAt _).comp hw) hm k
  dsimp only at he
  rw [funext (slate_arc U g i hU τ k v),funext (slate_arc U g i hU τ k w)] at he; exact he
private lemma turn_roll (x : Link G g.count)(s : Signed) : orderTurn s (tiltCopy g G x)=tiltCopy g G (orderTurn s x) := by
  let T:=fun t:ℝ=> t•x
  have hv:Tendsto T (𝓝[>]0) (𝓝 0):= by simpa using! (((continuous_id (X:=ℝ)).smul (continuous_const (y:=x))).tendsto 0).mono_left nhdsWithin_le_nhds
  let a:=tiltCopy g G; let u:= orderTurn (G:=G) (m:=g.count) s; let v:=orderTurn (G:=G) (m:=f) s
  have hA:=a.continuous.tendsto' 0 0 (map_zero _); have ht:=u.continuous.tendsto' 0 0 (map_zero _); have hp:=v.continuous.tendsto' 0 0 (map_zero _)
  obtain ⟨t,hX,H,h⟩:= (eventually_pos.and (((hp.comp (hA.comp hv)).eventually input_encodes).and ((hA.comp (ht.comp hv)).eventually input_encodes))).exists
  have hh (t) : input G f (v (a (T t)))=input G f (a (u (T t))) := (Eq.symm (flip_links ..)).trans (by rw [show input G f (a (T t))=_ from tilt_yes _ _ (T t),tilt_action g G (input G g.count _) s,flip_links]; exact Eq.symm (tilt_yes ..))
  apply smul_right_injective (Link G f) hX.ne'
  change t • (v (a x))= t • (a (u x))
  rw [←map_smul,←map_smul,←map_smul,←map_smul]
  exact H.symm.trans ((congr_arg content (hh t)).trans h)
lemma slant_travel {F H : BoardU D R G} {s : Signed}(h : Honor s F H f)(hf : ∀ i j,Pens (F i j))(hV : ∀ i j,Pens (H i j)) : Honor s F H g.count := by
  intro i φ k j v
  let a:= plug φ R ∘ F k j; let b:=plug (twisting s φ) R ∘ H k j
  let w:= g.assemble (0,i); have he:s.act i=g.residue (s.act w):= by rw [tilt_move, g.assemble_res]
  have hp: orderTurn s (tiltCopy g G v)=_ := turn_roll g v s
  calc
    _ = rootSong a f (s.act w) (tiltCopy g G v) := by rw [he, slate_t g (s.act w) (show Pens a from (hf k j).shaped _)]
    _ = rootSong b f w (orderTurn s (tiltCopy g G v)) := h w φ k j _
    _ = _ := by rw [hp, slate_t g w (show Pens b from (hV k j).shaped _),g.assemble_res]
end tiling
variable {x : ℕ→BoardU D R G}{X : BoardU D R G}
lemma arco_t (h : ℝ→Link G c)(P : Reel (Psalm (Lines G c 1)))(he : AnalyticAt ℝ h 0) (hp : ∀ j,Grass (P j)) (n): ContDiffAt ℝ ∞ (arco c P h n) 0 := ContDiffAt.sum (s:=range (n+1)) (f:=fun j t=> t^j*P j (h t)) (fun j _=> (contDiffAt_id.pow j).mul (((hp j).smooth.contDiffAt.comp _ he.contDiffAt).of_le le_top))
lemma pen_arco {α : Type} [Fintype α] [DecidableEq α] {Z:ℕ→Screed ℝ α}{X:Screed ℝ α}
    (h : ∀ i j,Hurled (fun l=> Z l i j) (X i j)) (s : Site c) (h':ℕ) (w:ℝ→PAC α c) (he:AnalyticAt ℝ w 0) (k n:ℕ) :
    Tendsto (fun i=> ink (year (fun i' t=>large s (h'+i') (Z i i') (w t)) n) k) atTop (𝓝 (ink (year (fun i' t=> large s (h'+i') (X i') (w t)) n) k)) := by
  let A (U : Screed ℝ α) p r t := t^p * rootSong (U p r) c s (w t)
  have hu (U : Screed ℝ α) i' j : ContDiffAt ℝ ∞ (A U i' j) 0 := (contDiffAt_id.pow i').mul (((root_smooth s _).contDiffAt.comp _ he.contDiffAt).of_le le_top)
  have hh (U : Screed ℝ α) : ink (year (fun i' t=>large s (h'+i') (U i') (w t)) n) k= ∑ j∈range (n+1),∑ l∈range (h'+j+1), ink (A U j l) k := by
    unfold year large; simp_rw [Finset.sum_apply,smul_eq_mul,Finset.mul_sum]; change ink (fun t=> ∑ i∈_,∑ j∈_,A U i j t) k=_; rw [ink_list (range (n+1)) _ (fun i _=>ContDiffAt.sum (fun j (_:j∈Finset.range (h'+i+1))=> hu U i j))]; exact sum_congr rfl fun i _=> ink_list (range _) (A U i) (fun j _=> hu U i j) _
  simp_rw [hh]; have hf j l : Tendsto (fun i=> ink (A (Z i) j l) k) atTop (𝓝 (ink (A X j l) k)) := ((appeal w (fun t:ℝ=>t^j) (he.contDiffAt.of_le le_top) (contDiffAt_id.pow _) k (r:=l)).continuous.continuousAt.tendsto).comp (pens_tuft (h j l) c s)
  exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> hf i j))
lemma Parade.moving (h : ∀ i j,Hurled (fun l=> x l i j) (X i j))(hp : ∀ i,Parade m τ (x i)): Parade m τ X := by
  intro φ i a b ha hb hv k; dsimp only
  refine pulse_bound (fun j hj=> ?_) (arco_t _ _ ha (fun i=>dryL ..) _) (arco_t _ _ hb (fun i=>dryL ..) _)
  let F l e j:= plug φ R ∘ x l e j; let K e j:= plug φ R ∘ X e j
  have he e j : Hurled (fun l=> F l e j) (K e j):= (h e j).maps _
  refine tendsto_nhds_unique_of_eventuallyEq (pen_arco (Z:=F) he i τ a ha j k) (pen_arco (Z:=F) he i τ b hb j k) (Eventually.of_forall (fun l=>?_))
  exact aspiredV (hp l φ i a b ha hb hv k) (ink_aspire (arco_t _ _ ha (fun j=>dryL i _ _) k)) (ink_aspire (arco_t _ _ hb (fun j=>dryL i _ _) k)) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
lemma Honor.moving {y : ℕ→BoardU D R G}{Y : BoardU D R G} (h : ∀ i j,Hurled (fun l=>x l i j) (X i j))(hp : ∀ i j,Hurled (fun l=>y l i j) (Y i j)){s : Signed}(he : ∀ i,Honor s (x i) (y i) m) : Honor s X Y m := by
  intro i φ p r v
  let P := plug φ R; let F:=plug (twisting s φ) R
  exact tendsto_nhds_unique_of_eventuallyEq (((ContinuousMultilinearMap.apply ℝ _ ℝ (fun _:Fin r=> v)).continuous.continuousAt.tendsto).comp (pens_tuft ((h p r).maps P) _ (s.act i))) (((ContinuousMultilinearMap.apply ℝ _ ℝ (fun _:Fin r=> orderTurn s v)).continuous.continuousAt.tendsto).comp (pens_tuft ((hp p r).maps F) m i)) (Eventually.of_forall (fun j=> he j i φ p r v))
end YM.RG08.Loom
