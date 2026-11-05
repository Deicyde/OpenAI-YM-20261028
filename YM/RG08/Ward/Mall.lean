import YM.RG08.Ward.Chalet
import YM.Push.SECTOR_MEASURE.Gauges
/-!
# Invariance of absolute localized integrand: all positive coefficients come from germ.
Collars proof only, no sector-wise estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles
open PertExtension.Series.Tested
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f n : Side} (S : StepData c f) {G : Gauge} (T : Forest S.ratio)
section laws
variable {X : Type} {W : Config G n→ℝ} (h : Pointwise (W ∘ input G n)) (ℓ : Filter X)
    {U : X→Config G n} {k : X→ Site n → G.El}
include h
lemma gauge_force (hu : Tendsto U ℓ (𝓝 1)) (hk : Tendsto k ℓ (𝓝 1)) :
    ∀ᶠ x in ℓ,W (Lattice.gauge (k x) (U x))= W (U x) := by
  let p x : Swatch G n := (frameLog (k x),content (U x))
  have he : ContinuousAt (frameLog (G:=G) (n:=n)) 1 := by
    refine ContinuousAt.comp (g:=(gaugeColor (G:=G) (n:=n)).symm) (f:=fun (x:Coats G n) i=>plogC G (x i)) ?_ (continuousAt_pi.mpr fun i=>?_)
    · exact gaugeColor.symm.continuousAt
    have hL : ContinuousAt (plogC G) ((1:Coats G n) i) := (show ContinuousAt G.plog (G.mat 1) from G.mat_one.symm ▸ G.plog_diff.continuousAt).comp G.continuous_mat.continuousAt
    exact hL.comp (f:=fun x:Coats G n=>x i) ((continuous_apply _).continuousAt)
  have hp : Tendsto p ℓ (𝓝 0) := ((show Tendsto _ _ _ from (frameLog_one (G:=G) (n:=n) ▸ he.tendsto).comp hk)).prodMk_nhds ((content_one (G:=G) (m:=n) ▸ (content_real G n).1.tendsto).comp hu)
  filter_upwards [hp.eventually moveField_germ,hp.eventually h.guard, hu.eventually content_encodes,hk.eventually switch_frameLog] with x hx hV he' hp'
  change W (input G n (moveField (p x)))= W (input G n (content (U x))) at hV; rw [hx, shiftLinks] at hV; simp only [p,he',hp'] at hV -- `p` rw
  exact hV
lemma hue_force (hu : Tendsto U ℓ (𝓝 1)) (z : G.El) :
    ∀ᶠ x in ℓ,W (Lattice.gauge (fun _=>z) (U x))=W (U x) := by
  have hp := (content_one (G:=G) (m:=n) ▸ (content_real G n).1.tendsto).comp hu
  filter_upwards [hp.eventually (h.stained z),hu.eventually content_encodes] with x hx hz
  change W (input G n (stain z (content (U x))))= W (input G n (content (U x))) at hx; rw [← stain_cons,hz] at hx; exact hx
lemma spin_force (hu : Tendsto U ℓ (𝓝 1)) (z : Signed) :
    ∀ᶠ x in ℓ,W (pull z 0 (U x))=W (U x) := by
  have hp := (content_one (G:=G) (m:=n) ▸ (content_real G n).1.tendsto).comp hu
  filter_upwards [hp.eventually (h.rotate z),hu.eventually content_encodes] with x hx hz
  change W (input G n (flipCoords z ℝ (content (U x))))=W (input G n (content (U x))) at hx; rw [← flip_links, hz] at hx; exact hx
end laws
variable {κ : S.Choices} {V : ℕ → Config G f → ℝ} {v w : ℝ → Link G c} {k : ℕ} {X : Type} {ℓ : Filter X}
    {R : X→ Config G c}{x : X→Config G f} {b : X→Site f→G.El}
lemma shield_k (h : S.patch.Branches S.kernel G) (V : Config G c) (v : Config G f) (b : Site f→ G.El) :
    tickets S (gauge (b ∘ S.ratio.embed) V) (S.prediction (gauge b v) κ)=tickets S V (S.prediction v κ) := by
  rw [(Push.SectorMeasure.choice_gauge h _ _ _).2]
  unfold tickets; congr 1; apply Finset.sum_congr rfl; intro i _; conv_rhs=> rw [← G.price_conj (b (S.ratio.embed i.1)) _]
  congr 1 -- rewrite orientation
  unfold Lattice.gauge; dsimp only [Function.comp_apply]; group
lemma ticket_spin (s : Signed) (U V : Config G c) : tickets S (pull s 0 U) (pull s 0 V)=tickets S U V := by
  unfold tickets; congr 1; conv_rhs=> rw [← Equiv.sum_comp (StepData.sendBonds s (0:Site c))]
  apply Finset.sum_congr rfl; intro i _
  rw [rerun,rerun]; split; swap; · rfl
  let x:=U (sendEdge s 0 i); let y:= V (sendEdge s 0 i)
  change G.price (x⁻¹ * (y⁻¹)⁻¹)= G.price (x*y⁻¹)
  rw [← G.price_inv (x*y⁻¹),show (x*y⁻¹)⁻¹=x*(x⁻¹*(y⁻¹)⁻¹)*x⁻¹ by group,G.price_conj]
private lemma pureFold (x : Site f) : T.foldAt (G:=G) (1:Config G f) x=(1:G.El) := by -- p extraneous
    unfold Forest.foldAt; suffices H : ∀ p y,travel (1:Config G f) y p=1 by rw [H,inv_one]
    intro p; induction p with
    | nil=> exact fun _=>rfl
    | cons d p hp=> intro y; unfold travel; rw [hp,Step.read]; simp
lemma wipe_fee (hx : Tendsto x ℓ (𝓝 1)) (h : S.patch.Branches S.kernel G) (hW : ∀ i,Pointwise (V i ∘ input G f)) (t : X→ℝ) :
    ∀ᶠ i in ℓ, laboratory S κ k V (t i) (R i) (T.drape (wick T (x i)))= laboratory S κ k V (t i) (R i) (x i) := by
  let b x' := T.foldAt (x x')
  have he : Tendsto b ℓ (𝓝 1) := tendsto_pi_nhds.mpr (fun i=> by
    change Tendsto (fun a=> T.foldAt (x a) i) _ (𝓝 1); exact (by simpa only [pureFold S T i] using! (((T.folds i).tendsto (1:Config G f)).comp hx))) -- maybe p
  have ht := fun i=> gauge_force (hW i) ℓ hx he
  filter_upwards [(eventually_all_finset (Finset.range (k+2+1))).mpr (fun i _=> ht i)] with i hi
  have hv:=shield_k S (κ:=κ) h (R i) (x i) (b i); rw [show b i ∘ _=1 from funext fun x=> T.fold_root .., gauge_one] at hv
  rw [Profiles.wears]; change tickets S _ (S.prediction (Lattice.gauge (b i) (x i)) κ) + _ = _; unfold laboratory; rw [hv]; congr 1; exact Finset.sum_congr rfl fun j hj=> congr_arg _ (hi j hj)
end YM.RG08.Reflect
