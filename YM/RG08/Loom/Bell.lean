import YM.RG08.Loom.Gallery
/-!
# Paid gauge/Signed tree moves. Extend Opinion but same local station
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
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent Profiles PertExtension.Chart
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {p c f : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable {v w : ℝ→Link G c} {n h j τ e : ℕ} {k : KernelChoices} {D : ℕ}{R : ℝ} {φ φ' : Exam D} {κ : S.Choices}
variable {U U' H H' : BoardU D R G} {V : ℕ→ Config G f→ℝ}{F F' : Air G} {W W' : Site S.ratio.count → ℕ→Config G f→ℝ} {B K : FreeResolvent.FaceRow} {σ : ChartRatio G} {o o' : Site c}
local notation "Ξ" => treeMatrix G S T K
local notation "Ω" => ℝ × T.Slice G
local notation "P" => (T.Slice G)
local notation "l" => 𝓝 ((0:ℝ), (1:P))
local notation "ℓ" => 𝓝 (1:Config G f)
private lemma sailReady (hv : ∀ i,Pointwise (V i∘input G f)) (g : S.patch.Branches S.kernel G)(F : ℝ→ Config G f ≃ₜ Config G f)
    (hx : Tendsto (bayExit S T F) l ℓ) (hv' : Tendsto (bayExit S T (fun t=> (F t).symm)) l ℓ) (hp : ∀ t,MeasurePreserving (F t) (prior G f) (prior G f))
    (hE : ∀ t,Cart G T (F t)) (hE' : ∀ t, Cart G T (F t).symm)
    (hB : ∀ a b,Shell G f (W' a b))
    (he : ∀ᶠ p:Ω in l, laboratory S κ n V p.1 (input G c (p.1 • w p.1)) (bayExit S T F p)=laboratory S κ n V p.1 (input G c (p.1 • v p.1)) (T.drape p.2))
    (hU : ∀ᶠ p:Ω in l,chapel G S n W τ h p.1 (T.drape p.2)=chapel G S n W' τ h p.1 (bayExit S T F p)) : ∃ e, WalkPays S G T e κ n h τ v w V W W' := by
  let E t:= carriage G T _ (hE t) (hE' t)
  have hW : Tendsto (Profiles.wick T) ℓ (𝓝 1) := by rw [← wick_b G T]; exact (continuous_wick T).tendsto _
  let f' := bayExit S T F; let u (p:Ω):= T.drape (Profiles.wick T (f' p))
  have ha : Tendsto u l ℓ := ((drape_b G T) ▸ T.continuous_drape.tendsto (1:P)).comp (hW.comp hx)
  have hz (a b) := (hB a b).coast f' u _ l hx ha (Eventually.of_forall (fun i=> (Profiles.wears T (f' i)))) -- infer gauge
  refine ⟨E,hW.comp hx,hW.comp hv',fun t=> preserving G T _ (hp t) _ _,?_⟩
  have hi:= wipe_fee S T hx g hv (κ:=κ) (R:=fun p:Ω=> input G c (p.1 • w p.1)) (t:=Prod.fst) (k:=n)
  filter_upwards [he,hU,hi,eventually_all.mpr (fun j=>(eventually_all_finset (range (n+τ+1))).mpr (fun b _=> hz j b))] with i ht hh hV hp
  refine ⟨congr_arg (fun v:ℝ=> Real.exp (-v/i.1^2)) ((hV.trans ht).symm),?_⟩
  rw [hh]; change chapel G S n W' τ h i.1 (f' i)=chapel G S n W' τ h i.1 (u i)
  unfold chapel; refine sum_congr rfl fun a _=>?_ ; congr 1; refine sum_congr rfl fun j hj=> congr_arg _ (hp a j hj).symm

lemma sails_gauge (hv : ∀ i,Pointwise (V i ∘ input G f))(h : S.patch.Branches S.kernel G)(hO : ∀ a b,Shell G f (W a b))
    (he : GaugeNear (suitify v) (suitify w)) : ∀ h' n τ, ∃ e, WalkPays S G T e κ n h' τ v w V W W := by
  obtain ⟨d,z,hz,he⟩:=he; intro h' n τ
  let f' t:= d t ∘ S.ratio.parent; let e t:= gaugeWalk G (f' t); let i t: Site f→G.El:=(f' t) * fun _=>z⁻¹; let u p:= T.drape (p:Ω).2
  have hx : Tendsto u l ℓ := baySimp S T; have hu : Tendsto Prod.fst l (𝓝 0):=continuous_fst.tendsto ((0:ℝ),(1:P))
  have hh : Tendsto (fun p:Ω=> f' p.1) l (𝓝 (fun _=>z)) := tendsto_pi_nhds.mpr (fun j=> tendsto_pi_nhds.mp (hz.comp hu) (S.ratio.parent j))
  have hw {q : G.El} {i : Ω→ (Site f→ G.El)} (h : Tendsto i l (𝓝 (fun _=>q))) : Tendsto (fun p:Ω=> Lattice.gauge (i p) (u p)) l ℓ :=
    tendsto_pi_nhds.mpr fun j=> by
      have hv := ((tendsto_pi_nhds.mp h j.1).mul (tendsto_pi_nhds.mp hx j)).mul ((tendsto_pi_nhds.mp h (j.1+step j.2)).inv)
      simpa using! hv
  let Y:= bayExit S T e
  have hF : Tendsto Y l ℓ :=hw hh; have hX := hw (i:= fun p=> fun _=>z) tendsto_const_nhds
  have hg : Tendsto (fun p:Ω=> i p.1) l (𝓝 1) := by
    have hp :(fun q':Site f=>z)*(fun _=>z⁻¹)=1 := funext fun _=>mul_inv_cancel z
    exact hp ▸ hh.mul (g:=fun _=> (fun _=>z⁻¹)) tendsto_const_nhds
  have hl (p:Ω) : Lattice.gauge (i p.1) (Lattice.gauge (fun _=>z) (u p))=Y p := by
    funext x; change _ = Lattice.gauge (f' p.1) _ x; simp only [Lattice.gauge,i, Pi.mul_apply]; group; rfl
  have hy t : Cart G T (e t).symm := by
    intro k h v; exact gauge_cart G T (f' t)⁻¹ k h v
  apply sailReady S G T hv h e hF (hw (q:=z⁻¹) hh.inv) (fun t=> prior_gauge _) (fun t=> gauge_cart G T _) hy hO; swap
  · filter_upwards [eventually_all.mpr (fun a=>(eventually_all_finset (range (n+τ+1))).mpr (fun b _=> (hO a b).coast u Y (fun p=>f' p.1) l hx hF (Eventually.of_forall fun _=>rfl)))] with p hp
    unfold chapel; exact sum_congr rfl fun i _=> congr_arg ((((S.ratio.count.val):ℝ) ^ h'/↑(Fintype.card (Site S.ratio.count)))* ·) (sum_congr rfl fun j hj=> congr_arg (p.1^j * ·) (hp i j hj).symm)
  filter_upwards [(eventually_all_finset (range (n+2+1))).mpr (fun j _=> (hue_force (hv j) l hx z).and (gauge_force (hv j) _ hX hg)),hu.eventually he] with x hp H
  unfold laboratory; change input G c (x.1 • w x.1)=_ at H; rw [H]; change tickets S _ (S.prediction (Y x) κ)+_ = _
  have ht : d x.1 = f' x.1 ∘ S.ratio.embed := funext fun _=> by unfold f'; simp [S.ratio.embed_parent]
  rw [ht, show S.prediction (Y x) κ = S.prediction (Lattice.gauge (f' x.1) (T.drape x.2)) κ from rfl,shield_k S h]; congr 1; refine Finset.sum_congr rfl fun j hj=> ?_
  refine congr_arg (x.1^(2*j)* ·) ?_; change V j (Y x)= V j (u x); rw [← hl]; exact (hp j hj).2.trans (hp j hj).1
lemma pullers_one (s : Signed): Tendsto (pull (K:=G.El) s (0:Site f)) ℓ ℓ := by simpa only [show pull s 0 (1:Config G f)=1 from by funext i; simp [rerun]] using (continuous_pull s (0:Site f)).tendsto (1:Config G f)
lemma sails_signed (s : Signed) (h : S.patch.Branches S.kernel G) (hW : ∀ i,Pointwise (V i ∘ input G f))
    (hv : ∀ᶠ t in 𝓝 (0:ℝ),input G c (t • w t)=pull s 0 (input G c (t•v t))) (hV : ∀ a b,Shell G f (W' a b))
    (p : Site S.ratio.count≃ Site S.ratio.count)(hq : ∀ i a, W' i a ∘ (pull s 0)=ᶠ[ℓ] W (p i) a) : ∀ h' n τ, ∃ e, WalkPays S G T e κ n h' τ v w V W W' := by
  intro h' n τ
  let e:= signedWalk G f s; let u x:= T.drape (x:Ω).2
  have hx : Tendsto u l ℓ := baySimp S T
  apply sailReady S G T hW h (fun _=> e) ((pullers_one G s).comp hx) ((pullers_one G s⁻¹).comp hx) (fun _=> prior_pull ..) (fun _=> signed_cart G T s) (fun _=> signed_cart G T s⁻¹) hV; swap
  · filter_upwards [hx.eventually (eventually_all.mpr fun i=>(eventually_all_finset (range (n+τ+1))).mpr (fun j _=> hq i j))] with x hy
    unfold chapel; rw [← Equiv.sum_comp p (fun i'=> _ * ∑ j∈_, x.1^j * W i' j _)] -- fix
    apply sum_congr rfl; intro i _; congr 1; apply sum_congr rfl; intro j hj; congr 1; exact (hy i j hj).symm
  let i:= S.withinChoice s 0 κ; let Q x:= pull s 0 (u x)
  have hi := hx.eventually (Work.F04.prediction_germ (S:=S) h i κ)
  filter_upwards [hi,(continuous_fst.tendsto ((0:ℝ),(1:P))).eventually hv,
    (eventually_all_finset (range (n+2+1))).mpr (fun j _=> spin_force (hW j) l hx s)] with x he hV hd
  let U:=input G c (x.1 • v x.1); have hs:S.ratio.embed 0=0:=map_zero S.ratio.root
  have hz:= S.prediction_channel h s 0 (u x) κ; rw [hs,show S.prediction (u x) (S.withinChoice s 0 κ)=_ from he] at hz
  rw [hV]; unfold laboratory; change tickets S _ (S.prediction (Q x) _)+_= _
  rw [show S.prediction (Q x) κ=_ from hz,ticket_spin]; congr 1; exact Finset.sum_congr rfl fun j hj=> congr_arg _ (hd j hj)
end YM.RG08.Loom
