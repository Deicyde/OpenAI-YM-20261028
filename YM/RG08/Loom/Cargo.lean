import YM.RG08.Loom.Guard
/-!
# Producing genuine near-unit germ from all extracted arc equations.
Allow comparison with changed BOTH micro-frames near the same unit cell.
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
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {α : Type} {G : Gauge} {D p n r k τ : ℕ} {m c f : Side} {R : ℝ} {i : Site m}
variable {U V : Screed ℝ (Loc G 1)} {W : Config G m→ℝ}
structure Shell (G : Gauge) (m : Side) (W : Config G m→ℝ) : Prop where
  measure : Measurable W
  hol : ContDiffAt ℝ ω (W ∘ input G m) 0
  coast : ∀ {X : Type} (v w:X→Config G m) (g:X→Site m→G.El) (l:Filter X), Tendsto v l (𝓝 1)→ Tendsto w l (𝓝 1)→ (∀ᶠ t in l,w t=gauge (g t) (v t))→ W ∘ w=ᶠ[l] W ∘ v
structure Cargo (i : Site m) (τ k n : ℕ)(U : Screed ℝ (Loc G 1))(W : Config G m→ℝ) : Prop extends Shell G m W where
  scores_at : ∀ j≤ n, Tensor.coeff (W ∘ input G m) j 0=stitch (strand τ k U j) m i
lemma strand_tid (h : ∀ i j,Tidy (U i j)) : Tidy (strand τ k U r) := by unfold strand; split; exact h ..; exact Tidy.zero ..
lemma large_past [Fintype α] [DecidableEq α] (U : Spine ℝ α) (n : ℕ) (x : PAC α m) (i : Site m) : (fun t:ℝ=>large i n U (t • x))=peval (fun j=> rootSong (U j) m i x) n := by
  funext t; unfold large peval Zone.eval; rw [Finset.sum_apply]; exact sum_congr rfl fun k _=> root_scaleX ..
lemma large_jet (i : Site m) [Fintype α] [DecidableEq α] (U : Spine ℝ α) (hv : ∀ i,Tidy (U i)) (he:r≤n) : Tensor.coeff (large i n U) r 0=stitch (U r) m i := by
  have he' := large_smooth (L:=n) i U; apply Tensor.ext_diag _ _ (Tensor.coeff_symm (he'.contDiffAt.of_le le_top)) ((hv r).sym i); funext x
  rw [← jet_coefficient, ← pulse_ray _ _ (he'.contDiffAt.of_le le_top),large_past]; exact congr_fun ((ink_aspire ((peval_stop n _).contDiffAt.of_le le_top)).unique (Aspiration.polynomial _ _)) r |>.trans (if_pos he)
private lemma colorSure (h : Shore i τ U) (he : τ ≤ n+p) (t : G.El) (x : Link G m) :
    let q:= large i n (strand τ p U); q (stain t x)=q x := by
  intro q; let a (z : ℝ):= z • x; let b(z:ℝ):=z • stain t x
  have ha : AnalyticAt ℝ a 0 := (contDiffAt_id.smul contDiffAt_const).analyticAt
  have hb : AnalyticAt ℝ b 0 := (contDiffAt_id.smul contDiffAt_const).analyticAt
  have hp : GaugeNear a b := ⟨fun _ _=> t,t,tendsto_const_nhds, Eventually.of_forall fun z=> by unfold a b; rw [← map_smul (stain t),stain_cons]⟩
  have hx:= shore_line i h p n he a b ha (zero_smul ..) hb (zero_smul ..) hp
  let S (x : Link G m) k:= rootSong (strand τ p U k) m i x
  rw [show large i n (strand τ p U) ∘ a= peval (S x) n from large_past .., show large i n (strand τ p U) ∘ b =peval (S (stain t x)) n from large_past ..] at hx
  unfold q large; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j hj; have he := Nat.le_of_lt_succ (mem_range.mp hj)
  change S _ j= S _ j
  simpa only [he,↓reduceIte] using aspiredV hx.turn (Aspiration.polynomial _ _) (Aspiration.polynomial _ _) he
private lemma make_fit (h : Shore i τ U)(he : τ≤ n+p)(x : Link G m) :
    let P:= large i n (strand τ p U); Fit (n+1) (fun t:ℝ=> P (t • x)) (fun t:ℝ=> suave P (input G m (t • x))) := by
  let V:=fun t:ℝ=> t • x
  let W:=foyer ∘ input G m ∘ V; let A:=content ∘ W
  have hC : ContDiffAt ℝ ω V 0 := contDiffAt_id.smul contDiffAt_const
  have ha : Army (input G m ∘ V) 0 := Army.powL hC; have hv:= foyer_hol ha
  have hA : W 0=1:= by simp [W,V]
  have hO : A 0=0 := by simp [A,hA,content_one]
  let k:=fun t=> embassy (input G m (V t)); have hh : GaugeNear V A := ⟨k,1,by
      have hY := (embassy_c.continuousAt.comp ha.cont).tendsto; simpa [V,outset] using! hY,(show ∀ᶠ t:ℝ in 𝓝 0,input G m (content (W t))=W t from (hA ▸ (show Tendsto W (𝓝 0) (𝓝 (W 0)) from hv.cont.tendsto)).eventually content_encodes)⟩
  exact shore_line i h p n he V A hC.analyticAt (zero_smul ..) ((hv.logL hA).analyticAt) hO hh
lemma shelved (h : Shore i τ U) (he : τ ≤ n+p)(hu : ∀ i j,Tidy (U i j)) : ∃ W:Config G m→ℝ,Cargo i τ p n U W := by
  let L:= large i n (strand τ p U); have ht : ContDiffAt ℝ ω L 0 := (large_smooth i _).contDiffAt
  let P:=input G m; have hP : Army P 0 := Army.powL (v:=id (α:=Link G m)) contDiffAt_id -- fix
  have hg : Army (foyer ∘ P) 0 := foyer_hol hP; have hp : foyer (P 0)=1:=by simp [P]
  obtain ⟨Z,hZ,Hz⟩:=(content_real G m).2; let F:=L ∘ Z ∘ foyer
  have hm : Measurable F := (large_smooth (L:=n) i _).continuous.measurable.comp (hZ.comp foyer_c.measurable)
  have hF : F=ᶠ[𝓝 1] suave L := ((foyer_c.tendsto' 1 1 foyer_unit).eventually Hz).mono fun q hq=>congr_arg L hq
  have hx : Tendsto P (𝓝 0) (𝓝 1) := by simpa [P] using input_cont.tendsto (0:Link G m)
  have hV := hF.comp_tendsto hx; have hd := hg.logL hp
  have hD : ContDiffAt ℝ ω (F ∘ P) 0 := (show ContDiffAt ℝ ω (suave L ∘ P) 0 from (show ContDiffAt ℝ ω L (content (foyer (P 0))) from by rw [hp,content_one]; exact ht).comp (f:=fun x=> content (foyer (P x))) 0 hd).congr_of_eventuallyEq hV
  refine ⟨F, ⟨hm,hD, ?_⟩,fun j hj=>?_⟩
  · intro X v w k l hv hw hh
    apply EventuallyEq.trans (hF.comp_tendsto hw); apply EventuallyEq.trans _ (hF.symm.comp_tendsto hv)
    filter_upwards [suave_speaks L (fun u x=> colorSure h he u x) hv (k:=k), hh] with x hX hY; simp only [Function.comp_apply,hY]; exact hX
  rw [← large_jet i _ (fun j=> strand_tid hu) hj]
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm (hD.of_le le_top)) (Tensor.coeff_symm (ht.of_le le_top)); funext x
  have hA := make_fit h he x; let W:=fun t:ℝ=> t • x
  have hh: Tendsto W (𝓝[>]0) (𝓝 0) := by simpa [W] using! ((continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hh' : Fit (n+1) ((F∘P) ∘ W) (L ∘ W) := (Fit.supply (hV.comp_tendsto hh) _).join hA.turn
  exact aspiredV hh' (directions (hD.of_le le_top) x) (directions (ht.of_le le_top) x) hj

-- Fit statement also in own parameter. k = requested grade bound
lemma fileFit {x : ℝ→ Link G m} (hx : ContinuousAt x 0) {W : ℕ→Config G m→ℝ} (hp : ∀ p,Cargo i τ p (k+τ) U (W p)) :
    Fit (τ+(k+1)) (fun t:ℝ=> ∑ p∈Finset.range (k+τ+1), t^p* W p (input G m (t • x t))) (fun t=> t^τ *arco m (fun e=>large i (τ+e) (U e)) x k t) := by
  have ht (t:ℝ) : t^τ*arco m (fun e=>large i (τ+e) (U e)) x k t = ∑ p ∈Finset.range (k+τ+1), t^p*large i (k+τ-p) (strand τ p U) (t•x t) := Eq.symm (resume ..)
  simp_rw [ht]
  refine Fit.emp (s:=Finset.range (k+τ+1)) (f:=fun p t=> t^p * W p (input G m (t•x t))) (fun p hv=>?_)
  have hI:= Finset.mem_range.mp hv
  have he:= (jet_path (W p∘input G m) x (life_price (hx.tendsto.mono_left nhdsWithin_le_nhds)) ((hp p).hol.of_le le_top) (k+τ-p)).right (ruler p p le_rfl)
  rw [show τ+(k+1)=p+(k+τ-p+1) by omega]; refine he.join (Fit.supply (Eventually.of_forall ?_) _)
  intro t; change t^p * (∑ b∈Finset.range _,_)= t^p * _
  congr 1; unfold large; rw [Finset.sum_apply]; refine sum_congr rfl fun a ha=>?_ ; rw [jet_coefficient, (hp p).scores_at a (by have he:= Finset.mem_range.mp ha; omega)]; exact Eq.symm (root_scaleX ..)
end YM.RG08.Loom
