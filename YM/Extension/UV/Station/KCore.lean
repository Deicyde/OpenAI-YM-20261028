import YM.Extension.UV.Station.FlowValue
import YM.Extension.UV.Station.Tangent
/-! Low jet identity on the same horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.StationaryData
open Filter Lattice Wilson Precision Function Exterior Laurent RG Tree Bloch WilsonStartup.Change Stationary
open scoped Matrix ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {N:Levels G} {c:Side} {W:PathData G} {V:Horizon N} {m p n:ℕ} {σ C Λ r z:ℝ} {X:MapPrices}
local notation "c₀" => N.S.side m p
private def fiscal (B:Matrix (Body 1 c) (Body 1 c) ℝ) (x:fieldDir G c 1) := ∑ i:G.ColorIndex, dotProduct (parts G 1 x i) (B *ᵥ parts G 1 x i)
private def phases (k:ℕ) (B:Matrix (Body 1 c) (Body 1 c) ℝ) (x:Link G c) := if k=2 then fiscal B (arm G c 1 x) else 0

lemma low_works (hR:W.Bounds (N.params m).clip σ C Λ) (hV:Floor (V.H n m) (N.params m).clip c₀ r z)
    (hw:Bid.Sworn (V.H n m) c₀ G) (hs:Attached (V.H n m) W): Pointwise (intended (m:=c₀) (N.params m).clip W) ∧ ContDiffAt ℝ ω (AT c₀ (N.params m).clip W) 0 ∧ ∀ k≤2,∀ x:Stationary.Link G c₀,
    dirT (intended (N.params m).clip W) k 0 x=phases k (Linear.Kactual V n m p) x:=by
 have ht:= turns_low W.cubic hR.width hR.three (m:=c₀)
 have hq:= (turns_low W.quartic hR.width hR.four (m:=c₀)).weaker (s:=3) (by norm_num)
 have hs':=stain_knit W _ hR (m:=c₀)
 have h₃:=stain_ink W.cubic hR.width hR.three (fun i=>(hR.invariant i).2.1) (m:=c₀)
 have h₄:=stain_ink W.quartic hR.width hR.four (fun i=>(hR.invariant i).2.2) (m:=c₀)
 rw [intent]
 refine ⟨(hs'.add h₃).add h₄,rep_budget W ⟨_,_,_,hR⟩,fun k hk x=>?_⟩
 have hv:=low_columns hR hs hV hw
 unfold dirT; rw [iteratedFDeriv_add_apply (hs'.analytic.add h₃.analytic|>.contDiffAt.of_le le_top) (h₄.analytic.contDiffAt.of_le le_top),iteratedFDeriv_add_apply (hs'.analytic.contDiffAt.of_le le_top) (h₃.analytic.contDiffAt.of_le le_top)]
 have h₃' := (rays_jet h₃.analytic 3).mp ht k (lt_of_le_of_lt hk (by norm_num)); have h₄' := (rays_jet h₄.analytic 3).mp hq k (lt_of_le_of_lt hk (by norm_num))
 rw [h₃',h₄',add_zero,add_zero]
 generalize hk' : k=q at *; clear hk' k
 interval_cases q <;> dsimp [phases]
 · exact hv.1
 · rw [iteratedFDeriv_one_apply,hv.2.1]; rfl
 change iteratedFDeriv ℝ 2 (inputSeries _ _) 0 _ = _
 rw [show (fun _:Fin 2=>x)=![x,x] by ext i j; fin_cases i <;> simp,hv.2.2]
 rfl

variable {O:ChartRatio G} {K:Kin V O} {T T':PathData G} {φ:ℕ→ℕ} {s:Supply.Sheet G} {D:Supply.Rolls s} {P:PostCost D}
private lemma fiscal_cont (x:fieldDir G c 1) : Continuous (fun M=> fiscal M x) :=continuous_finset_sum _ fun _ _=>by fun_prop
lemma preliminary (hk:K.Planned P) (hV:V.Suffices X) (hS:∀ n≥m, Bid.Sworn (V.H n m) c₀ G) (h:Flutter (N.params m).clip (fun i=>K.path (φ i) m) T c₀) (hφ:Tendsto φ atTop atTop)
    {M : Matrix (Body 1 c₀) (Body 1 c₀) ℝ} (hM:Tendsto (fun i=>Linear.Kactual V i m p) atTop (nhds M)):
    Pointwise (intended (m:=c₀) (N.params m).clip T) ∧ ∀ k≤2,∀ v,dirT (intended (N.params m).clip T) k 0 v=phases k M v:=by
 let W i:=K.path (φ i) m
 have hh:=hφ.eventually (eventually_ge_atTop m)
 have hv : ∀ᶠ i in atTop, ∀ k≤2,∀ v,dirT (intended (N.params m).clip (W i)) k 0 v=phases k (Linear.Kactual V (φ i) m p) v:=by
   filter_upwards [hh,h.bound_var] with i hi ⟨σ,C,Λ,hZ⟩
   exact (low_works hZ (hV.all _ _ hi c₀) (hS _ hi) (hk.links _ _ hi)).2.2
 refine ⟨?_,?_⟩
 · obtain ⟨σ,C,Λ,hZ⟩:=h.bound_root
   rw [intent]; exact ((stain_knit _ _ hZ).add (stain_ink T.cubic hZ.width hZ.three (fun i=>(hZ.invariant i).2.1))).add (stain_ink T.quartic hZ.width hZ.four (fun i=>(hZ.invariant i).2.2))
 have ht:=h.reading (E:=Stationary.Link G c₀) (input G c₀) (input_zero ..) (fun i=> show ContDiffAt ℝ ω (fun x=>G.mat (represent (arm G c₀ 1 x) i)) 0 from (Work.F03.represent_smooth i).contDiffAt.comp (0:Link G c₀) (arm G c₀ 1).contDiff.contDiffAt)
 intro k hk v; apply tendsto_nhds_unique (f:=fun i=>dirT (intended (N.params m).clip (W i)) k 0 v) (l:=atTop) ?_ ?_
 · exact tracks_t _ _ _ ht k v
 suffices Tendsto (fun i=>phases k (Linear.Kactual V (φ i) m p) v) atTop (nhds (phases k M v)) from this.congr' (hv.mono (fun i hi=>(hi k hk v).symm))
 unfold phases; split_ifs
 · exact ((fiscal_cont _).continuousAt.tendsto.comp hM).comp hφ
 exact tendsto_const_nhds
lemma basal_comparison (hk:K.Planned P) (hV:V.Suffices X) (hf:Linear.SizeFloor N.clock.kernel.penalty N) (hS:∀ n≥m,Bid.Sworn (V.H n m) c₀ G)
 (φ ψ:ℕ→ℕ) (hφ:Tendsto φ atTop atTop) (hψ:Tendsto ψ atTop atTop) {T':PathData G}
 (h₁ : Flutter (N.params m).clip (fun i=>K.path (φ i) m) T c₀) (h₂ : Flutter (N.params m).clip (fun i=>K.path (ψ i) m) T' c₀) : Matches 2 (AT c₀ (N.params m).clip T) (AT c₀ (N.params m).clip T') 0 :=by
 obtain ⟨M,hM⟩:=Linear.K_tendsto V hV hf m p
 have h_L := preliminary hk hV hS h₁ hφ hM
 have h_R := preliminary hk hV hS h₂ hψ hM
 have hx : Matches 2 (intended (m:=c₀) (N.params m).clip T) (intended _ T') 0:=⟨h_L.1.analytic.contDiffAt,h_R.1.analytic.contDiffAt,fun i hi=>dirT_ext h_L.1.analytic.contDiffAt h_R.1.analytic.contDiffAt (fun v=> (h_L.2 i hi v).trans (h_R.2 i hi v).symm)⟩
 have he(T:PathData G) : intended (N.params m).clip T ∘ (arm G c₀ 1).symm= AT c₀ (N.params m).clip T:=funext fun i=> by dsimp [Function.comp_apply,intended,input,AT]; rw [(arm G c₀ 1).apply_symm_apply]
 exact he T ▸ he T' ▸ (show Matches 2 (intended (N.params m).clip T) (intended (N.params m).clip T') ((arm G c₀ 1).symm 0) from ((arm G c₀ 1).symm.map_zero.symm ▸ hx)).comp_refl (arm G c₀ 1).symm.contDiff.contDiffAt
end YM.Extension.UV.StationaryData
