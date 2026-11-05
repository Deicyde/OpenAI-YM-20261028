import YM.RG08.Action.Walkprice
/-! # Path derivative difference; pre/post switch to smoothing A0 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Staffer
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect Conductor Bloch UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m c f L : Side} {F : Link G m→ℝ} {r i j : ℕ}
variable {V : Verse (Loc G 1)}
lemma directed (h : Pointwise F) (x : PAC (Candles G) m)(hp : ∀ j≤ r,Tensor.coeff F j 0=recital (V j) m) (hf : ∀ j,Summable (V j)) :
    let a:=fderiv ℝ (dragged G m) 0 x
    stanza (V r) m a=stanza (V r) m (bundleLink x)-∑ j∈range r, stanza (cropWax (V j) r) m x := by
  intro a
  let P t:= dragged G m ((t:ℝ)•x); let A t:= ((t:ℝ) • (bundleSites (G:=G) (m:=m)) x)
  have hu : P 0=0:= by unfold P; simp
  have Hx: AnalyticAt ℝ P 0 := AnalyticAt.comp (f:=fun t:ℝ=>t•x) ((zero_smul ℝ x).symm ▸ dragged_analytic) (analyticAt_id.smul analyticAt_const)
  obtain ⟨v,hv,he⟩:= stretchable Hx hu
  have HT : HasDerivAt (fun t:ℝ=> t • v t) (v 0) 0 := by simpa using! (hasDerivAt_id (0:ℝ)).smul hv.differentiableAt.hasDerivAt
  have H : v 0=a := (HT.congr_of_eventuallyEq (f₁:=P) he).unique (Push.side _ dragged_analytic.differentiableAt x) -- names
  have hh: Tendsto A (𝓝 0) (𝓝 0) := (show Continuous A from continuous_id.smul continuous_const).tendsto' _ _ (zero_smul ..)
  have hF k (hi:k≤r) : jet F k=stanza (V k) m := by rw [jet_coefficient,hp k hi]; rfl
  have hs: Fit (r+1) (fun t=>F (t • bundleLink x)) (fun t=> ∑ k∈range (r+1), stanza (V k) m (P t)) := by
    have hy:= jet_path F v (life_price (hv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)) (h.analytic.contDiffAt.of_le le_top) r
    refine (Fit.join (Fit.supply ?_ _) hy).join (Fit.supply ?_ _)
    · filter_upwards [(hh.eventually h.guard).filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds] with t ht hp
      have hh:P t=moveField (A t) := by unfold P dragged A; rw [Function.comp_apply,map_smul]
      change F (t • bundleLink x)=_; rw [←hp,hh]; exact ht.symm
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
    apply sum_congr rfl; intro k hk; rw [ht,mnemonic,hF k (by have hz:=mem_range.mp hk; omega)]; rfl
  have hl (j) : ContDiffAt ℝ ∞ (stanza (V j) m∘ P) 0 := ((stanza_smooth ..).contDiffAt.of_le le_top).comp _ Hx.contDiffAt
  have hh:= aspiredV hs (directions (h.analytic.contDiffAt.of_le le_top) _) (ink_aspire (ContDiffAt.sum (fun i _=>hl i))) (Nat.le_refl r)
  have he' : ink (fun t:ℝ=> stanza (V r) m (P t)) r=stanza (V r) m a := by
    let g t := stanza (V r) m (v t)
    have ht : ContDiffAt ℝ ∞ g 0 := ((stanza_smooth ..).contDiffAt.of_le le_top).comp _ hv.contDiffAt
    let V' t:= t^r*g t
    have hr : (fun t=> stanza (V r) m (P t))=ᶠ[𝓝 0] V' := he.mono (fun i hi=> by dsimp only; rw [hi, mnemonic])
    have hx := aspiredV (Fit.supply (hr.filter_mono nhdsWithin_le_nhds) (r+1)) (ink_aspire (hl _)) (ink_aspire (f:=V') ((contDiffAt_id.pow r).mul ht)) (Nat.le_refl r)
    change ink _ r=ink V' r at hx
    rw [hx, show ink V' r= _ from ink_t_pow g ht r r, if_pos le_rfl, Nat.sub_self, ink_0]; unfold g; rw [H]
  change jet F r (bundleLink x)=ink (fun t=>∑ k∈range (r+1), stanza (V k) m (P t)) r at hh
  rw [ink_list (range (r+1)) (fun i t=> stanza (V i) m (P t)) (fun i _=> hl i), Finset.sum_range_succ,he',hF r le_rfl] at hh
  rw [hh]; have he : ∀ i, ink (fun t=> stanza (V i) m (P t)) r= stanza (cropWax (V i) r) m x := fun i=> silkOpus (hf i) x
  simp_rw [he,add_sub_cancel_left]
lemma emblem (α β : Type)[Fintype α][Fintype β](F : Shale α i)(T : Cross L α β) : flow F T=scrollL (grapes L F) T := rfl
lemma flow_view (F : Shale (Candles G) i) (Q : Cross L (Candles G) (Loc G 1)) (hk : Summable F) (hv : Whole Q)(x : PAC (Loc G 1) c) :
    let s : Ratio c (c*L):=⟨L,rfl⟩
    stanza (flow F Q) c x= stanza F (c*L) (installed s Q *ᵥ x) := by
  intro s; rw [emblem _ _ _, scroll_play (grapes_summable L hk) hv]; exact grapes_stanza s (Q.acts c *ᵥ x) hk

end YM.RG08.Staffer
