import YM.Extension.UV.Station.ValidLimit
import YM.AnalyticNext.CUBIC_MATCH.Terms.Normal
/-! Local Taylor accounting at zero. None of the masked return maps interchanges follow by suppressing flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.StationaryData
open Set Filter Function RG Wilson
open scoped Topology BigOperators Classical ContDiff
section combination
variable {E F V D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup D] [NormedSpace ℝ D]
  {f f' : ℕ→E→F} {g g' : E→F}{r: WithTop ℕ∞} {x:E}
structure Tracks (r:WithTop ℕ∞) (f:ℕ→E→F) (g:E→F) (x:E) : Prop where
  at_each : ∀ᶠ n in atTop, ContDiffAt ℝ r (f n) x
  at_limit : ContDiffAt ℝ r g x
  jet (k:ℕ): k ≤ r → Tendsto (fun n=> iteratedFDeriv ℝ k (f n) x) atTop (nhds (iteratedFDeriv ℝ k g x))
lemma mapply {ι:Type*} [Fintype ι] {M:ι→Type*} [∀i,NormedAddCommGroup (M i)] [∀i,NormedSpace ℝ (M i)] {h : ℕ→ ContinuousMultilinearMap ℝ M F} {y} (hh:Tendsto h atTop (𝓝 y)) {v:ℕ→∀ i,M i} {z:∀ i,M i} (hv:Tendsto v atTop (𝓝 z)) : Tendsto (fun n=> h n (v n)) atTop (𝓝 (y z)):=by
  suffices he:Tendsto (fun n=> (h n-y) (v n)) atTop (nhds 0) from by simpa [sub_add_cancel] using he.add (y.cont.continuousAt.tendsto.comp hv)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) (Eventually.of_forall fun n=> ContinuousMultilinearMap.le_opNorm ..) ?_
  have ht : Tendsto (fun n=> ∏ i, ‖v n i‖) atTop (nhds (∏ i,‖z i‖)) := tendsto_finsetProd _ (fun i hi=>(tendsto_pi_nhds.mp hv i).norm)
  simpa only [norm_zero,sub_self,zero_mul] using ((hh.sub_const y).norm.mul ht)
namespace Tracks
variable (h:Tracks r f g x)
include h
lemma add (hh:Tracks r f' g' x): Tracks r (fun i=>f i+f' i) (g+g') x:= by
  have hp := h.at_each; have hp' := hh.at_each; have hz:=hp.and hp'
  refine ⟨hz.mono (fun i hi=>hi.1.add hi.2),h.at_limit.add hh.at_limit,?_⟩
  intro k hk; rw [iteratedFDeriv_add_apply (h.at_limit.of_le hk) (hh.at_limit.of_le hk)]; apply ((h.jet k hk).add (hh.jet k hk)).congr'; filter_upwards [hz] with n ⟨h,h'⟩; exact (iteratedFDeriv_add_apply (h.of_le hk) (h'.of_le hk)).symm
lemma neg : Tracks r (fun i=> -f i) (-g) x:= by
  refine ⟨h.at_each.mono (fun _ hi=>hi.neg),h.at_limit.neg,fun k hk=> ?_⟩
  simp only [iteratedFDeriv_neg_apply]; exact (h.jet k hk).neg
lemma sub (hh:Tracks r f' g' x): Tracks r (fun i=>f i-f' i) (g-g') x:= by simpa only [sub_eq_add_neg] using h.add hh.neg
omit h in
lemma unswerving (g:E→F)(hg:ContDiffAt ℝ r g x):Tracks r (fun _=>g) g x:=⟨Eventually.of_forall (fun _=>hg),hg,fun _ _=> tendsto_const_nhds⟩
lemma evaluated : Tendsto (fun i=>f i x) atTop (𝓝 (g x)) := by
  let z : ℕ→(Fin 0→E):= fun _=>0
  have hv := mapply (h.jet 0 (mod_cast bot_le)) (show Tendsto z atTop (𝓝 0) by exact tendsto_const_nhds); simpa only [iteratedFDeriv_zero_apply] using hv
lemma weaken {s:WithTop ℕ∞}(hs:s≤r):Tracks s f g x:=⟨h.at_each.mono fun _ hn=>hn.of_le hs,h.at_limit.of_le hs,fun k hk=>h.jet k (hk.trans hs)⟩
lemma same (h':f'=f) (he:g'=g) :Tracks r f' g' x := h' ▸ he ▸ h
omit h in
set_option linter.unusedSectionVars false in
lemma finset_sum {ι:Type*} (A:ι→ℕ→E→F) (B:ι→E→F) (s:Finset ι) (H:∀ i∈s,Tracks r (A i) (B i) x): Tracks r (fun i y=>∑ t∈s,A t i y) (fun y=>∑t∈s, B t y) x:=by
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using unswerving _ contDiffAt_const
  | @insert a s ha ih => exact ((H a (Finset.mem_insert_self ..)).add (ih (by exact fun i hi=> H _ (Finset.mem_insert_of_mem hi)))).same (by funext _ _; rw [Finset.sum_insert ha];rfl) (by funext _; rw [Finset.sum_insert ha];rfl)
include h in
set_option maxHeartbeats 2000000 in
lemma comply {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p:ℕ→F→V} {q:F→V}(hv:Tracks r p q (g x)) (ht:∀ᶠ i:ℕ in atTop, g x=f i x): Tracks r (fun i=>p i ∘ f i) (q ∘ g) x:=by
  refine ⟨(h.at_each.and (hv.at_each.and ht)).mono (fun i hz=>ContDiffAt.comp _ (show ContDiffAt ℝ r (p i) (f i x) from hz.2.2 ▸ hz.2.1) hz.1),hv.at_limit.comp _ h.at_limit,fun k hk=>?_⟩ -- rewrites before placeholder
  have he (a:OrderedFinpartition k) : Tendsto (fun n=>iteratedFDeriv ℝ a.length (p n) (f n x)) atTop (nhds (iteratedFDeriv ℝ a.length q (g x))) := (hv.jet a.length (le_trans (by exact_mod_cast a.length_le) hk)).congr' (ht.mono fun i hi=>by rw [hi])
  let K (a:OrderedFinpartition k) := a.compAlongOrderedFinpartitionL ℝ E F V
  have hu a := mapply (h:=fun n=>K a (iteratedFDeriv ℝ a.length (p n) (f n x))) ((K a).continuous.continuousAt.tendsto.comp (he a)) (v:=fun n i=>iteratedFDeriv ℝ (a.partSize i) (f n) x) (tendsto_pi_nhds.mpr fun i=>h.jet (a.partSize i) (le_trans (by exact_mod_cast a.partSize_le i) hk))
  have hy: Tendsto (fun n=> (ftaylorSeries ℝ (p n) (f n x)).taylorComp (ftaylorSeries ℝ (f n) x) k) atTop (nhds ((ftaylorSeries ℝ q (g x)).taylorComp (ftaylorSeries ℝ g x) k)):=by
    apply tendsto_finsetSum; intro a _; exact hu a
  rw [iteratedFDeriv_comp hv.at_limit h.at_limit hk]
  apply hy.congr'; filter_upwards [ht,h.at_each,hv.at_each] with n hi hn hn'
  rw [hi] at hn'; exact Eq.symm (iteratedFDeriv_comp hn' hn hk)
section product
variable {p:ℕ→E→V} {q:E→V}
-- mapply for different family type above
lemma inline (p:F→V) (hp:ContDiffAt ℝ r p (g x))(hf : ∀ᶠ i in atTop,g x=f i x) :Tracks r (fun i=>p ∘ f i) (p ∘ g) x:=h.comply (unswerving _ hp) hf
lemma linear (p:F→L[ℝ] V):Tracks r (fun i=>p ∘ f i) (p ∘ g) x:= by
  refine ⟨h.at_each.mono (fun i w=>p.contDiff.contDiffAt.comp x w),p.contDiff.contDiffAt.comp x h.at_limit,fun k hk=> ?_⟩
  rw [p.iteratedFDeriv_comp_left h.at_limit hk]
  have hh:= ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _:Fin k=>E) F V p).continuous.continuousAt.tendsto.comp (h.jet k hk))
  apply hh.congr'
  filter_upwards [h.at_each] with n hn; dsimp only [Function.comp_apply]; rw [p.iteratedFDeriv_comp_left hn hk]; rfl
lemma pair (p:ℕ→E→V) (hp:Tracks r p q x): Tracks r (fun n y=>(f n y,p n y)) (fun y=>(g y,q y)) x:= by
  refine (h.linear (ContinuousLinearMap.inl ℝ F V) |>.add (hp.linear (ContinuousLinearMap.inr ℝ F V))).same (by funext; simp) (by funext; simp)
end product
end Tracks
end combination
end YM.Extension.UV.StationaryData
