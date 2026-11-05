import YM.Extension.UV.Station.Flutter
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open scoped ContDiff Topology BigOperators
open Finset Filter YM.WilsonStartup.Change
namespace YM.Extension.UV.StationaryData
variable {E F V : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup V][NormedSpace ℝ V] {f:ℕ→E→F}{h:E→F}{x:E}

namespace Tracks
lemma outside (w:Tracks ∞ f h x) (g:F→V) (hg:ContDiffAt ℝ ω g (h x)): Tracks ∞ (fun n=>g ∘ f n) (g ∘ h) x:=by
  have he:= w.evaluated
  have hh:= he.eventually (hg.eventually (by simp))
  refine ⟨(w.at_each.and hh).mono (fun i hi=>hi.2.of_le (m:=∞) le_top |>.comp _ hi.1),hg.of_le (m:=∞) le_top|>.comp _ w.at_limit,fun k hk=>?_⟩
  have hv (a:OrderedFinpartition k):=hg.continuousAt_iteratedFDeriv (k:=a.length) le_top |>.tendsto.comp he
  let K (a:OrderedFinpartition k):= a.compAlongOrderedFinpartitionL ℝ E F V
  have hu a := mapply (h:=fun n=>K a (iteratedFDeriv ℝ a.length g (f n x))) ((K a).continuous.continuousAt.tendsto.comp (hv a)) (v:=fun n i=>iteratedFDeriv ℝ (a.partSize i) (f n) x) (tendsto_pi_nhds.mpr fun i=>(w.jet (a.partSize i) (le_trans (by exact_mod_cast (a.partSize_le i)) hk)))
  have hy: Tendsto (fun n=>FormalMultilinearSeries.taylorComp (ftaylorSeries ℝ g (f n x)) (ftaylorSeries ℝ (f n) x) k) atTop (nhds (FormalMultilinearSeries.taylorComp (ftaylorSeries ℝ g (h x)) (ftaylorSeries ℝ h x) k)):=by apply tendsto_finsetSum; intro a _;exact hu a
  rw [iteratedFDeriv_comp (hg.of_le le_top) w.at_limit hk]; apply hy.congr'
  filter_upwards [hh,w.at_each] with n hn hp; exact (iteratedFDeriv_comp (hn.of_le (m:=∞) le_top) hp hk).symm
lemma vert_moving {p:ℕ→(E×F)→V}{g:E×F→V}{t:E×F}(h:Tracks ∞ p g t): Tracks ∞ (vert ∘ p) (vert g) t:=by
 let L := ContinuousLinearMap.inr ℝ E F
 have ht (Q:E×F→V) (hQ:ContDiffAt ℝ ∞ Q t): (fun x=> fderiv ℝ Q x ∘L L) =ᶠ[𝓝 t] vert Q:= by
    filter_upwards [(hQ.of_le (by norm_cast : (1:WithTop ℕ∞) ≤ ∞)).eventually (by simp)] with ⟨x,y⟩ hxy
    have hd : HasFDerivAt (fun y : F => (x,y)) L y := (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
    exact ((hxy.differentiableAt (by simp)).hasFDerivAt.comp y hd).fderiv.symm
 have hx : Tracks ∞ (fun i z => fderiv ℝ (p i) z ∘L L) (fun z=>fderiv ℝ g z ∘L L) t:=h.next.linear ((ContinuousLinearMap.apply ℝ _ L).comp (ContinuousLinearMap.compL ℝ _ _ _))
 have he := ht g h.at_limit
 have hy : ∀ᶠ n in atTop, (fun z=>fderiv ℝ (p n) z ∘L L) =ᶠ[𝓝 t] vert (p n):= h.at_each.mono fun n=>ht (p n)
 refine ⟨(hy.and hx.at_each).mono <| fun i hi=>hi.2.congr_of_eventuallyEq hi.1.symm,hx.at_limit.congr_of_eventuallyEq he.symm,fun k hk=> ?_⟩
 rw [← (he.iteratedFDeriv ℝ k).self_of_nhds]; exact (hx.jet k hk).congr' (hy.mono fun n hn=> (hn.iteratedFDeriv ℝ k).self_of_nhds)
end Tracks
variable {q:ℕ→E→ℝ}{p:E→ℝ}{z:ℕ→E→ℝ}{r:E→ℝ}{f:ℕ→E→F}{g:E→F}{k: ℕ}
lemma prod_contour (hz:Tracks ∞ q p x)(hr:Tracks ∞ z r x) : Tracks ∞ (fun n=>q n*z n) (p*r) x:= ((hz.pair _ hr).outside (fun ⟨u,v⟩=>((u:ℝ)*v)) (((contDiffAt_fst (𝕜:=ℝ)).mul contDiffAt_snd))).same rfl rfl
lemma finproduct {ι:Type} (f:ι→ℕ→E→ℝ)(g:ι→E→ℝ)(s:Finset ι)(h:∀ i∈s,Tracks ∞ (f i) (g i) x): Tracks ∞ (fun n=> ∏ i∈s,f i n) (∏ i∈s,g i) x:=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [prod_empty]; exact Tracks.unswerving _ contDiffAt_const
 | insert i s hi ih=> simp only [Finset.prod_insert hi]; exact prod_contour (h i (Finset.mem_insert_self ..)) (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
noncomputable def slice_det {ι:Type} [Fintype ι][DecidableEq ι] (fr:ι→F) (q:E×F→ℝ) (z:E×F):ℝ:=Matrix.det (Matrix.of fun i j => iteratedFDeriv ℝ 2 (fun w=>q (z.1,w)) z.2 ![fr i,fr j])
-- iteration with explicit Key
lemma determinant_tracks {ι:Type} [Fintype ι][DecidableEq ι] {H:ℕ→E×F→ℝ}{Q:E×F→ℝ}(fr:ι→F)(h:Tracks ∞ H Q 0) : Tracks ∞ (slice_det fr ∘ H) (slice_det fr Q) 0 :=by
  let f (P:E×F→ℝ) i j (z:E×F) := iteratedFDeriv ℝ 2 (fun w=>P (z.1,w)) z.2 ![fr i,fr j]
  have hi i j : Tracks ∞ (fun n=>f (H n) i j) (f Q i j) 0:= by
    unfold f; simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,Matrix.cons_val_one]
    change Tracks ∞ (fun n z=>vert (vert (H n)) z (fr i) (fr j)) (fun z=>vert (vert Q) z (fr i) (fr j)) 0
    -- Tracks.vertical currently only 0! restrict x to 0
    have hv := h.vert_moving.vert_moving.outside (fun L=>(L:F→L[ℝ] F→L[ℝ]ℝ) (fr i) (fr j)) ((contDiffAt_id.clm_apply contDiffAt_const).clm_apply contDiffAt_const)
    exact hv
  let J (P:E×F→ℝ) (z:E×F):= ∑ s: Equiv.Perm ι,Equiv.Perm.sign s • ((∏ i,f P (s i) i) z)
  have hJ : Tracks ∞ (J ∘ H) (J Q) 0:=by
     apply Tracks.finset_sum (fun s n z=>(Equiv.Perm.sign s) • ((∏ i,f (H n) (s i) i) z)) _ _; intro s hs
     have ho:= finproduct (fun i n=>f (H n) (s i) i) _ univ (fun i hi'=>hi (s i) i)
     exact ho.outside (fun y:ℝ=>Equiv.Perm.sign s • y) (by simp only [Units.smul_def]; exact contDiffAt_id.const_smul _)
  have he (P:E×F→ℝ): slice_det fr P = J P := funext fun z=> by simp only [J,slice_det,Matrix.det_apply, Matrix.of_apply,f, Finset.prod_apply]
  exact hJ.same (funext fun n=>he _) (he _)
end YM.Extension.UV.StationaryData
