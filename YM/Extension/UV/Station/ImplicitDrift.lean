import YM.Extension.UV.Station.Partition
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology BigOperators Classical
open Finset Filter YM.WilsonStartup.Change
namespace YM.Extension.UV.StationaryData
variable {E F V : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
abbrev Lift (E F:Type) := E×F
abbrev Profile (E F:Type):= E × F → ℝ
set_option linter.unusedSectionVars false

namespace Tracks
lemma next {f:ℕ→E→F}{g:E→F}{x:E}(h:Tracks ∞ f g x): Tracks ∞ (fun i=> fderiv ℝ (f i)) (fderiv ℝ g) x:=by
 refine ⟨h.at_each.mono (fun _ hi=>hi.fderiv_right (by norm_cast)),h.at_limit.fderiv_right (by norm_cast),fun k _=>?_⟩
 let e:=continuousMultilinearCurryRightEquiv' ℝ k E F
 have hv:= h.jet (k+1) (by exact_mod_cast (le_top (a:=(k:ENat)+1)))
 have ht:= ContinuousAt.tendsto e.continuous.continuousAt |>.comp hv
 simpa [e,Function.comp_def,iteratedFDeriv_succ_eq_comp_right] using ht
local notation "Star"=>E×F
private lemma vert_rule (P:Star→ℝ)(h:ContDiffAt ℝ ∞ P 0):(fun z=> fderiv ℝ P z ∘L (ContinuousLinearMap.inr ℝ E F)) =ᶠ[𝓝 0] vert P:=by
 filter_upwards [(h.of_le (m:=1) (by exact_mod_cast (le_top (a:=(1:ENat))))).eventually (by simp)] with z hz
 exact (hz.differentiableAt (by simp)|>.hasFDerivAt.comp z.2 ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))).fderiv.symm
lemma vertical {f:ℕ→(E×F)→ℝ}{g:E×F→ℝ}(h:Tracks ∞ f g 0): Tracks ∞ (vert ∘ f) (vert g) (0:Star):=by
 let L := ContinuousLinearMap.inr ℝ E F
 have hx : Tracks ∞ (fun i z => fderiv ℝ (f i) z ∘L L) (fun z=>fderiv ℝ g z ∘L L) (0:Star):=h.next.linear ((ContinuousLinearMap.apply ℝ _ L).comp (ContinuousLinearMap.compL ℝ _ _ _)) -- check
 have he := vert_rule g h.at_limit
 have hy : ∀ᶠ n in atTop, (fun z=>fderiv ℝ (f n) z ∘L L) =ᶠ[𝓝 0] vert (f n):= h.at_each.mono fun n=>vert_rule (f n)
 refine ⟨(hy.and hx.at_each).mono <| fun i hi=>hi.2.congr_of_eventuallyEq hi.1.symm,hx.at_limit.congr_of_eventuallyEq he.symm,fun k hk=> ?_⟩
 rw [← (he.iteratedFDeriv ℝ k).self_of_nhds]; exact (hx.jet k hk).congr' (hy.mono fun n hn=> (hn.iteratedFDeriv ℝ k).self_of_nhds)
end Tracks
lemma clm_comp_apply (f:ℕ→E→L[ℝ] F)(g:E→L[ℝ] F) (x:ℕ→E)(y:E) (h:Tendsto f atTop (𝓝 g))(hx:Tendsto x atTop (𝓝 y)): Tendsto (fun n=>f n (x n)) atTop (𝓝 (g y)):=by
 exact ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds hx))
lemma connection (f:ℕ→E→F) (g:E→F)(x:E)(h:Tracks ∞ f g x): Tendsto (fun i=> fderiv ℝ (f i) x) atTop (𝓝 (fderiv ℝ g x)):=h.next.evaluated
lemma tensor_joint (h:E×F→V)(p:E→E)(q:E→F) (x:E){k} (hp:ContDiffAt ℝ ∞ p x)(hq:ContDiffAt ℝ ∞ q x) (v:E): dirT (fun z=> (p z,q z)) k x v=(dirT p k x v,dirT q k x v):=by
 ext1 <;> rw [dirT,iteratedFDeriv_prodMk hp hq (show (k:WithTop ENat) ≤ ∞ by exact_mod_cast (le_top (a:=(k:ENat))))] <;> rfl
private def solo (k:ℕ):Finset (OrderedFinpartition (k+1)) := univ.filter fun c=>c.length=1
lemma solo_pos (k:ℕ)  : 0<(solo k).card:=by
 let c : OrderedFinpartition (k+1) := {
    length:=1
    partSize:=fun _=>k+1
    partSize_pos:=by intros; omega
    emb:=fun _ i=>i
    emb_strictMono:=fun _ _ _ h=>h
    parts_strictMono:=Subsingleton.strictMono _
    disjoint:=fun _ _ _ _ h=>False.elim (h (Subsingleton.elim _ _))
    cover:=fun x=>⟨0,Set.mem_range_self x⟩ }
 exact card_pos.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
abbrev bundle (P:Profile E F): Lift E F→F→L[ℝ] ℝ := vert P
private def D (P:Profile E F): F→L[ℝ] F→L[ℝ] ℝ := fderiv ℝ (bundle P) 0 ∘L ContinuousLinearMap.inr ℝ E F
lemma layer_station (u:E→F)(P:Profile E F)(h:Station P u) (hs:ContDiffAt ℝ ω P 0) v k:
    ∑ a∈univ \ solo k, contribution a (bundle P) (graph u) 0 v + ((solo k).card : ℝ) • fderiv ℝ (bundle P) 0 (dirT (graph u) (k+1) 0 v)=0:=by
 have hh : graph u 0=0:=by exact Prod.ext rfl h.starts
 have hp : ContDiffAt ℝ ∞ (bundle P) (graph u 0):= by rw [hh]; apply ((matches_self 1 hs).diff_vert.left.of_le le_top)
 have ht := pipeline (bundle P) (graph u) _ hp (h.chart.of_le (by exact le_top)) (k+1) v
 have hz := congr_arg (fun A=>@A (fun _=>v)) ((h.law.iteratedFDeriv ℝ (k+1)).self_of_nhds) -- A type inference
 have hz : dirT (bundle P ∘ graph u) (k+1) 0 v=0 := by unfold dirT; rw [(h.law.iteratedFDeriv ℝ (k+1)).self_of_nhds]; simp
 rw [ht,← sum_sdiff (subset_univ (solo k))] at hz
 rw [←hz]; congr 1
 suffices ∀ a∈solo k, contribution a (bundle P) (graph u) 0 v=fderiv ℝ (bundle P) 0 (dirT (graph u) (k+1) 0 v) by rw [sum_congr rfl this,sum_const, Nat.cast_smul_eq_nsmul ℝ]
 intro a ha
 have hℓ := (mem_filter.mp ha).2
 haveI : Nonempty (Fin a.length):= by rw [hℓ]; infer_instance
 unfold contribution
 rw [show (fun i=>dirT (graph u) (a.partSize i) 0 v)=(fun _=>dirT (graph u) (k+1) 0 v) from funext fun i=> by rw [solo_part _ hℓ i],hℓ,iteratedFDeriv_one_apply,hh]
variable [CompleteSpace F]
lemma solved {H:ℕ→Profile E F} {J:Profile E F} (f:ℕ→E→F) (g:E→F)
   (h:Tracks ∞ H J (0:Lift E F)) (hω:∀ᶠ n in atTop, ContDiffAt ℝ ω (H n) 0) (hj:ContDiffAt ℝ ω (J) 0) (hf:∀ᶠ n in atTop,Station (H n) (f n)) (hg:Station J g)
   (hy:∀ᶠ n in atTop,(D (H n)).IsInvertible) (hq:(D J).IsInvertible) :
     ∀ k v, Tendsto (fun n=>dirT (f n) k 0 v) atTop (𝓝 (dirT g k 0 v)):=by
 intro k; induction k using Nat.strong_induction_on with
 | h k ih=> cases k with
    | zero=> intro v; simp only [dirT_zero,hg.starts]; exact Filter.EventuallyEq.tendsto (hf.mono fun i hi=>hi.starts)
    | succ k=>
      intro v
      let s:=univ \ solo k
      let t:=((solo k).card:ℝ)
      let Δ n:=dirT (graph (f n)) (k+1) 0 v; let q:=dirT (graph g) (k+1) 0 v
      have he : graph g 0=0:=by exact Prod.ext rfl hg.starts
      have hi a (ha:a∈s):∀ i,a.partSize i≤k:=by
        intro i
        letI : Nonempty (Fin a.length) := ⟨i⟩ -- bound order
        by_contra! hℓ
        have hx : Subsingleton (Fin a.length):= ⟨fun p j=>by
            have hji (u:Fin a.length):u=i:=by by_contra hu; have hh:=combined_parts a u i hu; have hv:=a.partSize_pos u; omega
            rw [hji j,hji p]⟩
        have hl:a.length=1:=Nat.eq_one_of_dvd_one (?_) -- or cases a.length with 0 impossible;1 rfl; succ too. Fintype.card_eq_one_iff_nonempty_subsingleton
        · exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨mem_univ _, hl⟩)
        have hv := Fintype.card_le_one_iff_subsingleton.mpr hx; have hpos:= i.isLt; simp only [Fintype.card_fin] at hv; simpa using (show a.length=1 by omega)
      have huv k' (hk:k'≤k) : Tendsto (fun n=>dirT (graph (f n)) k' 0 v) atTop (𝓝 (dirT (graph g) k' 0 v)):=by
        have hh:=(tendsto_const_nhds (f:=atTop) (x:=dirT (id:E→E) k' 0 v)).prodMk_nhds (ih k' (by omega) v) -- `f:=atTop`?
        rw [show (graph g)=(fun z=>(id z,g z)) by rfl,tensor_joint J id g _ contDiffAt_id (hg.regular.of_le le_top)]; apply hh.congr'
        filter_upwards [hf] with n hh; exact (tensor_joint J id (f n) _ contDiffAt_id (hh.regular.of_le le_top) v).symm
      have hl:= partial_tends (s:=s) (fun i=>graph (f i)) (bundle ∘ H) (graph g) (bundle J) v hi (fun a _=>a.length_le) (he.symm ▸ hf.mono fun n hn=>Prod.ext rfl hn.starts) huv (he.symm ▸ h.vertical)
      have hlim : Tendsto (fun n=> t • fderiv ℝ (bundle (H n)) 0 (Δ n)) atTop (𝓝 (t • fderiv ℝ (bundle J) 0 q)):= by
        rw [(neg_eq_of_add_eq_zero_right <| layer_station g J hg hj v k).symm]
        apply hl.neg.congr'; filter_upwards [hf,hω] with n hn hn'; exact neg_eq_of_add_eq_zero_right <| layer_station _ _ hn hn' v k
      have ht : t>0:=by unfold t; exact_mod_cast solo_pos k
      have heq:Tendsto (fun n=> fderiv ℝ (bundle (H n)) 0 (Δ n)) atTop (𝓝 (fderiv ℝ (bundle J) 0 q)):=by simpa only [inv_smul_smul₀ ht.ne'] using (hlim.const_smul t⁻¹)
      let α:=dirT (id:E→E) (k+1) 0 v
      have hEq (f:E→F)(hf:ContDiffAt ℝ ∞ f 0)(P:Profile E F) : fderiv ℝ (bundle P) 0 (dirT (graph f) (k+1) 0 v)=fderiv ℝ (bundle P) 0 (α,0) + D P (dirT f (k+1) 0 v):=by rw [show (graph f)=(fun z=>(id z,f z)) by rfl,tensor_joint P id f _ contDiffAt_id hf]; change (fderiv ℝ (bundle P) 0) (α, dirT f (k + 1) 0 v) = _ + (fderiv ℝ (bundle P) (0:E×F)) (0, dirT f (k + 1) 0 v); simpa only [Prod.mk_add_mk, add_zero, zero_add] using map_add (fderiv ℝ (bundle P) 0) (α,0) (0,dirT f (k+1) 0 v)
      have hdF:=connection _ _ _ h.vertical
      have hv : Tendsto (fun n=> fderiv ℝ (bundle (H n)) 0 (α,0)) atTop _ := clm_comp_apply _ _ _ (α,0) hdF tendsto_const_nhds
      have hd : Tendsto (fun n=>D (H n)) atTop (𝓝 (D J)) := ContinuousAt.tendsto (show ContinuousAt (fun U=>(U:Lift E F →L[ℝ] F→L[ℝ] ℝ) ∘L ContinuousLinearMap.inr ℝ E F) (_:_) by fun_prop) |>.comp hdF
      have hm : Tendsto (fun n => D (H n) (dirT (f n) (k+1) 0 v)) atTop (𝓝 (D J (dirT g (k+1) 0 v))):=by
        have hn:=heq.sub hv
        simp_rw [q,hEq _ (hg.regular.of_le le_top) J,add_sub_cancel_left] at hn
        apply hn.congr'; filter_upwards [hf] with i hi
        change (fderiv ℝ (bundle (H i)) 0) (Δ i) - (fderiv ℝ (bundle (H i)) 0) (α,0) = _
        rw [show (fderiv ℝ (bundle (H i)) 0) (Δ i)= _ + D _ _ from hEq _ (hi.regular.of_le le_top) _,add_sub_cancel_left]
      have hI : Tendsto (fun i=>(D (H i)).inverse) atTop (𝓝 (D J).inverse):=ContinuousAt.tendsto ((hq.contDiffAt_map_inverse (n:=1)).continuousAt) |>.comp hd
      rw [← hq.inverse_apply_self (dirT g (k+1) 0 v)]; exact (clm_comp_apply _ _ _ _ hI hm).congr' (hy.mono fun n hn=> hn.inverse_apply_self ..)
#print axioms solved
end YM.Extension.UV.StationaryData
