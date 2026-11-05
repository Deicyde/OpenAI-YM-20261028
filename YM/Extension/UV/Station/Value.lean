import YM.Extension.UV.Station.ImplicitDrift
/-! If lower incoming jets match, the stationary pullback difference at the first
unmatched jet is the pure incoming difference through the linear response.
No equality of finite-cutoff representations imposed. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology BigOperators
open Finset Filter YM.WilsonStartup.Change
namespace YM.Extension.UV.StationaryData
variable {E F V : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
private lemma lawful {P:Profile E F}{u:E→F} (h:Station P u) (hf:ContDiffAt ℝ ω P 0): Work.F04.vert P ∘ graph u=ᶠ[𝓝 0] 0:=by
 filter_upwards [h.law,h.home.eventually (hf.eventually (by simp))] with x hx hh
 exact ((Work.F04.hasFDerivAt_slice P x (u x) (hh.differentiableAt (by simp))).fderiv).symm.trans hx
lemma grade_tangent {P:Profile E F}{u:E→F} (h:Station P u)(hf:ContDiffAt ℝ ω P 0) (v:F) (x:E):
    dirT P 1 0 (0,v) =0 ∧ iteratedFDeriv ℝ 2 P 0 ![fderiv ℝ (graph u) 0 x,(0,v)] =0 ∧ iteratedFDeriv ℝ 2 P 0 ![(0,v),fderiv ℝ (graph u) 0 x] =0 := by
 have hz: Work.F04.vert P (graph u 0)=0 := (lawful h hf).self_of_nhds; rw [h.at0] at hz
 have hder := (lawful h hf).fderiv_eq (𝕜:=ℝ)
 have hu :=congr_arg (fun Q:E→L[ℝ] F→L[ℝ] ℝ =>Q x v) hder
 rw [fderiv_comp _ (show DifferentiableAt ℝ (Work.F04.vert P) (graph u 0) by rw [h.at0]; exact (Work.F04.vert_smooth P _ hf).differentiableAt (by simp)) (h.chart.differentiableAt (by simp)), show fderiv ℝ (0:E→F→L[ℝ] ℝ) 0=0 by simp,h.at0] at hu
 have ht := hf.iteratedFDeriv_comp_perm ![fderiv ℝ (graph u) 0 x,(0,v)] (Equiv.swap (0:Fin 2) 1)
 have hq := (Work.F04.vert_rate P 0 hf (fderiv ℝ (graph u) 0 x) v).symm.trans (show _=0 from hu)
 rw [show ((![fderiv ℝ (graph u) 0 x,(0,v)] ∘ Equiv.swap (0:Fin 2) 1))= ![(0,v),fderiv ℝ (graph u) 0 x] by ext i <;> fin_cases i <;> simp] at ht
 rw [dirT_one,show fderiv ℝ P (0:E×F) ((0,v):E×F)=Work.F04.vert P (0:E×F) v by rfl,hz]; exact ⟨rfl,hq,ht.trans hq⟩
lemma few_tokens {k} (a:OrderedFinpartition k) (i:Fin a.length) (hi : a.partSize i+1≥k):
    a.length=1 ∨ a.length=2:=by
 by_contra! h
 obtain ⟨j,u,hj,hij,hiu,hju⟩ : ∃ j c:Fin a.length, c≠i ∧ j≠i ∧ i≠c ∧ j≠c:=by
   have hv : ∃ j:Fin a.length, j≠i:=by
      by_contra! hv; have := (Fintype.card_le_one_iff_subsingleton (α:=Fin a.length)).mpr ⟨fun a b=>(hv a).trans (hv b).symm⟩
      simp only [Fintype.card_fin] at this; have := i.isLt; omega
   obtain ⟨j,hJ⟩:=hv
   have hc : ∃ u:Fin a.length, u≠i ∧ j≠u:=by
      by_contra! hu; have : univ ⊆ ({i,j}:Finset (Fin a.length)):= fun u _=> mem_insert.mpr (if h:u=i then Or.inl h else Or.inr (mem_singleton.mpr (hu u h).symm))
      have hh := card_le_card this; simp only [card_univ,Fintype.card_fin,card_insert_of_notMem (s:=({j}:Finset _)) (fun v=>False.elim (hJ ((mem_singleton.mp v).symm))),card_singleton] at hh; have := i.isLt; omega
   exact ⟨j,hc.choose,hc.choose_spec.1,hJ,hc.choose_spec.1.symm,hc.choose_spec.2⟩
 have he : ∑ j∈({i,u,j}:Finset (Fin a.length)),a.partSize j≤k:= (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)).trans_eq (counts_parts a)
 simp [hiu, hj,hju, Ne.symm hij,Ne.symm hju] at he
 have := a.partSize_pos u; have :=a.partSize_pos j; omega
lemma graded_part {k m:ℕ} (p:Fin m→ℕ)
    (hl : ∀ i,0<p i) (hm : ∀ i j, i≠j → p i + p j ≤ k) (i:Fin m) (hi : p i+1≥k)(hx:2≤p i) (hℓ:m=1 ∨ m=2)
    {P:Profile E F}{f g:E→F}{v} (hp:Station P f)(hg0:g 0=0)(hz:g 0=f 0) (hs:ContDiffAt ℝ ω P 0)(ht:ContDiffAt ℝ ω g 0)
    (he:dirT (graph g) 1 0 v=dirT (graph f) 1 0 v):
    iteratedFDeriv ℝ m P (graph g 0) (fun i=> dirT (graph g) (p i) 0 v)=0:=by
 have hu k (h:k≥2):dirT (graph g) k 0 v=(0,dirT g k 0 v):=by
   rw [show graph g=(fun x=>(id x,g x)) from rfl,tensor_joint P _ _ _ contDiffAt_id (ht.of_le le_top)]
   congr 1; obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
   have hu (v:E): fderiv ℝ (id:E→E) v=ContinuousLinearMap.id ℝ E:=by simp
   rw [show 2+k=k+1+1 by omega,dirT,iteratedFDeriv_succ_eq_comp_right]; simp [funext hu,Function.comp_def,iteratedFDeriv_succ_const]
 rw [show graph g 0=graph f 0 from Prod.ext rfl hz,hp.at0]
 rcases hℓ with rfl|rfl  
 · rw [iteratedFDeriv_one_apply,hu _ (Subsingleton.elim i 0 ▸ hx)]; simpa only [dirT_one] using (grade_tangent hp hs (dirT g (p 0) 0 v) v).1
 suffices ∀ u j (hne:j≠u),p u≥2 → p j=1 → iteratedFDeriv ℝ 2 P 0 (fun i=> dirT (graph g) (p i) 0 v)=0 by
   have hpj j (h:j≠i): p j=1 := by have hv:=hm _ _ h.symm; have hv:= hl j; omega
   fin_cases i <;> [exact this 0 1 (by decide) hx (hpj 1 (by norm_num)); exact this 1 0 (by decide) hx (hpj 0 (by norm_num))]
 intro u j hne hU hJ
 have hy : (fun i : Fin 2=>dirT (graph g) (p i) 0 v)= ![dirT (graph g) (p 0) 0 v,dirT (graph g) (p 1) 0 v]:=by ext i <;> fin_cases i <;> rfl
 rw [hy]; fin_cases u <;> fin_cases j <;> try { exact False.elim <| hne rfl }
 · change p 1=1 at hJ; change 2 ≤ p 0 at hU; rw [hu _ hU,hJ,he,dirT_one]; exact (grade_tangent hp hs ..).2.2
 · change p 0=1 at hJ; change 2 ≤ p 1 at hU; rw [hu _ hU,hJ,he,dirT_one]; exact (grade_tangent hp hs ..).2.1
lemma project_shell {k:ℕ} {P J:Profile E F}{f g:E→F}
    (hp:Station P f) (hq:Station J g) (hv:ContDiffAt ℝ ω P 0)
    (he:∀ j≤k+1,iteratedFDeriv ℝ j (graph f) 0=iteratedFDeriv ℝ j (graph g) 0) v : dirT (P ∘ graph f) (k+3) 0 v=dirT (P ∘ graph g) (k+3) 0 v:=by
 have h1 : ContDiffAt ℝ ∞ P (graph f 0):=(hp.at0.symm ▸ hv.of_le le_top)
 have h2 : ContDiffAt ℝ ∞ P (graph g 0):=(hq.at0.symm ▸ hv.of_le le_top)
 have h : dirT (graph f) 1 0 v=dirT (graph g) 1 0 v:=DFunLike.congr_fun (he _ (by omega)) _
 rw [pipeline _ _ _ h1 (hp.chart.of_le le_top),pipeline _ _ _ h2 (hq.chart.of_le le_top)]
 refine sum_congr rfl fun a ha=> ?_
 by_cases hl:∀ i:Fin a.length, a.partSize i≤k+1
 · unfold contribution; congr! 2; rw [hp.at0,hq.at0]; case e'_6 i => exact DFunLike.congr_fun (he _ (hl i)) _
 obtain ⟨i,hi⟩:=not_forall.mp hl; have hu:k+3 ≤ a.partSize i+1:=by omega
 exact ((graded_part a.partSize a.partSize_pos (fun i j=>combined_parts a _ _) i hu (by omega) (few_tokens a i hu) hp (hg0:=hp.starts) (hz:= rfl) hv hp.regular (g:=f) rfl).trans
 (graded_part a.partSize a.partSize_pos (fun i j=>combined_parts a _ _) i hu (by omega) (few_tokens a i hu) hp (hg0:=hq.starts) (hz:=hq.starts.trans hp.starts.symm) hv hq.regular h.symm).symm)


lemma pure_pull {k:ℕ} (hk : 1 ≤ k) {g:F→V}{w:E→F} (hu:ContDiffAt ℝ ω g 0) (hp:ContDiffAt ℝ ω w 0) (hw:w 0=0) (hz:∀ j<k,iteratedFDeriv ℝ j g 0=0)(v:E):
 dirT (g ∘ w) k 0 v=dirT g k 0 (dirT w 1 0 v):=by
 haveI : NeZero k:= ⟨by omega⟩
 rw [pipeline g w _ (hw.symm ▸ hu.of_le le_top) (hp.of_le le_top)]
 rw [sum_eq_single_of_mem (.atomic k) (mem_univ _) ?_]
 · unfold contribution; rw [hw]; rfl
 intro a _ ha; have hh : a.length<k := lt_of_le_of_ne a.length_le (fun h=> ha (full_part a h))
 rw [contribution,hw,hz _ hh]; rfl
lemma residual_pull {k:ℕ} {g f:F→V}{w:E→F} (hm:Matches k g f 0) (hp:ContDiffAt ℝ ω w 0) (hw:w 0=0) (v:E):
 dirT (g ∘ w) (k+1) 0 v - dirT (f ∘ w) (k+1) 0 v=dirT g (k+1) 0 (dirT w 1 0 v) - dirT f (k+1) 0 (dirT w 1 0 v):=by
 suffices h: ∀ {G:Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (p q:G→V), Matches k p q 0 → ∀ i x,dirT (p-q) i 0 x=dirT p i 0 x-dirT q i 0 x by
   rw [← h _ _ ((show Matches k g f (w 0) from hw.symm ▸ hm).comp_refl hp),← h _ _ hm]
   apply pure_pull (g:=g-f) (by omega) (hm.left.sub hm.right) hp hw
   intro j hj
   rw [iteratedFDeriv_sub_apply (hm.left.of_le le_top) (hm.right.of_le le_top),hm.jets j (by omega),sub_self]
 intro G h0 h1 p q H i x
 exact DFunLike.congr_fun (iteratedFDeriv_sub_apply (H.left.of_le (le_top (a:=(i:WithTop ENat)))) (H.right.of_le le_top)) (fun _:Fin i=>x)

lemma verdict_value {k:ℕ} {P J:Profile E F}{f g:E→F} [FiniteDimensional ℝ E][FiniteDimensional ℝ F]
 (hp:Station P f)(hj:Station J g) (hy:Matches (k+2) P J 0) (hd:Definite P) : Matches (k+1) (graph f) (graph g) 0 ∧
 ∀ v, dirT (P ∘ graph f) (k+3) 0 v-dirT (J ∘ graph g) (k+3) 0 v=dirT P (k+3) 0 (dirT (graph f) 1 0 v)-dirT J (k+3) 0 (dirT (graph f) 1 0 v):=by
 let hv:= (compare hy hp hj hd).1
 refine ⟨hv,fun v=>?_⟩
 rw [project_shell hp hj hy.left hv.jets v,show dirT (graph f) 1 0 v=dirT (graph g) 1 0 v from DFunLike.congr_fun (hv.jets 1 (by omega)) (fun _:Fin 1=>v)]
 apply residual_pull hy hj.chart hj.at0
end YM.Extension.UV.StationaryData
