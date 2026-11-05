import YM.UVExtension.Lamppost.Capsule
import YM.Progress.DIRECTED_RECIPE.Shelves
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Filter Set RG Progress.DirectedRecipe Push.AbsoluteSums
open scoped BigOperators Classical
variable {A B C D X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {M: Opening D Z} (P:Meter A B) (Q:Meter X B) (v w:D→P.Slot) {f g:Z→ℝ}

lemma both (F:Atlas P M v f)(H:Atlas P M w g) : Nonempty (Atlas P M (fun d i x=> v d i x+w d i x) (fun z=> f z+g z)):=by
  refine ⟨⟨fun z i x=> F.f z i x+ H.f z i x,fun d i x=> by rw [Complex.ofReal_add]; exact congr_arg₂ (·+·) (F.exacts ..) (H.exacts ..),fun i x=> bends_add (F.pulse i x) (H.pulse i x),fun z hz=>?_⟩⟩
  obtain ⟨p,h,hP⟩:= (F.bounds z hz).afloat; obtain ⟨q,hq,hQ⟩:= (H.bounds z hz).afloat
  exact ⟨fun i=>p i+q i,fun i=>⟨add_nonneg (h i).1 (hq i).1,fun x=>(norm_add_le ..).trans (add_le_add ((h i).2 x) ((hq i).2 x))⟩, fun i=> by simpa only [mul_add] using budget_plus (hP i) (hQ i)⟩
lemma lit (v:P.Slot)(b:ℝ)(h:P.MeasureP v b): Nonempty (Atlas P M (fun _=> v) (fun _=>b)):=by
  refine ⟨⟨fun _ i x => ↑(v i x),fun _ _ _=>rfl,fun i x=> bumps _ _ (differentiableOn_const _),fun _ _=>?_⟩⟩
  obtain ⟨f,hf,hb⟩:=h.afloat; exact ⟨_,fun i=> ⟨(hf i).1,fun x=> (Complex.norm_real _).trans_le ((hf i).2 x)⟩,hb⟩
lemma raiseCredit (F:Atlas P M v f)(h:∀ z∈ M.span, f z ≤ g z): Nonempty (Atlas P M v g):= by
  refine ⟨⟨F.f,F.exacts,F.pulse,fun z hz=>?_⟩⟩; obtain ⟨p,hp,hQ⟩:= (F.bounds z hz).afloat; exact ⟨p,hp,fun i=> budget_loosen (hQ i) (h z hz)⟩

lemma inserted (p:A ↪ X)(w:D→ Q.Slot)(q: ∀ i, Q.test (p i)→P.test i) (he:∀ d i k,w d (p i) k=v d i (q i k)) (hx:∀ i,i ∉ range p →∀ d k, w d i k=0)
    (hc:∀ i j,Q.cost i (p j)≤P.cost i j)(F:Atlas P M v f) : Nonempty (Atlas Q M w f):=by
  let u (a:X)(h:a∈range p):= h.choose
  have hu (i:X)(h:i∈range p): p (u i h)=i:= h.choose_spec
  let t (z:Z): Q.CSlot:= fun i x=> if h:i∈range p then F.f z (u i h) (q _ (hu i h|>.symm ▸ x)) else 0 -- eq bypass
  have hr z i x: t z (p i) x= F.f z i (q i x) := by
    let h: p i∈range p:= mem_range_self _; unfold t; rw [dif_pos h]
    suffices H:∀ (k:A)(hk:p k=p i), F.f z k (q k (hk.symm ▸ x))= F.f z i (q i x) from H (u (p i) h) (hu _ h)
    intro k hk; have ha:=p.injective hk; subst k; rfl
  refine ⟨⟨t,fun d i x=> ?_,fun i x=> ?_,fun z hz=> ?_⟩⟩
  · by_cases h:i∈range p; obtain ⟨i,rfl⟩:=h; rw [hr,F.exacts,he]
    unfold t; rw [dif_neg h,hx i h d x]; exact Complex.ofReal_zero.symm
  · unfold t; split; next => exact F.pulse _ _
    exact bumps _ _ (differentiableOn_const _)
  obtain ⟨b,hb,hP⟩:= (F.bounds z hz).afloat; let a i:= Function.extend p b 0 i; have hl i:a (p i)=b i:= p.injective.extend_apply ..
  have hk i(h:i∉range p): a i=0:= Function.extend_apply' b (0:X→ℝ) i h
  have hV i: 0 ≤ a i:=by by_cases h:i∈range p; obtain ⟨i,rfl⟩:=h; rw [hl]; exact (hb i).1; rw [hk i h]
  refine ⟨a,fun i=>⟨hV _,fun j=>?_⟩, fun i=>?_⟩
  · by_cases h:i∈range p
    · obtain ⟨i,rfl⟩:=h; rw [hr,hl]; exact (hb i).2 _
    unfold t; rw [dif_neg h,norm_zero]; exact hV _
  refine budget_of_sum (fun j=>mul_nonneg (Q.nonneg ..) (hV j)) fun s=> ?_
  let S:= s.preimage p p.injective.injOn; have he:S.map p⊆ s:=by intro j hj; obtain ⟨x,hx,rfl⟩:= Finset.mem_map.mp hj; exact Finset.mem_preimage.mp hx
  rw [← Finset.sum_subset he (fun x hx h=> ?_),Finset.sum_map]; swap
  · rw [hk x (by rintro ⟨x,rfl⟩; exact h (Finset.mem_map_of_mem _ (show x ∈ S from Finset.mem_preimage.mpr hx))),mul_zero]
  refine (Finset.sum_le_sum (fun i (_:i∈S)=> ?_)).trans (budget_sum (hP i) S)
  rw [hl]; exact mul_le_mul_of_nonneg_right (hc ..) (hb i).1
end YM.UVExtension.Lamppost
