import YM.Next.RANK.Flux.Colour

/-!
# Clean before log in MARKED-only gas. Attributed leading values before

Proof used only on projection targets, but uses all marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→Site n}
variable {Q : BudgetPoint} (S : ι→ Plug G ζ Q.threshold)
variable (P : κ → Lining G ζ Q.threshold) (u : ι→Prop)
-- represent all burn/log exclusions. purity check only after health.
section
variable [Fintype ι] [Fintype κ]

def pitch (U : Config G n) := chair (feet (sunny S)) (fun i=>(sunny S i).amount Q.threshold U) (univ.filter (fun i:Bright S=> u i.val))

def brightLinks (F : Bright S): Bright (panel S P):= by
  let x:= solitary S P F.val; refine ⟨x,fun h=> ?_⟩; apply F.property; change (S F.val).inventory.Nonempty; rw [show (S F.val).inventory=(panel S P x).inventory from ?_]; exact h
  exact (pan_vital S P x |>.trans (solo_things S P F.val).2.1).symm
omit [Fintype ι] [Fintype κ] in
lemma brightPaths (i : Bright S): clean S P u (brightLinks S P i).val ↔ u i.val:= by
  let p:=solitary S P i.val
  have hp:p.val={.inl i.val}:=rfl
  change clean S P u p ↔ _;unfold clean;rw [hp,asideL,mainline];simp
omit [Fintype ι] [Fintype κ] in
lemma ties1 (i : Bright S) :
    let K:=sunny (panel S P) (brightLinks S P i)
    let p:=sunny S i
    K.fires=p.fires∧ K.extent=p.extent ∧ ∀ U,K.amount Q.threshold U=p.amount Q.threshold U:= by
  intro K p; let Z:= panel S P;let v:=brightLinks S P i
  obtain ⟨hl,hv,hh,H⟩:= solo_things S P i.val
  have he: Z v.val = .regular K:= bright_valid ..
  have hx: S i.val=.regular p:=bright_valid ..
  refine ⟨?_, ?_,fun U=> ?_⟩
  · exact (congr_arg Plug.fires he).symm.trans ((pan_mark ..).trans (hh.trans (congr_arg _ hx)))
  · exact (congr_arg Plug.extent he).symm.trans ((pan_extent ..).trans (hl.trans (congr_arg _ hx)))
  have hu : ¬ Plug.landed (S i.val):= i.property
  have hg: ¬ (vital S P (solitary S P i.val)).Nonempty:= fun h=> hu (show (S i.val).inventory.Nonempty from hv ▸ h)
  have H₀ : (Z v.val).tolls U=p.amount Q.threshold U:= ((pan_price S P v.val U).trans (if_neg (fun H=> hg H.1))).trans ((H U).trans (congr_arg (fun i: Plug G ζ Q.threshold=>i.tolls U) hx))
  exact (congr_arg (fun i:Plug G ζ Q.threshold=>i.tolls U) he).symm.trans H₀
omit [Fintype ι] [Fintype κ] in
lemma twins (x : Bright (panel S P)) (hp : clean S P u x.val) : ∃ i : Bright S,u i.val∧x=brightLinks S P i:= by
  obtain ⟨i,hi⟩:=south S P x.val hp.1
  have hh:=x.property;unfold Plug.landed at hh
  rw [pan_vital,hi,(solo_things S P i).2.1] at hh
  refine ⟨⟨i,hh⟩,?_,Subtype.ext hi⟩
  exact (brightPaths S P u ⟨i,hh⟩).1 (by change clean _ _ _ (solitary _ _ i); rw [← hi]; exact hp)
omit [Fintype ι] [Fintype κ] in
private lemma arch (F : ι↪κ) (a : ι→veil V) (b : κ→ veil V) (X : ι → Support n) (Y : κ → Support n) (p : Finset ι)
    (hx : ∀ i,a i=b (F i)) (hp : ∀ i,X i=Y (F i)) : chair X a p=chair Y b (p.map F):= by
  unfold chair;rw [show (p.map F).powerset=p.powerset.map (Finset.mapEmbedding F).toEmbedding from ?_, Finset.sum_map]
  swap
  · symm; apply Finset.eq_of_subset_of_card_le
    intro i hi; obtain ⟨a,h,rfl⟩:=mem_map.mp hi; apply mem_powerset.mpr; exact map_subset_map.mpr (mem_powerset.mp h)
    simp
  apply sum_congr rfl;intro i _; split_ifs with h he he
  · change ∏ j∈i,a j=∏ j∈i.map F,b j;rw [Finset.prod_map];exact prod_congr rfl fun i _=>hx i
  · exfalso; apply he; intro u hu v hv H; change u∈i.map F at hu; change v∈i.map F at hv; obtain ⟨u,h₁,rfl⟩:= mem_map.mp hu; obtain ⟨v,h₂,rfl⟩:= mem_map.mp hv; change Disjoint _ _; have ht:= h h₁ h₂ (fun hh=> H (congr_arg _ hh));change Disjoint (X u) (X v) at ht; rw [hp,hp] at ht;exact ht
  · exfalso; apply h; intro u hu v hv H; change Disjoint (X u) (X v);rw [hp,hp];exact he (mem_map.mpr ⟨_,hu,rfl⟩) (mem_map.mpr ⟨_,hv,rfl⟩) (F.injective.ne H)
  rfl
lemma clean_log (U : Config G n):
    let X:= panel S P; let A:= sunny X
    Poly.pass (∑ i∈ univ.filter (rawclean S P u),(Bond A i).amount Q.threshold U) = pitch S u U:= by
  intro X A; let v:=Bright X; let F : Bright S↪ v:=
    ⟨brightLinks S P, fun i j h=>Subtype.ext (Sum.inl.inj (singleton_inj.mp (congr_arg (fun z:v=>z.val.val) h)))⟩
  let D:= univ.filter (fun i:Bright S=>u i.val); let V':=univ.filter (fun i:v=> clean S P u i.val)
  have hv : D.map F=V':= by
    ext i; constructor
    · intro h; obtain ⟨w,hw,rfl⟩:=mem_map.mp h; exact mem_filter.mpr ⟨mem_univ _,(brightPaths ..).2 (mem_filter.mp hw).2⟩
    intro h; obtain ⟨j,hj,rfl⟩:= twins S P u i (mem_filter.mp h).2; exact mem_map.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩,rfl⟩
  have h : pitch S u U = chair (feet A) (fun i=>(A i).amount Q.threshold U) V':= by
    rw [← hv]; exact arch F _ _ _ _ D (fun i=> ((ties1 S P i).2.2 U).symm) (fun i=>(ties1 S P i).2.1.symm)
  apply Eq.trans _ h.symm; apply Eq.trans _ (monarch A Q.threshold U V'); apply congr_arg Poly.pass;apply Finset.sum_congr _ (fun _ _=> rfl)
  ext i; simp only [mem_filter,mem_univ,true_and,V']; constructor
  · intro H j hj; exact mem_filter.mpr ⟨mem_univ _,H _ hj⟩
  exact fun H j hj=> (mem_filter.mp (H hj)).2
end
end YM.Next.Rank.Flux
