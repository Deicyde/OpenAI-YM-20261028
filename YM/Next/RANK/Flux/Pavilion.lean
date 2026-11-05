import YM.Next.RANK.Flux.Panels

/-!
# Exact merger equality on Stage evacuation
Use subset reindex to Party. Requires attach for every Pet occurrence inside
it (meets a tangible Plug with required mode, not inferred from flag vanishing except at
boundary restoration). Applies exactly even when projection lookups wind. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}
variable (S : ι→ Plug G ζ t) (P : κ → Lining G ζ t)

def unmark (p : Finset ι) (T : Support n) := packed (fun i=> (S i).extent) p ∧ p.biUnion (fun i=> (S i).inventory)=T
def buoy (p : Finset (ι ⊕ κ)) (U : Config G n) := unmark S p.toLeft (flags t U) ∧ glasses S P p

def appar (F : Finset (Party S P)) := F.biUnion Subtype.val

lemma appFound {F : Finset (Party S P)} {D : Support n} (h : unmark (panel S P) F D) : ((appar S P F).toLeft.biUnion (fun i=>(S i).inventory))=D := by
  symm; rw [← h.2]; ext i; simp_rw [mem_biUnion,pan_vital]; constructor
  · rintro ⟨j,hj,hp⟩; obtain ⟨s,hs,hq⟩:=mem_biUnion.mp hp; exact ⟨s,mem_toLeft.mpr (mem_biUnion.mpr ⟨_,hj,mem_toLeft.mp hs⟩),hq⟩
  rintro ⟨p,hp,h⟩; obtain ⟨j,hj,hi⟩:=mem_biUnion.mp (mem_toLeft.mp hp); exact ⟨j,hj,mem_biUnion.mpr ⟨p,mem_toLeft.mpr hi,h⟩⟩

lemma appDist {F : Finset (Party S P)} {D : Support n} (h : unmark (panel S P) F D) : packed (lamps S P) F:= by
  intro i hi j hj H; have hx:= h.1 hi hj H; change Disjoint (panel S P i).extent (panel S P j).extent at hx; rwa [pan_extent,pan_extent] at hx
lemma appBuoy {F : Finset (Party S P)} {U : Config G n} (h : unmark (panel S P) F (flags t U)) : buoy S P (appar S P F) U:= by
  let v:= appar S P F; have he : packed (fun i=>(S i).extent) v.toLeft := by
    intro i hi j hj hh; obtain ⟨u,hu,hρ⟩:=mem_biUnion.mp (mem_toLeft.mp hi); obtain ⟨p,hp,hσ⟩:=mem_biUnion.mp (mem_toLeft.mp hj)
    rcases eq_or_ne u p with rfl|hv
    · exact u.property.2.1 (mem_toLeft.mpr hρ) (mem_toLeft.mpr hσ) hh
    exact ((appDist S P h hu hp hv).mono_left (show (S i).extent⊆lamps S P u from (dishfest S P i) ▸ spans S P u hρ)).mono_right (show (S j).extent⊆lamps S P p from (dishfest S P j) ▸ spans S P p hσ)
  refine ⟨⟨he,appFound S P h⟩,he,fun j hj=>?_⟩
  obtain ⟨p,hp,hj⟩:=mem_biUnion.mp (mem_toRight.mp hj)
  obtain ⟨i,hi,H⟩:=p.property.2.2 j (mem_toRight.mpr hj)
  exact ⟨_,mem_toLeft.mpr (mem_biUnion.mpr ⟨_,hp,mem_toLeft.mp hi⟩),H⟩

lemma apparParts (F : Finset (Party S P)) {U} (h : unmark (panel S P) F U) : Parts (dish S P) (appar S P F) = F.image Subtype.val:= by
  rw [show appar S P F=(F.image Subtype.val).biUnion id by ext;simp [appar]];apply separates
  · intro i hi; obtain ⟨u,hu,rfl⟩:=mem_image.mp hi; exact u.property.1
  intro i hi j hj hQ; obtain ⟨v,hv,rfl⟩:=mem_image.mp hi; obtain ⟨z,hz,rfl⟩:=mem_image.mp hj; exact appDist S P h hv hz (fun h=> hQ (congr_arg _ h))
lemma every_app {U p} (h : buoy S P p U) : ∃ F, unmark (panel S P) F (flags t U) ∧ appar S P F=p := by
  let X:= dish S P; let T:=Parts X p; let F:=T.preimage (Subtype.val (p:=fun v=>Spark X v∧glasses S P v)) Subtype.val_injective.injOn
  have hx (i) (hp:i∈T) : glasses S P i:= by
    have hu:= (Ac.lives X p hp).1
    refine ⟨fun i hi j hj hh=> h.2.1 (toLeft_subset_toLeft hu hi) (toLeft_subset_toLeft hu hj) hh,fun j hj=>?_⟩
    obtain ⟨a,ha,hh⟩:=h.2.2 j (toRight_subset_toRight hu hj); refine ⟨a,?_,hh⟩;apply mem_toLeft.mpr
    have hZ:Sum.inr j∈i:= mem_toRight.mp hj; rw [← contains X hp _ hZ]
    apply (bright ..).2; refine ⟨mem_toLeft.mp ha,ReflTransGen.single ⟨hu hZ,mem_toLeft.mp ha,?_⟩⟩
    obtain ⟨x,hx,h₁⟩:= hh.1; exact ⟨x,h₁,(show x∈dish S P (.inl a) from (dishfest S P a).symm ▸ hx)⟩
  have he:F.image Subtype.val=T:= by
    ext i; constructor
    · rintro h; obtain ⟨v,hv,rfl⟩:=mem_image.mp h; exact mem_preimage.mp hv
    intro hi; refine mem_image.mpr ⟨(⟨i,(lives X p hi).2,hx i hi⟩:Party S P),mem_preimage.mpr hi,rfl⟩
  have ht:appar S P F=p:= by rw [show appar S P F=(F.image Subtype.val).biUnion id by ext;simp [appar];rfl,he]; exact reconstruct X p
  have hd:packed (fun i=>(panel S P i).extent) F:= by
    intro i hi j hj H; change Disjoint (panel S P i).extent (panel S P j).extent; rw [pan_extent,pan_extent]; exact Ac.separate X p (mem_preimage.mp hi) (mem_preimage.mp hj) (fun hh=> H (Subtype.ext hh))
  exact ⟨F, ⟨hd, ((appFound S P (D:=F.biUnion fun i=> (panel S P i).inventory) ⟨hd,rfl⟩).symm.trans (by rw [ht]; exact h.1.2))⟩, ht⟩
lemma lamps_value (p : Finset (Party S P)) {U : Config G n} (h : unmark (panel S P) p (flags t U)): ∏ i∈p,(panel S P i).tolls U= ∏ i∈appar S P p,(speck S P i).covets U:= by
  rw [appar,prod_biUnion]; swap
  · intro i hi j hj he;apply disjoint_left.mpr;intro z hv hz;obtain ⟨x,hx⟩:= (speck S P z).active;exact disjoint_left.mp (appDist S P h hi hj he) (spans S P i hv hx) (spans S P j hz hx)
  apply prod_congr rfl; intro i hi; rw [pan_price,if_neg]; rfl
  rintro ⟨hh,hP⟩
  have hf : tint S P i U:= by
    unfold tint; rw [← h.2]; ext x; rw [mem_inter,mem_biUnion]; constructor
    · rintro ⟨hn,j,hj,hx⟩; rw [pan_vital] at hx; rcases eq_or_ne i j with rfl|he; exact hx; exact False.elim (disjoint_left.mp (appDist S P h hi hj he) hn (spines S P j hx))
    intro hn; exact ⟨spines S P i hn,i,hi,by rw [pan_vital];exact hn⟩
  exact hP hf

variable [Fintype ι] [Fintype κ]

def deck_at (U : Config G n) := ∑ p∈univ.filter (fun p=> unmark S p (flags t U)),∏ i∈p,(S i).tolls U

def embellished (U : Config G n) := ∑ p∈univ.filter (fun p=> unmark S p (flags t U)),
    (∏ i∈p,(S i).tolls U)*(∏ j∈ univ.filter (fun j=> earns S P j p), ((raised (P j)).covets U+1))
lemma flood (U) : deck_at (panel S P) U = embellished S P U:= by
  let T(p) := buoy S P p U; let f s:= ∏ i∈s,(speck S P i).covets U
  let L:=∑ p∈univ.filter T,f p
  have hx: deck_at (panel S P) U=L:= by
    refine sum_bij (fun p hp=> appar S P p) ?_ ?_ ?_ (fun p hp => lamps_value S P p (mem_filter.mp hp).2)
    · intro i hi; exact mem_filter.mpr ⟨mem_univ _,appBuoy _ _ (mem_filter.mp hi).2⟩
    · intro i hi j hj h; exact Finset.image_inj Subtype.val_injective|>.mp (Eq.trans (apparParts S P i (mem_filter.mp hi).2).symm (by rw [h,apparParts S P j (mem_filter.mp hj).2]))
    intro i hi; obtain ⟨p,hp,h⟩:= every_app S P (mem_filter.mp hi).2; exact ⟨p,mem_filter.mpr ⟨mem_univ _,hp⟩,h⟩
  rw [hx]; unfold L embellished; rw [sum_filter]
  let E (a:Finset ι) (b: Finset κ) : veil V:= if T (a.disjSum b) then f (a.disjSum b) else 0
  rw [show ∑ p:Finset (ι ⊕ κ),(if T p then f p else 0)=∑ p:Finset ι × Finset κ,E p.1 p.2 from (Fintype.sum_equiv Finset.sumEquiv.symm.toEquiv _ _ (fun _=> rfl) : _ = ∑ p,if T p then f p else 0).symm,Fintype.sum_prod_type,sum_filter]; apply sum_congr rfl; intro a _
  by_cases hh : unmark S a (flags t U)
  · rw [if_pos hh, Finset.prod_add,mul_sum]; let B:= univ.filter (fun j=> earns S P j a)
    have ht b : T (a.disjSum b)↔b⊆B:= by
      simp only [T,buoy,glasses, Finset.toLeft_disjSum, Finset.toRight_disjSum, hh,true_and]; exact ⟨fun h i hi=> mem_filter.mpr ⟨mem_univ _,h.2 i hi⟩,fun h=>⟨hh.1,fun i hi=> (mem_filter.mp (h hi)).2⟩⟩
    rw [← sum_subset (subset_univ B.powerset)]; apply sum_congr rfl; intro i hi; unfold E; rw [if_pos (ht i|>.mpr (mem_powerset.mp hi))]; unfold f;rw [prod_disjSum, Finset.prod_const_one,mul_one];
    · congr 1; exact prod_congr rfl (fun i _=>p_coverVal _ _)
    intro i _ hi; exact if_neg (fun h=> hi (mem_powerset.mpr (ht i|>.mp h)))
  rw [if_neg hh]; apply sum_eq_zero; intro i hi; exact if_neg (fun h=> hh ((show (Finset.toLeft (a.disjSum i))=a from toLeft_disjSum ..) ▸ h.1))
end YM.Next.Rank.Flux
