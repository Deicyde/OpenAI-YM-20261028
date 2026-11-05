import YM.Next.RANK.Advice

/-!
# Quiet incidences after enriching threshold-change mergers
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ α β : Type}
variable {ζ : V→Site n} {τ t : ℝ}
variable (A : α→ Burst G n t) (B : β→ Wickless G n τ) (X : Siren G n τ)
variable (K : ι→ Lifted G ζ t) (W : κ→ Strike G ζ τ)

structure Germs where
  p : α ↪ ι
  q : β ↪ κ
  left i : K (p i)=enroll ζ (A i)
  right i : W (q i)=(B i).credit ζ
  old i : (K i).fires = quiet V → i ∈ Set.range p
  ink i : (W i).fires = quiet V → i ∈ Set.range q

section
variable {V Y : Type} (x : V↪Y)
private lemma spark_id [DecidableEq Y] (a : Finset V) (u : V→Support n) (v : Y→Support n) (he : ∀ i,v (x i)=u i) :
    Ac.Spark u a ↔ Ac.Spark v (a.image x):= by
  constructor
  · intro h; refine ⟨h.1.image _,fun b hb c hc=>?_⟩
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hb; obtain ⟨j,hj,rfl⟩:=mem_image.mp hc
    apply ReflTransGen.lift x _ i j (h.2 i hi j hj)
    rintro u w ⟨hu,hw,i,Ht,Hv⟩; exact ⟨mem_image_of_mem _ hu,mem_image_of_mem _ hw,i,(he u).symm ▸ Ht,(he w).symm ▸ Hv⟩
  intro h; obtain ⟨i,hi⟩:=h.1; obtain ⟨z,hz,rfl⟩:=mem_image.mp hi
  refine ⟨⟨_,hz⟩,fun i hi j hj=>?_⟩
  have hp b (H: Ac.chain v (a.image x) (x i) b) : ∃ s∈a,x s=b ∧ Ac.chain u a i s := by
    induction H with
    | refl=> exact ⟨i,hi,rfl,.refl⟩
    | @tail w b h hb ih=>
      obtain ⟨d,hd,rfl,hR⟩:=ih; obtain ⟨hw,hB,k,hk,ht⟩:=hb; obtain ⟨y,hy,rfl⟩:= mem_image.mp hB
      refine ⟨y,hy,rfl,.tail hR ⟨hd,hy,k,?_,?_⟩⟩; exacts [he d ▸ hk,he y▸ ht]
  obtain ⟨d,_,hx,hD⟩:=hp (x j) (h.2 _ (mem_image_of_mem _ hi) _ (mem_image_of_mem _ hj)); exact x.injective hx ▸ hD
end

namespace Germs
variable {A B K W} (C : Germs A B K W)

def castX (_X : Siren G n τ) := (⟨Sum.map (Sum.map C.p C.q) id,Sum.map_injective.mpr ⟨Sum.map_injective.mpr ⟨C.p.injective,C.q.injective⟩, injective_id⟩⟩ : Branch α β n ↪ Branch ι κ n)
private abbrev newA (A : α→Burst G n t) := enroll (Empty.elim : Empty→ Site n) ∘ A
private abbrev newB (B : β→Wickless G n τ) := fun i=> (B i).credit (Empty.elim : Empty → Site n)
lemma strength (i : Branch α β n): vol K W X (castX C X i)=vol (newA A) (newB B) X i:= by
  rcases i with (i|i)|i
  · change halo 8 (K (C.p i)).extent=_; rw [C.left];rfl
  · change (W (C.q i)).extent=_; rw [C.right];rfl
  rfl
lemma toLeft (i : Finset (Branch α β n)) : (i.image (castX C X)).toLeft.toLeft= i.toLeft.toLeft.image C.p:= by
  ext u; simp only [mem_toLeft,mem_image]; constructor
  · rintro ⟨(a|b)|c,hi,H⟩
    · exact ⟨a,hi,Sum.inl.inj (Sum.inl.inj H)⟩
    · exact False.elim (Sum.inr_ne_inl (Sum.inl.inj H))
    exact False.elim (Sum.inr_ne_inl H)
  rintro ⟨a,hi,rfl⟩; exact ⟨.inl (.inl a),hi,rfl⟩
lemma toRight (i : Finset (Branch α β n)) : (i.image (castX C X)).toRight=i.toRight:= by
  ext u; simp only [mem_toRight,mem_image]; constructor
  · rintro ⟨a|b,hi,H⟩
    · exact False.elim (Sum.inl_ne_inr H)
    have H':b=u:= Sum.inr.inj H; subst b; exact hi
  intro h; exact ⟨.inr u,h,rfl⟩
lemma turnsy (i : Finset (Branch α β n)) : cast K W X (i.image (castX C X)) ↔ cast (newA A) (newB B) X i:= by
  have ht j:(K (C.p j)).extent=(newA A j).extent:= by rw [C.left]; rfl
  unfold cast; rw [toLeft,toRight]; refine and_congr (spark_id _ i _ _ (strength X C)).symm (and_congr_right fun _=>?_); constructor
  · intro h a ha b hb hn; change Disjoint (newA A a).extent (newA A b).extent; rw [← ht,← ht]; apply h (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) (fun H=> hn (C.p.injective H))
  intro h a ha b hb hn
  obtain ⟨x,hx,rfl⟩:=mem_image.mp ha; obtain ⟨z,hz,rfl⟩:=mem_image.mp hb; change Disjoint (K (C.p x)).extent (K (C.p z)).extent; rw [ht,ht]; exact h hx hz (fun hQ=>hn (congr_arg _ hQ))

def matinee (i : Domino (newA A) (newB B) X) : Domino K W X:=⟨i.val.image (castX C X),(turnsy X C i.val).mpr i.property⟩
lemma rooms (i): Settle K W X (matinee X C i)=Settle (newA A) (newB B) X i:= by
  ext u; simp only [matinee,Settle,mem_biUnion,mem_image,exists_exists_and_eq_and,strength];
lemma sym_inside (i U) : inside K W X (matinee X C i) U ↔ inside (newA A) (newB B) X i U:= by
  have h : (matinee X C i).val.toLeft.toLeft.biUnion (fun j=> (K j).inventory)=i.val.toLeft.toLeft.biUnion (fun j=> (newA A j).inventory):= by
    ext u; simp only [matinee,toLeft,mem_biUnion,mem_image,C.left, exists_exists_and_eq_and];rfl
  unfold inside; rw [rooms,h,(show (matinee X C i).val.toRight=i.val.toRight from toRight X C i.val)]

private lemma fuel_cast (i U) : ∃ z : ℝ, fuel K W X (castX C X i) U=Nreal z ∧ fuel (newA A) (newB B) X i U=Nreal z:= by
  rcases i with (i|i)|i
  · refine ⟨(A i).value U,?_,(singles _).symm⟩
    change (K (C.p i)).amount U=_; rw [C.left]; exact (singles _).symm
  · refine ⟨(B i).value U,?_,vacant _ _ _⟩
    change (W (C.q i)).occ U=_; rw [C.right]; exact vacant _ _ _
  exact ⟨X.value i U,rfl,rfl⟩
lemma quiescent i: (teat K W X (matinee X C i)).fires=quiet V:= by
  apply Subtype.ext; ext j
  simp only [matinee,teat,scene,alarmCount,quiet,Census.quiet,mem_biUnion,mem_image,exists_exists_and_eq_and, notMem_empty, iff_false, not_exists]; rintro ((x|x)|x) ⟨h,hg⟩
  · change j∈(K (C.p x)).fires.val at hg; rw [C.left] at hg; exact notMem_empty _ hg
  · change j∈(W (C.q x)).fires.val at hg; rw [C.right] at hg; exact notMem_empty _ hg
  exact notMem_empty _ hg
lemma moment (i U) : (teat K W X (matinee X C i)).value U=(teat (newA A) (newB B) X i).value U:= by
  have he : ∃ z : ℝ, (teat K W X (matinee X C i)).amount U=Nreal z ∧ (teat (newA A) (newB B) X i).amount U=Nreal z:= by
    rw [teat_pay,teat_pay]; split_ifs with h hX he
    · choose z hz ht using fun a=> fuel_cast X C a U
      unfold quake; refine ⟨∏ i∈ i.val,z i, ?_,?_⟩
      · simp only [matinee,prod_image (castX C X).injective.injOn,hz,map_prod]
      simp only [ht,map_prod]
    · exact False.elim (hX ((sym_inside X C i U).1 h))
    · exact False.elim (h ((sym_inside X C i U).2 he))
    exact ⟨0,(map_zero _).symm,(map_zero _).symm⟩
  obtain ⟨z,hx,he⟩:=he
  change (teat _ _ _ _).amount U = S11 _ at hx he; rw [singles] at hx he
  have ht:= congr_arg (fun q:veil V=> q.part (quiet V)) hx
  have hp:= congr_arg (fun q:veil Empty=> q.part (quiet Empty)) he
  unfold Lifted.amount at ht hp
  simp only [Poly.part_send,quiescent, (peas (V:=Empty) _ A X B i).mode] at ht hp; exact (by simpa using ht : (teat K W X (matinee X C i)).value U=(↑z:ℂ)).trans (by simpa using hp.symm)

lemma mat_range (i : Domino K W X) (hv : (teat K W X i).fires=quiet V) : ∃ p : Domino (newA A) (newB B) X,i=matinee X C p:= by
  let f:=castX C X; let y:= i.val.preimage f f.injective.injOn
  have h (j) (hj : j∈i.val) : chosen K W j=quiet V:= by
    let H:=teat K W X i
    apply Subtype.ext; ext v; refine ⟨fun h=> ?_, fun h=> False.elim (notMem_empty v h)⟩
    rw [← hv]; exact mem_biUnion.mpr ⟨j,hj,h⟩
  have hz : y.image f=i.val:= by
    ext v; constructor
    · rintro H; obtain ⟨x,hx,rfl⟩:=mem_image.mp H; exact mem_preimage.mp hx
    intro H; have h:v∈ Set.range f:=by
      rcases v with (i|i)|i
      · obtain ⟨u,hu⟩:= C.old i (h _ H); exact ⟨.inl (.inl u),congr_arg Sum.inl (congr_arg Sum.inl hu)⟩
      · obtain ⟨u,hu⟩:= C.ink i (h _ H); exact ⟨.inl (.inr u),congr_arg Sum.inl (congr_arg Sum.inr hu)⟩
      exact ⟨.inr i,rfl⟩
    obtain ⟨v,rfl⟩:=h; exact mem_image.mpr ⟨v,mem_preimage.mpr H,rfl⟩
  exact ⟨⟨y,(turnsy X C y).mp (hz.symm ▸ i.property)⟩,Subtype.ext hz.symm⟩

include C in
lemma background [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] (x) (U) : column (teat K W X) x U= column (teat (newA A) (newB B) X) x U:= by
  unfold column; let f:=matinee X C; let s:=univ.image f
  have ht: Injective f:=fun a b h=> Subtype.ext (image_injective (castX C X).injective (congr_arg Subtype.val h))
  rw [← sum_subset (subset_univ s), sum_image ht.injOn]
  · apply sum_congr rfl; intro j hj; let i:=matinee X C j
    have hv: (teat K W X i).inventory=(teat (newA A) (newB B) X j).inventory:= toRight X C j.val
    have hs: (teat K W X i).extent=(teat (newA A) (newB B) X j).extent:= rooms X C j
    dsimp only [f]
    change (if (teat K W X i).fires=_ ∧((teat K W X i).extent,(teat K W X i).inventory)=x.val then (teat K W X i).value U else _) = _
    rw [hv,hs,(show (teat K W X i).value U=_ from moment X C j U),(show (teat K W X i).fires=quiet V from quiescent X C j)]; have hp:= (peas _ A X B j).mode; rw [hp]; simp
  intro a ha hn; split
  · rename_i h; obtain ⟨x,rfl⟩:= mat_range X C a h.1; exact False.elim (hn (mem_image.mpr ⟨x,mem_univ _,rfl⟩))
  rfl
end Germs
end YM.Next.Rank.Alarm
