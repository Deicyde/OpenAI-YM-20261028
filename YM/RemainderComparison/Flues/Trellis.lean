import YM.RemainderComparison.Flues.Mayer

/-!
# Term-for-term collection without weakening the layout

Mallow.Passage combinatorics generalised to annotated supports over same
Pipes. We don't use `prod_ne_zero_iff`; there are zero divisors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums Finset Merge Work.H03
open Mosaic Mosaic.Verse Marker GridRenewal.Rain
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι θ : Type}[DecidableEq θ] {α:Type*} {J : Census θ}
variable (H:Yard ι α G n) (L:Scone ι α G n) (P:BudgetPoint) (root:ι→Support n)(Z:Set ι)
local notation "C" => fireplace H L
variable (F:ℕ ≃ (fireplace H L).Pellet) (a:α) (U:Config G n) (z:ι→Poly J)
variable {k:ℕ} {gV:θ→ℝ} (hZ:Serif.Chorus J gV Z z k) (h:H.Sounds P root) (hl:L.Rises P root)
local notation "D" => flash H L P Z F
set_option quotPrecheck false
local notation "M" => (D).manifest a
local notation "N" => H.manifest a
local notation "X" => fly H L P Z a U z
local notation "Y" => (D).gala P Z z a U
local notation "g" => ember H L Z a U z
set_option quotPrecheck false
local notation "fp" => fun i : ℕ=> (F i).val
local notation "S" => cinders L Z a U z

def tunnel (p:Finset ℕ): Finset Ovens.Label := p.biUnion (fun i=> (F i).val)
local notation "Λ" => tunnel H L F
lemma flown (b:Finset Ovens.Label) (he:(N).admissible P U b.toLeft) : X b= ∏ j∈b,g j:=by
   unfold fly Yard.gala Photo.fronts; rw [if_pos he,prod_sum_eq_prod_toLeft_mul_prod_toRight]; rfl
lemma steam (p:Ovens.Label): g p= (↑(stoke H L Z a p U):ℂ) • controls Z z (rune H L p):=by cases p<;> rfl
lemma vapor (s:Finset Ovens.Label): ∏ i∈s,g i= (↑(∏ i∈s,stoke H L Z a i U):ℂ) • controls Z z (∑ i∈s,rune H L i):=by
   simp_rw [steam]; rw [prod_smul,Complex.ofReal_prod]; refine congr_arg (_ • ·) ?_; induction s using Finset.induction with
   | empty => simp [controls]
   | insert i s hp hh=> rw [prod_insert hp,sum_insert hp,hh]; unfold controls; rw [Multiset.map_add,Multiset.prod_add]

variable {H L P F a U z}
lemma stove {i}
   (hp: (addr F P i).eligible P.threshold U):
      (D).song Z z a U i= ∏ j∈ (F i).val,g j:=by unfold Yard.song; rw [vapor]; unfold flash; dsimp only; rw [if_pos hp]
lemma floor_enter {i}(p:Finset ℕ)(hp:(M).admissible P U p)(hi:i∈p) : (addr F P i).support ∩ RG.flags P.threshold U= (addr F P i).inventory:=by
    rw [← hp.2]; ext x; simp only [mem_inter,mem_biUnion]; constructor
    · rintro ⟨hx,k,hk,h'⟩; by_cases h:k=i
      · subst i; exact h'
      exact False.elim ((disjoint_left.mp (hp.1 hk hi h)) ((addr F P k).inventory_sup h') hx)
    exact fun h=>⟨(addr F P i).inventory_sup h,i,hi,h⟩ -- M forced definitional but simp
lemma flags_floor (p:Finset ℕ): (C).plot (Λ p) = p.biUnion (fun i => (C).plot (F i).val):=by
    ext i; simp only [plot,tunnel,mem_toLeft,lefts,mem_biUnion]; constructor
    · rintro ⟨j, ⟨k,hk,h'⟩,h⟩; exact ⟨k,hk,j,h',h⟩
    rintro ⟨k,hk,j,hj,h⟩; exact ⟨j,⟨k,hk,hj⟩,h⟩
lemma importers {p:Finset ℕ}(hp:(M).admissible P U p): (N).admissible P U ((Λ p).toLeft):=by
    refine ⟨fun i hi j hj hij => ?_, (show (C).plot (Λ p)=RG.flags P.threshold U from (flags_floor (F:=F) p).trans hp.2)⟩
    obtain ⟨k,hk,hk'⟩:= mem_biUnion.mp (mem_toLeft.mp (show i∈((Λ p).toLeft) from hi))
    obtain ⟨v,hv,hv'⟩:= mem_biUnion.mp (mem_toLeft.mp (show j∈((Λ p).toLeft) from hj))
    by_cases he:k=v
    · subst v; exact (F k).property.2.2 (Finset.mem_toLeft.mpr hk') (Finset.mem_toLeft.mpr hv') hij
    exact Disjoint.mono (subset_biUnion_of_mem (C).patch hk') (subset_biUnion_of_mem (C).patch hv') (hp.1 hk hv he)
lemma sets (p:Finset ℕ)(hp:(M).admissible P U p): (p : Set ℕ).PairwiseDisjoint (fun i=> (F i).val):=by
    intro i hi j hj hn; apply Finset.disjoint_left.mpr; intro k hk hk'
    have hh : Disjoint ((C).patch k) ((C).patch k):= Disjoint.mono (subset_biUnion_of_mem (C).patch hk) (subset_biUnion_of_mem (C).patch hk') (hp.1 hi hj hn)
    have hv : ((C).patch k).Nonempty:= by
       rcases k with k|k
       · exact (H.more k).inventory_ne.mono (H.more k).inventory_sup
       exact L.rest k
    exact (Finset.nonempty_iff_ne_empty.mp hv) (disjoint_self.mp hh)
include h
lemma hatched {p:Finset ℕ}(hp:(M).admissible P U p): X (Λ p)=Y p:=by
   unfold Yard.gala Photo.fronts; rw [if_pos hp]; rw [flown _ _ _ _ a U z _ (importers Z hp),tunnel, prod_biUnion (sets Z _ hp)]; refine prod_congr rfl fun i hi=>?_ ; by_cases h' : (addr F P i).eligible P.threshold U
   · exact (stove Z h').symm
   have hx : (D).glow a i U=0:= if_neg h'; unfold Yard.song; rw [hx,Complex.ofReal_zero,zero_smul]
   by_contra hn; apply h'; refine ⟨floor_enter Z p hp hi,fun j hj=> (h.families a).permit j U (fun he=> ?_)⟩
   apply hn (prod_eq_zero (mem_toLeft.mp hj) _); rw [steam]; change H.glow a j U=0 at he; change (↑(H.glow a j U):ℂ) • controls _ z _=0; rw [he,Complex.ofReal_zero,zero_smul]

omit h in
lemma tunnels_image (p:Finset ℕ): Λ p=(p.image fun i=> (F i).val).biUnion id:=by ext i; simp [tunnel]
omit h in
lemma monot (p:Finset ℕ)(hp:(M).admissible P U p): Ac.Parts (C).patch (Λ p) = p.image fun i=>(F i).val:=by
    rw [tunnels_image]; refine Ac.separates (C).patch _ (fun i hi=>?_) (fun i hi j hj hn=>?_)
    · obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact (F j).property.2.1
    obtain ⟨k,hk,rfl⟩:=mem_image.mp (show i∈p.image _ from hi); obtain ⟨j',hj',rfl⟩:=mem_image.mp (show j∈p.image _ from hj)
    exact hp.1 hk hj' (fun hp=> hn (congr_arg (fp) hp))
variable (F)
-- infer implicit notation
omit h
include hl
lemma covering {b:Finset Ovens.Label}(hb:X b≠0): ∃ p:Finset ℕ, Λ p=b ∧ (M).admissible P U p:=by
   have ht:(N).admissible P U b.toLeft := Classical.byContradiction fun he=> hb (by unfold fly Yard.gala Photo.fronts; rw [if_neg he,zero_mul])
   rw [flown _ _ _ _ _ _ _ _ ht] at hb; let v:= Ac.Parts (C).patch b
   have hu p (hp:p∈v): (C).contains p:=by
       obtain ⟨hF,hS⟩:=Ac.lives (C).patch b hp
       refine ⟨?_, hS,fun i hi j hj hn=>ht.1 (toLeft_subset_toLeft hF hi) (toLeft_subset_toLeft hF hj) hn⟩; obtain ⟨x,hx⟩:=hS.1
       rcases x with i|i
       · exact ⟨i,mem_toLeft.mpr hx⟩
       have hv: ¬ Healthy P.threshold (L.leg i) U := fun he=> hb (prod_eq_zero (hF hx) (by rw [steam,show stoke H L Z a (Sum.inr i) U = _ from L.ashes Z (hl.leaked i a U he), Complex.ofReal_zero,zero_smul]))
       obtain ⟨z',hz,hz'⟩:= Finset.not_disjoint_iff.mp hv; rw [← ht.2] at hz'; obtain ⟨j,hj,hm⟩:=mem_biUnion.mp hz'; let k:= (Sum.inl j : Ovens.Label); have hJ : k∈ b:= mem_toLeft.mp hj
       have hc: Ac.chain (C).patch b (Sum.inr i) k:= .single ⟨hF hx,hJ,z',hz,(H.more j).inventory_sup hm⟩
       exact ⟨j,mem_toLeft.mpr (show k∈p from by rw [← Ac.contains (C).patch hp (Sum.inr i) hx]; exact (Ac.bright (C).patch _ _).2 ⟨hJ,hc⟩)⟩
   let d:= fun p : ↥v=> F.symm ⟨p.val,hu _ p.prop⟩; let s:=v.attach.image d
   have he : s.image (fp)=v:=by
      ext i; constructor
      · intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; obtain ⟨k,hk,rfl⟩:=mem_image.mp hj; simp [d]
      intro hi; let k : ↥v:= ⟨i,hi⟩; exact mem_image.mpr ⟨d k,mem_image_of_mem _ (mem_attach ..), show (F (d k)).val=i by simp [k,d]⟩
   have hs : Λ s=b:= by rw [tunnels_image,he]; exact Ac.reconstruct ..
   refine ⟨s,hs,fun i hi j hj hn=>?_,?_⟩
   · have hb (i) (h:i∈s): (F i).val∈v:= he ▸ Finset.mem_image_of_mem (fp) h
     exact Ac.separate (C).patch b (hb i hi) (hb j hj) (fun he=>hn (F.injective (Subtype.ext he)))
   change s.biUnion (fun i=> (C).plot (F i).val)= _
   rw [← flags_floor, hs]; exact ht.2
include h
lemma gathering (t:Poly J)(hs: HasSum X t): HasSum Y t:=by
  have hz i(hi:Y i≠0):(M).admissible P U i:= Classical.byContradiction fun he=> hi (if_neg he)
  let u: Function.support Y → Function.support X:= fun i=> ⟨Λ i.val, show X (Λ i.val)≠0 from (hatched (z:=z) root Z h (hz i.val i.prop)) ▸ i.prop⟩
  have he : Injective u:=by
     intro i j h; apply Subtype.ext; apply Finset.image_injective (Subtype.val_injective.comp F.injective)
     change i.val.image (fp)= j.val.image (fp)
     rw [← monot Z _ (hz i.val i.prop),← monot Z _ (hz j.val j.prop), show Λ i.val=Λ j.val from congr_arg Subtype.val h]
  have hu : Surjective u:=by
     rintro ⟨b,hb⟩; obtain ⟨s,hs,hp⟩:= covering root Z F hl (show X b≠0 from hb); refine ⟨⟨s,?_⟩,Subtype.ext hs⟩
     change Y s≠0; rw [← hatched (z:=z) root Z h hp, hs]; exact hb
  refine ((Equiv.ofBijective u ⟨he,hu⟩).hasSum_iff_of_support ?_).mpr hs
  exact fun i=>hatched (z:=z) root Z h (hz _ i.prop)
end YM.RemainderComparison.Flues
