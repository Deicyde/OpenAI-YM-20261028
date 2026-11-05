import YM.MergeProof.West.Form
import YM.Next.RANK.Flux.Orb
/-!
# Dependencies and algebraic split of the logarithm
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Marker Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {A E ι V:Type*}
lemma g_honors [CommRing A] [CommRing E] [Algebra ℂ A] [Algebra ℂ E] (f:A →ₐ[ℂ] E) (X:Clump ι) (g:ι→A):
    f (honors X g)=honors X (f ∘ g):=by
  induction X with
  | nil=>simp [honors]
  | cons x l h=>
    have he (l : List ι): f (l.map g).prod = (l.map (f ∘ g)).prod:=by induction l <;> simp [*]
    simp only [honors,List.map_cons,List.sum_cons,_root_.map_add,map_mul,f.commutes,he]; exact congr_arg (_+·) h
variable [Fintype V][DecidableEq V]
def embraces (Y:grove V) : Prop:=∀ v t,t∈Y v → ∀ i∈t.2,i.val ⊆ v.val
lemma embraces.prime : embraces (primeLog V):= by rintro v t ht; obtain rfl:=List.mem_singleton.mp ht; exact fun i hi=> (List.mem_singleton.mp hi).le
variable {X D:grove V}(h:embraces X)
namespace embraces
include h
lemma adds (s:ℝ): embraces (stretchLog V s X):=by rintro v t ht; obtain ⟨l,hl,rfl⟩:= List.mem_map.mp ht; exact h v l hl
lemma gpack (H:embraces D): embraces (packs V X D):=by
  rintro v t ht i hi
  obtain ⟨w,hw,hT⟩:= List.mem_flatMap.mp ht; obtain ⟨z,hz,hZ⟩:= List.mem_flatMap.mp hT; obtain ⟨x,hx,rfl⟩:= List.mem_map.mp hZ
  rcases List.mem_append.mp hi with he|he; exact subset_trans (h _ _ hz i he) (mem_powerset.mp (mem_toList.mp hw)); exact subset_trans (H _ _ hx i he) sdiff_subset
lemma bark (i:ℕ): embraces (snag V X i):= by
  induction i with
  | succ i H=>rw [snag]; exact gpack H h
  | zero=> rintro v t ht; by_cases h:v=quiet V
           · simp only [snag, h,if_true, List.mem_singleton] at ht; subst t; simp
           simp [snag,h] at ht
lemma knees : embraces (sprout V X):=by rintro v t hT; obtain ⟨i,-,hi⟩:= List.mem_flatMap.mp hT; exact (bark h i).adds _ v t hi
lemma axes (k:ℕ): embraces (stout V X k):=by
  induction k with
  | zero=>exact fun _ _ hx=>False.elim (List.not_mem_nil hx)
  | succ i H=>intro v t ht; exact (List.mem_append.mp ht).elim (H v t) (fun l=> (List.mem_append.mp l).elim (h v t) (H.knees.adds _ v t))
end embraces
lemma yolk_club : embraces (yolk V):= embraces.prime.axes _
open Flux
lemma sectional (Y:veil V)(A B:Finset V)(h:Disjoint A B) (s : modes V)(hs:s.val⊆ A∪B): (bed A Y * bed B Y).part s= Y.part (scene (s.val∩A))*Y.part (scene (s.val∩B)):= by
  have hx : s.val \ (s.val∩A)=s.val∩ B:= by
    ext v; constructor
    · intro hH; obtain ⟨hL,hR⟩:=mem_sdiff.mp hH; exact mem_inter.mpr ⟨hL,(mem_union.mp (hs hL)).resolve_left (fun h0=>hR (mem_inter.mpr ⟨hL,h0⟩))⟩
    intro hH; obtain ⟨h₁,h₂⟩:=mem_inter.mp hH; exact mem_sdiff.mpr ⟨h₁,fun hz=> disjoint_left.mp h (mem_inter.mp hz).2 h₂⟩
  rw [Glyph.part_mul, Finset.sum_eq_single (s.val∩A),hx, Flux.shelve,Flux.shelve,if_pos,if_pos]
  · exact inter_subset_right
  · exact inter_subset_right
  swap; · exact fun h=>False.elim (h (mem_powerset.mpr inter_subset_left))
  intro b hb hB
  rw [Flux.shelve,Flux.shelve]; split_ifs with h₁ h₂ hd
  · have hp:= mem_powerset.mp hb
    apply False.elim (hB (Finset.Subset.antisymm (subset_inter hp h₁) (fun x hX=> ?_)))
    obtain ⟨hs,hX⟩:=mem_inter.mp hX; contrapose! hX; intro he; exact disjoint_left.mp h he (h₂ (show x∈s.val\b from mem_sdiff.mpr ⟨hs,hX⟩))
  all_goals simp
lemma splits_apart (Y:veil V)(hg:Y.part (quiet V)=1)(A B:Finset V) (h:Disjoint A B)
    (ha:A.Nonempty)(hb:B.Nonempty)(s:modes V)(hs:s.val=A∪B)(H: ∀ l : modes V, l.val ⊆ s.val → Y.part l=Y.part (scene (l.val∩A))*Y.part (scene (l.val∩B))):
    (medicine (yolk V) Y).part s=0:= by
  let F:= medicine (yolk V) Y
  have he : bed s.val Y=bed A Y*bed B Y:= by
    ext i; rw [Flux.shelve]; split
    · next hx=> exact (H i hx).trans (sectional Y A B h i (hx.trans hs.le)).symm
    next hx=>
      rw [Glyph.part_mul]; symm; apply Finset.sum_eq_zero; intro l hh; rw [Flux.shelve,Flux.shelve];split_ifs with hl hy hz
      · apply False.elim (hx ?_); rw [hs]; exact Finset.Subset.trans (union_sdiff_of_subset (mem_powerset.mp hh) |>.ge) (union_subset_union hl hy)
      all_goals simp
  have hk:= belly Y hg
  have hx:= bedrock A hk; have hv:=bedrock B hk
  have hu : bed s.val F=bed A F+bed B F:= by
    refine Expands.uniq (bedrock _ hk) ⟨?_,?_⟩
    · rw [Poly.part_plus,hx.1,hv.1,zero_add]
    rw [pass_add _ _ hx.1 hv.1,hx.2,hv.2,he]
  obtain ⟨a,ha⟩:=ha; obtain ⟨b,hb⟩:=hb
  have h₁ : ¬s.val⊆A:=fun hx=> disjoint_left.mp h (hx (hs.symm ▸ (show b∈A∪B from mem_union_right _ hb))) hb
  have h₂ : ¬s.val⊆B:=fun hx=> disjoint_left.mp h ha (hx (hs.symm ▸ (show a∈A∪B from mem_union_left _ ha)))
  have H:= congr_arg (fun P=> Poly.part P s) hu; rw [Poly.part_plus, Flux.shelve,if_pos (Finset.Subset.refl _), Flux.shelve,Flux.shelve,if_neg h₁,if_neg h₂,add_zero] at H
  exact H
end YM.Next.Rank.Tapes.West
