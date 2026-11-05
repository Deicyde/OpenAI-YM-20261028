import YM.Next.RANK.Flux.Orb

/-!
# Exact marked Needle LOG, all subsets before any phases

For gas of marked atoms with nonzero marker: no repeats. Take an unlimited ghost
alphabet first (one needle per address). LOG over those, local expansion useful
for any restricted gas under the given support exclusions. Pivot formula for
marking any parent before estimates (no volume prefactor). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac
open scoped BigOperators Classical

variable {V W ι : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

-- disj geometry. log coefficients carried as complex
section
variable {n : Side} (X : V → Support n) (f : V → veil W)

def packed (a : Finset V) : Prop := (a:Set V).PairwiseDisjoint X

def chair (a : Finset V) := ∑ z∈ a.powerset,if packed X z then (∏ i∈z,f i) else 0

def pipe (i : V) : veil V:=Poly.send (slot i) 1
lemma cluster_form (s : Finset V) : (∏ i∈s, pipe i)= Poly.send (scene s) 1:= by
  induction s using Finset.induction_on with
  | empty=> rw [prod_empty,scene_nil]; rfl
  | insert i s hi ih=> rw [prod_insert hi,ih,pipe,plate_pair,if_pos]; simp only [slot,Census.fire,one_mul,singleton_union]; rfl; simpa [slot,Census.fire,scene] using hi

def aura (s : Finset V):= chair X pipe s
lemma aura_part (s q : Finset V): (aura X s).part (scene q)=(if q⊆s ∧ packed X q then 1 else 0) := by
  unfold aura chair; rw [Poly.part_sum];simp_rw [cluster_form]
  by_cases h:q⊆s
  · rw [sum_eq_single q]; split; swap
    · rename_i hh;simp only [hh,and_false,↓reduceIte,Poly.part_nil]
    · rename_i hp; simp [h,hp]
    · intro j _ hn; split; rw [Poly.part_send,if_neg (fun he => hn (((same_scene ..).1 he).symm))]; rfl
    simp [h]
  rw [if_neg (fun H=> h H.1)]; refine sum_eq_zero fun i hi=> ?_; split; rw [Poly.part_send,if_neg]; exact fun hh=> h (((same_scene ..).mp hh).symm ▸ mem_powerset.mp hi); rfl
lemma vacuum_chair (s : Finset V) : (aura X s).part (quiet V)=1:= by
  rw [← scene_nil,aura_part,if_pos];exact ⟨empty_subset _,by simp [packed]⟩

def herald (s : Finset V): veil V := Exponential.connected _ (vacuum_chair X s)
lemma herald_spec (s : Finset V) : Expands (herald X s) (aura X s):= Exponential.connected_spec ..
lemma compass {s q : Finset V} (h : q⊆s) : bed q (herald X s)=herald X q:= by
  have he:= bedrock q (herald_spec X s); have hv: bed q (aura X s)=aura X q:= by
    ext i; change (bed q (aura _ s)).part (scene i.val)=(aura X q).part (scene i.val)
    rw [shelve,aura_part,aura_part]
    change (if i.val⊆_ then _ else _)= _
    split_ifs with h₁ h₂ h₃ hw <;> grind
  exact (hv ▸ he : Expands _ (aura X q)).uniq (herald_spec X q)

def majesty (q : Finset V): ℂ:= (herald X univ).part (scene q)
lemma throne (s q : Finset V): (herald X s).part (scene q)= if q⊆s then majesty X q else 0:= by rw [← compass X (subset_univ s)]; exact shelve ..
lemma majesty_zero : majesty X ∅=0:= (herald_spec X _).1
lemma throne_up (q : Finset V) : herald X q=∑ s∈ q.powerset, Poly.send (scene s) (majesty X s):= by
  ext i; rw [Poly.part_sum]; change (herald _ _).part (scene i.val)= ∑ s∈ q.powerset, (Poly.send _ _).part (scene i.val)
  rw [throne]; split_ifs with hx
  · rw [Finset.sum_eq_single i.val]; simp; intro j _ h; rw [Poly.part_send,if_neg (fun h' => h (Subtype.ext_iff.mp h'.symm))]; simp [hx]
  symm; refine sum_eq_zero fun _ hv=> ?_; rw [Poly.part_send,if_neg]; exact fun h => hx ((same_scene ..|>.mp h).symm ▸ mem_powerset.mp hv)

-- ratio via removing pivot. relevant subsets touch its support. combin formula integral

def rests (q : Finset V) (v : V):= (q.erase v).filter (fun i=> Disjoint (X v) (X i))
lemma withdrawn (v : V) {q : Finset V} (hv : v∈q) : aura X q = aura X (q.erase v)+ pipe v*aura X (rests X q v):= by
  ext i; rw [Poly.part_plus]; let t:= i.val; change Poly.part _ (scene t)=Poly.part _ (scene t)+Poly.part _ (scene t)
  by_cases ht:v∈t
  · have hh:¬t⊆ q.erase v:=fun h=>Finset.notMem_erase v q (h ht)
    have hf:t \ {v}= t.erase v:= by ext; simp [and_comm]
    have he:t ⊆ q ∧ packed X t ↔ t.erase v⊆rests X q v ∧ packed X (t.erase v):= by
      constructor
      · rintro ⟨H,D⟩; exact ⟨fun j hj=> mem_filter.mpr ⟨erase_subset_erase v H hj,D ht (mem_erase.mp hj).2 (mem_erase.mp hj).1.symm⟩,
          fun i hi j hj hz=> D (mem_erase.mp hi).2 (mem_erase.mp hj).2 hz⟩
      rintro ⟨h₁,h₂⟩; refine ⟨fun j hj=> ?_,fun i hi j hj H=>?_⟩
      · by_cases h:j=v; exact h.symm ▸ hv
        exact (mem_erase.mp (mem_filter.mp (h₁ (mem_erase.mpr ⟨h,hj⟩))).1).2
      rcases eq_or_ne i v with rfl|hi'
      · exact (mem_filter.mp (h₁ (mem_erase.mpr ⟨H.symm,hj⟩))).2
      rcases eq_or_ne j v with rfl|hj'
      · exact (mem_filter.mp (h₁ (mem_erase.mpr ⟨H,hi⟩))).2.symm
      exact h₂ (mem_erase.mpr ⟨hi',hi⟩) (mem_erase.mpr ⟨hj',hj⟩) H
    rw [pipe,plate,aura_part,aura_part,if_neg (show ¬(t⊆q.erase v ∧ packed X t) from fun H=>hh H.1),show (slot v).val={v} from rfl,show (scene t).val=t from rfl,if_pos (show {v} ⊆ t from singleton_subset_iff.mpr ht), zero_add,one_mul,aura_part]; simp only [hf,he]
  have h₁:t ⊆ q.erase v ↔ t⊆ q:= by
    refine ⟨fun h=>subset_trans h (erase_subset ..),fun H j hj=> mem_erase.mpr ⟨?_,H hj⟩⟩
    intro h;exact ht (h ▸ hj)
  rw [pipe,plate,aura_part,aura_part,show (slot v).val={v} from rfl,show (scene t).val=t from rfl,if_neg (show ¬{v}⊆ t from fun h=> ht (singleton_subset_iff.mp h)),add_zero];simp only [h₁]

def omitX (q : Finset V) (v : V):= (q.erase v).powerset \ (rests X q v).powerset
omit [Fintype V] in
lemma plural {q u : Finset V} {v : V} (h : u∈ omitX X q v): (u.biUnion X ∩ X v).Nonempty:= by
  obtain ⟨he,hz⟩:=mem_sdiff.mp h
  by_contra H
  refine hz (mem_powerset.mpr fun i hi=> mem_filter.mpr ⟨mem_powerset.mp he hi,disjoint_left.mpr fun j hj hJ=>?_⟩)
  exact H ⟨j,mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,hi,hJ⟩,hj⟩⟩
omit [Fintype V] in
lemma omen {q u : Finset V} {v : V} (h : u∈ omitX X q v):u.Nonempty:= by
  obtain ⟨j,hj⟩:=plural X h; obtain ⟨i,H,-⟩:=mem_biUnion.mp (mem_inter.mp hj).1; exact ⟨i,H⟩

def breeze (q : Finset V) (v : V) : veil V:=Poly.pass (herald X (rests X q v) - herald X (q.erase v))
lemma assist {q : Finset V} {v : V} (h : v∈q): herald X q=herald X (q.erase v)+ pipe v*breeze X q v:= by
  let P:=q.erase v;let R:=rests X q v;let b:=breeze X q v; let l:=pipe v
  have h₁: (l*b).part (quiet V)=0:=by
    rw [show l=Poly.send _ _ from rfl, plate, if_neg];exact fun H=> notMem_empty v (H (mem_singleton_self v))
  have he:l*l=0:=by unfold l pipe; rw [plate_pair,if_neg]; simp [slot,Census.fire]
  have H₂: b* Poly.pass (herald X P)=aura X R := by
    unfold b breeze
    rw [← pass_add,sub_add_cancel]; exact (herald_spec ..).2; exact ((part_sub ..).trans (sub_eq_zero.mpr ((herald_spec ..).1.trans (herald_spec ..).1.symm))); exact (herald_spec ..).1
  let W:=herald X P
  apply Expands.uniq (herald_spec X q); refine ⟨(Poly.part_plus ..).trans ?_,?_⟩
  · change _+Poly.part (l*b) _=_;rw [h₁,(herald_spec ..).1, add_zero]
  change Poly.pass (W+l*b)=_
  rw [pass_add _ _ (herald_spec ..).1 h₁, ride h₁ (show l*b*(l*b)=0 by rw [mul_mul_mul_comm,he, zero_mul]), withdrawn X v h]
  change _= aura X P+l*aura X R
  rw [mul_comm (Poly.pass W),add_mul,one_mul,mul_assoc,H₂,add_comm,(herald_spec ..).2]

end
end YM.Next.Rank.Flux
