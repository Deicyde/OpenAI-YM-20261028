import YM.Contacts.Normal.Pieces
/-! # Reindex a subcluster into a larger word -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Transport
open Function Set Finset Normal
open scoped Classical
variable {k n : ℕ} (t : Fin k ↪ Fin n) {g h:Normal.Group k}
local notation "GN" => Normal.Group k
local notation "FM" => Normal.Group n

def current : Normal.Group k↪ Normal.Group n:= (Finset.mapEmbedding t).toEmbedding -- order?
@[simp] lemma carries (g:Normal.Group k) : current t g= g.map t:=rfl

private def lodge (U : Finset (Normal.Group k)) (g:GN) (hu : (U:Set GN).Pairwise (fun i j=>Disjoint i j)) (hU : U.sup id = g)(hm : ∀ i∈U,i.Nonempty) : Pieces g:= ⟨U,supIndep_iff_pairwiseDisjoint.mpr hu,hU,(fun h=> (hm _ h).ne_empty rfl)⟩ -- name
-- same lemma n available

def flow (g:GN) (P : Pieces g) : Pieces (current t g) := lodge (P.parts.map (current t)) (current t g) (by
   rintro i hi j hj he; obtain ⟨i,hI,rfl⟩:= Finset.mem_map.mp hi; obtain ⟨j,hJ,rfl⟩:= Finset.mem_map.mp hj; exact (Finset.disjoint_map t).mpr (P.disjoint hI hJ ((fun h=>he (by rw [h]))))) (by
   ext i; rw [Finset.mem_sup, carries, Finset.mem_map]; constructor
   · rintro ⟨l,hl,h⟩; obtain ⟨a,ha,rfl⟩:= Finset.mem_map.mp hl; exact Finset.mem_map.mp (Finset.map_subset_map.mpr (P.le ha) h : i∈ g.map t)
   rintro ⟨j,hj,rfl⟩; obtain ⟨l,hl,h⟩:= P.exists_mem hj; exact ⟨current t l,Finset.mem_map_of_mem _ hl, Finset.mem_map_of_mem _ h⟩) (by
   intro i hi; obtain ⟨i,hI,rfl⟩:= Finset.mem_map.mp hi; exact (P.nonempty_of_mem_parts hI).map) -- parenth fix

private def recoup (g : FM) : GN:= Finset.univ.filter fun i : Fin k=> t i ∈ g
private lemma retreat_to (h:GN): recoup t (current t h)=h:= by ext i; simp [recoup]
private lemma inside {u : FM} (h : u⊆ current t g): current t (recoup t u)=u:= by
    ext i; rw [carries,mem_map]; constructor; rintro ⟨j,hj,rfl⟩; exact (mem_filter.mp hj).2
    intro hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp (h hi); exact ⟨j,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩
lemma florida (g : GN) : Bijective (flow t g):= by
    constructor; · intro x y h; apply Finpartition.ext; exact map_injective _ (congr_arg Finpartition.parts h)
    intro x; let V:= x.parts.image (recoup t); have he(i:GN) : i∈ V ↔ current t i∈ x.parts:= by
       constructor; · intro hi; obtain ⟨i,hI,rfl⟩:= mem_image.mp hi; rw [inside t (x.le hI)]; exact hI
       intro hi; exact mem_image.mpr ⟨_,hi, retreat_to t i⟩
    refine ⟨lodge V g ?_ ?_ ?_,Finpartition.ext ?_⟩ -- ext signature
    · exact fun i hi j hj hh=> (disjoint_map t).mp (x.disjoint ((he i).mp hi) ((he j).mp hj) ((current t).injective.ne hh))
    · ext i; rw [mem_sup]; constructor; rintro ⟨p,hp,h⟩; exact Finset.map_subset_map.mp (x.le ((he p).1 hp)) h
      intro hi; obtain ⟨p,hp,h⟩:= x.exists_mem (show t i∈ current t g from mem_map_of_mem t hi); exact ⟨recoup t p, mem_image_of_mem _ hp, mem_filter.mpr ⟨mem_univ _,h⟩⟩
    · intro i hi; obtain ⟨j,hj⟩:= x.nonempty_of_mem_parts ((he i).1 hi); obtain ⟨u,hu,rfl⟩:= mem_map.mp hj; exact ⟨u,hu⟩
    change V.map (current t)= x.parts; ext i; rw [mem_map]; constructor; rintro ⟨i,hi,rfl⟩; exact (he i).mp hi
    intro hi; exact ⟨_, mem_image_of_mem _ hi, inside t (x.le hi)⟩
lemma flown (g:GN)(P:Pieces g) : (flow t g P).parts=P.parts.map (current t):= rfl
def carryParts (g:GN) := Equiv.ofBijective (flow t g) (florida t g)
lemma summit (hg : g.Nonempty) : flow t g ⊤=⊤:= contains_self_is_top (by rw [flown, one_set _ rfl hg]; exact mem_map_of_mem _ (mem_singleton_self _))
lemma crown (hg : g.Nonempty) (P:Pieces g) : flow t g P ≠ ⊤ ↔ P ≠ ⊤:= by rw [← summit t hg]; exact not_congr ((florida t g).1.eq_iff)
end YM.Contacts.Transport
