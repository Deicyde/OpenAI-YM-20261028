import YM.Ac.Table
import YM.Pressure.Seeds
import YM.SectorNext.RECONNECTED_LOCALITY.Parts


set_option warningAsError false

/-!
# Compulsory packet selection at the actual Store

Use actual D'(V), fine seeds at actual
plaquettes not macro owners, noise seeds at physical bonds. `g` the joining
radius (e.g. 500B) not necessarily the bound on the overlap support of
packet products; keep the latter at least that large through component tests.
No spontaneous seed at each path whose footprint contains a frozen link. User
must equip products with complete tested placement rules; not implementing the
choice of all localized paths or that A^{-1} can be given a local dependence!
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect

open RG Lattice Wilson Words Pressure

variable {c f : Side} {S : StepData c f}

namespace Fleet

abbrev Seed (c f : Side) := Cell f ⊕ Bond c ⊕ Site c
abbrev Packet (c f : Side) := Finset (Seed c f)

/-- Enumerate typed seeds even at overlap or unused. -/
def manifest (A : Stores S) : Finset (Seed c f) := A.costs.disjSum (A.aisles.disjSum A.flags)
def scan (s : Finset (Seed c f)) : Stores S := ⟨s.toLeft,s.toRight.toLeft,s.toRight.toRight⟩

@[simp] theorem scanned (A : Stores S) : scan (manifest A)=A := by cases A; simp [scan,manifest]

@[simp] theorem record (s : Finset (Seed c f)) : manifest (scan (S:=S) s)=s := by simp [scan,manifest, Finset.toLeft_disjSum_toRight]

/-- Join compulsory seeds on *complete* common physical support. -/
def whereAt (S : StepData c f) : Seed c f → Support c := Sum.elim (Pressure.startPos S) (Sum.elim pinPos fun i => {i})

def spans (S : StepData c f) (g : ℕ) (e : Seed c f) := halo g (whereAt S e)





/-- Packet for each complete 500B-connected seed set, not per tree or seed count.
Can include internal seeds already at the *same* projected place. -/
def packs (S : StepData c f) (g : ℕ) (s : Finset (Seed c f)) : Finset (Packet c f) := Ac.Parts (spans S g) s

@[simp] lemma seeds (g : ℕ) (s : Finset (Seed c f)) : (packs S g s).biUnion id=s := Ac.reconstruct ..

lemma arise (g : ℕ) (p : Finset (Packet c f)) (he : Pieces (spans S g) p) :
    packs S g (p.biUnion id) = p := Ac.separates _ p he.2 he.1

abbrev Label (c f : Side) (α : Type*) := Packet c f ⊕ ℕ ⊕ α

variable {G : Gauge} {α par : Type*}

def useSeeds : Label c f α → Finset (Seed c f) := Sum.elim id fun _ => ∅
def events (s : Finset (Label c f α)) : Finset (Seed c f) := s.biUnion useSeeds

def stored (i : Label c f α) : Support c := (scan (S:=S) (useSeeds i)).flags

def kSet (s : Finset (Label c f α)) : Finset ℕ := s.toRight.toLeft
def addSet (s : Finset (Label c f α)) : Finset α := s.toRight.toRight

def draft (g : ℕ) (A : Stores S) (b : Finset ℕ) (s : Finset α) : Finset (Label c f α) :=
    (packs S g (manifest A)).disjSum (b.disjSum s)

/-- Deterministically remove the optional choices, retaining the primary tables.
-$V$ recipe can continue to use actual $D'$ at other sites if needed to
complete a cov matrix (entry-locality still required). -/
def core (s : Finset (Label c f α)) : Finset (Label c f α) := s.toLeft.disjSum ((kSet s).disjSum ∅)

@[simp] lemma draft_packets (g : ℕ) (A : Stores S) (b : Finset ℕ) (s : Finset α) :
    (draft g A b s).toLeft=packs S g (manifest A) := by simp [draft]

@[simp] lemma draft_k (g : ℕ) (A : Stores S) (b : Finset ℕ) (s : Finset α) :
    kSet (draft g A b s)=b := by simp [draft,kSet]

@[simp] lemma draft_add (g : ℕ) (A : Stores S) (b : Finset ℕ) (s : Finset α) :
    addSet (draft g A b s)=s := by simp [draft,addSet]

@[simp] lemma draft_core (g : ℕ) (A : Stores S) (b : Finset ℕ) (s : Finset α) :
    core (draft g A b s)=draft g A b ∅ := by simp [core,draft,kSet]

lemma list_events (s : Finset (Label c f α)) : events s=s.toLeft.biUnion id := by
  ext x; constructor
  · intro hx; obtain ⟨q,hq,hp⟩:=Finset.mem_biUnion.mp hx
    rcases q with p|p
    · exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_toLeft.mpr hq,hp⟩
    exact (Finset.notMem_empty _ hp).elim
  intro hx
  obtain ⟨q,hq,hp⟩:=Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨.inl q,Finset.mem_toLeft.mp hq,hp⟩

@[simp] lemma draft_events (g : ℕ) (A : Stores S) (b : Finset ℕ) (s : Finset α) : events (draft g A b s)=manifest A := by
  simp [list_events]

lemma accounts (s : Finset (Label c f α)) : region (stored (S:=S)) s=(scan (S:=S) (events s)).flags := by
  ext x; simp [scan,region,stored,events]

/-- Full selection gate on raw addresses; old K supports disjoint, **not** requiring
augmented K footprints disjoint. Compulsory packet duplicate/accidental neighbor must fail
already within a component. All additional h eligibility (near/remote defaults etc) belongs
pointwise WITHIN the corresponding X.value even at zeros. Here `parent` permits countably many
marked variants of a given optional h, only one per term. Read its common footprint when needed.
-/
def required (S : StepData c f) (T : Activities G f) (g : ℕ) (parent : α → par)
    (l : Label c f α) (s : Finset (Label c f α)) : Prop := match l with
    | .inl p => Ac.Spark (spans S g) p ∧ ∀ q, Sum.inl q ∈ s → p≠q → Disjoint (region (spans S g) p) (region (spans S g) q)
    | .inr (.inl i) => ((∀ j∈ kSet s,i≠j→Disjoint (T.forced i).support (T.forced j).support) ∧
        ∀ x∈(T.forced i).inventory, ∃ p∈s.toLeft,∃ a : Cell f,.inl a∈p ∧ x∈ touched a)
    | .inr (.inr i) => ∀ j∈addSet s,parent j = parent i → j=i

/-- Origin validity check on a K list, BEFORE tossing seeds. -/
def origins (T : Activities G f) (A : Stores S) (b : Finset ℕ) : Prop :=
    ((b : Set ℕ).Pairwise (fun i j => Disjoint (T.forced i).support (T.forced j).support)) ∧
      ∀ i∈b,∀ x∈(T.forced i).inventory, ∃ q∈ A.costs,x∈touched q

/-- No selections of alternatives twice at their parent. -/
def pure (parent : α → par) (s : Finset α) := ∀ i∈s,∀ j∈s,parent j=parent i → j=i

theorem classified (T : Activities G f) (g : ℕ) (parent : α → par) (s : Finset (Label c f α)) :
    permits (required S T g parent) s ↔ Pieces (spans S g) s.toLeft ∧
      origins T (scan (S:=S) (events s)) (kSet s) ∧ pure parent (addSet s) := by
  have he (x : Site f) : (∃ p∈s.toLeft,∃ a : Cell f,Sum.inl a∈p ∧ x∈ touched a) ↔
        ∃ q∈(scan (S:=S) (events s)).costs,x∈touched q := by
    simp only [scan,list_events,Finset.mem_toLeft, Finset.mem_biUnion]
    constructor
    · rintro ⟨i,hi,q,hq,hx⟩; exact ⟨q,⟨i,hi,hq⟩,hx⟩
    · rintro ⟨q,⟨i,hi,hq⟩,hx⟩; exact ⟨i,hi,q,hq,hx⟩
  have hp (i) : i∈kSet s ↔ Sum.inr (Sum.inl i)∈s := by simp [kSet]
  have hq (i) : i∈addSet s ↔ Sum.inr (Sum.inr i)∈s := by simp [addSet]
  constructor
  · intro h
    have ht (i) (hi : i∈s.toLeft) := h _ (Finset.mem_toLeft.mp hi)
    have hu (i) (hi : i∈kSet s) := h _ ((hp i).mp hi)
    refine ⟨⟨fun i hi j hj hn => (ht i hi).2 j (Finset.mem_toLeft.mp hj) hn,fun i hi => (ht i hi).1⟩,
      ⟨fun i hi j hj => (hu i hi).1 j hj,fun i hi x hx => (he x).1 ((hu i hi).2 x hx)⟩,?_⟩
    intro i hi; exact h _ ((hq i).mp hi)
  rintro ⟨hT,h1,h2⟩ (i|j|j) hj
  · refine ⟨hT.2 _ (Finset.mem_toLeft.mpr hj),fun j hm hn => ?_⟩
    exact hT.1 (Finset.mem_toLeft.mpr hj) (Finset.mem_toLeft.mpr hm) hn
  · exact ⟨fun i hi => h1.1 ((hp j).mpr hj) hi,fun x h => (he _).2 (h1.2 _ ((hp j).mpr hj) x h)⟩
  exact h2 _ ((hq j).mpr hj)

@[simp] theorem draft_perm {T : Activities G f} {g : ℕ} {parent : α → par} {A : Stores S} {b : Finset ℕ} {t : Finset α} :
    permits (required S T g parent) (draft g A b t) ↔ origins T A b ∧ pure parent t := by
  rw [classified]; simp [packs,Words.partition]

@[simp] theorem draft_coverage {g : ℕ} {A : Stores S} {b : Finset ℕ} {t : Finset α} :
    region (stored (S:=S)) (draft g A b t) = A.flags := by rw [accounts]; simp

theorem restored {T : Activities G f} {g : ℕ} {parent : α → par} {s : Finset (Label c f α)}
    (h : permits (required S T g parent) s) :
    draft g (scan (S:=S) (events s)) (kSet s) (addSet s) = s := by
  unfold draft; rw [record, list_events, arise _ _ ((classified T g parent s).1 h).1]; simp [kSet,addSet,Finset.toLeft_disjSum_toRight]

/-- Exactly reconstruct permitted physical selections & alternatives, not identifying even at zero. -/
theorem draft_inj (g : ℕ) : Function.Injective (fun p : Stores S × Finset ℕ × Finset α => draft g p.1 p.2.1 p.2.2) := by
  rintro ⟨A,b,t⟩ ⟨A',b',t'⟩ (h : draft g A b t=draft g A' b' t')
  have he : A=A' := by simpa using congr_arg (fun i => scan (S:=S) (events i)) h
  have hh : b=b' := by simpa only [draft_k] using congr_arg kSet h
  have hv : t=t' := by simpa only [draft_add] using congr_arg addSet h
  rw [he,hh,hv]

/-- The price check for keeping gate eligibility. Location obligations for consumed
`A,S,K` values are stronger, at each $V$ endpoint and tag coordinate, even on mask zeros. -/
theorem stationed (T : Activities G f) (g : ℕ) (parent : α → par) (W : Label c f α → Support c)
    (hp : ∀ p, region (spans S g) p ⊆ W (.inl p))
    (hk : ∀ j,(T.forced j).support.image S.ratio.parent ⊆ W (.inr (.inl j)))
    (hv : ∀ i j,parent j=parent i → ¬Disjoint (W (.inr (.inr i))) (W (.inr (.inr j)))) :
    Retained W (required S T g parent) := by
  have hd (T T' P P' : Support c) (H : T ⊆ P) (H' : T' ⊆ P') (hh : ¬Disjoint T T') : ¬Disjoint P P' := by
    intro he; obtain ⟨x,hx,hx'⟩:=Finset.not_disjoint_iff.mp hh
    exact Finset.disjoint_left.mp he (H hx) (H' hx')
  have h (l : Label c f α) (s b : Finset (Label c f α))
      (Hs : ∀ j,¬Disjoint (W l) (W j) → (j∈s↔j∈b)) (H : required S T g parent l s) : required S T g parent l b := by
    rcases l with p|i|i
    · refine ⟨H.1,fun j hj hn => of_not_not fun hz => ?_⟩
      exact hz (H.2 j ((Hs _ (hd _ _ _ _ (hp p) (hp j) hz)).mpr hj) hn)
    · constructor
      · intro j hj hn
        by_contra! he
        obtain ⟨x,hx,hy⟩:=Finset.not_disjoint_iff.mp he

        have ht : ¬Disjoint (W (.inr (.inl i))) (W (.inr (.inl j))) := Finset.not_disjoint_iff.mpr
          ⟨S.ratio.parent x,hk i (Finset.mem_image_of_mem _ hx),hk j (Finset.mem_image_of_mem _ hy)⟩
        have hh : Sum.inr (Sum.inl j)∈s := (Hs _ ht).mpr (by simpa [kSet] using hj)
        exact he (H.1 j (by simpa [kSet] using hh) hn)
      intro x hx
      obtain ⟨p,hm,q,hq,ht⟩ := H.2 x hx
      have hr := hk i (Finset.mem_image_of_mem S.ratio.parent ((T.forced i).inventory_sup hx))
      have hh : _ ∈ W (.inl p) := hp p (Finset.mem_biUnion.mpr ⟨_,hq,halo_subset g _ (Finset.mem_image_of_mem S.ratio.parent ht)⟩)
      exact ⟨p,Finset.mem_toLeft.mpr ((Hs _ (Finset.not_disjoint_iff.mpr ⟨_,hr,hh⟩)).mp (Finset.mem_toLeft.mp hm)),q,hq,ht⟩
    intro j hj hn
    have he := (Hs _ (hv i j hn)).mpr (show Sum.inr (Sum.inr j)∈b by simpa [addSet] using hj)
    exact H j (by simpa [addSet] using he) hn
  intro l s b H
  exact propext ⟨h l s b H,h l b s fun j he => (H j he).symm⟩

end Fleet
end YM.SectorNext.Reconnect
