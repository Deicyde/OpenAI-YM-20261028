import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Windows

/-!
# Ordered chains: spelling/geometry

Use one bond block at each route node. Traces combine all colors along
same route. All positions implicit even last entry ending at own block;
finite enumeration per length includes all those canonical column tags. Do
not separate the letters on period or on sectorized likelihoods. Stencil
price via each transition enough on this band. Arcs that fail invariant
endpoint distance won't count; applies even when supports wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals  Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ : Type} {c f : Side} {S : StepData c f} {G : Gauge}

def Itinerary (f : Side) : ℕ → Type
  | 0 => Unit
  | k+1 => Bond f × Itinerary f k

namespace Itinerary
instance : ∀ {n : ℕ}, Fintype (Itinerary f n)
  | 0 => by rw [Itinerary]; infer_instance
  | n+1 => by rw [Itinerary]; let _ := @Itinerary.instFintype n; infer_instance

variable {n : ℕ}
def next {n : ℕ} (l : Itinerary f (n+1)) : Bond f := Prod.fst l
def after {n : ℕ} (l : Itinerary f (n+1)) : Itinerary f n := Prod.snd l
def bank (j : Bond f) (l : Itinerary f n) : Itinerary f (n+1) := Prod.mk j l
@[simp] lemma next_bank (j : Bond f) (l : Itinerary f n) : next (bank j l)=j := rfl
@[simp] lemma after_bank (j : Bond f) (l : Itinerary f n) : after (bank j l)=l := rfl
@[simp] lemma bank_all (p : Itinerary f (n+1)) : bank (next p) (after p)=p := by cases p; rfl

def chart (f : Side) (n : ℕ) : Itinerary f (n+1) ≃ Bond f × Itinerary f n where
  toFun p := (next p,after p)
  invFun p := bank p.1 p.2
  left_inv _ := bank_all _
  right_inv _ := Prod.ext rfl rfl

lemma sum_components (u : Itinerary f (n+1) → ℝ) :
    (∑ i, u i)=∑ j,∑ l : Itinerary f n, u (bank j l) := by
  rw [← Equiv.sum_comp (chart f n).symm u,Fintype.sum_prod_type]; rfl

def linear (i : Bond f) : {n : ℕ} → Itinerary f n → List (Bond f)
  | 0,_ => [i]
  | _+1,l => i::linear (next l) (after l)

def arrive (i : Bond f) : {n : ℕ} → Itinerary f n → Bond f
  | 0,_ => i
  | _+1,l => arrive (next l) (after l)
lemma final_here (i : Bond f) : ∀ {n : ℕ} (p : Itinerary f n), arrive i p ∈ linear i p
  | 0,p => by simp [arrive,linear]
  | n+1,p => List.mem_cons_of_mem i (final_here _ _)

def hop (S : StepData c f) (d : ℕ) (i j : Bond f) :=
    ∃ x∈ends S i,∃ y∈ends S j, separation x y ≤ d
lemma hop_ok (S : StepData c f) {d : ℕ} (i j : Bond f) (h : separation (atEdge S i) (atEdge S j) ≤ d) :
    hop S d i j := ⟨_,center_end _,_,center_end _,h⟩
lemma hop_cost {d : ℕ} {i j : Bond f} (h : hop S d i j) : separation (atEdge S i) (atEdge S j) ≤ d+2 := by
  obtain ⟨x,hx,y,hy,h⟩ := h
  have ha : separation (atEdge S i) x ≤ 1 := by rw [separation_comm]; exact stride _ hx
  have he := add_le_add ha ((separation_triangle _ y (atEdge S j)).trans (add_le_add h (stride _ hy)))
  exact ((separation_triangle _ x _).trans he).trans_eq (by omega)

def Armed (S : StepData c f) (d : ℕ) (i : Bond f) : {n : ℕ} → Itinerary f n → Prop
  | 0,_ => True
  | _+1,p => hop S d i (next p) ∧ Armed S d (next p) (after p)

/-- invariant super footprint. `C` keeps seed table, data, and gaussian
post queries -- still needs sufficient m for eventual stencil costs. -/
def town (S : StepData c f) (B m : ℕ) (i : Bond f) := halo (m*B) (ends S i)
def visited (S : StepData c f) (B m : ℕ) (i : Bond f) : {n : ℕ} → Itinerary f n → Support c
  | 0,_ => town S B m i
  | _+1,p => town S B m i ∪ visited S B m (next p) (after p)
lemma city (S : StepData c f) (m B : ℕ) (i : Bond f) : atEdge S i∈town S B m i := halo_subset _ _ (center_end _)
lemma cities (S : StepData c f) (m B : ℕ) (i : Bond f) : ∀ {n : ℕ} (l : Itinerary f n),
    atEdge S i∈visited S B m i l
  | 0,_ => city ..
  | _+1,_ => mem_union_left _ (city ..)
lemma checking (S : StepData c f) (m B : ℕ) (i : Bond f) (j : Site c) (h : j∈town S B m i) :
    separation (atEdge S i) j ≤ m*B+1 := by
  obtain ⟨x,hx,hh⟩ := halo_spec.mp h
  exact ((separation_triangle _ x _).trans (add_le_add ((separation_comm ..).trans_le (stride i hx)) hh)).trans_eq (Nat.add_comm ..)

def steady (m : ℕ) := ballCost (m+1)
lemma bridges {m B : ℕ} (i : Bond f) (h : 0 < B) : coverNumber B (town S B m i) ≤ steady m := by
  apply (Corona.cover_mono (X:= neighbors ((m+1)*B) (atEdge S i)) _ B).trans (Corona.tile _ _ _ h)
  intro x he; apply (neighbors_mem ..).mpr
  have hp := checking S m B i x he; rw [Nat.add_mul, Nat.one_mul]; omega
lemma pockets {B m d : ℕ} (hb : 0 < B) (he : d+2 ≤ m*B) (i : Bond f) : ∀ {n : ℕ} (l : Itinerary f n),
    Armed S d i l → coverNumber B (visited S B m i l) ≤ (n+1)*steady m
  | 0,l,_ => by simpa only [Nat.reduceAdd,Nat.one_mul] using! bridges (S:=S) (m:=m) i hb
  | n+1,l,h => by
    have hx : atEdge S (next l) ∈ town S B m i := halo_spec.mpr ⟨_,center_end i, (hop_cost h.1).trans he⟩
    exact ((Corona.meets_sum hx (cities S m B (next l) (after l)) _).trans
      (add_le_add (bridges i hb) (pockets hb he (next l) (after l) h.2))).trans_eq (by ring)
lemma tenure {B m d : ℕ} (he : d+2 ≤ m*B+1) (i : Bond f) : ∀ {n : ℕ} (l : Itinerary f n),
    Armed S d i l → ∀ x∈visited S B m i l, separation (atEdge S i) x ≤ (n+1)*(m*B+1)
  | 0,_,_,x,h => by simpa only [Nat.reduceAdd,Nat.one_mul] using! checking S m B i x h
  | n+1,l,h,x,hx => by
    rcases mem_union.mp hx with hi|hi
    · exact (checking S m B i x hi).trans (by nlinarith)
    exact ((separation_triangle _ _ _).trans (add_le_add ((hop_cost h.1).trans he)
      (tenure he (next l) (after l) h.2 x hi))).trans_eq (by ring)

end Itinerary
end YM.ConnectedActivityE6.Pulse
