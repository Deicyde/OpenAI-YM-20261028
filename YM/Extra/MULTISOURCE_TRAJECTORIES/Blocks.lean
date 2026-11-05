import YM.Extra.MULTISOURCE_TRAJECTORIES.Localization
/-!
# Economical windows for the localized conditional coefficients

A maximal packing of native B-balls, patches of radius 2B. No divisibility
requirement. Count the full fragment alphabet per root by traversing a
minimizing cover and snapping it to the packing, also for X winding, before
counting arbitrary subsets (both marker names and decorations). Uniform
base per cover-ball if occupancy is bounded; no base growing as the number
of choices of *native* offsets or the periods. Constants extremely crude.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open RG Wilson Marker Lattice Corona Function Filter MeasureTheory Finset
open scoped Topology BigOperators ContDiff Classical
variable {V : Type} {n : Side} (b : ℕ)

def Spread (s : Finset V) (o : V → Site n) := ∀ i∈s,∀ j∈s,i ≠ j → b+b < separation (o i) (o j)







structure Net (b : ℕ) (n : Side) where
  bases : Support n
  dense : halo (2*b) bases=univ
  apart : Spread b bases id



def numbers (r : ℕ) : ℕ := (r+r+1)^4






namespace Net
variable {b} (Z : Net b n)

def region (x : Site n) := halo (2*b) {x}

def windows : Windows n := ⟨Z.bases.image (region (b:=b)), by
  apply eq_univ_of_forall; intro x; obtain ⟨i,hi,hx⟩ := halo_spec.mp (Z.dense.symm ▸ mem_univ x)
  exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ hi,halo_spec.mpr ⟨i,mem_singleton_self _,hx⟩⟩⟩






def step (x : Site n) := Z.bases.filter (fun i => separation x i ≤ 6*b)
def walks (x : Site n) : ℕ → Finset (List (Site n))
  | 0 => {[]}
  | k+1 => (Z.step x).biUnion (fun y => (walks y k).image (y :: ·))





lemma travel {r : ℕ → Site n} (hr : ∀ i,r i∈Z.bases) {x} (hx : separation x (r 0) ≤ 6*b)
    (h : ∀ i,separation (r i) (r (i+1)) ≤ 6*b) (k : ℕ) : ∃ l∈Z.walks x k,∀ i,i<k → r i∈l.toFinset := by
  induction k generalizing x r with
  | zero => exact ⟨[],mem_singleton_self _,fun _ hi => by omega⟩
  | succ k ih =>
    obtain ⟨l,hl,H⟩ := ih (r:=fun i => r (i+1)) (fun i => hr _) (h 0) (fun i => h (i+1))
    refine ⟨r 0 :: l,mem_biUnion.mpr ⟨r 0,mem_filter.mpr ⟨hr _,hx⟩,mem_image_of_mem _ hl⟩,fun i hi => ?_⟩
    cases i with
    | zero => simp
    | succ i => exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (H i (by omega))))




end Net

def score (m : ℕ) := numbers 4*m+numbers 4
def chips (m : ℕ) : ℕ := (numbers 6 * 2^score m)^13


variable {b} (Z : Net b n)
namespace Alphabet
variable [DecidableEq V] [Fintype V] (R : Marker.Census V) (o : V → Site n) (core : V → Support n)

abbrev Full := Hot R × Z.windows.Piece
def wall (a : Full Z R) := Windows.patch (a.1.val.val.biUnion core) a.2.val






end Alphabet
end YM.Extra.Trajectories
