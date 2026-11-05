import YM.Push.RELAY_DIFFERENCE.Lanes
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# A Range input from a termwise single-source dictionary

Instead of requiring a comparison of aggregate budgets independently,
prove it from a concrete labelled identification hypothesis (
incl the unit), and fiscal prices. Must be exact on the very same
polynomial L, not new Lanes for singleton. Use left derivative estimates
proved for oriented copies, and exponent/order currency on the real
stages. No spent derivatives from an accumulated cost. First provide the
isolated dictionary of components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.Single
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Labels Lattice Cells Marker Overlay Stock Bid Source Mix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {C : Family G} {N p m i d r : ℕ} {f : Extraction.Order} {F : Trial C} {n : Side}

/-! ### Support and mass under rotations -/

def rotor (s : Signed) (x : Site n) : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight x)

lemma cover_price (s : Signed) (b : Site n) (D : Support n) (M : ℕ) :
    coverNumber M (D.image (affine s b)) ≤ coverNumber M D := by
  classical
  let e : Equiv.Perm (Site n) := rotor s b
  have ht (x y : Site n) : separation (e x) (e y)=separation x y := by
    change separation (s.act x+b) (s.act y+b) = _
    rw [separation_translate, separation_signed]
  obtain ⟨A,h,hA⟩ := coverNumber_realized M D
  rw [←hA,←Finset.card_image_of_injective A e.injective]
  apply Corona.list_cost
  let Z := halo M A
  let W := halo M (A.image e)
  have hh (x : Site n) : x∈Z ↔ e x ∈ W := by
    change x ∈ halo M A ↔ e x∈halo M (A.image e)
    rw [halo_spec, halo_spec]; constructor
    · rintro ⟨i,hi,he⟩; exact ⟨e i,Finset.mem_image_of_mem _ hi,(ht i x).symm ▸ he⟩
    rintro ⟨y,hy,he⟩; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy; exact ⟨j,hj,(ht j x) ▸ he⟩
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (hh y).mp (h.1 hy)
  · intro x hx y hy
    obtain ⟨u,rfl⟩ := e.surjective x
    obtain ⟨v,rfl⟩ := e.surjective y
    exact Relation.ReflTransGen.lift (p:=Corona.Touch W 1) (r:=Corona.Touch Z 1) e
      (fun i j he => ⟨(hh _).mp he.1,(hh _).mp he.2.1,(ht ..).symm ▸ he.2.2⟩)
      u v (h.2 u ((hh _).mpr hx) v ((hh _).mpr hy))








/-! ### Costs of the canonical singleton dictionary -/

variable (S : Solo C F d)

def germ (N p i : ℕ) := (S.duet N p).voice i

def roots (N p i : ℕ) : ℕ → Support (C.side i p)
  | 0 => (C.localSection d).footprint 0
  | j+1 => (germ S N p i).support j

def bareSet (C : Family G) (N p i j : ℕ) := ((C.path.rep N p i).activities.forced j).support

def body (N p i : ℕ) : ℕ → Config G (C.side i p) → ℂ
  | 0 => let R := C.path.rep N p i
         let L := C.labels.level d
         (C.localSection d).places (L.scaled R.p.threshold⁻¹ (L.core (germ S N p i).x)) 0
  | j+1 => (germ S N p i).regular j





/-- Unmasked one-body dictionary costs for actual singleton (rotations
may have link-dependent signs). Support price independent of placement;
every argument tests the *same* lists of bounds from Format/cap. -/
structure Ledger (S : Solo C F d) (P : Prices) (N p i : ℕ) where
  rays : ℕ → ℝ
  force : ℕ → ℝ
  lengths j : 0 ≤ rays j ∧ ∀ x : Site (C.side i p),∀ (t : Signed) (b : Bool),
     let L := C.path.rep N p i
     grain L.p ((roots S N p i j).image (affine t x)) (oriented (body S N p i j) b t x) x (rays j)
  sends j : 0 ≤ force j ∧ ∀ x : Site (C.side i p),∀ (t : Signed) (b : Bool) (U),
     ‖oriented ((germ S N p i).forced j) b t x U‖ ≤ force j
  listed : SumBudget (fun j => (C.path.rep N p i).p.mass (roots S N p i j) (rays j)) (payee S N p i/P.coin i)
  burden : SumBudget (fun j => (C.path.rep N p i).p.mass (bareSet C N p i j) (force j)) (payee S N p i/P.coin i)
  units : ∀ b,‖hand b ((germ S N p i).x 0)‖ ≤ payee S N p i/P.coin i





variable {P : Prices} {W : Worth} {S}


end YM.Push.RelayDifference.Single
