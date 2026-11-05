import YM.Bid.Drops
import YM.Next.WARD_BIN.Crest
import YM.Next.WARD_BIN.Flush



/-!
Only for scope of copies of a singleton in the same genealogy. Wants estimates ONLY on provisional-radius *high* terms
with an extra unit of support exponent; anchors separated and no thinning on
copies. Does not demand/assume closed budgets at the OUTPUT radii. Includes
density identities actual group fields and renormalized β choice from that H. No factorial estimates implied by path spec. Our Θ choice = nonfactorial cap
charged per marker, requires e.g. paying from raw output costs at this order
(no free dropping the factorial in E). Provisional loss b variable.

A **missing estimate**.

Don't
infer even this narrow step demand from `RRaw` semantics or G01-I04.

Enough to demand Volley when i
sufficiently large (period-independent after cutoff page choice).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Array
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay Source Bid Crest Wheels
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {W : Worth} {d ℓ N p i : ℕ} {t t' v u w κ' b : ℝ} (D : Page C d N p)

abbrev Cast (C : Family G) (ℓ p : ℕ) := Site (C.side ℓ p)
abbrev set (C : Family G) (ℓ p : ℕ) := Full (Cast C ℓ p)
abbrev Wing (C : Family G) (p ℓ i : ℕ) := Crest G (C.side i p) (set C ℓ p)
abbrev Plane (C : Family G) (N p i ℓ : ℕ) := Bands (set C ℓ p) (C.path.rep N p i)
abbrev zone (C : Family G) (ℓ i p : ℕ) := Mix.camp C p ℓ i
abbrev Moves (C : Family G) (ℓ p N i : ℕ) (s : Cast C ℓ p→Signed) :=
  (v : Cast C ℓ p) → (C.path.rep N p i).activities.Moves (s v) (zone C ℓ i p v)

def cap₁ (C : Family G) (i : ℕ) := C.path.levels.clock.hatCoupling i ^4 /64
def cap₂ (C : Family G) (i : ℕ) := C.path.levels.clock.hatCoupling i ^3 /64
def pressure (C : Family G) (b : ℝ) (d i : ℕ) := (↑(C.S.block i).val:ℝ)^d*(b:ℝ)

/-- Stage receipts for this quota are independent of p,N≥i. Need for paying
back at puffs L = L^γ. Not a P.Step theorem. Use only after i large. -/
def Quota (C : Family G) (d : ℕ) (b : ℝ) (i : ℕ) := 1 ≤ b ∧
  puffs (C.S.block i)*pressure C b d i ≤ Real.exp ((C.path.levels.clock.coverSize i:ℝ)/64)

def read {G : Gauge} {C : Family G} {ℓ N p i : ℕ} (B : Plane C N p i ℓ) (s : (set C ℓ p).Mode)
    (U : Config G (C.side i p)) : ℂ := (B.density U).part s

def drift (B : Plane C N p (i+1) ℓ) (L : Plane C N p i ℓ) (d : ℕ) (s : Mode (Cast C ℓ p)) :=
  read L s=Ride.bump (C.S.block i).val s (fun _ => d) • ((C.path.levels.clock.op i p).push (C.path.β N p (i+1)) (read B s))

-- Raw functions are scrambled together, not as separate families.
variable {s : Cast C ℓ p → Signed} {r : Cast C ℓ p → Bool}

def vhosts (C : Family G) {s : Cast C ℓ p → Signed} (r : Cast C ℓ p → Bool) (m : Moves C ℓ p N i s)
    (F : Coefficient (brim C d) (C.side i p)) (v) :=
  (Rib.single F 0 (C.localSection d) (C.path.rep N p i).p).cross (m v) (r v)

structure Crisp (C : Family G) {ℓ N p d i} {s : Cast C ℓ p → Signed} (r : Cast C ℓ p → Bool)
    (m : Moves C ℓ p N i s) (F : Coefficient (brim C d) (C.side i p)) (t w : ℝ) : Prop where
  ticket : F.Format 0 C.params (C.path.rep N p i) ∧ F.remBound 0 (C.path.rep N p i) (κ C.path i) t
  charged : w*(t+(brim C d).coeffSize F.x) ≤ cap₁ C i
  seated x : (vhosts C r m F x).Pitched (C.path.rep N p i)
  pressed x : (vhosts C r m F x).Rents (C.path.rep N p i) w (cap₁ C i) (κ C.path i)

/-- Port for one-step input, set immediately from L_m AFTER stage with allowed
delays.

Require compatible lifts of labels (here for all Moves).

Need `Page.Works` (aligned flow on this family) separately. The width used for
singleton caps at coarse end is the larger w·puffs. No promise those caps
hold: will establish them below WITHOUT changing that same Coefficient map. -/
def Volley (b : ℝ) (i : ℕ) : Prop :=
    ∀ (ℓ) (_ : ℓ ≤ i),
    let X := C.path.rep N p i
    let Y := C.path.rep N p (i+1)
    let o := zone C ℓ (i+1) p; let z := zone C ℓ i p
    Hollow Y.p o → Hollow X.p z → ∀ (s : Cast C ℓ p → Signed) (r : Cast C ℓ p → Bool)
    (f : Moves C ℓ p N (i+1) s) (g : Moves C ℓ p N i s) (x : Baton (brim C d) (C.side (i+1) p))
    (w : ℝ),0<w →
    let F := D.line.stage (i+1) x
    let P := D.line.stage i (D.line.flow i x)
    ∀ c t : ℝ, Crisp C r f F c w → Crisp C r g P t (w*puffs (C.S.block i)) →
      ∀ B : Wing C p ℓ (i+1), B.Green Y o → B.Rich Y o (fun _ => w) 0 (cap₂ C (i+1)) (κ C.path (i+1)) →
    ∃ L : Wing C p ℓ i, L.Green X z ∧ L.Rich X z (fun _ => w/pressure C b d i) 1 (cap₂ C i) (κ C.path i) ∧
      ∀ l : Mode (Cast C ℓ p), 2 ≤ l.val.card → drift (meld (vhosts C r f F) B Y) (meld (vhosts C r g P) L X) d l

abbrev Tee {C : Family G} {s : Cast C ℓ p → Signed} (P : Coefficient (brim C d) (C.S.side i p)) (r : Cast C ℓ p → Bool) (J : Moves C ℓ p N i s) (X : Wing C p ℓ i) := meld (vhosts C r J P) X (C.path.rep N p i)

lemma host (J : Moves C ℓ p N i s) (r : Cast C ℓ p→Bool) (F : Coefficient (brim C d) (C.side i p)) (v) :
    (vhosts C r J F v).root=zone C ℓ i p v := by simp [vhosts,Rib.cross,Rib.single,affine]



variable {J : Moves C ℓ p N i s} {U : Coefficient (brim C d) (C.side i p)} {B : Wing C p ℓ i}

lemma activate (h : Crisp C r J U t w) (hf : B.Green (C.path.rep N p i) (zone C ℓ i p)) : (Tee U r J B).Active :=
  B.joined h.seated (by simp_rw [host]; exact hf)






variable {D} {Z : Finset Cover}


end YM.WardBin.Array
