import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Cards
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Projection
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Uniformizer
import YM.Next.BOUNDARY.Assembly
import YM.Next.EXTRACTION.Base
import YM.Next.FOUNDATIONS.Primary



/-!
# Support routing for the local numerical criterion

No rerolling. Only frost variables which are indeed frozen, breeze
coordinates at the actual non-tree active bonds. Require the recorded
support reaches both endpoint projections. The compilers producing real
terms are responsible for adding their other complete dependencies; no
certificate here of a gauge invariant representation or of locality in V.

`Roster` tests the dependency *on y,z,k in the integral*, not stability of
covariances across nearby V. Postage has to use the indicated per-sector,
same-forest, physical marginal prescriptions. `off` is only an entry test,
not assuming independence of forest weights or products. Also don't treat a
submatrix of a precision as defining the covariances of these marginals.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp
open Function Filter Lattice Wilson RG Pressure Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open Push.SectorMeasure Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}
  {F : Forest S.ratio}

/-- Use only actual integration arguments. -/
structure Ribbon {c f : Side} {S : StepData c f} (F : Forest S.ratio) (X : Support c) where
  frost : Finset F.Free
  ice e : e ∈ frost → S.ratio.parent e.val.1 ∈ X ∧ S.ratio.parent (e.val.1+Lattice.step e.val.2) ∈ X
  breeze : Finset F.Free
  wind e : e ∈ breeze → S.ratio.parent e.val.1 ∈ X ∧ S.ratio.parent (e.val.1+Lattice.step e.val.2) ∈ X

namespace Ribbon
variable {X : Support c} (U : Ribbon F X) {A : Stores S}

abbrev live := (↥U.frost)
abbrev lit (G : Gauge) := (↥U.breeze) × G.ColorIndex
abbrev Page (G : Gauge) := LinkArray G U.live × Vec (U.lit G)

structure Placed (U : Ribbon F X) (x : ℝ) (A : Stores S) : Prop where
  frost e : e∈U.frost → chill A x F e
  breeze e : e∈U.breeze → ¬chill A x F e

variable {U}
def slide (h : U.Placed x A) : U.live ↪ Frozen A x F :=
  ⟨fun a => ⟨a.val,h.frost _ a.property⟩,fun _ _ ht => Subtype.ext (congr_arg (fun x : Frozen A x F => x.val) ht)⟩
def lighten (h : U.Placed x A) : U.lit G ↪ Rows.In x A F (G:=G) :=
  ⟨fun a => (⟨a.1.val,h.breeze _ a.1.property⟩,a.2),fun _ _ ht => Prod.ext
    (Subtype.ext (congr_arg (fun i : Rows.In x A F (G:=G) => i.1.val) ht)) (congr_arg (fun i : Rows.In x A F (G:=G) => i.2) ht)⟩

def look (h : U.Placed x A) (y : Room G x F A) : Page U G :=
  ⟨fun i => y.1 (slide h i), fun i => y.2 (lighten h i)⟩

def reel (C : Gaussian.Table (Rows.In x A F (G:=G))) (h : U.Placed x A) :=
    C.submatrix (lighten h) (lighten h)

lemma measure (C : Gaussian.Table (Rows.In x A F (G:=G))) (hC : C.PosDef) (h : U.Placed x A) :
    MeasurePreserving (look h)
      ((piHaar G (Frozen A x F)).prod (cloud C)) ((piHaar G U.live).prod (cloud (reel C h))) :=
  (Projection.pi_projection G.probHaar (slide h)).prod (Projection.cloud_projection hC (lighten h))

end Ribbon

variable {T : Tube G S} {R : Rep G f} {D : Allocation G S x W}
  {L : Almanac T D R F} {V : Config G c} {E ι : Type} [DecidableEq E] {K : Cards S ι E}

/-- External requirement on marginal alignment. At one V. Can pad alphabet
with unused zero labels for inter-V passports (read sets needn't be static;
the *Cards* agreements for the corresponding theorem do matter).
Sample at a completion with the actual D'. Require read sets also placed
in EVERY assembled family where used, not just at a sample. -/
structure Roster (L : Almanac T D R F) (V : Config G c) (K : Cards S ι E) where
  ribbon (i : ι) : Ribbon F (K.X i)
  sample : ι → Stores S
  real (i : ι) : (sample i).flags=RG.flags (temp x) V
  checked i : (ribbon i).Placed x (sample i)
  localized k l i : Tags.Synchronized (K.X i) k l → Ribbon.reel (L.C (sample i) V k) (checked i) =
    Ribbon.reel (L.C (sample i) V l) (checked i)
  secure (A : Stores S) (Q : Finset ι) (n : Finset E) (ha : A.flags=RG.flags (temp x) V)
    (hQ : K.Makes A n Q) (i : Q) : (ribbon i).Placed x A
  records (A : Stores S) (k : S.Choices) (Q : Finset ι) (n : Finset E) (ha : A.flags=RG.flags (temp x) V)
    (hQ : K.Makes A n Q) (i : Q) : Ribbon.reel (L.C A V k) (secure A Q n ha hQ i)=
      Ribbon.reel (L.C (sample i) V k) (checked i)
  off (A : Stores S) (k : S.Choices) (Q : Finset ι) (n : Finset E) (ha : A.flags=RG.flags (temp x) V)
    (hQ : K.Makes A n Q) (i j : Q) : i ≠ j → ∀ a b, L.C A V k
      (Ribbon.lighten (secure A Q n ha hQ i) a) (Ribbon.lighten (secure A Q n ha hQ j) b)=0

namespace Roster
variable (H : Roster L V K)

abbrev point (i) := (H.ribbon i).Page G
def air (i : ι) (k : S.Choices) := Ribbon.reel (L.C (H.sample i) V k) (H.checked i)
abbrev paper (i : ι) (k : S.Choices) : Measure (H.point i) :=
  (piHaar G (H.ribbon i).live).prod (cloud (H.air i k))

def primary (i : ι) : Room G x F (H.sample i) → H.point i := Ribbon.look (H.checked i)
lemma measured (h : L.Available V) (i : ι) k :
    MeasurePreserving (H.primary i) (L.climate V (H.sample i) k) (H.paper i k) :=
  Ribbon.measure _ (h.trueCov (H.sample i) k (H.real i)).nativePos (H.checked i)

abbrev Script := (i : ι) → S.Choices → H.point i → ℝ


def rates (ψ : H.Script) (i) k := ∫ y,ψ i k y ∂H.paper i k


def uniform (ψ : H.Script) := ∀ i k l,Tags.Synchronized (K.X i) k l → ψ i k=ψ i l

variable {H} {ψ : H.Script}



variable {A : Stores S} {Q : Finset ι} {m : Finset E}

def imprint (H : Roster L V K) (ψ : H.Script) (hx : A.flags=RG.flags (temp x) V) (h : K.Makes A m Q) (k : S.Choices)
    (y : Room G x F A) := ∏ i : Q, ψ i k (Ribbon.look (H.secure A Q m hx h i) y)

theorem freezeApart (hx : A.flags=RG.flags (temp x) V) (h : K.Makes A m Q) (i j : ↥Q) (hr : i ≠ j)
    (a b) : Ribbon.slide (H.secure A Q m hx h i) a ≠ Ribbon.slide (H.secure A Q m hx h j) b := by
  intro hz
  have he := congr_arg Subtype.val hz
  change a.val=b.val at he
  have hb := h.1 (show i.val∈(↑Q : Set ι) from i.property) j.property (mt Subtype.ext hr)
  exact Finset.disjoint_left.mp (show Disjoint (K.X i.val) (K.X j.val) from hb)
    ((H.ribbon i.val).ice _ a.property).1 (he.symm ▸ ((H.ribbon j.val).ice _ b.property).1)

/-- At fixed k. No Hölder shares or independence on Y from elsewhere needed
beyond the physical read warrants. -/
theorem valued (paid : L.Available V) (k : S.Choices) (hφ : ∀ i, Integrable (ψ i k) (H.paper i k))
    (hx : A.flags=RG.flags (temp x) V) (h : K.Makes A m Q) :
    Integrable (H.imprint ψ hx h k) (L.climate V A k) ∧
      (∫ y,H.imprint ψ hx h k y ∂L.climate V A k)= ∏ i∈Q,H.rates ψ i k := by
  have hi := Projection.integrals (I:=↥Q) G.probHaar (paid.trueCov A k hx).nativePos
    (fun i => Ribbon.slide (H.secure A Q m hx h i)) (freezeApart hx h)
    (fun i => (Ribbon.lighten (H.secure A Q m hx h i) : _ → Rows.In x A F (G:=G)))
    (H.off A k Q m hx h) (fun i => H.air i k) (H.records A k Q m hx h)
    (fun i => ψ i k) (fun i => hφ i.val)
  refine ⟨hi.1,hi.2.trans ?_⟩; change ∏ i : Q,H.rates ψ i k = _
  exact prod_coe_sort Q (fun i => H.rates ψ i k)
end Roster
end YM.AnalyticBridge.Sharp
