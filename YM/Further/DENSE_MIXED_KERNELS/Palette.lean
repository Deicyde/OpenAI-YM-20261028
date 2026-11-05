import YM.Further.DENSE_MIXED_KERNELS.Stroke

/-!
# A constructor pricing the *marked* ingredients, inc variants

Stroke costs for H/K all allocated here, before recenter.
Vacuum-only ingredients which coexist in the component (e.g. packet
multipliers, any unmarked numerical profiles/ratios etc left for
reindexing) have their uncolored expenses as inputs. These are inputs on
the integrand of each component; they must be the actual REQUIRED factors
on the stated table. No bound on a mixed integral postulated. In the
common case that chart zones for some vacuum factors are only through
an internal protector, multiply by external ψ=1 on that support before use,
keep its support in the geometry. Don't move masks depending on the
unheld U through this step.

Useful independently of Stroke roots on vacuum partners;
for x ONLY marks it suffices to take envelope/travel controls on `View`
and letter geometry/variant tests (see `Embroidery`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Pads
open Port Gaussian Surface Tree Push.SectorMeasure Extra.Multi Labels Marker Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V α β : Type} [DecidableEq V] {R : Census V} {n m : Side} {G : Gauge} {S : StepData m n}
    {F : Forest S.ratio} {A : ChartRatio G} {H : Port A} {Y : Rep G n} {L : Bands R Y}
    {x : Chain (α⊕β)} {ρ : α→Pieces} {U : Config G m} {P : Directions G m→Prop}
    {D : Word H F x L ρ} {k q : ℕ} {g w d T r c C b t : ℝ}

-- α are marked; β vacuum addresses even on an alphabet carrying both kinds
-- of evaluations. Use with eligibility/connectivity/rights **separately** checked.
-- unitized ingredients mandatory on mark slots! In particular Vac assumptions on
-- `wash` below are just on 1 there. support pricing nonzero labels; γ and ψ sizes
-- chosen after L. does NOT test which factors *should* have those eligibility rules.
structure Palette (D : Word H F x L ρ) (g w d : ℝ) where
  dye : Chi
  draw : x.Index → Stroke D.model.J D.model.K
  vac : x.Index → Config G m → D.model.Before→ℂ
  water : ∀ i, (x.2 i).isLeft → vac i=1
  fixed : ∀ i v y,D.initial i v y=(draw i).mark (D.model.base v) dye g w d y*vac i v y
  sheet : ∀ i:D.model.J, ∃ j, i∈ (draw j).J

namespace Palette
variable (s : Palette D g w d)

def wash (i : x.Index) (v : Config G m) (p : D.model.After) := s.vac i v ((D.model.base v).mapUp g p)



include s in
lemma caged (u) (hw : 0<w) : D.Caged g (2*w) u := by
  intro p h i
  obtain ⟨j,hj⟩ := s.sheet i
  have hh : D.initial j u p ≠ 0 := Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ _)
  rw [s.fixed] at hh; exact ((s.draw j).held _ hw (left_ne_zero_of_mul hh) _ hj).le


/-- Still need extension of the actual vaccuum numerical formulas. Air here
is on factor values/kernels before any integration. Patches may be paid
separately as in Stretch; sufficient condition stripping the protections
right off. Uses Ratio-type local form if required; no near criterion on
K/H amplitudes themselves (held fixed later). Includes unweighted
conditions; only Momentum will charge weights. -/
structure Air (s : Palette D g w d) (U : Config G m) (k : ℕ) : Prop where
  feel : let W := D.model.base
    ∃ b c C d' t : ℝ, ∃ q : ℕ, 0≤b ∧ 0<c ∧ 1≤C ∧ 0<d' ∧ 0≤t ∧ ∀ᶠ v in 𝓝 0,
      let V := increment U v; Glides W V g t k UnitDirs c C ∧
      (∀ i, Measurable (s.wash i V)) ∧
      ∀ y∈(W V).Perch, let z := ((W V).mapUp g y).2
        ∃ u : x.Index → ℝ, (∀ i,Pitch (fun x => s.wash i x y) V UnitDirs k (b * (1+‖z‖)^q*Real.exp (u i)) 1) ∧
          ∑ i,u i ≤ (W V).B y.1 z z - d'*‖z‖^2



variable {p : x.Index→ℝ}

/-- Graded proof for *just* wash on StepData for this occurrence. On φ terms
must give it even when there are large-field partners, and on marked
it is on the constant 1. -/
structure Tide (s : Palette D g w d) (U : Config G m) (P : Directions G m→Prop) (p : x.Index → ℝ)
    (T c C : ℝ) (k q : ℕ) : Prop where
  wash : let W := D.model.base
    ∃ a t : ℝ,∃ R L : x.Index → D.model.After→ℝ,0≤ t ∧ t≤T ∧ 0≤ a ∧ Glides W U g t k P c C ∧
      Fourth ((W U).aboard D.model.fare g) R ∧ Fourth ((W U).aboard D.model.fare g) L ∧
      ∀ i,(s.draw i).temper H s.dye k t + a ≤ T ∧ ∀ y,y ∈ (W U).Perch → Pitch (fun v => s.wash i v y)
        U P k (p i * R i y * L i y) (a*(W U).tower g y^q)



/-- Wash estimates on rough component. -/
structure Drain (s : Palette D g w d) (p : x.Index→ℝ) (U) : Prop where
  flow : Dark D.model.base D.model.fare s.wash U p g


end Palette
end YM.Further.DenseMixedKernels
