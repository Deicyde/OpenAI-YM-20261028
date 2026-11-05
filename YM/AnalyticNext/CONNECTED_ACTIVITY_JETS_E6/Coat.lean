import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogLink
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Remainder

/-!
# Coat of a sector

Real variables: full dummy Slice inputs allowed, unused tree positions in arrays
ignored. One chart/covariance on this Coat. `issued` prepares a *single* shell
radius for this L especially for the weak extensions while appending/erasing
stencils. No canopy edits to V branch masks. W and REAL distances. `Coat`
can be instantiated at arbitrary compatible sector data; later use on actual
`PLOT`/owned components with footprints, never changing fine tree during a
sectorized push.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent SectorMeasure Tags  SliceRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S}

/-- Post-L, pre-sector requirement on actual step. -/
structure ShellAccess (S : StepData c f) (G : Gauge) (x W A γ : ℝ) : Prop where
  log : Reliable G (A*Pressure.fiery G x S.patch.L) γ
  exacts : ∀ (F : Forest S.ratio) (U : Config G f) (V : Config G c) (e : Bond f) (k : S.Choices),
    SliceSet S F U → Interior S x W (atEdge S e) (radiusB x/4) U k V →
    G.chord (U e*(replica S.ratio V e)⁻¹) ≤ A*Pressure.fiery G x S.patch.L

lemma shell_access (G : Gauge) (P : Teller G) (D : Patch) (L : Side) {W : ℝ} (hw : 0 < W) :
    ∃ K γ : ℝ, 0<K ∧ 0<γ ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
    S.patch=D → S.patch.L=L → Room P S T x → ShellAccess S G x W K γ := by
  obtain ⟨C,hC,h⟩ := cops_at G P L
  obtain ⟨γ,r,hr,hg⟩ := reliable G
  let K := shellPrice D C W
  have hK : 0<K := shellPrice_pos D hC.le hw
  refine ⟨K,γ,hK,(hg r hr le_rfl).price,?_⟩
  filter_upwards [((Rate.flame (G:=G) (L:=L)).mul_left K).below (by norm_num) _ hr] with x hx c f S T hS hL hh
  have hv : K*Pressure.fiery G x S.patch.L ≤ r := by rw [hL]; exact (le_abs_self _).trans hx
  refine ⟨hg _ (mul_pos hK hh.fiery) hv,?_⟩
  intro F U V e k hk hi
  exact (hi.displacement hw.le hh hC fun hh' => h _ _ _ hL hh F U V k hk e hh').trans_eq
    (congr_arg (· * _) (by unfold K; rw [hS]))

/-- View of the input record, no independent U, tree, tag or likelihood
rules. μ,A,C later defined on the complete choices, words/spells use this
view without moving variables. -/
structure Coat {S : StepData c f} (T : Tube G S) (F : Forest S.ratio) where
  seeds : Stores S
  x : ℝ
  χ : Chi
  width : ℝ  -- K in `cutLog`, separate larger gamma
  V : Config G c
  k : S.Choices
  Y : F.Slice G

namespace Coat
variable {F : Forest S.ratio} (X : Coat T F)

abbrev t := Pressure.fiery G X.x S.patch.L
abbrev B := radiusB X.x
abbrev R := till X.x
abbrev Hot := active F X.seeds X.B

def view (u : Directions G f) (i : F.Free) := if X.Hot i.val then increment (replica S.ratio X.V) u i.val else X.Y i

def input (u : Directions G f) : Config G f := F.drape (X.view u)

/-- Read vector for frame. `saved` includes only frozen nontree.
But the same logarithm can be used for initialization on active sites. -/
def small (i : Bond f) (U : Config G f) : G.Color := cutLog X.χ (X.width*X.t) (U i*(replica S.ratio X.V i)⁻¹)

def saved : Directions G f := fun i => if i∈F.trunks ∨ X.Hot i then 0 else X.small i (F.drape X.Y)

def lens (v : Directions G f) : Directions G f := fun i => if X.Hot i then v i else 0

def signal (v : Directions G f) : Directions G f := X.saved + X.lens v

/-- Value of the raw reply for a channel. Selection & square outside
this form. -/
def realPath (s : Signed) (p : Rod c f) (v : Directions G f) :=
    request T X.x (Oriented.choice s X.k) (pull s 0 X.V) p + orientedRow T X.R s p X.V (X.signal v)



lemma viewing (u : Directions G f) (p : Bond f) (he : X.Hot p) : X.input u p = increment (replica S.ratio X.V) u p :=
  (F.off_tree _ ⟨p,he.1⟩).trans (if_pos he)

lemma dormant (u : Directions G f) (p : Bond f) (he : ¬X.Hot p) : X.input u p = F.drape X.Y p := by
  by_cases hf : p∈F.trunks
  · exact (F.on_tree _ ⟨p,hf⟩).trans (F.on_tree _ ⟨p,hf⟩).symm
  exact (F.off_tree _ ⟨p,hf⟩).trans ((if_neg he).trans (F.off_tree _ ⟨p,hf⟩).symm)

lemma sliced (u : Directions G f) : SliceSet S F (X.input u) := fun e h => F.on_tree _ ⟨e,h⟩

lemma at_hot (u : Directions G f) (p : Bond f) (he : X.Hot p) : X.signal u p=u p := by simp [signal,lens,saved,he]
lemma on_trunk (u : Directions G f) (p : Bond f) (he : p∈F.trunks) : X.signal u p=0 := by
  have hf : ¬X.Hot p := fun h => h.1 he
  simp [signal,lens,saved,he,hf]

lemma saved_cost {W γ : ℝ} (h : ShellAccess S G X.x W X.width γ) (p) : ‖X.saved p‖ ≤ γ*(2*(X.width*X.t)) := by
  unfold saved; split
  next _ => rw [norm_zero]; exact mul_nonneg h.log.price.le (by have hk : 0<X.width*X.t := h.log.down; positivity)
  next _ => exact h.log.use X.χ _

/-- Joint evaluation on active and weak frozen inputs. Interior premise
only paid through this actual column of Y,V and k. -/
lemma agrees_at {W γ : ℝ} (h : ShellAccess S G X.x W X.width γ) (u : Directions G f) (p : Bond f)
    (he : Interior S X.x W (atEdge S p) (X.B/4) (X.input u) X.k X.V) :
      X.input u p = increment (replica S.ratio X.V) (X.signal u) p := by
  by_cases hb : X.Hot p
  · rw [X.viewing u p hb]; unfold increment; rw [at_hot X u p hb]
  by_cases hf : p∈F.trunks
  · rw [(X.sliced u) p hf,increment,X.on_trunk u p hf,G.mat_lieExp_zero,one_mul]
    exact (if_pos (F.trunk_internal (by simpa using hf))).symm
  let U := X.input u
  let g := U p*(replica S.ratio X.V p)⁻¹
  have hv : G.chord g ≤ X.width*X.t := h.exacts F U X.V p X.k (X.sliced u) he
  have hp : X.signal u p = cutLog X.χ (X.width*X.t) g := by
    simp only [Coat.signal, Pi.add_apply,lens,saved,hb,hf,or_self,↓reduceIte,add_zero]
    unfold g U small; rw [dormant _ u p hb]
  rw [increment,hp,h.log.kept X.χ _ hv]
  have hh := h.log.down
  have h0 : X.width * X.t ≤ 2*(X.width*X.t) := by dsimp only [Coat.t]; linarith
  rw [h.log.right _ (hv.trans h0),show g=U p*(replica S.ratio X.V p)⁻¹ from rfl]; group
  rfl

/-- At every annulus or remote row, including nonselected terms in H200
*before* using Mask.profiles. If caller uses Wide from a single packet,
the near/far distinction and Hot need to be passed *unchanged* via the
footprint-read checks on extended `A`.' -/
theorem required {x₀ : Site c} {W γ M : ℝ} (u : Directions G f)
    (h : ShellAccess S G X.x W X.width γ)
    (hp : ∀ i : Bond f, distAt S i x₀≤X.B → Interior S X.x W (atEdge S i) (X.B/4) (X.input u) X.k X.V)
    (hx : ∀ i : Bond f, distAt S i x₀≤X.B → X.Hot i → ‖u i‖≤M)
    (hm : γ*(2*(X.width*X.t)) ≤ M) : Grafted X.V (X.input u) (X.signal u) x₀ X.B M S := by
  constructor
  · intro i hi; exact X.agrees_at h _ _ (hp _ hi)
  intro i hi; by_cases he : X.Hot i
  · rw [X.at_hot u i he]; exact hx i hi he
  simp only [signal,lens,Pi.add_apply,if_neg he,add_zero]; exact (saved_cost X h _).trans hm

/-- Outside the compulsory regime. No need Wide for h estimates as
we use the *extensions* directly (even U may fail all budgets in that
sector and the likelihoods aren't charged as though normalized here). -/
theorem distant (v : Directions G f) (x : Site c) {M : ℝ} (hm : 0 ≤ M)
    (hz : ¬ Inside x X.seeds (11*X.B+1))
    (hp : ∀ i : Bond f, distAt S i x ≤ X.B → X.Hot i → ‖v i‖≤M) :
      Grafted X.V (X.input v) (X.signal v) x X.B M S := by
  have he (p) (hs : distAt S p x ≤ X.B) (hf : p∉F.trunks) : X.Hot p := by
    refine far_active X.seeds F p (clear hz (by unfold distAt at hs; omega)) hf
  constructor
  · intro i hi; by_cases hg : i∈F.trunks
    · rw [X.sliced v i hg, increment,X.on_trunk v i hg,G.mat_lieExp_zero,one_mul]
      exact (if_pos (F.trunk_internal (by simpa using hg))).symm
    rw [X.viewing v i (he i hi hg)]; unfold increment; rw [X.at_hot _ _ (he i hi hg)]
  intro i hi; by_cases hg : i∈F.trunks
  · rwa [X.on_trunk v i hg,norm_zero]
  rw [X.at_hot v _ (he i hi hg)]; exact hp i hi (he i hi hg)
end Coat
end YM.ConnectedActivityE6
