import YM.Further.DENSE_MIXED_KERNELS.Dark
import YM.Further.DENSE_MIXED_KERNELS.Operands
import YM.Further.DENSE_MIXED_KERNELS.View
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.ABSOLUTE_SUMS.Path


/-!
# Per-entry integral in the physical dictionary/marker variables

Take any realized system word of the forms here. The variant factors
are charged before its evaluation, one numbered occurrence at a time.
The entry has the indicated factorials (including at true repeated
alpha/id); pay even when visiting same operand locations many times.
The alphabet can instead be originally distinct with unity divisor.

Protected supports—not independent windows of each operand—pay the
Hold switch used here. V left regular estimates not attempted for
forced entries. The assignment of actual factors in a chosen Scheme
(must retain powers/scalars, likelihoods, and eligibility changes with exact
normalization; including choices of extensions of component functions)
and satisfying all primitive factor assumptions about them is still
a problem. See production theorems for using these estimates with that
input; not asserting an inhabited physical first system.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Lattice RG Wilson Precision Labels Marker Overlay Extra.Multi Extra.Multi.Merger Tree
open Port Gaussian Surface
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n m : Side} {S : StepData m n} {F : Forest S.ratio}
    {α β V : Type} [DecidableEq V] {R : Census V} {P : Rep G n}
    {A : ChartRatio G} {H : Port A} {ρ : α → Pieces} {L : Bands R P} {U : Config G m}

abbrev Chain.Index {α : Type} (c : Chain α) := Fin (c.1+1)
def catalog {α : Type} (x : Chain α) : Multiset α := Extra.Multi.Numbered.bag x.2
def oneWord {α : Type} (x : Chain α) : ℝ := (Extra.Multi.Numbered.divisor (catalog x):ℝ)⁻¹
lemma word_positive {α : Type} (x : Chain α) : 0< oneWord x := inv_pos.mpr (Extra.Multi.Numbered.divisor_pos _)
lemma costed {α : Type} (x : Chain α) (p : α → ℝ) : Merger.paid p (catalog x) = oneWord x * ∏ i,p (x.2 i) := by
  rw [Merger.paid,div_eq_mul_inv,mul_comm]
  congr 1
  exact congr_arg Multiset.prod (Multiset.map_map p x.2 Finset.univ.val)

-- Pre-cluster, also covers performance with unitary letter prices (there might e.g.
-- be only a marked source factor, in which case any protections can be
-- put on initial for that vertex). The beacon condition accounts for every
-- fine piece including K predicate. Some additional support billing
-- hypotheses needed outside per-entry theorem.
structure Word (H : Port A) (F : Forest S.ratio) (v : Chain (α ⊕ β)) (L : Bands R P) (ρ : α → Pieces) where
  model : View H F
  initial : v.Index → Config G m → model.Before → ℂ
  beacon : ∀ i j,v.2 i=Sum.inl j → model.Held (inspected (blocks L (ρ j)))

variable {x : Chain (α⊕β)}
namespace Word
variable (D : Word H F x L ρ) (g : ℝ) (U : Config G m)

def post (i : x.Index) (U : Config G m) (p : D.model.After) := D.initial i U ((D.model.base U).mapUp g p)
def pre (p : D.model.Before) : ℂ := ink L x ρ (D.model.config U g p) * ∏ i,D.initial i U p

/-- Physical pre-integral (no Jacobian costs have been manually
removed from this normalized component integral); scalar from changing the step
itself to such components needs to remain in the unmarked step ledger, not
per marker. -/
def value := (oneWord x) • (∫ p, D.pre g U p ∂(D.model.base U).ante D.model.fare)

def cast (p : D.model.After) := ink L x ρ (D.model.recover p)
def uncolored := whole D.model.base (D.post g) g

def body (y : D.model.After) (v : Config G m) := D.cast y * D.uncolored g y v
abbrev inside := ambient H D.model.J D.model.K D.model.fare

def Prepared (g : ℝ) (U : Config G m) := ∀ p∉ (D.model.base U).gateway g, (∏ i,D.initial i U p)=0

theorem tied (h : L.Active) (p : D.model.Before) :
    ink L x ρ (D.model.config U g p)=D.cast ((D.model.base U).mapDown g p) := by
  apply Finset.prod_congr rfl; intro i _
  cases he : x.2 i
  case inl j => exact home L h _ _ _ (View.probes _ U g (D.beacon _ _ he) p)
  case inr j => rfl

lemma pays_in (h : L.Active) (hp : D.Prepared g U) (hy : 0<g) (ht : (D.model.base U).Valid)
    (he : Integrable (fun i => D.body g i U) D.inside) :
    Integrable (D.pre g U) ((D.model.base U).ante D.model.fare) ∧
    D.value g U= (oneWord x) • ∫ y,D.body g y U ∂D.inside := by
  let Z := D.model.base U
  let q (i) := D.cast i * ∏ j,D.post g j U i
  have hx : (fun i => D.body g i U) = fun i => Z.confirm g i • q i := by
    ext1 i; simp only [body,uncolored,whole,q, Complex.real_smul,Z]; ring
  rw [hx] at he
  have h1 (v) (hv : v∉Z.gateway g) : D.pre g U v=0 := by unfold pre; rw [hp v hv,mul_zero]
  have h2 (v) (hv : v∈Z.gateway g) : D.pre g U v=q (Z.mapDown g v) := by
    unfold q pre Z at *; rw [tied D g U h]; congr 1
    exact Finset.prod_congr rfl fun j _ => by unfold post; rw [Surface.upDown g hy hv]
  obtain ⟨hh,hE⟩ := ht.first_copy (φ:=q) (f:=D.pre g U) hy he h1 h2
  refine ⟨hh,?_⟩
  unfold value; rw [hE]
  exact congrArg (fun a => oneWord x • (∫ y,a y ∂D.inside)) hx.symm

structure Green (u : Config G m) (P' : Directions G m → Prop) (t c C : ℝ) (b : x.Index → ℝ) (k q : ℕ) : Prop where
  runs : Glides D.model.base u g t k P' c C
  tall : Arc D.model.base D.model.fare (D.post g) u P' b k q g t
  -- nearby even when off Good
  also : ∀ᶠ v in 𝓝 (0:Directions G m), (D.model.base (increment u v)).Valid ∧ D.Prepared g (increment u v)

variable {b : x.Index → ℝ} {P' : Directions G m → Prop} {k q : ℕ} {c C t : ℝ} {M : Pieces→ℝ}
    {γ : ℝ}

-- same as W.tally assumptions; provider should supply THIS Green on the
-- chosen u and extension. Does not assume or construct identity of F.reg.value
-- with the integral (see Scheme provider input).
theorem green_light (hc : 0<c) (hC : 1≤C) (ht : 0≤t) (hp : 0<g) (hy : g≤1)
    (h : L.Active) (hh : Inbox L γ M) (hκ : γ ≤ 1) (hb : ∀ i,0 ≤ b i) (hw : D.Green g U P' t c C b k q) :
    (∀ᶠ v in 𝓝 (0:Directions G m),Integrable (D.pre g (increment U v)) (((D.model.base (increment U v)).ante D.model.fare))) ∧
    Pitch (D.value g) U P' k (oneWord x * ( (∏ i,metric ρ M (x.2 i)) * (∏ i,b i) *
      billed H (Fintype.card x.Index) (Fintype.card ↥D.model.J) (Module.finrank ℝ (H.front D.model.J (H.Room D.model.K))) k q t c C)) 1 := by
  let w := ∏ i,metric ρ M (x.2 i)
  have hf : 0≤ w := Finset.prod_nonneg fun i _ => by cases x.2 i <;> first | exact hh.pos _ | exact zero_le_one
  have hcost y : ‖D.cast y‖ ≤ w := ink_bound L _ _ h hh hκ _
  have hm : Measurable D.cast := (ink_meas L x ρ h).comp D.model.bunched
  let E (v : Config G m) := ∫ y,D.body g y v ∂D.inside
  have Hh : ∀ᶠ v in 𝓝 (0:Directions G m), let V := increment U v; D.value g V=oneWord x • E V ∧
      Integrable (D.pre g V) ((D.model.base V).ante D.model.fare) := by
    filter_upwards [hw.also,(hw.tall.charter.insulate hm hf hcost).oft] with v ⟨hy,hv⟩ ht
    exact (D.pays_in g _ h hv hp hy ht.reads).symm
  refine ⟨Hh.mono (fun i hi => hi.2),?_⟩
  let G' : ℂ →L[ℝ] ℂ := oneWord x • ContinuousLinearMap.id ℝ _
  have he := Arc.evaluate hw.runs hw.tall hc hC hp hy ht hb D.cast hm hf hcost
  have hz v : ‖G' v‖ ≤ oneWord x*‖v‖ := by
    change ‖oneWord x • v‖ ≤ _; rw [norm_smul_of_nonneg (word_positive x).le]
  exact Pitch.congr' (Pitch.linear he G' hz (word_positive x).le) (Hh.mono fun i hi => hi.1)

theorem hard (h : L.Active) (hh : Inbox L γ M) (hκ : γ ≤ 1) (hp : 0<g) (hb : ∀ i,0≤ b i)
    (hw : Dark D.model.base D.model.fare (D.post g) U b g) (hh' : D.Prepared g U) :
    Integrable (D.pre g U) ((D.model.base U).ante D.model.fare) ∧
      ‖D.value g U‖ ≤ oneWord x*((∏ i,metric ρ M (x.2 i)) * (∏ i,b i) * 3) := by
  let w := ∏ i,metric ρ M (x.2 i)
  have hf : 0≤ w := Finset.prod_nonneg fun i _ => by cases x.2 i <;> first | exact hh.pos _ | exact zero_le_one
  have hcost y : ‖D.cast y‖ ≤ w := ink_bound L _ _ h hh hκ _
  obtain ⟨hl,hL⟩ := hw.evaluate hp hb _ ((ink_meas L x ρ h).comp D.model.bunched) hf hcost
  obtain ⟨hv,ht⟩ := D.pays_in g U h hh' hp hw.registered hl
  refine ⟨hv,?_⟩; rw [ht,norm_smul_of_nonneg (word_positive x).le]; exact mul_le_mul_of_nonneg_left hL (word_positive x).le

end Word
end YM.Further.DenseMixedKernels
