import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Ground
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Pricing
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stamped
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay


/-!
Joint applicability BEFORE using `Kernel.assembled`. In particular deriving
activity health and quantity receipts, kernel marginal payments and radii on
the two bindings used by a tag or window comparison. All statements are
pre-mask. Only structural and some zeroth payments are produced here; sheets
with the typed elementary jet costs are still producer inputs (not supplied
by the free no-hole tree inverse prices). Valuation tightening later.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Precision Tree Matrix
  Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian Push.Local Work.G07
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Board of structural and zeroth kernel/gap prices, independent of the
period. Commissioned at Teller.Funds steps late enough at fixed L and w;
operator chooses that specific chart ratio, profile, d etc. -/
structure Board (T : Tube G S) (q : Chi) (Z : ChartRatio G) (l : ℕ) (x α d M C C' η K u v : ℝ) : Prop where
  ratio : LocalRatio Z
  fee : 0 < α
  gap : 0 < η
  matrix : 1 ≤ K
  reaction : 0<u
  decay : 0<v
  lies : 2*d < firstRadius G
  room : 4*d < Z.radius
  polar : Polar l M
  changes : Changes G l C
  guard : GuardCost q Z l d C'
  branch : S.patch.Branches S.kernel G
  ample (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (D : Allocation G S x α) :
    Admitted A F x V k Z D d ∧ (A.flags = RG.flags (temp x) V → kernelPrices T F x k A V η K u v ∧
      ∀ β : ℝ, 0<β → Permitted x V k A F D Z d β (fog A F T x V k) (meanLog A F T x V k q d))



variable {T : Tube G S} {q : Chi} {Z : ChartRatio G} {l : ℕ} {x α d M C C' η K u v : ℝ} {R : Rep G f}



structure Authored (R : Rep G f) (δ w : ℝ) (m ℓ : ℕ → ℝ) : Prop where
  valid : R.activities.Valid R.p δ w
  E (i : ℕ) : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (m i)
  K (i : ℕ) : 0 ≤ ℓ i ∧ ∀ U, ‖R.activities.K i U‖ ≤ ℓ i
  raised (y : Site f) : SumBudget (fun i => if (R.activities.reg i).site=y then R.p.mass (R.activities.reg i).support (m i) else 0) δ
  hit (y : Site f) : SumBudget (fun i => if y∈(R.activities.forced i).support then R.p.mass (R.activities.forced i).support (ℓ i) else 0) w


namespace Kernel
variable {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {P : Location f I J} {h h' : Kernel G c I J ρ} {V : Config G c} {p : BudgetPoint} {y : Site c}

def parentBound (S : StepData c f) (P : Location f I J) (p : BudgetPoint) (y : Site c) (t : ℝ) :=
    t⁻¹*(∑ i : I, p.threshold*(1+(separation (S.ratio.parent (P.address (.inl i)).1) y:ℝ))^p.power)

def tint (G : Gauge) := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : G.ColorIndex => ℝ)).symm.toContinuousLinearMap
def stageCost (G : Gauge) (t g a b : ℝ) := a+(t⁻¹*|g|)*(‖tint G‖ * b)
lemma combined {D : Directions G c → Prop} {t g a b v w : ℝ} (ht : 0<t) (hv : 0≤v) (hw : 0≤w)
    (e : ∀ i, Compare l D V ((t⁻¹:ℝ) • (h.mean · i)) ((t⁻¹:ℝ) • (h'.mean · i)) a b 1)
    (he : ∀ i, Compare l D V (h.draw · i) (h'.draw · i) v w 1) (i : I) :
    Compare l D V ((t⁻¹:ℝ) • (h.stage g · i)) ((t⁻¹:ℝ) • (h'.stage g · i)) (stageCost G t g a v) (stageCost G t g b w) 1 := by
  have hh := Compare.pi (f:=fun W j => h.draw W (i,j)) (fun j : G.ColorIndex => he (i,j)) hv hw zero_le_one
  have H := (e i).add ((hh.map (tint G) (norm_nonneg _) (fun x => (tint G).le_opNorm x)).smul_const_left (t⁻¹*g))
  simp_rw [abs_mul,abs_of_pos (inv_pos.mpr ht) (a:=t⁻¹)] at H
  have heq (h : Kernel G c I J ρ) W : tape (h.draw W) i = tint G (fun j => h.draw W (i,j)) := rfl
  simp only [stage, heq,stageCost,Pi.add_apply,Pi.smul_def,smul_add,smul_smul] at H ⊢; exact H

lemma Exposure.use {g t a b v w : ℝ} (ht : 0<t) (hB : 0≤a) (hB' : 0≤b) (hv : 0≤v) (hw : 0≤w)
    (he : ∀ i, Compare l (p.dirBound y) V ((t⁻¹:ℝ) • (h.mean · i)) ((t⁻¹:ℝ) • (h'.mean · i)) a b 1)
    (hx : ∀ i, Compare l (p.dirBound y) V (h.draw · i) (h'.draw · i) v w 1)
    (hW : ∀ i, ‖h.stage g V i‖ ≤ firstRadius G) (hE : ∀ i, ‖h'.stage g V i‖ ≤ firstRadius G) :
    Exposure S P h h' g t l (p.dirBound y) V (parentBound S P p y t) (stageCost G t g a v) (stageCost G t g b w) := by
  have hg := p.threshold_pos
  have ht' : 0 ≤ parentBound S P p y t := by unfold parentBound; positivity
  refine ⟨ht',(by unfold stageCost; positivity),(by unfold stageCost; positivity),?_,combined ht hv hw he hx,hW,hE⟩
  intro A ha i e
  exact (ha (S.ratio.parent e.1,e.2)).trans (by rw [parentBound, ← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]; exact Finset.single_le_sum (f:=fun i => p.threshold*(1+(separation (S.ratio.parent (P.address (.inl i)).1) y:ℝ))^p.power) (fun _ _ => by positivity) (Finset.mem_univ i))

structure Collected (R : Rep G f) (s w : Finset ℕ) (U : Config G f) (l : ℕ) (m : ℕ → ℝ) : Prop where
  contained : w ⊆ s
  healthy i (hi : i∈w) : Healthy R.p.threshold (R.activities.reg i).support U
  chart i (hi : i∈s) : Push.Local.Chart l (choice R w i) U
  budget i (hi : i∈s) z (hz : R.p.dirBound (R.activities.reg i).site z) :
    0 ≤ m i ∧ ∀ j ≤ l, ‖leftDerivs (choice R w i) (List.replicate j z) U‖ ≤ m i
  price i (hi : i∈s) : 0≤m i
variable {s w r o : Finset ℕ} {δ b : ℝ} {m n ℓ ε : ℕ → ℝ}
lemma Authored.collect (a : Authored R δ b m ℓ) {U : Config G f} (hw : w⊆s) (h : ∀ i∈w, Healthy R.p.threshold (R.activities.reg i).support U) (hl : l≤ R.p.order) :
    Collected R s w U l m := by
  have he i (hi : i∈w) := a.valid.regular.smooth i |>.smooth U (h i hi)
  refine ⟨hw,h,fun i hi => ?_,fun i hi z hz => ⟨(a.E i).1,?_⟩,fun i _ => (a.E i).1⟩
  · unfold choice; split
    next h => exact (he i h).of_le (by exact_mod_cast hl)
    exact contDiffAt_const
  unfold choice; split
  next hi => exact fun j hj => (a.E i).2 U (h i hi) _ (by simpa using hj.trans hl) fun z hz' => by rwa [(List.mem_replicate.mp hz').2]
  intro j _; change ‖leftDerivs (fun _ : Config G f => (0:ℝ)) _ U‖ ≤ _; simpa [Work.G07.left_const] using (a.E i).1
lemma Collected.transfer {U' : Config G c} (hu : Collected R s w (h.atLinks S P (coupling R.beta) U') l m) (hv : Collected R s r (h'.atLinks S P (coupling R.beta) U') l m)
    (hn : ∀ i∈s,0≤n i ∧ ∀ j ≤ l, ∀ z, R.p.dirBound (R.activities.reg i).site z →
      ‖leftDerivs (choice R w i) (List.replicate j z) (h.atLinks S P (coupling R.beta) U') - leftDerivs (choice R r i) (List.replicate j z) (h'.atLinks S P (coupling R.beta) U')‖ ≤ n i) : Transfer s w r R S P h h' l U' m n :=
  ⟨hu.contained,hv.contained,fun i hi => ⟨hu.price i hi,(hn i hi).1, hu.chart i hi,hv.chart i hi,
    fun j hj z hz => (hu.budget i hi z hz).2 j hj,fun j hj z hz => (hv.budget i hi z hz).2 j hj,(hn i hi).2⟩⟩

def Steady (S : StepData c f) (P : Location f I J) (h : Kernel G c I J ρ) (R : Rep G f) (o : Finset ℕ) (V : Config G c) :=
  ∀ i ∈ o, ∀ᶠ z in 𝓝 (0 : Directions G c), Agrees (inspected (R.activities.forced i).support)
    (h.atLinks S P (coupling R.beta) (increment V z)) (h.atLinks S P (coupling R.beta) V)
lemma Steady.fixed (a : Authored R δ b m ℓ) (hS : Steady S P h R o V) {i : ℕ} (hi : i∈o) : h.heavy S P R i ∘ increment V =ᶠ[𝓝 0] (fun _ => h.heavy S P R i V) :=
  (hS i hi).mono fun _ hz => (a.valid.forced.reads i).allReads _ _ _ _ _ hz
lemma Steady.freeze (a : Authored R δ b m ℓ) (hw : Steady S P h R o V) (he : Steady S P h' R o V) (hh : ∀ i ∈ o, ‖h.heavy S P R i V-h'.heavy S P R i V‖ ≤ ε i) : Freeze o R S P h h' V ℓ ε :=
  fun i hi => ⟨(a.K i).2 _, (a.K i).2 _,hh i hi, hw.fixed a hi,he.fixed a hi⟩
end Kernel

namespace Leaf
open Kernel
variable {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {A : Stores S} {F : Forest S.ratio} {h : Kernel G c I J ρ} {V : Config G c} {R : Rep G f}
    {L : Leaf G A x F I J ρ} {Y z k} {s o b : Finset ℕ} {m n ℓ ε : ℕ → ℝ} {δ w : ℝ}

structure Qualified (L : Leaf G A x F I J ρ) (R : Rep G f) (V : Config G c) (h : Kernel G c I J ρ) (l : ℕ) (η K : ℝ) (s w : Finset ℕ) (m : ℕ → ℝ) : Prop where
  ground : Ground h V η⁻¹
  margins : Margins h V η K
  enrollment (i : I) : ‖h.stage (coupling R.beta) V i‖ ≤ firstRadius G
  collects : Collected R s w (h.atLinks S L.location (coupling R.beta) V) l m

lemma qualifies (B : Board T q Z l x α d M C C' η K u v) (D : Allocation G S x α) (he : L.Binds T k R.beta q d Y z V h)
    (hA : A.flags = RG.flags (temp x) V) (auth : Authored R δ w m ℓ) (hR : Reads L R s o b) (hk : l≤R.p.order)
    (hw : ∀ i : I, ‖tape (axis T F A V k q d R.beta Y z) (L.hot i)‖ ≤ 2*d) :
    Qualified L R V h l η K s (lights s R (field T F A V k q d R.beta Y z)) m := by
  have h := kernelPrices.margins T F x k A V L B.branch (fun O W ht => ((B.ample W k O F D).2 ht).1) hA he
  refine ⟨h.ground V B.gap,h,fun i => ?_,?_⟩
  · rw [he.charts]; exact (hw i).trans B.lies.le
  refine Kernel.Authored.collect auth (Finset.filter_subset ..) (fun i hi => ?_) hk
  obtain ⟨hx,hQ⟩ := Finset.mem_filter.mp hi
  exact (he.health (hR.E _ hx) _).mpr hQ

variable {h' : Kernel G c I J ρ} {F' : Forest S.ratio} {A' : Stores S} {L' : Leaf G A' x F' I J ρ} {y : Site c} {p : BudgetPoint} {a ν B γ μ₁ μ₂ : ℝ}

lemma Qualified.certify {X X' : Finset ℕ}
    (B₀ : Board T q Z l x α d M C C' η K u v) (auth : Authored R δ w m ℓ)
    (hW : Qualified L R V h l η K s X m) (hE : Qualified L' R V h' l η K s X' m) (hl : L.location = L'.location)
    (hu : Steady S L.location h R o V) (hv : Steady S L'.location h' R o V)
    (hK : ∀ i∈o, ‖h.heavy S L.location R i V-h'.heavy S L'.location R i V‖ ≤ ε i)
    (hn : ∀ i∈s,0≤n i ∧ ∀ j ≤ l, ∀ z, R.p.dirBound (R.activities.reg i).site z →
      ‖leftDerivs (Kernel.choice R X i) (List.replicate j z) (h.atLinks S L.location (coupling R.beta) V) - leftDerivs (Kernel.choice R X' i) (List.replicate j z) (h'.atLinks S L'.location (coupling R.beta) V)‖ ≤ n i)
    (hM : Matrices h h' l (p.dirBound y) V a ν) (hμ : ∀ i, Compare l (p.dirBound y) V ((R.p.threshold⁻¹:ℝ) • (h.mean · i)) ((R.p.threshold⁻¹:ℝ) • (h'.mean · i)) μ₁ μ₂ 1)
    (h₁ : 0≤μ₁) (h₂ : 0≤μ₂) (hB : 0≤B) (hγ : 0≤γ) (hZ : ∀ i, Compare l (p.dirBound y) V (h.draw · i) (h'.draw · i) B γ 1) :
    let g := coupling R.beta; let t:=R.p.threshold
    Certified S L.location h h' R q Z d l (p.dirBound y) V s X X' o M C C' η⁻¹ a ν (parentBound S L.location p y t) (stageCost G t g μ₁ B) (stageCost G t g μ₂ γ) m n ℓ ε := by
  intro g t
  have he := hE.collects
  rw [← hl] at hv hn he
  rw [← hl] at hK
  refine ⟨B₀.polar,B₀.changes,B₀.guard,hW.ground,hE.ground,hM,
    Exposure.use R.p.threshold_pos h₁ h₂ hB hγ hμ hZ hW.enrollment hE.enrollment, hW.collects.transfer he hn, hu.freeze auth hv hK⟩
end Leaf
end YM.AnalyticBridge.MarginalMultiplier3b1d
