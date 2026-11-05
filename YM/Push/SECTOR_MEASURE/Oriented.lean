import YM.Laurent.Turn
import YM.Next.FLUCTUATIONS.Grants
import YM.Push.SECTOR_MEASURE.Grant
import YM.Work.H03

/-!
# Extend intact sector payment to the cut crown's orientation average

Retain one Forest and one tag array; at a turned expression use
turned tags and a turned copy of the same tree. No resampling. Keep
Plot prerequisites *through a single global booking*, so the same
price applies to all contributions. Average energies, not densities
(, RG.PathData.inChannels's averaging convention).
Still before uncut tails, and not a gas estimate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f n : Side} {S : StepData c f} {P : Teller G} {T : Tube G S} {x W κ : ℝ}

/-- Point receipt needed for *simultaneous* expenditure on several
orientations. -/
def PointCharge (T : Tube G S) (x W κ : ℝ) : Prop :=
    ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Plot A U k V x W →
      κ*(fiery G x S.patch.L)^2*A.shares ≤ A.assessed T x U (S.prediction U k) V

theorem PointCharge.charged (h : PointCharge T x W κ) (he : P.Funds S T) : Charged T x W κ :=
  charged_at he fun A F V a k ha => h F A _ k V (fun i hi => F.on_tree a ⟨i,hi⟩) ha

theorem points_grant (P : Teller G) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ᶠ W : ℝ in atTop, 0 < W ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop, 0 < x ∧ 0 < fiery G x L ∧
        ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L = L →
          100*(1+radiusB x) ≤ c.val → P.Funds S T → PointCharge T x W κ := by
  obtain ⟨n,h⟩ := (Next.Fluctuations.grants P).precedes
  refine ⟨n,fun L hL => ?_⟩
  filter_upwards [h L hL,eventually_gt_atTop 0] with W hw hw'
  obtain ⟨κ,hκ,hp⟩ := hw
  refine ⟨hw',κ,hκ,?_⟩
  filter_upwards [hp.late,eventually_gt_atTop 0,(Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0)]
    with x hx hu ht
  refine ⟨hu,Work.E09.temp_pos ht,fun c f S T hs hR hT F A U k V hm he => ?_⟩
  rw [hs]
  exact hx c f S hs hR T hT F A U k V hm he

namespace Oriented

section turn

variable (s : Signed)

def choice (s : Signed) (k : S.Choices) := (S.withinChoice s 0).symm k

theorem carry (h : S.patch.Branches S.kernel G) (k : S.Choices) (U : Config G f) :
    S.likelihood (pull s 0 U) (choice s k) = S.likelihood U k ∧
      S.prediction (pull s 0 U) (choice s k) = pull s 0 (S.prediction U k) := by
  have hl : S.ratio.embed 0=0 := S.ratio.root.map_zero
  have he := S.mass_channel h s 0 U (choice s k)
  have hp := S.prediction_channel h s 0 U (choice s k)
  simp_rw [choice,hl,Equiv.apply_symm_apply] at he hp
  exact ⟨he,hp⟩

def faces (s : Signed) (n : Side) : Equiv.Perm (Cell n) := Equiv.ofBijective (Face.send s 0)
  ⟨Face.injective_send s 0, Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩

/-- Records needed by an expression in turned coordinates. -/
def turnStore (s : Signed) (A : Stores S) : Stores S where
  costs := A.costs.map (faces s f).symm.toEmbedding
  aisles := A.aisles.map (StepData.sendBonds s 0).symm.toEmbedding
  flags := A.flags.map (StepData.sendSites s 0).symm.toEmbedding

theorem same_price (A : Stores S) : (turnStore s A).shares = A.shares := by simp [turnStore, Stores.shares]

theorem wire_pulled (Q V : Config G n) (b : Bond n) :
    wire (pull s 0 Q) (pull s 0 V) b = wire Q V (sendEdge s 0 b) := by
  have ht (u v : G.El) : G.chord (u⁻¹*(v⁻¹)⁻¹) = G.chord (u*v⁻¹) := by
    rw [← G.chord_inv (u*v⁻¹), show (u*v⁻¹)⁻¹ = u*(u⁻¹*(v⁻¹)⁻¹)*u⁻¹ by group,G.chord_conj]
  unfold wire pull sendEdge Step.read
  split
  · exact ht ..
  rfl

lemma pull_seeded {A : Stores S} (hm : S.patch.Branches S.kernel G) {U : Config G f} {V : Config G c}
    {k : S.Choices} (h : Seeded A U k V x W) :
    Seeded (turnStore s A) (pull s 0 U) (choice s k) (pull s 0 V) x W := by
  constructor
  · intro p
    have hl : toll (pull s 0 U) p = toll U (faces s f p) :=
      Face.send_price U p s 0 G.chord G.chord_inv fun k g => G.chord_conj g k
    have he : p ∈ (turnStore s A).costs ↔ faces s f p ∈ A.costs := by
      simp [turnStore]
    rw [hl,he]; exact h.fine _
  · intro b; rw [(carry s hm k U).2,wire_pulled]
    have he : b ∈ (turnStore s A).aisles ↔ (StepData.sendBonds s 0 b) ∈ A.aisles := by
      dsimp only [turnStore]; simp
    rw [he]; exact h.coarse (sendEdge s 0 b)
  have hp := Work.H03.flags_send s (0:Site c) (temp x) V
  let e := StepData.sendSites s (0:Site c)
  have hh : ((RG.flags (temp x) (pull s 0 V)).map e.toEmbedding) = RG.flags (temp x) V := by
    rw [Finset.map_eq_image]; exact hp
  change A.flags.map e.symm.toEmbedding = _
  rw [h.exactFlags,← hh]; ext; simp

/-- Turn the (one, actual) tree g-coordinate.
No wrap ambiguity in parent action because block ratio odd. -/
private def rotatedStep (F : Forest S.ratio) (i : Site f) := (F.up (s.act i)).rotate s⁻¹

private theorem lands (F : Forest S.ratio) (i : Site f) :
    s.act (i+(rotatedStep s F i).vec) = s.act i + (F.up (s.act i)).vec := by
  rw [s.act_add,rotatedStep,Step.vec_rotate,Signed.act_inv]

private theorem in_leaf (i : Site f) (h : leaf S.ratio i) : leaf S.ratio (s.act i) := by
  unfold leaf at *
  intro he; apply h
  rw [S.ratio.parent_signed S.patch.odd_side, S.ratio.signed] at he
  exact s.act_injective he

def turnForest (F : Forest S.ratio) : Forest S.ratio where
  up := rotatedStep s F
  height i := F.height (s.act i)
  bound i := F.bound _
  rise i hi := by rw [lands]; exact F.rise _ (in_leaf s i hi)
  stays i hi := by
    apply s.act_injective
    rw [← S.ratio.parent_signed S.patch.odd_side, ← S.ratio.parent_signed S.patch.odd_side,lands]
    exact F.stays _ (in_leaf s i hi)

theorem turn_sliced (F : Forest S.ratio) (U : Config G f) (h : SliceSet S F U) :
    SliceSet S (turnForest s F) (pull s 0 U) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := ((turnForest s F).trunk_mem_iff _).1 hi
  let k := rotatedStep s F j
  have he : k.read (pull s 0 U) j = 1 := by
    have ht := h _ ((F.trunk_mem_iff _).mpr ⟨_,in_leaf s j hj,rfl⟩)
    rw [Step.pull_read]
    simp only [k, rotatedStep, Step.rotate_mul, mul_inv_cancel,Step.rotate_one,affine,add_zero,Step.read]
    simp [ht]
  unfold Step.read at he
  split at he
  · exact inv_eq_one.mp he
  exact he

end turn

def averaged (F : Signed → ℝ) := (Fintype.card Signed : ℝ)⁻¹ * ∑ s, F s

lemma av_add (F H : Signed → ℝ) : averaged (fun s => F s + H s) = averaged F + averaged H := by
  simp only [averaged, Finset.sum_add_distrib, mul_add]

lemma av_sub (F H : Signed → ℝ) : averaged (fun s => F s - H s) = averaged F - averaged H := by
  simp only [averaged, Finset.sum_sub_distrib, mul_sub]

lemma av_const (r : ℝ) : averaged (fun _ => r) = r := by
  have h : 0 < (Fintype.card Signed : ℝ) := by exact_mod_cast Fintype.card_pos
  simp [averaged,h.ne']

lemma av_mono {F H : Signed → ℝ} (h : ∀ s, F s ≤ H s) : averaged F ≤ averaged H := by
  unfold averaged; gcongr _ * ?_; exact Finset.sum_le_sum fun i _ => h i

def wholeGap (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) : ℝ :=
  averaged fun s => crownGap T x (pull s 0 U) (pull s 0 V)

def meanEnergy (A : Stores S) (T : Tube G S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
  averaged fun s =>
    (turnStore s A).assessed T x (pull s 0 U) (S.prediction (pull s 0 U) (choice s k)) (pull s 0 V)

def meanRest (A : Stores S) (T : Tube G S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
  averaged fun s => unassigned (turnStore s A) T x (pull s 0 U) (choice s k) (pull s 0 V)

/-- Cut crown, average Gap. Don't replicate the likelihood or noise,
and don't demand that all predictors use the minimizing branch. -/
def enters (T : Tube G S) (β x : ℝ) (k : S.Choices) (V : Config G c) (U : Config G f) :=
  taggedKernel S β k U V * Real.exp (-β * wholeGap T x U V)

def leaves (A : Stores S) (T : Tube G S) (β x : ℝ) (k : S.Choices) (V : Config G c) (U : Config G f) :=
  S.likelihood U k * Real.exp (-β * meanRest A T x U k V)

lemma enters_eq (hm : S.patch.Branches S.kernel G) (A : Stores S) (β x : ℝ) (k : S.Choices)
    (V : Config G c) (U : Config G f) :
    enters T β x k V U = prefactor S G β * Real.exp (-β * meanEnergy A T x U k V) * leaves A T β x k V U := by
  let Q := S.prediction U k
  let m := ∑ i, Tube.monetary S Q V i
  have he : S.noise β Q V = prefactor S G β * Real.exp (-β*m) := by
    unfold StepData.noise m prefactor
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.mul_sum, Real.exp_sum]; congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold StepData.penaltyWeight Tube.monetary wire; rw [G.chord_price]; ring_nf
  have hg : meanEnergy A T x U k V + meanRest A T x U k V = m + wholeGap T x U V := by
    unfold meanEnergy meanRest wholeGap
    rw [← av_const m, ← av_add, ← av_add]
    apply congr_arg averaged
    funext s
    dsimp only [crownGap,unassigned]; rw [T.locates]
    have hu : (∑ i, Tube.monetary S (S.prediction (pull s 0 U) (choice s k)) (pull s 0 V) i) = m := by
      rw [(carry s hm k U).2]; unfold Tube.monetary; simp_rw [wire_pulled]
      exact Equiv.sum_comp (StepData.sendBonds s 0) fun i => Tube.monetary S Q V i
    rw [hu]; abel
  unfold enters leaves taggedKernel; rw [he]
  calc
    _ = prefactor S G β * S.likelihood U k * Real.exp (-β*(m+wholeGap T x U V)) := by rw [mul_add,Real.exp_add]; ring
    _ = _ := by rw [← hg,mul_add,Real.exp_add]; ring

lemma mean_pays (F : Forest S.ratio) (A : Stores S) (x W : ℝ) (U : Config G f) (k : S.Choices)
    (V : Config G c) (hm : S.patch.Branches S.kernel G) (hU : SliceSet S F U)
    (hx : Seeded A U k V x W) (he : Alive S U k) (h : PointCharge T x W κ) :
    κ*(fiery G x S.patch.L)^2*A.shares ≤ meanEnergy A T x U k V := by
  rw [← av_const (κ*(fiery G x S.patch.L)^2*A.shares)]
  apply av_mono; intro s
  have hl : Alive S (pull s 0 U) (choice s k) := by simpa only [Alive,(carry s hm k U).1] using he
  have hh := h (turnForest s F) (turnStore s A) (pull s 0 U) (choice s k) (pull s 0 V)
    (turn_sliced s F U hU) ((pull_seeded s hm hx).plot hl)
  rw [same_price s A] at hh; exact hh

section envelopes
variable {α : Type*} [MeasurableSpace α] {U : α → Config G f} {V : α → Config G c}

lemma env_mean {F : Signed → α → ℝ} (h : ∀ i, Envelope (F i)) :
    Envelope (fun a => averaged fun s => F s a) := (Envelope.const _).mul (Envelope.sum _ F h)

lemma pulling_meas {n : Side} (s : Signed) {U : α → Config G n} (h : Measurable U) :
    Measurable (fun a => pull s 0 (U a)) := (continuous_pull ..).measurable.comp h

lemma env_enters (hT : P.Funds S T) (β x : ℝ) (k : S.Choices) (h : Measurable U) (l : Measurable V) :
    Envelope (fun a => enters T β x k (V a) (U a)) := by
  have hm : Envelope (fun a => wholeGap T x (U a) (V a)) := env_mean
    (F:=fun s a => crownGap T x (pull s 0 (U a)) (pull s 0 (V a)))
    fun s => env_gap hT x (pulling_meas s h) (pulling_meas s l)
  exact (env_tagged β k (funds_branch hT) h l).mul (((Envelope.const _).mul hm).exp)

lemma env_leaves (hT : P.Funds S T) (A : Stores S) (β x : ℝ) (k : S.Choices)
    (h : Measurable U) (l : Measurable V) :
    Envelope (fun a => leaves A T β x k (V a) (U a)) := by
  have hm : Envelope (fun a => meanRest A T x (U a) k (V a)) := env_mean
    (F:=fun s a => unassigned (turnStore s A) T x (pull s 0 (U a)) (choice s k) (pull s 0 (V a)))
    fun s => env_unassigned hT x _ (pulling_meas s h) (pulling_meas s l) _
  exact (env_likelihood k (funds_branch hT) h).mul (((Envelope.const _).mul hm).exp)
end envelopes

section sums
variable (D : Allocation G S x W) (F : Forest S.ratio) (β : ℝ) (V : Config G c)
  (g : S.Choices → F.Slice G → ℝ) (A : Stores S)

lemma turn_parts (hT : P.Funds S T) (hg : ∀ k, Integrable (g k) (F.order G)) :
    let L := fun k a => g k a * enters T β x k V (F.drape a)
    let R := fun A k a => g k a * leaves A T β x k V (F.drape a)
    (∀ k, Integrable (L k) (F.order G) ∧ ∀ A : Stores S, Integrable (R A k) (F.order G)) ∧
      (∑ A : Stores S, D.column A F V L) = tagTotal F L := by
  intro L R
  have h k : Integrable (L k) (F.order G) ∧ ∀ A : Stores S, Integrable (R A k) (F.order G) := by
    constructor
    · simpa only [L,mul_comm,smul_eq_mul] using Env.smul_L1
        (env_enters hT β x k F.continuous_drape.measurable (V:=fun _ => V) measurable_const) (hg k)
    intro A
    simpa only [R,mul_comm,smul_eq_mul] using Env.smul_L1
      (env_leaves hT A β x k F.continuous_drape.measurable (V:=fun _ => V) measurable_const) (hg k)
  exact ⟨h,D.partitions (funds_branch hT) _ _ _ (fun k => (h k).1)⟩

/-- Payment for every sector with the orientation-averaged cut rows,
not asserting anything yet for full/uncut or reweighting costs. -/
lemma turn_charge (hT : P.Funds S T) (h : PointCharge T x W κ) (hβ : 0 ≤ β)
    (hg : ∀ k, Integrable (g k) (F.order G)) (hz : ∀ k a, 0 ≤ g k a) :
    D.column A F V (fun k a => g k a * enters T β x k V (F.drape a)) ≤ earn S G x κ β A.shares *
      D.column A F V (fun k a => g k a * leaves A T β x k V (F.drape a)) := by
  let hb := funds_branch hT
  let m := earn S G x κ β A.shares
  let L := fun k a => g k a * enters T β x k V (F.drape a)
  let R := fun k a => g k a * leaves A T β x k V (F.drape a)
  change (∑ k, ∫ a, D.portion A F V L k a ∂F.order G) ≤ m * ∑ k, ∫ a, D.portion A F V R k a ∂F.order G
  rw [Finset.mul_sum]; apply Finset.sum_le_sum
  intro k _
  obtain ⟨h1,h2⟩ := (turn_parts D F β V g hT hg).1 k
  rw [← integral_const_mul]
  apply integral_mono (D.portion_integrable hb A F V L k h1)
    ((D.portion_integrable hb A F V R k (h2 A)).const_mul _)
  intro a
  let U := F.drape a
  change D.bill A k U V * (g k a * enters T β x k V U) ≤ m * (D.bill A k U V * (g k a * leaves A T β x k V U))
  by_cases ht : Alive S U k
  swap
  · simp [enters,taggedKernel,dead ht,leaves]
  by_cases he : D.bill A k U V = 0
  · simp [he]
  have hl := mean_pays F A x W U k V hb (fun i hi => F.on_tree a ⟨i,hi⟩) (D.actual _ _ _ _ he) ht h
  rw [enters_eq hb A]
  have hy : prefactor S G β * Real.exp (-β * meanEnergy A T x U k V) ≤ m := by
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left hl (neg_nonpos.mpr hβ))) (prefactor_pos β).le
  simp_rw [mul_left_comm m]
  have hu : 0 ≤ leaves A T β x k V U := mul_nonneg (S.likelihood_pos ..) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy hu) (hz k a))
    (D.nonneg ..)

end sums
end Oriented
end YM.Push.SectorMeasure
