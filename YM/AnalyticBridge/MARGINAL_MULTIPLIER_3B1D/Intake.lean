import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Marginal

/-!
Positive-order sheet obligations. Need NOT supply zeroth jet prices to use
them here, nor prove global smoothness for hard sectors. Common thresholds
only, actual order/temperature/coupling (no assumption hats = beta). Include
evaluation of all ordered derivatives' size relative to the density price at
the same cloud. Not an estimate on the pending factor in `Sector.lean`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian SourceBounds Next.Foundations Push.Local Marginal Leaf Kernel
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ]
    {T : Tube G S} {R : Rep G f} {F : Forest S.ratio} {A : Stores S} {x α d : ℝ} {k : S.Choices} {q : Chi} {Z : ChartRatio G} {V : Config G c}
    {E η K u v M C C' B μ : ℝ} {l : ℕ} {p : BudgetPoint} {y : Site c} {D : Directions G c → Prop}

structure Higher {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (l : ℕ) (D : Directions G c → Prop) (V : Config G c) (f : Config G c → X) (C : ℝ) : Prop where
  smooth : Chart l f V
  pays (i : List (Directions G c)) : i.length ≤ l → i ≠ [] → (∀ a∈i, D a) → ‖leftDerivs f i V‖ ≤ C
lemma Higher.settle {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : Config G c → X} (h : Higher l D V f B)
    (hh : ‖f V‖ ≤ K) (he : 0≤B) : Compare l D V f f (K+B) 0 1 := Compare.same (by
  refine ⟨h.smooth,add_nonneg ((norm_nonneg _).trans hh) he,zero_le_one,fun i hi hD => ?_⟩
  rw [one_pow,mul_one]; rcases eq_or_ne i [] with rfl|hr
  · exact hh.trans (le_add_of_nonneg_right he)
  exact (h.pays i hi hr hD).trans (le_add_of_nonneg_left ((norm_nonneg _).trans hh)))

structure Incoming (h : Kernel G c I J ρ) (t : ℝ) (l : ℕ) (D : Directions G c → Prop) (V : Config G c) (B μ : ℝ) : Prop where
  price : 0≤B
  scale : 0≤μ
  cov i j : Higher l D V (fun W => h.cov W i j) B
  gram i j : Higher l D V (fun W => h.gram W i j) B
  signal i : Higher l D V (h.signal · i) B
  offset i : Higher l D V (h.offset · i) B
  draw i : Higher l D V (h.draw · i) B
  mean i : Higher l D V ((t⁻¹:ℝ) • (h.mean · i)) μ

variable {L : Leaf G A x F I J ρ} {h : Kernel G c I J ρ} {Y z}
lemma enters (B₀ : Board T q Z l x α d M C C' η K u v) (D' : Allocation G S x α)
    (he : L.Binds T k R.beta q d Y z V h) (ha : A.flags=RG.flags (temp x) V) (hp : Power T x R.beta k A V q d F E)
    (hw : ∀ i, ‖h.stage (coupling R.beta) V i‖ ≤ 2*d) (ht : R.p.threshold = fiery G x S.patch.L) (hh : Incoming h R.p.threshold l D V B μ) :
    let g := coupling R.beta; let t := R.p.threshold
    let μ' := ‖Kernel.tint G‖*E; let H := (K + E*YM.SectorNext.Remainder.Scales.p G S.patch.L x) + g⁻¹*(2*d+μ'*t)
    h.Matrices h l D V (H+B) 0 ∧ (∀ i, Compare l D V ((t⁻¹:ℝ) • (h.mean · i)) ((t⁻¹:ℝ) • (h.mean · i)) (μ'+μ) 0 1) ∧ 0≤μ'+μ := by
  intro g t μ' H
  have hi := kernelPrices.margins T F x k A V L B₀.branch (fun O W ht => ((B₀.ample W k O F D').2 ht).1) ha he
  have hK : 1 ≤ K := B₀.matrix
  have hE : 1 ≤ E := hp.paid
  have hg : 0 < g := coupling_pos hp.beta
  have hT : 0 < t := R.p.threshold_pos
  let p := YM.SectorNext.Remainder.Scales.p G S.patch.L x
  have hP : 0<p := YM.SectorNext.Remainder.Scales.pos ..
  have hμ : 0 ≤ μ' := by unfold μ'; positivity
  have hd := B₀.guard.pos
  let zFee := g⁻¹*(2*d+μ'*t); have hf : 0≤zFee := by unfold zFee; positivity
  have hk' : K ≤ H := by change K≤(K+E*p)+zFee; nlinarith
  have hm i : ‖h.mean V i‖ ≤ μ'*t := by
    rw [he.mean, show t=fiery G x S.patch.L from ht]
    let v := meanLog A F T x V k q d Y
    change ‖tint G (fun j => v (L.hot i,j))‖ ≤ _
    rw [show t=fiery G x S.patch.L from ht] at hT
    rw [show μ'=‖tint G‖*E by rfl, mul_assoc]
    exact ((tint G).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => hp.crm ..) (norm_nonneg _))
  have hz (i : I × G.ColorIndex) : ‖h.draw V i‖ ≤ H := by
    apply le_trans ?_ (show zFee ≤ H by change zFee ≤ K+E*p+zFee; nlinarith)
    let a := tape (h.draw V)
    have hi := norm_sub_le (h.stage g V i.1) (h.mean V i.1)
    rw [stage, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hg.le] at hi
    exact (PiLp.norm_apply_le (a i.1) i.2).trans ((le_inv_mul_iff₀ hg).mpr (hi.trans (add_le_add (hw _) (hm _))))
  have hB := hh.price
  refine ⟨⟨add_nonneg (zero_le_one.trans (hK.trans hk')) hB, le_rfl,
    fun i j => (hh.cov i j).settle ((sub_upper hi.C.cols ..).trans hk') hB, fun i j => (hh.gram i j).settle ((sub_upper hi.Q.cols ..).trans hk') hB,
    fun i j => Compare.same (Bound.const _ (((sub_upper hi.H.cols i j).trans hk').trans (le_add_of_nonneg_right hB)) zero_le_one), fun i => (hh.offset i).settle ?_ hB, fun i => (hh.draw i).settle (hz i) hB,fun i => (hh.signal i).settle ?_ hB⟩,
    fun i => (hh.mean i).settle ?_ hh.scale,add_nonneg hμ hh.scale⟩
  · rw [he.offset]; exact (hp.rows Y _).trans (show E*p ≤ H by change E*p ≤ K+E*p+zFee; linarith)
  · rw [he.signal]; exact (hp.fees ..).trans (hK.trans hk')
  rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hT).le,inv_mul_le_iff₀ hT,mul_comm]; exact hm i

-- Uniform cost for all jets through l IN ADDITION to the basic ticket.
def overhead (S : StepData c f) (P : Location f I J) (ρ : Type) [Fintype ρ] (p : BudgetPoint) (y : Site c) (R : Rep G f) (Z : ChartRatio G)
    (l : ℕ) (x d M C C' η K E B μ : ℝ) (s : Finset ℕ) (m : ℕ → ℝ) :=
    let g := coupling R.beta; let t:=R.p.threshold
    let u := ‖Kernel.tint G‖*E; let H := (K+E*YM.SectorNext.Remainder.Scales.p G S.patch.L x) + g⁻¹*(2*d+u*t)+B
    let a := stageCost G t g (u+μ) H
    compositionCost l (expenseCost G I J ρ l t (spare Z R.beta) d C C' M η⁻¹ H a (parentBound S P p y t) s m) * (door_growth I l a t d C'+1)^l
lemma overhead_nn {δ w : ℝ} {s : Finset ℕ} {m ℓ : ℕ → ℝ} (e : Authored R δ w m ℓ) (h : Board T q Z l x α d M C C' η K u v) (hE : 1 ≤ E) (hB : 0 ≤ B) (hμ : 0 ≤ μ) {P : Location f I J} :
    0 ≤ overhead S P ρ p y R Z l x d M C C' η K E B μ s m := by
  have he := zero_lt_one.trans_le hE; have hK := zero_lt_one.trans_le h.matrix; have hη := h.gap
  have ht := R.p.threshold_pos
  have hc := zero_lt_one.trans_le h.changes.one; have hc' := zero_lt_one.trans_le h.guard.paid; have hm := zero_lt_one.trans_le h.polar.1
  have hP := YM.SectorNext.Remainder.Scales.pos G S.patch.L x; have hd := h.guard.pos
  let H := (K+E*YM.SectorNext.Remainder.Scales.p G S.patch.L x) + (coupling R.beta)⁻¹*(2*d+‖Kernel.tint G‖*E*R.p.threshold)+B
  have hH : 0≤H := by unfold H coupling; positivity
  have h' (i : ℕ) := (e.E i).1; have hs := p.threshold_pos
  have hL₁ := (logCost_nn (Fintype.card (I × G.ColorIndex)) l hH (inv_nonneg.mpr hη.le)).1
  have hL₂ := (logCost_nn (Fintype.card ((I⊕J) × G.ColorIndex)) l hH (inv_nonneg.mpr hη.le)).1
  have hI := (stock_nn (Fintype.card (I × G.ColorIndex)) l hH (inv_nonneg.mpr hη.le)).1
  let a := stageCost G R.p.threshold (coupling R.beta) (‖tint G‖*E+μ) H
  have hA : 0≤a := by unfold a stageCost; positivity
  change 0 ≤ compositionCost _ (expenseCost _ _ _ _ _ _ _ _ _ _ _ _ H a _ _ _) * (door_growth I _ a .. +1)^l
  unfold expenseCost ledgerCost correctionCost
  dsimp only
  change 0 ≤ compositionCost _ (|_| + 2⁻¹*(_+_)+(2⁻¹*(_*(H*H)*2^l)+_+2⁻¹*((Fintype.card (I × G.ColorIndex):ℝ)*(_*(H*((stock (Fintype.card (I × G.ColorIndex)) H η⁻¹ l + H)*H)))*3^l))+_+_) * _
  unfold parentBound fieldCost pivotCost kinematic door_growth Kernel.aperture compositionCost
  have hg := G.colorScale_pos
  have hm := Finset.sum_nonneg (s:=s) fun i _ => h' i
  positivity

lemma self_certificate {s o b : Finset ℕ} {m ℓ : ℕ → ℝ} {δ w : ℝ} (B₀ : Board T q Z l x α d M C C' η K u v) (D' : Allocation G S x α)
    (he : L.Binds T k R.beta q d Y z V h) (ha : A.flags=RG.flags (temp x) V) (hp : Power T x R.beta k A V q d F E)
    (auth : Authored R δ w m ℓ) (hR : L.Reads R s o b) (hl : l ≤ R.p.order)
    (hw : ∀ i, ‖h.stage (coupling R.beta) V i‖ ≤ 2*d) (ht : R.p.threshold = fiery G x S.patch.L)
    (hf : Steady S L.location h R o V) (hh : Incoming h R.p.threshold l (p.dirBound y) V B μ) :
    let g := coupling R.beta; let t := R.p.threshold
    let u := ‖Kernel.tint G‖*E; let H := (K + E*YM.SectorNext.Remainder.Scales.p G S.patch.L x) + g⁻¹*(2*d+u*t)+B
    let U := Leaf.field T F A V k q d R.beta Y z; let r := Leaf.lights s R U
    Margins h V η K ∧ Certified S L.location h h R q Z d l (p.dirBound y) V s r r o M C C' η⁻¹ H 0 (parentBound S L.location p y t) (stageCost G t g (u+μ) H) 0 m 0 ℓ 0 := by
  intro g t u H U r
  have hq := Leaf.qualifies B₀ D' he ha auth hR hl (fun i => (he.charts i).symm ▸ hw i)
  obtain ⟨hM,hE,h'⟩ := enters B₀ D' he ha hp hw ht hh
  have hz : stageCost G t g 0 0=0 := by simp [stageCost]
  have h := hq.certify (n:=0) (ε:=0) B₀ auth hq rfl hf hf (by intros; simp) (fun _ _ => ⟨le_rfl,by intros; simp⟩) hM hE h' le_rfl hM.abs_nn le_rfl hM.draw
  dsimp only at h
  change Certified _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (stageCost G t g 0 0) _ _ _ _ at h
  rw [hz] at h; exact ⟨hq.margins,h⟩

lemma paid_jet {s o b : Finset ℕ} {m ℓ : ℕ → ℝ} {δ w : ℝ} (B₀ : Board T q Z l x α d M C C' η K u v) (D' : Allocation G S x α)
    (he : L.Binds T k R.beta q d Y z V h) (ha : A.flags=RG.flags (temp x) V) (hp : Power T x R.beta k A V q d F E)
    (auth : Authored R δ w m ℓ) (hR : L.Reads R s o b) (hl : l ≤ R.p.order)
    (ht : R.p.threshold = fiery G x S.patch.L) (hf : ContinuousAt (h.stage (coupling R.beta) ∘ increment V) 0)
    (hh : (∀ i, ‖h.stage (coupling R.beta) V i‖ ≤ 2*d) → Steady S L.location h R o V ∧ Incoming h R.p.threshold l (p.dirBound y) V B μ) (hB : 0≤B) (hμ : 0 ≤ μ) :
    let r := Leaf.lights s R (Leaf.field T F A V k q d R.beta Y z)
    let f := h.multiplier S L.location R q Z d r o
    let cost := ticket G I J K (spare Z R.beta) η s o m ℓ * overhead S L.location ρ p y R Z l x d M C C' η K E B μ s m
    Push.Local.Chart l f V ∧ ∀ i : List (Directions G c), i.length ≤ l → (∀ z∈i,p.dirBound y z) →
      ‖leftDerivs f i V‖ ≤ allowance ((fog A F T x V k).submatrix L.active L.active) (η/4) cost (project L.active z) := by
  intro r f cost
  have hOH := overhead_nn (ρ:=ρ) (s:=s) (p:=p) (y:=y) (P:=L.location) auth B₀ hp.paid hB hμ
  by_cases hw : ∀ i, ‖h.stage (coupling R.beta) V i‖ ≤ 2*d
  · obtain ⟨hP,hC⟩ := self_certificate B₀ D' he ha hp auth hR hl hw ht (hh hw).1 (hh hw).2
    have hU := (assembled hC _ le_rfl le_rfl).west
    refine ⟨hU.smooth,fun i hi hi' => ?_⟩
    let U := stageCost G R.p.threshold (coupling R.beta) (‖Kernel.tint G‖ * E+μ) ((K+ E*YM.SectorNext.Remainder.Scales.p G S.patch.L x)+(coupling R.beta)⁻¹ * (2*d+‖tint G‖*E*R.p.threshold)+B)
    have hg : 1 ≤ (door_growth I l U R.p.threshold d C'+1) := by
      apply le_add_of_nonneg_left; unfold door_growth Kernel.aperture compositionCost; have h := hC.fields.size; have := B₀.guard.pos; have hU : 0≤U := h; have := R.p.threshold_pos; have := B₀.guard.paid; positivity
    apply ((hU.pays i hi hi').trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg hi) hU.nn)).trans
    have hE := true_expense (P:=L.location) hP he hp (by
      refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (s:=r) (g:=m) (fun j hj => ?_)).trans (Finset.sum_le_sum_of_subset_of_nonneg hC.transfer.1 (fun j _ _ => (auth.E j).1))))
      obtain ⟨ha,hv⟩ := Finset.mem_filter.mp hj
      exact (auth.E j).2 _ ((he.health (hR.E j ha) _).mpr hv) [] (Nat.zero_le _) (by simp)) B₀.ratio B₀.matrix B₀.gap B₀.guard.pos B₀.room
    rw [he.cov, he.draw] at hE
    let E0 := overhead S L.location ρ p y R Z l x d M C C' η K E B μ s m
    let H := ∏ i∈o, ℓ i
    let EX := Real.exp (h.expense S L.location R q Z d r V)
    let Q := Real.exp (valuation G I J K (spare Z R.beta) η s m)
    change H*(_*EX)*_ ≤ _
    apply le_trans (le_of_eq (b:= (H*E0)*EX) (by unfold E0 overhead; ring)) ((mul_le_mul_of_nonneg_left hE (mul_nonneg (Finset.prod_nonneg fun j _ => (auth.K j).1) hOH)).trans_eq ?_)
    change H*E0*(allowance ((fog A F T x V k).submatrix L.active L.active) _ Q (project L.active z))= _
    unfold allowance cost ticket E0 Q H; ring
  push Not at hw
  obtain ⟨i,hi⟩ := hw
  have hF : Bound l (p.dirBound y) V f 0 0 := blank S L.location R q Z _ _ B₀.guard.pos ((continuous_apply i).continuousAt.comp hf) hi
  refine ⟨hF.smooth,fun i hi he => (hF.pays i hi he).trans ?_⟩
  rw [zero_mul]; have ht := Finset.prod_nonneg (s:=o) fun j _ => (auth.K j).1
  unfold allowance cost ticket; have h := shrink_pos (η/4) (project L.active z); positivity
end YM.AnalyticBridge.MarginalMultiplier3b1d
