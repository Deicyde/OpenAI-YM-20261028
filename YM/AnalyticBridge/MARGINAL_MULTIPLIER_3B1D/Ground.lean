import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Sector
import YM.Next.FOUNDATIONS.Readout
import YM.Work.B13

/-!
Joint post-L zeroth matrix estimates for the *literal* choices. No source,
mean or derivative prices used to prove these. Includes local full-submatrix
gaps and determinant column budgets without a card-dependent bound per column.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Precision Tree Matrix
  Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

section generic
variable {ι τ σ : Type} [Fintype ι] [Fintype τ] [DecidableEq ι] {η K : ℝ}
variable {A : Gaussian.Table ι} {p : ι → Site c}
lemma local_gap (h : Gapped A η) (e : τ ↪ ι) : Gapped (A.submatrix e e) η := by
  let L := Equiv.ofInjective _ e.injective
  intro x
  have hh := held_gap h (Set.range e) (x ∘ L.symm)
  have he [Fintype (Set.range e)] (F : Set.range e → ℝ) : (∑ i, F i) = ∑ i : τ, F (L i) := (L.sum_comp F).symm
  unfold Schur.principal sumSq at hh; unfold dotProduct mulVec at hh; simp_rw [dotProduct, he, Function.comp_apply,L.symm_apply_apply] at hh
  exact hh
lemma local_column (h : Pours A p p 0 K) (e : τ ↪ ι) : flared K (A.submatrix e e) := by
  intro i
  have he : ∀ j, Wisps.rate 0 (separation (p j) (p (e i))) = 1 := by simp [rate]
  apply le_trans ?_ (h.col (e i))
  simp_rw [he,one_mul,Matrix.submatrix_apply]
  rw [← Finset.sum_map _ e (fun x => |A x (e i)|)]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => abs_nonneg _
lemma sub_upper (h : flared K A) : Upper A K := fun i j => (Finset.single_le_sum (f:=(|A · j|)) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans (h j)
lemma gap_price (hA : A.PosDef) (hη : 0<η) (hg : Gapped A η) : Upper A⁻¹ η⁻¹ := by
  intro i j
  let v := A⁻¹ *ᵥ (Pi.single (M:=fun _ => ℝ) j 1)
  have he := hg v
  have hx : A *ᵥ v=Pi.single (M:=fun _ => ℝ) j 1 := by
    unfold v; rw [mulVec_mulVec,A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),one_mulVec]
  rw [hx,dotProduct_single_one] at he
  have hu (k : ι) := (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun i => (v i)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)) hη.le).trans he
  have hj : v j ≤ η⁻¹ := by
    rw [← one_div, le_div_iff₀ hη]
    by_contra! h; nlinarith [hu j]
  change |A⁻¹ i j| ≤ _; rw [show A⁻¹ i j=v i by simp [v,Matrix.col]]
  by_contra! hr
  have hη' := inv_pos.mpr hη
  have ht := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hr hη'.le (by decide : (2:ℕ)≠0)) hη
  rw [sq_abs,sq η⁻¹,← mul_assoc, mul_inv_cancel₀ hη.ne',one_mul] at ht; linarith [hu i]

-- joint per-window comparison, column ordering matters for the sector mean.
lemma per_approx {v C : ℝ} (hv : 0<v) (hA : A.PosDef) (hgap : Gapped A η) (hη : 0<η)
    (ha : Pours A p p v K) {W : ι → Set ι} (h : Pours (per W A) p p v C) (hi : Pours A⁻¹ p p 0 C)
    {r : ℕ} (hw : Bars W p r) : Pours (per W A-A⁻¹) p p 0 ((C*(K*C+1))*rate (-v) r) := by
  let L := per W A
  let E := A*L-1
  have hs := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have H : Pours (-1 : Gaussian.Table ι) p p v 1 := by
    constructor
    · norm_num
    all_goals intro i; simp [Matrix.one_apply,apply_ite abs,mul_ite,rate]
  have he : Pours E p p v (K*C+1) := by unfold E; rw [sub_eq_add_neg]; exact (ha.fuse h hv.le).bind H
  have ht (i j : ι) : rate 0 (separation (p i) (p j)) * |E i j| ≤ rate (-v) r * (rate v (separation (p i) (p j))*|E i j|) := by
    by_cases hu : separation (p j) (p i) ≤ r
    · rw [show E i j=0 by change (A*L) i j-(1:Gaussian.Table ι) i j=0; rw [show (A*L) i j = _ from per_check hw hs hgap hη j (hw _ _ hu),sub_self],abs_zero,mul_zero,mul_zero,mul_zero]
    unfold rate; rw [← mul_assoc,← Real.exp_add]; gcongr; rw [separation_comm]; have hr := Nat.cast_le (α:=ℝ).mpr (lt_of_not_ge hu).le; nlinarith
  have hc : Pours E p p 0 (rate (-v) r*(K*C+1)) := by
    refine ⟨mul_nonneg (rate_pos ..).le he.pos,fun i => ?_,fun j => ?_⟩
    · exact (Finset.sum_le_sum (fun j _ => ht i j)).trans ((Finset.mul_sum ..).symm.trans_le (mul_le_mul_of_nonneg_left (he.row i) (rate_pos ..).le))
    exact (Finset.sum_le_sum (fun i _ => ht i j)).trans ((Finset.mul_sum ..).symm.trans_le (mul_le_mul_of_nonneg_left (he.col j) (rate_pos ..).le))
  have hx : L-A⁻¹=A⁻¹*E := by unfold E; rw [Matrix.mul_sub,← Matrix.mul_assoc, A.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),Matrix.one_mul, Matrix.mul_one]
  change Pours (L-A⁻¹) _ _ _ _; rw [hx]; exact (hi.fuse hc (by rfl)).weaker le_rfl (le_of_eq (by ring))

structure BlockPrices (A : Gaussian.Table ι) (η K : ℝ) : Prop where
  solvent : A.PosDef
  gap : Gapped A η
  cols : flared K A
lemma block_prices [DecidableEq τ] (hA : A.PosDef) (h : Gapped A η) (hl : Pours A p p 0 K) (e : τ ↪ ι) : BlockPrices (A.submatrix e e) η K :=
  ⟨hA.submatrix e.injective,local_gap h e,local_column hl e⟩
lemma weaker_gap (h : Gapped A K) (he : η ≤ K) : Gapped A η := fun x => (mul_le_mul_of_nonneg_right he (sumSq_nn x)).trans (h x)
end generic

section actual
variable (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) (A : Stores S) (V : Config G c)
private def frontFee (G : Gauge) (P : Patch) (σ : ℝ) := ((Fintype.card G.ColorIndex : ℝ) * (Fintype.card (Site P.L) * Fintype.card Axis)) * wealth σ
private lemma frontFee_eq (σ : ℝ) {P : Patch} (S : StepData c f) (G : Gauge) (h : S.patch=P) : keyFee S G σ = frontFee G P σ := by subst P; rfl
private lemma fees (P : Patch) (G : Gauge) (v : ℝ) : 0 ≤ frontFee G P v := by unfold frontFee; have h := wealth_nn v; positivity

def credit (W : Rows.In x A F (G:=G) → Set (Rows.In x A F (G:=G))) (η K u v : ℝ) : Prop := let Q := Rows.gram T x V k (shots S x) A F; let C := clouded W Q
  let p := front (x:=x) A F (G:=G)
  Pours Q p p 0 K ∧ Pours C p p 0 K ∧ Pours (per W Q) p p 0 K ∧
    Q.PosDef ∧ C.PosDef ∧ Gapped Q η ∧ Gapped C η ∧
    Pours (per W Q-Q⁻¹) p p 0 (u*rate (-v) (radiusB x/60))

def kernelPrices (η K u v : ℝ) : Prop := credit T F x k A V (panels A F) η K u v

lemma credit_post (Pt : Teller G) (P : Patch) (hp : P.Branches Pt.bind G) : ∃ η K u v : ℝ, 0<η ∧ 1 ≤ K ∧ 0<u ∧ 0<v ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags = RG.flags (temp x) V → ∀ W, Bars W (front A F) (radiusB x/60) → credit T F x k A V W η K u v := by
  obtain ⟨σ,M,η,b,E,hσ,hM,hη,hb,hE,H⟩ := opaqueCost G P Pt hp
  let B := frontFee G P
  obtain ⟨u,U,η',hu,hU,hη',hw⟩ := Schur.windows hσ hη hM B (fees P G)
  obtain ⟨w,C,hW,h'w,hC,hg⟩ := provides hσ hη hM
  let v := w/2; have hv : 0<v := half_pos hW
  let m := B v * C; let K := 1 + M+m
  have hm : 0 ≤ m := mul_nonneg (fees P G v) hC.le
  let Δ := m*(M*m+1)+1
  have hd : 0 < Δ := by unfold Δ; positivity
  have ht : Tendsto (fun x : ℝ => radiusB x/60) atTop atTop := Filter.tendsto_atTop.mpr (fun i => (Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)).mono fun x hx => by omega)
  refine ⟨min η η',K,Δ,v,lt_min hη hη',(by unfold K; linarith),hd,hv,?_⟩
  filter_upwards [ht.eventually hw,H] with x hx hh
  intro c f S T hP hc hT A F k V hV W he
  let Q := Rows.gram T x V k (shots S x) A F
  let p := front A F (G:=G) (x:=x)
  obtain ⟨hp,hq,hA,-,-⟩ := hh S T hP hc hT A F k V hV
  have hQ := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hB : Revenue p B := fun v hv i => (front_price v hv A F G i (x:=x)).trans_eq (frontFee_eq v S G hP)
  obtain ⟨-,hG,hI⟩ := hx p Q W hB hp hQ hq he
  have H j i := hg p W Q hp hQ hq i j
  have hL := Revenue.per _ hB hW hC.le (fun i j => (H i j).1)
  have hI' := Revenue.per _ hB hW hC.le (fun i j => (H i j).2)
  have hc := (hL.bind hL.turn).scale (1/2)
  have hδ := per_approx hv hA hq hη (hp.weaker ((half_le_self hW.le).trans h'w) le_rfl) hL (hI'.weaker hv.le le_rfl) he
  have he' : m ≤ K := by unfold K; linarith
  refine ⟨hp.weaker hσ.le (by unfold K; linarith),hc.weaker hv.le ?_, hL.weaker hv.le he',hA,hI,weaker_gap hq (min_le_left ..),weaker_gap hG (min_le_right ..),hδ.weaker le_rfl ?_⟩
  · change |(1/2:ℝ)| * (m+m) ≤ K; rw [abs_of_nonneg (by norm_num)]; linarith
  apply mul_le_mul_of_nonneg_right ?_ (rate_pos ..).le; unfold Δ m v; linarith

lemma kernel_post (Pt : Teller G) (P : Patch) (hp : P.Branches Pt.bind G) : ∃ η K u v : ℝ, 0<η ∧ 1 ≤ K ∧ 0<u ∧ 0<v ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags = RG.flags (temp x) V → kernelPrices T F x k A V η K u v := by
  obtain ⟨η,K,u,v,hη,hK,hu,hv,H⟩ := credit_post Pt P hp
  refine ⟨η,K,u,v,hη,hK,hu,hv,?_⟩
  filter_upwards [H,Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hx hr
  exact fun S T hs hN hT A F k V hV => hx S T hs hN hT A F k V hV (panels A F) (boards A F G hr)

structure Margins {I J ρ : Type} [Fintype I] [Fintype J] (h : Kernel G c I J ρ) (V : Config G c) (η K : ℝ) : Prop where
  Q : BlockPrices (h.gram V) η K
  C : BlockPrices (h.cov V) η K
  H : BlockPrices h.flat η K
lemma Margins.ground {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {h : Kernel G c I J ρ} {η K : ℝ} (he : Margins h V η K) (hη : 0<η) : Kernel.Ground h V η⁻¹ :=
  ⟨he.C.solvent,he.Q.solvent,he.H.solvent,inv_nonneg.mpr hη.le, gap_price he.C.solvent hη he.C.gap, gap_price he.H.solvent hη he.H.gap⟩

lemma kernelPrices.margins {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {h : Kernel G c I J ρ} (L : Leaf G A x F I J ρ)
    {q Y z} {d η K u v β : ℝ} (hp : S.patch.Branches S.kernel G) (hi : ∀ (O : Stores S) (V' : Config G c), O.flags = RG.flags (temp x) V' → kernelPrices T F x k O V' η K u v)
    (hw : A.flags = RG.flags (temp x) V) (hh : L.Binds T k β q d Y z V h) : Margins h V η K := by
  let O : Stores S := ⟨∅,∅,∅⟩
  have he₀ : O.flags = RG.flags (temp x) (1 : Config G c) := by
    ext s; have h := Next.Foundations.one_healthy (G:=G) (Finset.univ : Support c) (temp x) (temp_nonneg x)
    have := Finset.disjoint_left.mp h (Finset.mem_univ s); simpa [O] using this
  obtain ⟨hQ,hC,-,ha,hb,hv,hg,-⟩ := hi A V hw
  obtain ⟨hϕ,-,-,ht,-,hm,-⟩ := hi O 1 he₀
  constructor
  · rw [hh.gram]; exact block_prices ha hv hQ L.active
  · rw [hh.cov]; exact block_prices hb hg hC L.active
  rw [hh.flat]; unfold Leaf.paper; dsimp only; rw [← Native.ground_gram T F k x hp, Matrix.submatrix_submatrix]
  exact block_prices ht hm hϕ (L.free.trans (Native.lineEquiv F x (S:=S)).toEmbedding)
end actual
end YM.AnalyticBridge.MarginalMultiplier3b1d
