import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Background
import YM.Next.SCHEDULE.Pitfalls
import YM.Work.B18

/-!
First tilted-row price on active *and frozen* displacements and hence F₀
zeroth cost. Does not require differentiability of the frozen links wrt V
(this is a separate purchase for jets). Post-L across all the common data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.SourceBounds
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Precision Tree Matrix
  Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier Next.SectorChange.LocalJet
  Next.SectorChange.Motion Next.SectorChange.Rows
  Next.Fluctuations Bid FiniteMatrix Gaussian
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
  {T : Tube G S} {A : Stores S} {F : Forest S.ratio} {s : Signed} {V : Config G c} {x : ℝ}

lemma small (P : Patch) {δ : ℝ} (hδ : 0<δ) (G : Gauge) : ∀ᶠ x : ℝ in atTop, permit P*temp x≤δ := by
  filter_upwards [Work.E01.fiery_le G (1:Side) (permit P), (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
  simpa [fiery,betaF] using hx.trans he

def stakes (P : Patch) (r : ℕ) := (Fintype.card (Site P.L):ℝ) * (grain r * Fintype.card Axis)
lemma stakes_nn (P : Patch) (r : ℕ) : 0≤stakes P r := by unfold stakes grain; positivity
lemma settle_price (S : StepData c f) (y : Site c) (r : ℕ) (a : Directions G f) (B : ℝ) (he : ∀ i, ‖a i‖ ≤ B) (hb : 0≤B) : settle S y r a ≤ stakes S.patch r*B := calc
  _ ≤ ∑ _∈members S y r,B := Finset.sum_le_sum fun i _ => he i
  _ = (members S y r).card * B := by simp
  _ ≤ stakes S.patch r*B := mul_le_mul_of_nonneg_right (saves S y r) hb

lemma barrel_bound (P : PathData G) (r : ℕ) (U : Config G f) (b : LogArray G (Cell f)) (p : Cell f) {o σ C Λ B} (h : P.Bounds o σ C Λ)
    (hb : ∀ i, ‖b i‖ ≤ B) (he : 0≤B) : ‖barrel P r U b p‖ ≤ C * B := by
  obtain ⟨hz,hs,hc⟩ := h.rows p.2
  have ha := (hs.mul_right B)
  apply (norm_tsum_le_tsum_norm (barrel_summed P r U b p h).norm).trans ((Summable.tsum_le_tsum _ (barrel_summed P r U b p h).norm ha).trans (tsum_mul_right.trans_le (mul_le_mul_of_nonneg_right hc he)))
  intro i; dsimp only; split
  · rw [ norm_smul, Real.norm_eq_abs, G.norm_adjoint]
    refine mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by have := h.width; positivity))) (hb _) (norm_nonneg _) (hz i)
  · rw [norm_zero]; exact mul_nonneg (hz _) he

lemma bump_post (Pt : Teller G) (P : Patch) (hp : P.Branches Pt.bind G) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags = RG.flags (temp x) V →
    ∀ i, Rows.keep x (shots S x) A F i → ∀ a : Directions G f, ∀ b : ℝ, 0≤b → (∀ i, ‖a i‖≤b) → ‖Rows.bump T x V k a i‖ ≤ C*b := by
  obtain ⟨B,δ,hB,hδ,H⟩ := earned P Pt.bind G hp
  obtain ⟨C,hC,h₁⟩ := face_global G
  let n := Real.sqrt Pt.bind.penalty * (B*stakes P (predReach P))
  let j := C * stakes P 1
  let m := (max Pt.top.paths (Real.sqrt Pt.top.clip.direct))*j
  have hn : 0 ≤ n := by unfold n; have := stakes_nn P (predReach P); positivity
  have ht : 0≤j := mul_nonneg hC.le (stakes_nn P 1)
  have hm : 0≤m := mul_nonneg ((Real.sqrt_nonneg _).trans (le_max_right ..)) ht
  let D := 1+m+n
  have hD : 0<D := by unfold D; linarith
  refine ⟨D,hD,?_⟩
  filter_upwards [small P hδ G,small_span P,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+1)] with x hx hs hv
  intro c f S T ht' hN hT A F V k hA i hi a b hb ha
  have h := H S ht' hT.knobs F A V x hA hs (by omega) (by omega) hx
  obtain ⟨s,i|i⟩ := i
  let u := inChannel s (replica S.ratio V) a
  have hu i : ‖u i‖ ≤ b := (in_size ..).trans_le (ha _)
  · apply le_trans ?_ (mul_le_mul_of_nonneg_right (show m≤D by unfold D; linarith) hb)
    change ‖faceKick T x V a s i‖ ≤ m*b
    unfold faceKick; rw [hT.high]
    have hφ (i : Cell f) : ‖plaquetteJet S V s i a‖ ≤ j*b := by
      unfold plaquetteJet; rw [(plaquette_turn s V i (face_smooth _ _).contDiffAt).2]; apply (h₁ S i _ u).trans
      rw [show j*b=C*(stakes S.patch 1*b) by unfold j; rw [ht',mul_assoc]]; exact mul_le_mul_of_nonneg_left (settle_price S _ 1 u b hu hb) hC.le
    split
    · obtain ⟨l,u,h₁,h₂⟩:= hT.feeds
      exact (barrel_bound _ _ _ _ _ h₁ hφ (mul_nonneg ht hb)).trans ((mul_le_mul_of_nonneg_right (le_max_left ..) (mul_nonneg ht hb)).trans_eq (mul_assoc ..).symm)
    unfold m; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc]; exact mul_le_mul (le_max_right ..) (hφ _) (norm_nonneg _) ((Real.sqrt_nonneg _).trans (le_max_right ..))
  let u := inChannel s (replica S.ratio V) a
  have hu i : ‖u i‖ ≤ b := (in_size ..).trans_le (ha _)
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (show n≤D by unfold D; linarith) hb)
  obtain ⟨-,h₂,h₃⟩ := h.noise s k i hi
  change ‖-(Real.sqrt S.kernel.penalty • fderiv ℝ _ _ _)‖ ≤ _
  unfold n; rw [norm_neg, norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _), (block_turn s V i k h₂).2,hT.knobs,mul_assoc, mul_assoc, ← ht']
  exact mul_le_mul_of_nonneg_left ((h₃ _).trans (mul_le_mul_of_nonneg_left (settle_price S _ _ u b hu hb) hB.le)) (Real.sqrt_nonneg _)

lemma source_bound (Pt : Teller G) (P : Patch) (hp : P.Branches Pt.bind G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags = RG.flags (temp x) V →
    ∀ d, 0<d → d ≤ r * fiery G x P.L → ∀ q Y i, |Rows.source T x V k (shots S x) A F q d Y i| ≤ C*fiery G x P.L := by
  obtain ⟨B,hB,h⟩ := bump_post Pt P hp
  obtain ⟨C,hC,hQ⟩ := Background.base_post Pt P hp
  refine ⟨slip*(C+B*(2*r)),mul_pos slip_pos (by positivity),?_⟩
  filter_upwards [h,hQ] with x hx he
  intro c f S T hs hl ht A F V k hV d hd hδ q Y i
  have ha (e : Bond f) : ‖Rows.input x A F (autoShell q d V Y) e‖ ≤ 2*r*fiery G x P.L := by
    unfold Rows.input; apply le_trans ?_ (show 2*d ≤ 2*r*fiery G x P.L by linarith)
    split
    · split
      · exact patched_small q hd _
      · rw [norm_zero]; linarith
    · rw [norm_zero]; linarith
  have hf : 0≤fiery G x P.L := temp_nonneg _
  unfold Rows.source
  apply le_trans (b:=‖Rows.restrict x (shots S x) A F (Rows.base T x V k + _) i.1‖) (PiLp.norm_apply_le _ i.2)
  unfold Rows.restrict; split
  next hh =>
    rw [Pi.add_apply,norm_smul,Real.norm_of_nonneg slip_pos.le,mul_assoc,add_mul,mul_assoc B]; exact mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add (he S T hs hl ht A F V k hV _ hh)
      (hx S T hs hl ht A F V k hV _ hh _ _ (by positivity) ha))) slip_pos.le
  next _ => rw [norm_zero]; have := slip_pos; positivity

lemma move_bound (Pt : Teller G) (P : Patch) (hp : P.Branches Pt.bind G) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags = RG.flags (temp x) V →
      Pours (Rows.move T x V k (shots S x) A F) (down S) (front A F) (Pt.top.width/2) C := by
  obtain ⟨C,δ,hC,hδ,H⟩ := written Pt.bind P G Pt hp
  let v := Pt.top.width / 2
  let key := ((Fintype.card G.ColorIndex:ℝ)*(Fintype.card (Site P.L)*Fintype.card Axis))*wealth v
  let slot := (Fintype.card G.ColorIndex:ℝ)*(Fintype.card Signed*((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site P.L) * wealth v)+ Fintype.card Axis * wealth v))
  have hf : 0≤key := by unfold key; have := wealth_nn v; positivity
  let M := (max slot key)*C+1
  have hm : 0<M := by unfold M; positivity
  have hv : 0<v := half_pos Pt.top.width_pos
  refine ⟨M,hm,?_⟩
  filter_upwards [small P hδ G,small_span P,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+1)] with x hx hs hv'
  intro c f S T ht hN hT A F V k hA
  have H := H S T ht hT.knobs hT A V F x hA hs (by omega) (by omega) hx k
  have hj : Fintype.card (Site S.patch.L)=Fintype.card (Site P.L) := congr_arg (fun t : Patch => Fintype.card (Site t.L)) ht
  apply (Schur.pure Pt.top.width_pos hC H (down_price v hv S G) (front_price v hv A F G)).weaker le_rfl
  unfold slotFee keyFee; rw [hj]; dsimp only [M,key,slot]; exact le_add_of_nonneg_right zero_le_one
end YM.AnalyticBridge.MarginalMultiplier3b1d.SourceBounds
