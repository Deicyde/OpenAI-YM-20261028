import YM.Further.ROOTED_INTERACTING_REMAINDER.Pruning
import YM.Push.SECTOR_MEASURE.Gauges

/-!
# Profile integral elimination on each actual F

Quantities that may be tested after normalization. F is arbitrary.
At fixed V pay for the extra coarse rotations (not fixed to 1!
fine slice fixes only trunks). Especially, no fake iid assumption on the
predictor across the pivotal tests. Conditioning at fixed V for the
pointwise formula vs averaging V across prior using *all bonds* for the
partition-weighted formula gives different costs; keep them separate.
Likelihood kept in both. This pivot estimate need not hold through
arbitrary dropping of defaults.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Lattice RG Wilson Function Set Filter Tree Finset MeasureTheory
open SectorNext.Vacuum Pressure Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "Δ" => Module.finrank ℝ G.Color
local notation "Nf" => rich f
local notation "Nc" => Fintype.card (Site c)

/-- A legitimate leftover of profiled reaches even before the other local
operations. On arbitrary F (using its literal Slice and data through the SAME
choice). Standalone data envelope in further files. -/
def flight (M : Stores S) (t : ℝ) (i : S.Choices) (V : Config G c) (U : Config G f) :=
    ration M.costs t U * S.likelihood U i * gapper M.aisles t V (S.prediction U i)

lemma flight_nonneg (M : Stores S) (t : ℝ) (i : S.Choices) (V : Config G c) (U : Config G f) : 0≤flight M t i V U :=
  mul_nonneg (mul_nonneg (ration_nonneg ..) (S.likelihood_pos ..)) (gapper_nonneg ..)

lemma wing {α : Type*} [MeasurableSpace α]
    (hk : S.patch.Branches S.kernel G) (M : Stores S) (t : ℝ) (k : S.Choices)
    {V : α → Config G c} (hv : Measurable V)
    {U : α → Config G f} (hu : Measurable U) : Envelope (fun z => flight M t k (V z) (U z)) := by
  have hQ : Measurable (fun z => S.prediction (U z) k) := (S.prediction_meas hk k).comp hu
  have hR : Envelope (fun z => ration M.costs t (U z)) := Env.along (Env.compact (ration_cont ..)) hu
  have hS : Envelope (fun z => gapper M.aisles t (V z) (S.prediction (U z) k)) :=
    Env.along (F:=fun p : Config G c × Config G c => gapper M.aisles t p.1 p.2) (g:=fun z => (V z,S.prediction (U z) k)) (Env.compact (gapper_cont ..)) (hv.prodMk hQ)
  exact (hR.mul (env_likelihood k hk hu)).mul hS

lemma repack (F : Forest S.ratio) (M : Stores S) (t : ℝ) (k : S.Choices) (V : Config G c) (hk : S.patch.Branches S.kernel G) :
    (∫ a, flight M t k V (F.drape a) ∂F.order G) = ∫ U,flight M t k V U ∂prior G f := by
  apply (F.pack ..).symm
  · exact (wing hk M t k measurable_const measurable_id).integrable _
  intro z hz U
  rw [flight, (choice_gauge hk U k z).1,ration_GI M.costs t z U, (choice_gauge hk U k z).2]
  unfold Lattice.gauge; simp only [comp_apply,hz,one_mul,inv_one,mul_one]; rfl

lemma average_roots (M : Stores S) (t : ℝ) (k : S.Choices) (V : Config G c) (hk : S.patch.Branches S.kernel G) :
    (∫ U,flight M t k V U ∂prior G f) =
      ∫ U,(∫ z, flight M t k V (Lattice.gauge (z ∘ S.ratio.parent) U) ∂Measure.pi fun _=>G.probHaar) ∂prior G f := by
  let μ := Measure.pi fun _ : Site c=>G.probHaar
  let G' := fun (p : Config G f × (Site c → G.El)) => flight M t k V (Lattice.gauge (p.2 ∘ S.ratio.parent) p.1)
  have he : Measurable (fun (p : Config G f × (Site c → G.El)) => Lattice.gauge (p.2 ∘ S.ratio.parent) p.1) := by
    unfold Lattice.gauge; fun_prop
  have H : Envelope G' := wing hk M t k (V:=fun (_:Config G f × (Site c → G.El)) => V) measurable_const he
  let Q := fun U : Config G f => fun z : Site c → G.El => flight M t k V (Lattice.gauge (z ∘ S.ratio.parent) U)
  change _ = ∫ U,(∫ z,Q U z ∂μ) ∂prior G f
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have hz : Integrable (uncurry Q) ((prior G f).prod μ) := H.integrable _
  rw [integral_integral_swap hz]
  have hx (i) : (∫ x, Q x i ∂prior G f) = ∫ x,flight M t k V x ∂prior G f := by
    have hp := prior_gauge (i ∘ S.ratio.parent)
    have h1 : Measurable (flight M t k V) := (wing hk M t k measurable_const measurable_id).meas
    have hh := integral_map (φ:=gauge (i ∘ S.ratio.parent)) (μ:=prior G f) (f:=flight M t k V)
      hp.aemeasurable h1.aestronglyMeasurable
    rw [hp.map_eq] at hh; exact hh.symm
  simp_rw [hx]; simp only [integral_const,probReal_univ, one_smul]


/-- Worst powers retained at fixed V (before restoring scalar units).
There are `rich` fine pivots and independently #coarse sites minus one
coarse rotations; $\ell^1$ over all tags. Especially n=2. -/
theorem circuit (F : Forest S.ratio) (M : Stores S) (t K : ℝ) (V : Config G c) (hc : 2≤c.val)
    (hk : S.patch.Branches S.kernel G) (ht : 0<t) (hs : t≤1) (hK : 1 ≤ K)
    (hZ : (∫ i,draught t⁻¹ i ∂G.probHaar) ≤ K*t^Δ) :
    (∑ i : S.Choices, ∫ a,flight M t i V (F.drape a) ∂F.order G) ≤
      (K*t^Δ)^(Nf + (Nc-1))*(t⁻¹^Δ)^(M.costs.card+M.aisles.card) := by
  let L := K*t^Δ
  let H := t⁻¹^Δ
  have hL : 0≤L := mul_nonneg (zero_le_one.trans hK) (by positivity)
  have hH : 0≤H := by unfold H; positivity
  let Y := L^(Nc-1)*H^M.aisles.card
  have hY : 0≤Y := mul_nonneg (pow_nonneg hL _) (pow_nonneg hH _)
  have h (i : S.Choices) :
      (∫ U,flight M t i V U ∂prior G f) ≤
        ∫ U,ration M.costs t U*S.likelihood U i*Y ∂prior G f := by
    let ν := Measure.pi fun _ : Site c=>G.probHaar
    rw [average_roots M t i V hk]
    have he : Integrable (fun p : Config G f × (Site c → G.El) => flight M t i V (Lattice.gauge (p.2 ∘ S.ratio.parent) p.1)) ((prior G f).prod ν) :=
      (wing hk M t i (V:=fun (_ : Config G f × (Site c → G.El)) => V) measurable_const (by unfold Lattice.gauge; fun_prop)).integrable _
    apply integral_mono he.integral_prod_left -- which arg?
    · exact (((Env.compact (ration_cont ..)).mul (env_likelihood i hk measurable_id)).mul (Envelope.const _)).integrable _
    intro U
    let Q := S.prediction U i
    let g := fun z => Lattice.gauge z Q
    have ht' (z : Site c→G.El) : (z∘S.ratio.parent)∘S.ratio.embed=z := by
      funext j; dsimp; rw [S.ratio.embed_parent]
    have h0 (z : Site c→G.El) := choice_gauge hk U i (z ∘ S.ratio.parent)
    have h1 z : flight M t i V (Lattice.gauge (z ∘ S.ratio.parent) U)=
        ration M.costs t U*S.likelihood U i*gapper M.aisles t V (g z) := by
      rw [flight,ration_GI M.costs t (z ∘ S.ratio.parent) U,(h0 z).1,(h0 z).2,ht']
    simp_rw [h1]
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ration_nonneg ..) (S.likelihood_pos ..))
    refine le_trans (b:=∫ z,sill M.aisles t V (g z) ∂ν) ?_ (spill hc V Q _ ht hs hK hZ)
    let e := fun z : Site c→G.El => (V,g z)
    have he' : Continuous e := by unfold e g Lattice.gauge; fun_prop
    exact integral_mono (((gapper_cont ..).comp he').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (((sill_cont ..).comp he').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun z => gap_sill _ t ht V (g z))
  simp_rw [repack F M t _ V hk]
  apply (sum_le_sum fun i _ => h i).trans
  have hi (i : S.Choices) : Integrable (fun U => ration M.costs t U*S.likelihood U i * Y) (prior G f) :=
    (((Env.compact (ration_cont ..)).mul (env_likelihood i hk measurable_id)).mul (Envelope.const _)).integrable _
  rw [← integral_finsetSum _ (fun i _=>hi i)]
  simp_rw [← sum_mul,← mul_sum,S.chosen hk,mul_one,integral_mul_const]
  have hf : 2 ≤ f.val := hc.trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property)
  calc
    _ ≤ (L^Nf*H^M.costs.card)*Y := mul_le_mul_of_nonneg_right (pruned_default hf _ _ _ ht hs hK hZ) hY
    _ = _ := by unfold Y L H; rw [pow_add,pow_add]; ring

/-- At marginal, better extra pivot count, even in n=2. -/
theorem circulation (F : Forest S.ratio) (M : Stores S) (t K : ℝ) (hf : 2≤f.val)
    (hk : S.patch.Branches S.kernel G) (ht : 0<t) (hs : t≤1) (hK : 1≤K)
    (hZ : (∫ i,draught t⁻¹ i ∂G.probHaar) ≤ K*t^Δ) :
    (∫ V,(∑ i : S.Choices, ∫ a,flight M t i V (F.drape a) ∂F.order G) ∂prior G c) ≤
      (K*t^Δ)^(Nf + Fintype.card (Bond c))*(t⁻¹^Δ)^(M.costs.card+M.aisles.card) := by
  simp_rw [repack F M t _ _ hk]
  let L := K*t^Δ
  let b := t⁻¹^Δ
  let Y := L^(Fintype.card (Bond c)) * b^M.aisles.card
  have hY : 0≤Y := by unfold Y L b; have hm : 0<K := zero_lt_one.trans_le hK; positivity
  let g := flight (G:=G) M t
  let μ := prior G f
  let ν := prior G c
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  haveI : IsProbabilityMeasure ν := by unfold ν; infer_instance
  have hg (i : S.Choices) : Integrable (uncurry (g i)) (ν.prod μ) :=
    (wing hk M t i (V:=(Prod.fst : Config G c × Config G f → _)) measurable_fst measurable_snd).integrable _
  change (∫ V,(∑ i, ∫ a,g i V a ∂μ) ∂ν) ≤ _
  rw [integral_finsetSum Finset.univ (f:=fun i V => ∫ a,g i V a ∂μ) (fun i _ => (hg i).integral_prod_left)]
  simp_rw [integral_integral_swap (hg _)]
  have hi (i : S.Choices) := (hg i).swap.integral_prod_left
  change ∀ i, Integrable (fun U : Config G f=> ∫ V, g i V U ∂ν) μ at hi
  rw [← integral_finsetSum _ (fun i _=> hi i)]
  have he := pruned_default hf M.costs t K ht hs hK hZ
  have hr : Continuous (ration (G:=G) M.costs t) := ration_cont ..
  apply le_trans (b:=(∫ U,ration M.costs t U ∂μ)*Y)
  · rw [← integral_mul_const]; apply integral_mono (integrable_finsetSum _ (fun i _ => hi i))
      ((hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const _)
    intro U
    simp only [g,flight,integral_const_mul]
    calc
      _ ≤ ∑ i, ration M.costs t U * S.likelihood U i*Y := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (drain _ (S.prediction U i) ht hs hK hZ) (mul_nonneg (ration_nonneg ..) (S.likelihood_pos ..))
      _ = _ := by rw [←sum_mul,←mul_sum,S.chosen hk,mul_one]
  exact (mul_le_mul_of_nonneg_right he hY).trans_eq (by unfold Y L b; rw [pow_add,pow_add]; ring)

end YM.Further.RootedInteractingRemainder
