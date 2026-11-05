import YM.Next.FOUNDATIONS.LinkBounds
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Protected


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Use of local packet charge on tag integrals, with explicit measurable coordinates

No arbitrary pseudo-log outside its chart. Keep the physical input F and drape;
supply any masks/protectors with prices and measurability only where used (or
when specializing to global sector the Allocation still there, so many
hypotheses cup automatically). `actual` here always *before* dropping
prerequisites elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric Oriented Presented Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff ENNReal

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Supply a Borel logarithm with a fixed small near range. Not a section on
its whole domain! Necessary even if intending to zero out at switches. -/
structure Port (G : Gauge) where
  chart : G.El → G.Color
  borel : Measurable chart
  radius : ℝ
  price : ℝ
  hr : 0<radius
  hp : 1≤price
  sectioning u : G.chord u ≤ radius → G.lieExp (chart u)=u ∧ ‖chart u‖ ≤ price*G.chord u



def Port.relative (P : Port G) (S : StepData c f) (V : Config G c) (U : Config G f) : Directions G f :=
  fun i => P.chart (U i*(replica S.ratio V i)⁻¹)

lemma Port.readMeas (P : Port G) (S : StepData c f) (V : Config G c) (Y : Type*) [MeasurableSpace Y]
    (U : Y → Config G f) (h : Measurable U) : Measurable (fun y => P.relative S V (U y)) := by
  unfold relative; exact measurable_pi_lambda _ fun i => P.borel.comp (((measurable_pi_apply i).comp h).mul_const _)

/-- Even one Borel displacement method through all fields and choices, after suitable
entrance. Orientation sign read from each corresponding pulled pair (not assuming log
would be unchanged on reversal). -/
lemma born (P : Teller G) (L : Side) (W : ℝ) (hW : 0<W) (p : Port G) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L = L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ D F O A U k V (Q J : Window S), J.selects Q → Q.annulus O A D (radiusB x) →
      Wide O A D x W U k V → SliceSet S F U → J.charts U V (p.relative S V U) K x := by
  obtain ⟨C,hC,h⟩:=cleans_at P L W hW
  have hv : Tendsto (fun x => C*fiery G x L) atTop (𝓝 0) := by
    have he := (tally_g G L 0 1).const_mul C; rw [mul_zero] at he; exact he.congr fun x => by rw [fi]; ring
  refine ⟨p.price*C,one_le_mul_of_one_le_of_one_le p.hp hC,?_⟩
  filter_upwards [h,hv.eventually (ge_mem_nhds p.hr)] with x hx he
  intro c f S T hl hv hT D F O A U k V Q J hj hQ ho hu
  obtain ⟨a,-,hA⟩ := hx c f S T hl hv hT D F O A U k V hu ho
  have h y (hi : inSweep O A D (radiusB x) y) :
      PatchInputs (S:=S) U V (p.relative S V U) (p.price*C) x y := by
    intro i hf
    have hZ := ((hA y hi).chart i hf).2.2
    rw [← hl] at he
    let q := U i*(replica S.ratio V i)⁻¹
    obtain ⟨h1,h2⟩ := p.sectioning _ (show G.chord q ≤ _ from hZ.trans he)
    unfold Port.relative increment; change U i = G.lieExp (p.chart q)* _ ∧ _
    rw [h1]; unfold q; rw [inv_mul_cancel_right]
    rw [mul_assoc]; exact ⟨rfl,h2.trans (mul_le_mul_of_nonneg_left hZ (by linarith [p.hp]))⟩
  exact ⟨fun i hi => h _ (hQ.1 _ (hj.1 hi)),fun i hi => h _ (hQ.2.1 _ (hj.2 hi))⟩

section coords
variable {T : Tube G S} {x W κ : ℝ} (d : Allocation G S x W) (F : Forest S.ratio)
  (V : Config G c) (A O : Stores S) (Q J : Signed → Window S)
  (u : F.Slice G → Signed → Directions G f) (ρ H C β : ℝ) (n D : ℕ)
  (k : S.Choices) (χ : F.Slice G → ℝ)

def compulsory (T : Tube G S) (i : F.Slice G) := d.bill A k (F.drape i) V *
    S.likelihood (F.drape i) k * Comp T x β Q J O V k u (fun i => F.drape i) χ i

-- k dependence would be possible as well if priced. Here χ named per k; u needn't be
-- common here for subsequent integration to use, but P,V etc must be.
lemma compulsory_price {P : Teller G} {L : Side} {K : ℝ} (hT : P.Funds S T) (ha : Ledger P L W κ K H n D x)
    (hB : S.patch.L=L) (hb : 100*(1+radiusB x) ≤ c.val) (h : PointCharge T x W κ)
    (he : β∈Set.Icc (y G L x/2) (2*y G L x)) (hC : 0 ≤ C)
    (hc : Measurable χ) (hu : Measurable u)
    (hx : ∀ i, Real.exp ρ * ‖χ i‖ ≤ C*Real.exp (valuation O H n x G))
    (hI : ∀ i, d.bill A k (F.drape i) V ≠ 0 → Alive S (F.drape i) k →
      χ i ≠ 0 → ∀ s, Ensures (F.drape i) V O Q J x k (u i) W K D F A s) :
    Integrable (compulsory d F V A O Q J u β k χ T) (F.order G) ∧
    Real.exp ρ * ∫ i, ‖compulsory d F V A O Q J u β k χ T i‖ ∂F.order G ≤
      C*remaining O G x κ * ∫ i, d.bill A k (F.drape i) V * S.likelihood (F.drape i) k ∂F.order G := by
  let m i := d.bill A k (F.drape i) V * S.likelihood (F.drape i) k
  let v i := m i*χ i
  have hu' := F.continuous_drape (G:=G) |>.measurable
  have hh := funds_branch hT
  have hζ : Envelope m := (d.envelope hh (V:=fun _ => V) hu' measurable_const A k).mul (env_likelihood k hh hu')
  have hy i : 0≤m i := mul_nonneg (d.nonneg ..) (S.likelihood_pos ..)
  let X := compulsory d F V A O Q J u β k χ T
  let Y := Comp T x β Q J O V k u (fun i => F.drape i) v
  have hX : X=Y := by ext; unfold X Y compulsory Comp v m; ring
  let J0 : Set (F.Slice G) := {i | v i≠0}
  have hs (i) (he : i ∈ J0) : m i ≠ 0 ∧ χ i ≠ 0 := ⟨left_ne_zero_of_mul he,right_ne_zero_of_mul he⟩
  have H0 i (ht : i∈J0) := used (F.drape i) V O Q J k (u i) F A hB hb hT β K H W κ D n h ha he
    (fun e hv => F.on_tree i ⟨_,hv⟩) (hI i (left_ne_zero_of_mul (hs i ht).1) (alive_cost i ht) (hs i ht).2)
  have hm : Measurable X := hX ▸ check P T hT x β O V k _ _ v Q J hu' hu (hζ.meas.mul hc) fun i hv => (H0 i hv).1
  let A0 := C*remaining O G x κ
  have he1 : 0 ≤ A0 := by unfold A0 remaining; positivity
  have hY i : Real.exp ρ * ‖X i‖ ≤ A0*m i := by
    rw [hX]
    by_cases hh' : i ∉ J0
    · unfold Y Comp; rw [show v i=0 from Classical.not_not.mp hh',zero_mul,norm_zero,mul_zero]; exact mul_nonneg he1 (hy _)
    unfold Y Comp v; let f := vital β x (F.drape i) V O Q J T k (u i)
    have hr : 0≤f := (Real.exp_pos _).le
    change _ * ‖m i * χ i * f‖ ≤ _
    rw [norm_mul,norm_mul,Real.norm_of_nonneg hr,Real.norm_of_nonneg (hy _)]
    have hv := (H0 i (Classical.not_not.mp hh')).2
    have hg : Real.exp ρ*‖χ i‖*f ≤ A0 := le_trans (mul_le_mul (hx i) hv hr (mul_nonneg hC (Real.exp_pos _).le))
      (by unfold A0 remaining valuation; rw [hB,Real.exp_sub]; field_simp; rfl)
    linarith only [mul_le_mul_of_nonneg_right hg (hy i)]
  obtain ⟨Z,hZ⟩ := hζ.cost
  have hi : Integrable X (F.order G) := (show Envelope X from ⟨hm,Z*A0/Real.exp ρ,fun i => by
    rw [le_div_iff₀ (Real.exp_pos _),mul_comm]; exact (hY i).trans
      (by have hh : m i ≤ Z := le_trans (le_abs_self _) (hZ i); exact (mul_le_mul_of_nonneg_left hh he1).trans_eq (mul_comm ..))⟩).integrable _
  refine ⟨hi,?_⟩; rw [← integral_const_mul,← integral_const_mul]; exact integral_mono (hi.norm.const_mul _)
    ((hζ.integrable _).const_mul _) hY
where
  alive_cost i (ht : d.bill A k (F.drape i) V * S.likelihood (F.drape i) k * χ i ≠ 0) : Alive S (F.drape i) k :=
    (S.likelihood_pos ..).lt_of_ne' (right_ne_zero_of_mul (left_ne_zero_of_mul ht))
end coords
end YM.SectorNext.Remainder.Affine

noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric Oriented Presented Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f}

def Port.current (B : Port G) (S : StepData c f) (F : Forest S.ratio) (V : Config G c) (a : F.Slice G)
    (s : Signed) := B.relative S (pull s 0 V) (pull s 0 (F.drape a))

/-- For actual intact columns prior to reconnected counting. Per each of their chosen
support data, unconditional on affine coordinates. Can instead omit d if doing
applications after dropping defaults and directly use protected_purchase with the
requisite physical information. Doesn't bound unspecified likelihood weights if using
other than the actual intact choice likelihood. Caller χ includes collars and K/etc
priced as specified, not yet including any penalty Z / full frozen Haar or R.scale
factors which THEN also need the payments.
-/
lemma actual (P : Teller G) : ∃ N : ℕ, ∀ L : Side, N ≤ L.val → ∀ᶠ W : ℝ in atTop, 0<W ∧
    ∃ κ : ℝ, 0<κ ∧ ∀ (B : Port G) (H : ℝ) (n D : ℕ), ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    PointCharge T x W κ ∧
    ∀ (d : Allocation G S x W) (O A : Stores S) (F : Forest S.ratio) (β : ℝ),
      β∈Set.Icc (y G L x/2) (2*y G L x) →
      ∀ (V : Config G c) (Q J : S.Choices → Signed → Window S) (χ : S.Choices → F.Slice G → ℝ)
        (Λ ρ : ℝ), 0 ≤ Λ → (∀ k, Measurable (χ k)) → (∀ k i, Real.exp ρ * ‖χ k i‖ ≤ Λ*Real.exp (valuation O H n x G)) →
        (∀ k s, Owns (turnStore s O) (turnStore s A) x ∧
          (J k s).selects (Q k s) ∧ (Q k s).annulus (turnStore s O) (turnStore s A) D (radiusB x)) →
        let M k := compulsory d F V A O (Q k) (J k) (B.current S F V) β k (χ k) T
        (∀ k, Integrable (M k) (F.order G)) ∧
          (∀ k, Real.exp ρ * ∫ a, ‖M k a‖ ∂F.order G ≤ Λ*remaining O G x κ *
            ∫ i, d.bill A k (F.drape i) V * S.likelihood (F.drape i) k ∂F.order G) ∧
          Real.exp ρ * tagTotal F (fun k i => ‖M k i‖) ≤ Λ*remaining O G x κ := by
  obtain ⟨N,h⟩ := before_local P
  refine ⟨N,fun L hl => ?_⟩; filter_upwards [h L hl] with W hx
  obtain ⟨hw,κ,hK,h⟩ := hx
  refine ⟨hw,κ,hK,fun B H n D => ?_⟩
  obtain ⟨C,hC,hp⟩ := born P L W hw B
  filter_upwards [h C H D n,hp] with x hx hB
  intro c f S T hv hT hf
  obtain ⟨hw,hF⟩ := hx
  have hg := hF _ _ _ T hv hT hf
  refine ⟨hg,?_⟩
  intro d O A F β he V Q J χ Λ ρ hΛ hχ hY hs M
  let u := B.current S F V
  have hi : Measurable u := by
    refine measurable_pi_lambda _ fun s => ?_
    exact B.readMeas S _ _ _ ((continuous_pull s 0).measurable.comp F.continuous_drape.measurable)
  have hh k := compulsory_price d F V A O (Q k) (J k) u ρ H Λ β n D k (χ k) hf hw hv hT hg he hΛ (hχ k) hi (hY k)
    (by
      intro i ha hq _ s
      obtain ⟨hy,hk,h⟩ := hs k s
      have hb := funds_branch hf
      have h0 := pull_seeded s hb (d.actual _ _ _ _ ha)
      have hz : Alive S (pull s 0 (F.drape i)) (choice s k) := by unfold Alive; rw [(carry s hb k (F.drape i)).1]; exact hq
      have hh := wide_of_seeded (turnStore s O) _ D x W _ _ _ h0 hz
      refine ⟨hy,hh,hk,h,hB S T hv hT hf D (turnForest s F) _ _ _ _ _ _ _ hk h hh
        (turn_sliced s F _ (fun i hi => F.on_tree _ ⟨i,hi⟩))⟩)
  refine ⟨fun k => (hh k).1,fun k => (hh k).2,?_⟩
  unfold tagTotal; rw [Finset.mul_sum]; apply (Finset.sum_le_sum fun k (_:k∈Finset.univ)=> (hh k).2).trans
  rw [← Finset.mul_sum]; apply mul_le_of_le_one_right (mul_nonneg hΛ (Real.exp_pos _).le)
  have hi k : Integrable (fun i => d.bill A k (F.drape i) V * S.likelihood (F.drape i) k) (F.order G) := by
    have hk := funds_branch hf
    exact ((d.envelope hk F.continuous_drape.measurable measurable_const A k).mul (env_likelihood k hk F.continuous_drape.measurable)).integrable _
  rw [← integral_finsetSum _ fun k _ => hi k]
  apply le_trans (b:=∫ i : F.Slice G,(1:ℝ) ∂F.order G) _ (by simp)
  refine integral_mono (integrable_finsetSum _ fun k _ => hi k) (integrable_const _) fun i => ?_
  rw [← S.chosen (funds_branch hf) (F.drape i)]; exact Finset.sum_le_sum fun k _ => mul_le_of_le_one_left (S.likelihood_pos ..) (d.range ..)
end YM.SectorNext.Remainder.Affine
