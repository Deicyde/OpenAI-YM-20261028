import YM.SectorNext.LARGE_FIELD_REMAINDERS.RemoteGap


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Wide *local* prerequisites on the intact packet neighborhood

Use after geometry choices, including negative queries.

A records physical
choices affecting a packet O; don't demand that the remaining field U
realizes the unretained profile factors elsewhere.

Here keep actual V flag
correctness just through the stated halo; can impose more.

Works on true U in
that halo (also on true tree globally), shared rooted k not re-queried.

This is
through fixed-L geometry, incarnated on the Pressure/Sector choice radius
conventions (or use at that convention before reprojection).

We continue to
anchor positive row comparisons at their canonical initial sites; to track
all radius decisions at support cost (different problem), include all incident
endpoints as in Stores and broader support plan.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- D halo (on kernel costs). No intermediary estimator. `A` complete list for these
comparisons, including all merged/nonmerged seeds by their canonical addresses.
Use with O containing the merged seed choices of interest. Could use larger radii.
Flags outside this halo play no role in the estimate.
-/
structure Wide (O A : Stores S) (D : ℕ) (x w : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) : Prop where
  consumes p : ¬ Disjoint (O.dome ((D+5)*radiusB x)) (startPos S p) →
    ((p ∈ A.costs → fiery G x S.patch.L/4 ≤ toll U p) ∧ (p∉A.costs → toll U p ≤ fiery G x S.patch.L/2))
  drive b : ¬ Disjoint (O.dome ((D+5)*radiusB x)) (pinPos b) →
    ((b ∈ A.aisles → w*fiery G x S.patch.L ≤ wire (S.prediction U k) V b) ∧
      (b∉A.aisles → wire (S.prediction U k) V b ≤ 2*w*fiery G x S.patch.L))
  precise i : i∈O.dome ((D+5)*radiusB x) → (i∈A.flags ↔ i∈RG.flags (temp x) V)
  list i : i∈O.dome ((D+5)*radiusB x) → 0<S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i)

lemma wide_of_seeded (O A : Stores S) (D : ℕ) (x w : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c)
    (h : Seeded A U k V x w) (ha : Alive S U k) : Wide O A D x w U k V :=
  ⟨fun i _ => h.fine _,fun b _ => h.coarse _,fun i _ => by rw [h.exactFlags],fun i _ => listed_of_alive ha _⟩

def inSweep (O A : Stores S) (D B : ℕ) (p : Site c) := p∉A.dome (2*B) ∧ p∈O.dome (D*B)

lemma sweep_zone {O A : Stores S} {D B} {p : Site c} (h : inSweep O A D B p) (y : Site c) (hh : separation p y≤ B) :
    y∉A.place ∧ y∈O.dome ((D+5)*B) := by
  constructor
  · intro h0; exact h.1 (halo_spec.mpr ⟨y,h0,(separation_comm ..) ▸ (show separation p y≤2*B by omega)⟩)
  obtain ⟨z,hz,hz'⟩ := halo_spec.mp h.2
  refine halo_spec.mpr ⟨z,hz,?_⟩
  have hp := (separation_triangle z p y).trans (Nat.add_le_add hz' hh)
  rw [add_mul]; omega

lemma CleanFaces (O A : Stores S) (D : ℕ) (x w : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c)
    (h : Wide O A D x w U k V) (y : Site c) (hp : inSweep O A D (radiusB x) y) :
    let B := radiusB x; let t := fiery G x S.patch.L
    (∀ p : Cell f, separation y (S.ratio.parent p.1) ≤ B → toll U p ≤ t/2) ∧
      (∀ b : Bond c, separation y b.1 ≤ B → wire (S.prediction U k) V b ≤ 2*w*t) ∧
      (∀ b : Cell c, separation y b.1 ≤ B → toll V b ≤ temp x) ∧
      ∀ b : Site c, separation y b ≤ B → 0 < S.patch.frameMass S.kernel (expandAt (S.ratio.embed b) U) (k.1 b) := by
  intro B t
  have hi := sweep_zone hp
  refine ⟨fun p hx => ?_,fun b hx => ?_,fun b hx => ?_,fun b hx => h.list b (hi b hx).2⟩
  · obtain ⟨he,hh⟩:=hi _ hx
    have hX := Finset.mem_image_of_mem S.ratio.parent (Work.E01.base_touched p)
    apply (h.consumes p (fun hd => Finset.disjoint_left.mp hd hh hX)).2
    exact fun hg => he (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨_,hg,hX⟩)))
  · obtain ⟨he,hh⟩:=hi _ hx
    have hX : b.1∈pinPos b := by simp [pinPos]
    apply (h.drive b (fun hd => Finset.disjoint_left.mp hd hh hX)).2
    exact fun hg => he (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,hg,hX⟩)))
  · obtain ⟨he,hh⟩:=hi _ hx
    by_contra! h0
    exact he (Finset.mem_union_right _ ((h.precise _ hh).2 ((RG.flags_spec ..).mpr ⟨b,Work.E01.base_touched b,h0⟩)))

/-- Candidate canonical relative coordinates (for later affine and inactive shell
extensions). Even if outside chart and not actually logarithms on some link, only
use/prove in the displayed weak stencils! -/
private def displacement (S : StepData c f) (V : Config G c) (U : Config G f) : Directions G f :=
  fun i => G.plog (G.mat (U i*(replica S.ratio V i)⁻¹))

def thin (x : ℝ) := 2*radiusB x/5

structure Cleans (C x : ℝ) (U : Config G f) (V : Config G c) (p : Site c) (a : Directions G f) : Prop where
  chart (i : Bond f) : separation p (S.ratio.parent i.1) ≤ thin x →
    U i=increment (replica S.ratio V) a i ∧ ‖a i‖ ≤ C*fiery G x S.patch.L ∧ linking S V U i ≤ C*fiery G x S.patch.L
  scene : ∃ z : Site c→G.El,
    (∀ i : Bond c, separation p i.1 ≤ thin x → G.chord (gauge z V i) ≤ weakRadius (G:=G) C S.patch.L x) ∧
    (∀ i : Bond f, separation p (S.ratio.parent i.1) ≤ thin x →
      G.chord (gauge (z ∘ S.ratio.parent) U i) ≤ weakRadius (G:=G) C S.patch.L x)

set_option maxHeartbeats 550000 in
/-- Exterior applicability quote, at wide local ledger and both relative and
absolute gauges. Same `C` even for arbitrary fixed-size shell `D`. Profile constraints
local but tree and tag stencils still as physical in the claim. -/
lemma cleans_at (P : Teller G) (L : Side) (W : ℝ) (hw : 0<W) :
    ∃ C : ℝ, 1≤C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (D : ℕ) (F : Forest S.ratio) (O A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Wide O A D x W U k V → ∃ a : Directions G f, (∀ i∈F.trunks,a i=0) ∧
        ∀ p : Site c, inSweep O A D (radiusB x) p → Cleans (S:=S) C x U V p a := by
  obtain ⟨D,hD,HD⟩ := Work.E02.answer G L P.j P.bind
  obtain ⟨C₀,δ,hC₀,hδ,H⟩ := log_chart_cost G
  let M := (P.j+7)*L.val
  let K : ℝ := (2*(M:ℝ)+1)^4 * Fintype.card PlaqAxes
  let E : ℝ := D*K + 2*W
  let X : ℝ := 16*3^5*(Fintype.card PlaqAxes:ℝ)*2
  have hK : 0 ≤ K := by unfold K; positivity
  have he : 0<E := by unfold E; positivity
  have hX : 0≤X := by unfold X; positivity
  let C := E + C₀*E + X + 1
  have hp : 1≤C := by unfold C; nlinarith only [he,hC₀,hX]
  refine ⟨C,hp,?_⟩
  have hm : Tendsto (fun x => E*fiery G x L) atTop (𝓝 0) := by
    have ht := (tally_g G L 0 1).const_mul E; rw [mul_zero] at ht
    exact ht.congr fun x => by simp only [fi,pow_one,pow_zero]; ring
  filter_upwards [hm.eventually (ge_mem_nhds hδ),(year G L).eventually_gt_atTop 0, Work.E07.temp_coarse_le G L,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (20*(M+L.val+10))] with x hz hy hv hB
  intro c f S T hL hh hT A0 F O A U k V hU hA
  have hj := hT.atStep
  have hk := hT.knobs
  let B := radiusB x
  change 20*(M+L.val+10) ≤ B at hB
  change 100*(1+B) ≤ c.val at hh
  have hM : macroR S.patch=M := by rw [Work.E01.macroR_eq,hj,hL]
  have hsize : 100*macroR S.patch ≤ f.val := by
    have h : c.val ≤ f.val := by
      rw [S.sizes]
      have h := S.patch.L.property; change 0<S.patch.L.val at h; simpa using Nat.mul_le_mul_left c.val h
    omega
  let g := S.ratio
  let a := displacement S V U
  refine ⟨a, fun i hi => ?_,fun y he' => ?_⟩
  · unfold a displacement replica; rw [hU _ hi,if_pos (F.trunk_internal hi),inv_one,mul_one,G.mat_one,G.plog_one]
  let t := fiery G x S.patch.L; let o := thin x
  have ht : 0<t := by unfold t; rw [hL]; exact Work.E09.temp_pos hy
  obtain ⟨h1,h2,h3,h4⟩ := CleanFaces O A A0 x W U k V hA _ he'
  have hlink (i : Bond f) (he : separation y (g.parent i.1) ≤ o) : linking S V U i ≤ E*t := by
    let p := g.parent i.1
    have hh' : separation y p+2 ≤ B ∧ separation y p+M+L.val ≤ B := by change separation y p≤2*B/5 at he; omega
    have ha : usable S U p k := by
      intro z hz
      have hi : separation p (plank p z) ≤ 2 := Work.E08.separation_box_add _ hz
      exact h4 _ ((separation_triangle ..).trans ((Nat.add_le_add_left hi _).trans hh'.1))
    have hb := HD c f S hk hL hj hsize (by omega) F U hU V i k ha
    have hx : port S p U ≤ K*t := by
      unfold K; rw [← hM]
      apply Work.E08.port_le y B t ht.le
      · intro i hi; exact (h1 i hi).trans (by change t/2≤t; linarith)
      rw [hM,hL]; exact hh'.2
    have hh' : separation y p ≤ B := by omega
    unfold Bid.Cops at hb; unfold linking E; rw [add_mul,mul_assoc]
    refine hb.trans (add_le_add (mul_le_mul_of_nonneg_left hx hD.le) ?_)
    split
    · positivity
    exact h2 _ hh'
  refine ⟨fun i hi => ?_,?_⟩
  · obtain ⟨ha,hp⟩ := H _ (by rw [← hL] at hz; exact (hlink i hi).trans hz)
    refine ⟨?_, (hp.trans (mul_le_mul_of_nonneg_left (hlink i hi) hC₀.le)).trans ?_, (hlink i hi).trans ?_⟩
    · unfold increment a displacement; rw [ha, inv_mul_cancel_right]
    · have h1 : C₀*E ≤ C := by unfold C; linarith only [he,hX]
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 ht.le
    · apply mul_le_mul_of_nonneg_right _ ht.le; unfold C; nlinarith only [hC₀,he,hX]
  obtain ⟨z,hz⟩ := Work.E08.axial_patch y V o (B/2) (by change 2*B/5+1≤_; omega) (by omega)
    (temp x) (temp_nonneg _) (fun v he j => h3 (v,j) (he.trans (Nat.div_le_self _ _)))
  have hs a (h : separation y (a : Bond c).1 ≤ o) : G.chord (gauge z V a) ≤ X*((b x)^5*t) := by
    rw [← hL] at hv
    apply (hz _ h).trans
    have hk : (↑(B/2):ℝ) ≤ b x := (Nat.cast_le.mpr (Nat.div_le_self B 2)).trans
      (show (B:ℝ) ≤ Scales.b x from le_add_of_nonneg_left zero_le_one)
    have hl : 1≤b x := Scales.size x
    calc
      _ ≤ 16*(3*(b x))^5 * ↑(Fintype.card PlaqAxes)*(2*t) := by have hh := temp_nonneg x; gcongr <;> linarith
      _ = _ := by unfold X; ring
  have hx : E*t+X*((b x)^5*t) ≤ weakRadius (G:=G) C S.patch.L x := by
    have hb : 1≤(b x)^5 := one_le_pow₀ (Scales.size x)
    unfold weakRadius C t at *
    nlinarith [le_mul_of_one_le_left ht.le hb, mul_nonneg hC₀.le he.le]
  have ht' : 0≤X*(b x^5*t) := by unfold X; have := (zero_lt_one.trans_le (Scales.size x)); positivity
  refine ⟨z, fun i hi => (hs i hi).trans ((le_add_of_nonneg_left (mul_nonneg he.le ht.le)).trans hx),fun i hi => ?_⟩
  let e := z∘S.ratio.parent; let R := replica S.ratio V
  have hc : G.chord (gauge e R i) ≤ X*((b x)^5*t) := by
    change G.chord (gauge (constantGauge z S.ratio) (replica S.ratio V) i) ≤ _
    rw [copied _ S.patch.odd_side V z]; unfold replica; split
    · rw [G.chord_one]; exact ht'
    exact hs _ hi
  have hh : gauge e U i = (e i.1*(U i*(R i)⁻¹)*(e i.1)⁻¹)*gauge e R i := by unfold Lattice.gauge; group
  change G.chord (gauge e U i) ≤ _; rw [hh]
  apply (G.chord_triangle ..).trans
  rw [G.chord_conj]; exact (add_le_add (hlink i hi) hc).trans hx
end YM.SectorNext.Remainder.Affine
