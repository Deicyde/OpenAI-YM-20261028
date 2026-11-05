import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.PatchCap

/-!
# Outer shell payments (coarse and defects)

In  charge the *literal* undamaged rows at unsplit V,U. Extensions
for orientation-weak h's outside the packet may still use U,V here: no
old Plot/mask request for K; just Clean at V and the *individual* U
stencil's true patches. Therefore survive peeling away global sector
defaults. Includes N, in particular near a seed packet's weak annulus.
Error exponents post-L once V is weak. Uses E08–09 EBare service and same
Teller hypothesis here and RShape as appropriate elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

theorem letters_N (P : Teller G) (L : Side) :
    ∃ W, Rate G L (-2) W ∧ ∀ᶠ x : ℝ in atTop, 0 ≤ W x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch.L = L → Room P S T x → ∀ (V : Config G c) (i : Co c Gain), Clean V x i.1 (radiusB x/4+1) →
        |T.workN (till x) V (Pressure.temp x) i| ≤ W x := by
  obtain ⟨H,h,Hh⟩ := flattening P L
  obtain ⟨e,he,hg⟩ := read_guides P L h (Hh.mono fun _ he => he.1)
  let W x := e x^2 * (1/2:ℝ)
  have hw : Rate G L (-2) W := by convert (he.pow 2).mul_right (1/2:ℝ) using 1; norm_num
  refine ⟨W,hw,?_⟩
  filter_upwards [Hh,hg] with x hx hp
  refine ⟨by unfold W; positivity,?_⟩
  intro c f S T hL hR V i hi
  let B := radiusB x
  obtain ⟨g,b,hV,hb⟩ := hx.2 c f S T hL hR V i.1 (B/4) (by unfold B; omega) hi
  have hl : Clean (Lattice.gauge g V) x i.1 (B/4) := by
    intro j hj; rw [gauge_flags]; exact hi j (hj.trans (by unfold B; omega))
  have hs := (hp.2 c f S T hL hR _ b hb).2 i hl hV
  rw [DataKernel.ng hR.accepted,G.norm_adjoint] at hs
  rw [Tube.workN, abs_of_nonneg (by positivity)]
  exact le_trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hs 2) (by norm_num : (0:ℝ)≤2))
    (le_of_eq (by unfold W; ring))

/-- Price of C row. Even though using negative exponent later, can charge
it in an absolute test. -/
lemma letters_C (P : Teller G) (L : Side) :
    ∃ W, Rate G L (-2) W ∧ ∀ᶠ x : ℝ in atTop, 0 ≤ W x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch.L = L → Room P S T x → ∀ (V : Config G c) (i : Cell c), toll V i ≤ Pressure.temp x →
        |T.workC (till x) V (Pressure.temp x) i| ≤ W x := by
  obtain ⟨K,δ,hK,hδ,h⟩ := Work.E05.curvature_lower G
  let W x := (P.below.clip.direct*K/2) * (2*Pressure.fiery G x L)^4
  have hv : Rate G L (-2) W := by
    convert (((Rate.flame (G:=G) (L:=L)).mul_left 2).pow 4).mul_left (P.below.clip.direct*K/2) using 1
    norm_num
  refine ⟨W,hv,?_⟩
  filter_upwards [Work.E05.ultimately_cool δ hδ] with x hx
  have hh : 0 < P.below.clip.direct*K/2 := by have := P.below.clip.quadratic_pos; positivity
  refine ⟨mul_nonneg hh.le (by positivity : 0 ≤ (2*Pressure.fiery G x L)^4),?_⟩
  intro c f S T hL hR V i he
  have hp : -(W x) ≤ T.workC (till x) V (Pressure.temp x) i := by
    refine le_trans ?_ (Work.E05.workC_small T _ V _ i he K hK.le (h _ (he.trans hx.2)).1)
    apply neg_le_neg; unfold W; rw [hR.accepted.low]
    gcongr
    · exact hx.1
    simpa only [hL] using! hR.temperatures
  apply le_trans ?_ (neg_le_iff_add_nonneg.mp hp |> fun hh => show -T.workC (till x) V (Pressure.temp x) i ≤ W x by linarith)
  apply le_of_eq
  apply abs_of_nonpos
  have hn := (G.curvature_norm (faceValue V i))
  rw [Work.E05.workC_eq]
  have he' : (if toll V i=0 then 1 else min 1 (Pressure.temp x/toll V i))=1 := by
    split
    next hv => rfl
    next hv =>
      have ht : 0 < toll V i := lt_of_le_of_ne (G.chord_nonneg _) (Ne.symm hv)
      rw [min_eq_left ((le_div_iff₀ ht).mpr (by rwa [one_mul]))]
  rw [he', PathData.clipped, if_pos he]
  have hg := T.low.quadratic_pos.le
  change _ ≤ toll V i at hn
  nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hg]

/-- Both mismatch rows after the short cut in the **unaffected** chart.
Requires the same V and actual U in both rows. Uses the local gauge proof from FLUCTUATIONS. -/
theorem letters_LD (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G)
    (A : ℝ) (hA : 0 < A) {w : ℝ → ℝ} (hw : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0≤w x) :
    ∃ E, Rate G L (-(3/2)) E ∧
    ∀ᶠ x : ℝ in atTop, 0 ≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L →
    S.patch=D → Room P S T x → ∀ (U : Config G f) (V : Config G c) (b : Cell c) (k : S.Choices),
      Maximum A T x V → let B:= radiusB x; let R:=till x
      Clean V x b.1 B → ∀ u, Grafted V U u b.1 (B/2) (w x) S →
        |T.workL R U (S.prediction U k) V (Pressure.temp x) b| + |T.workD R V (Pressure.temp x) b| ≤ E x := by
  obtain ⟨W,H,h⟩ := layered P L hw hp
  obtain ⟨C,τ,r,hC,hτ,hr,hq⟩ := Next.Fluctuations.interior_cost P D hd
  let t x := Pressure.fiery G x L
  let d x := A*t x
  let e x := widen (till x) (W x) τ
  let M x := d x * (C*W x*e x)
  let V x := d x * (C*d x*e x)
  let F x := 2*M x + V x
  have he := H.broadens hτ ((hp.and h).mono fun _ hx => hx.1.trans hx.2.1)
  have hz : Rate G L (-(1/2)) d := Rate.flame.mul_left _
  have hm : Rate G L (-(3/2)) M := by convert hz.mul ((H.mul_left C).mul he) using 1; norm_num
  have hv : Rate G L (-(3/2)) V := by convert hz.mul ((hz.mul_left C).mul he) using 1; norm_num
  refine ⟨F,(hm.mul_left 2).add hv,?_⟩
  filter_upwards [H.below (by norm_num) r hr,h,hp] with x hx hh hp
  have hW := hp.trans hh.1
  have ht : 0 ≤ t x := by unfold t Pressure.fiery Pressure.temp; positivity
  have hd : 0 ≤ d x := mul_nonneg hA.le ht
  have he : 0 ≤ e x := widen_nonneg _ hW
  refine ⟨(by unfold F M V; positivity),?_⟩
  intro c f S T hL hP hR U Z b k hM B R hV u hu
  have hpos : 100≤B := hR.sight.1
  obtain ⟨z,g,H'⟩ := hh.2 c f S T hL hR Z U b.1 (B/2) (by change B/2 ≤ 32*B; omega)
    (hV.shrink (v:=b.1) (by rw [separation_self,zero_add]; omega)) u hu
  let y := Pressure.temp x
  have hb (i : Twin c) : ‖T.vision R y Z i‖ ≤ d x := by have he := hM.up i; rwa [hL] at he
  have hi (i : Bool) := hq c f S T hP hR.accepted k R (B/2) (by have he := hR.frame; unfold R till B; omega) U Z (W x) hW
    ((le_abs_self _).trans hx) (b,i) z H'.fine H'.coarse
  let Q := S.prediction U k
  let a := T.vision R y Z
  have he' i : |inner ℝ (a (b,i)) (lGap T R U Q Z (b,i))| ≤ M x := (abs_real_inner_le_norm ..).trans
    (mul_le_mul (hb _) (hi i).1 (norm_nonneg _) hd)
  have hv' i : |inner ℝ (a (b,i)) (dGap T R Z a (b,i))/2| ≤ V x/2 := by
    rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    apply (abs_real_inner_le_norm ..).trans
    exact mul_le_mul (hb _) ((hi i).2 a _ hd hb) (norm_nonneg _) hd
  rw [workL_gap,workD_gap,Fintype.sum_bool,Fintype.sum_bool]
  exact le_trans (add_le_add ((abs_add_le ..).trans (add_le_add (he' true) (he' false)))
    ((abs_add_le ..).trans (add_le_add (hv' true) (hv' false)))) (le_of_eq (by unfold F; ring))
end YM.ConnectedActivityE6.SliceRows
