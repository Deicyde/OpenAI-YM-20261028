import YM.Next.FLUCTUATIONS.Interior
import YM.Next.FLUCTUATIONS.Scales
import YM.Work.E01



/-!
# Unaffected defect producer

Only on unhit rows in the price ticket; all tests, indicators and records
remain the ones on the original V,U,tags. See `EBare` for precise Halo
& prerequisites (including actual tree). The threshold may depend on
ε as well as on P,L,W. No volume factor in this threshold.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Pressure.Stores Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f}

private def loss (A C t h e : ℝ) := 2*(A*t)*(C*h*e) + (A*t)*(C*(A*t)*e)

private lemma lower_cost (T : Tube G S) (U : Config G f) (V Q : Config G c) (x : Cell c) (R : ℕ)
    (A C t s h e : ℝ) (hA : 0≤A*t)
    (hm : ∀ i, ‖T.vision R s V i‖ ≤ A*t)
    (he : ∀ i : Bool, ‖lGap T R U Q V (x,i)‖ ≤ C*h*e ∧
      ‖dGap T R V (T.vision R s V) (x,i)‖ ≤ C*(A*t)*e) :
    -(loss A C t h e) ≤ T.workL R U Q V s x + T.workD R V s x := by
  let v := T.vision R s V
  have hf (i : Bool) : -(A*t*(C*h*e)) ≤ inner ℝ (v (x,i)) (lGap T R U Q V (x,i)) := by
    apply neg_le_of_abs_le
    exact (abs_real_inner_le_norm ..).trans (mul_le_mul (hm _) ((he i).1) (norm_nonneg _) hA)
  have hg (i : Bool) : -(A*t*(C*(A*t)*e)) ≤ inner ℝ (v (x,i)) (dGap T R V v (x,i)) := by
    apply neg_le_of_abs_le
    exact (abs_real_inner_le_norm ..).trans (mul_le_mul (hm _) ((he i).2) (norm_nonneg _) hA)
  unfold v at *
  rw [loss, workL_gap,workD_gap,Fintype.sum_bool,Fintype.sum_bool]
  linarith only [hf true,hf false,hg true,hg false]

private lemma delayed (L : Side) (A C D τ N ε : ℝ) (hD : 0<D) (ht : 0<τ) (hε : 0<ε) :
    let t (x : ℝ) := fiery G x L
    let h := stitchCost G L D
    let e x := widen (till x) (h x) τ
    ∀ᶠ x : ℝ in atTop, N * (radiusB x:ℝ)^4 * loss A C (t x) (h x) (e x) ≤ ε*(t x)^2 := by
  intro t h e
  obtain ⟨hf,hg⟩ := radius_stitch_errors G L D τ hD ht 4
  have he := (hg.const_mul (2*N*A*C)).add (hf.const_mul (N*A^2*C))
  simp only [mul_zero,add_zero] at he
  filter_upwards [he.eventually (ge_mem_nhds hε), (Work.E09.betaF_growth G L).eventually
    (eventually_gt_atTop 0)] with x hx hz
  have hu : 0<t x := Work.E09.temp_pos hz
  let q : ℝ := radiusB x
  let y := 2*N*A*C*(q^4*h x*e x/t x)+N*A^2*C*(q^4*e x)
  have hh : y ≤ ε := hx
  have hv : N*q^4 * loss A C (t x) (h x) (e x) = y * (t x)^2 := by
    unfold loss y; field_simp
  exact hv.trans_le (mul_le_mul_of_nonneg_right hh (sq_nonneg _))

private lemma patch_unique {A B : Patch} (h : A.L=B.L) (ht : A.J=B.J) : A=B := by
  cases A; cases B; congr

theorem bare : YM.Bid.EBare := by
  intro h3 h4 G P L W hW h8 ε hε
  -- Cost extraction by fixed shape. For ineligible requests prove the universal
  -- property by noticing they would have to supply the same patch certificate.
  by_cases hk : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap
  · refine ⟨Eventually.of_forall ?_⟩; intro x c f S hL _ T hT F A U k V _ _
    exact False.elim (hk ⟨S.patch,hL,hT.atStep,hT.kernel⟩)
  obtain ⟨D,hL,hD,hp⟩ := hk
  obtain ⟨C,τ,r,hC,hτ,hr,hco⟩ := interior_cost P D hp
  obtain ⟨A,hA,h⟩ := h4 h3 P
  obtain ⟨X,hX,hx⟩ := h8
  obtain ⟨N,hN⟩ := Work.E01.answer P (1:ℝ) (by norm_num)
  let w := stitchCost G L X
  have ht : Tendsto w atTop (𝓝 0) := by simpa only [pow_zero, one_mul,w] using radius_stitch G L X 0
  refine ⟨?_⟩
  filter_upwards [(h L W).late, hx.late, (hN L W hW).late, delayed (G:=G) L A C X τ N ε hX hτ hε,
    ht.eventually (ge_mem_nhds hr), (Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0),
    Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(predReach D+10))] with x hE hP hStore hv hw hh hm
  intro c f S hS hd T hT F Y U k V hF hY
  have hs : S.patch=D := patch_unique (hS.trans hL.symm) (hT.atStep.trans hD.symm)
  have hInc := hP c f S hS hd T hT F Y U k V hF hY
  have hMax := (hE c f S hS hd T hT F Y U k V hF hY).2.2
  have hPoints := (hStore c f S hS hd T hT F Y U k V hF hY).1.ours
  let t := fiery G x L
  have he : 0<t := Work.E09.temp_pos hh
  let g := widen (till x) (w x) τ
  have hg : 0≤w x := by unfold w stitchCost; rw [Work.E09.largeT_eq _ _ _ hh.le]; positivity
  have hf : 0 ≤ g := widen_nonneg _ hg
  have hM (i) : ‖T.vision (till x) (temp x) V i‖ ≤ A*t := by
    have he := hMax.up i; rwa [hS] at he
  have hB : 3*till x + 4 + predReach S.patch ≤ 2*radiusB x/5 := by
    rw [hs]; unfold till; omega
  let Q := S.prediction U k
  let s := Y.outs x \ Y.hit U Q V x
  let l := loss A C t (w x) g
  have hl : 0 ≤ l := by unfold l loss; positivity
  have hz (i : Cell c) (hi : i∈s) :
      -l ≤ T.workL (till x) U Q V (temp x) i + T.workD (till x) V (temp x) i := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hi
    obtain ⟨z,hV,hU⟩ := hInc i h1 h2
    apply lower_cost T U V Q i (till x) A C t (temp x) (w x) g (by positivity) hM
    intro j
    obtain ⟨ha,h⟩ := hco c f S T hs hT k _ _ hB U V (w x) hg hw (i,j) z hU hV
    exact ⟨ha,h _ (A*t) (by positivity) hM⟩
  have hy : (s.card:ℝ) ≤ N*(radiusB x:ℝ)^4*(Y.shares:ℝ) := by
    have hh := le_trans (card_le_card (show s ⊆ Y.outs x from sdiff_subset)) hPoints
    exact_mod_cast hh
  have hu : (s.card:ℝ)*l ≤ ε*t^2*Y.shares :=
    (mul_le_mul_of_nonneg_right hy hl).trans
      (le_trans (le_of_eq (by rw [mul_right_comm ((N:ℝ)*(radiusB x:ℝ)^4)]))
        (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg Y.shares)))
  change -(ε*t^2*Y.shares) ≤ talll T x U Q V s
  calc
    _ ≤ -((s.card:ℝ)*l) := by linarith only [hu]
    _ = ∑ _i∈s, -l := by simp
    _ ≤ _ := sum_le_sum hz
end YM.Next.Fluctuations
