import Mathlib.Analysis.Fourier.Convolution
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Curl
import YM.Next.ROTATIONS.Dyad
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Pitfalls
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Tier
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Multiplier
import YM.Work.B18

/-!
# Root value cost for the mean/linear-ratio integration

Price the genuine F0 array, even when off intact prerequisites (can
use same budget with sectored formulas and shared Y/tags).

In particular leave
smallness of μ itself as at  to other jobs.

No zooming, no V marks.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Pressure.Teller Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open Tier Wisps Schur LocalJet 
open SectorNext.Remainder   
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

section value
variable {G : Gauge} (J : Patch) (P : Teller G)

/-- Small helper for transporting termwise budgets through Schur/Pours. -/
lemma diary {c : Side} {Y I : Type} [Fintype I] [Fintype Y] {A : Matrix I Y ℝ} {p : I → Site c} {q : Y → Site c} {v C H : ℝ}
    (hv : 0≤v) (hH : 0≤H) (h : Pours A p q v C) (b : Vec Y) (hb : ∀ i, |b i| ≤ H) (i : I) : |(A *ᵥ b) i| ≤ C*H := by
  have hs := (h.weaker (e:=C) (t:=0) hv le_rfl).row i
  simp only [rate,zero_mul,Real.exp_zero,one_mul] at hs
  change |∑ j:Y, A i j * b j| ≤ _
  apply (Finset.abs_sum_le_sum_abs ..).trans
  simp_rw [abs_mul]
  apply le_trans (Finset.sum_le_sum (s:=Finset.univ) (g:=fun j=>|A i j| * H) (fun j _=>mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)))
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hs hH

private lemma common_move (h : J.Branches P.bind G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f)
    (T : Tube G S), S.patch=J → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (F : Forest S.ratio) (A : Stores S) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
      Pours (Rows.move T x V k (shots S x) A F) (Wisps.down S (G:=G)) (Wisps.front A F) (P.top.width/2) C := by
  obtain ⟨C,δ,hC,hδ,H⟩:=Wisps.written P.bind J G P h
  let v:=P.top.width/2
  let fee (v:ℝ):=((Fintype.card G.ColorIndex:ℝ)*(Fintype.card (Site J.L)*Fintype.card Axis))*Tier.wealth v
  let slot (v:ℝ) : ℝ := Fintype.card G.ColorIndex * ((Fintype.card Signed:ℝ)*
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site J.L)*wealth v)+Fintype.card Axis *wealth v))
  have hf (v:ℝ) : 0≤fee v := by unfold fee; have := Tier.wealth_nn v; positivity
  refine ⟨max (slot v) (fee v)*C,mul_nonneg ((hf _).trans (le_max_right ..)) hC,?_⟩
  filter_upwards [small_span J,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot J+1),
    Work.E01.fiery_le G (1:Side) (permit J),(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx hf hg hi
  intro c f S T hS he hP F A k V hV
  have ha : permit J*temp x ≤ δ := by simpa [fiery,betaF] using hg.trans hi
  have h := H S T hS hP.knobs hP A V F x hV hx (by omega) (by omega) ha k
  have hv : 0<v:=half_pos P.top.width_pos
  have ht := pure P.top.width_pos hC h (down_price v hv S G) (front_price v hv A F G (x:=x))
  have hh : Fintype.card (Site S.patch.L) = Fintype.card (Site J.L) := by rw [hS]
  unfold slotFee keyFee at ht; rw [hh] at ht; exact ht

-- Maximum cost for Mv/Mw also off the sector prerequisite
private lemma free_plot {c f : Side} (S : StepData c f) (x w : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) :
    ∃ B : Stores S,B.Plot U k V x w := by
  let B : Stores S := ⟨∅,∅,∅⟩
  have h b : B.dome b = ∅ := by ext; simp [Stores.dome,halo_spec,Stores.place,B]
  refine ⟨B,⟨fun _ ht=>?_,fun _ ht=>?_,fun _ ht=>?_,fun _ ht=>?_⟩⟩ <;> simp_all only [h,Finset.disjoint_empty_left,not_true_eq_false,Finset.notMem_empty]

private def per_cost (J : Patch) (r : ℕ) := 2*((Fintype.card (Site J.L):ℝ)*(grain r*(Fintype.card Axis)))
private lemma per_cost_nonneg (J : Patch) (r : ℕ) : 0 ≤ per_cost J r := by unfold per_cost grain; positivity

private lemma neighborhood {c f : Side} (S : StepData c f) (i : Site c) (r : ℕ) (a : Directions G f)
    (h : ∀ i, ‖a i‖ ≤ 2) : settle S i r a ≤ per_cost S.patch r := by
  change (∑ j∈members S i r, _) ≤ _
  apply le_trans (Finset.sum_le_sum (g:=fun _=> (2:ℝ)) (fun j _=>h j))
  rw [Finset.sum_const,nsmul_eq_mul]
  unfold per_cost; rw [mul_comm]; exact mul_le_mul_of_nonneg_left (saves S i r) (show 0≤(2:ℝ) by norm_num)

private lemma barrel_size {c f : Side} (S : StepData c f) (T : Tube G S) (h : P.Funds S T) (R : ℕ) (U : Config G f)
    (b : LogArray G (Cell f)) {K : ℝ} (hK : 0≤K) (hb : ∀ i, ‖b i‖ ≤ K) (i : Cell f) :
    ‖barrel T.up R U b i‖ ≤ P.top.paths*K := by
  obtain ⟨l,m,H,-⟩:= h.feeds
  obtain ⟨h1,h2,h3⟩:= H.rows i.2
  let p (l : ℕ) := (T.up.row i.2 l).2
  let q (l : ℕ) := (T.up.row i.2 l).1
  let D (i:ℕ):= |q i| * Wisps.rate P.top.width (p i).length
  let F (n:ℕ):G.Color := if (p n).length ≤ R then q n •
    G.adjoint (travel U i.1 (p n).walk) (b (Work.F03.slotFace (p n) i.1)) else 0
  have hs : Summable F := barrel_summed T.up R U b i H
  change ‖∑' n,F n‖ ≤ _
  calc
    _ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n,D n*K := by
      have he : Summable D := h2
      refine Summable.tsum_le_tsum (fun n=>?_) hs.norm (he.mul_right K)
      unfold F; split
      · rw [norm_smul,G.norm_adjoint,Real.norm_eq_abs]
        unfold D; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by have := P.top.width_pos; positivity))) (hb _) (norm_nonneg _) (h1 _)
      rw [norm_zero]; exact mul_nonneg (h1 _) hK
    _ ≤ _ := by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h3 hK

private lemma read_source {c f : Side} (S : StepData c f) (U : LogArray G (Slots S)) (i : Receipt G S) :
    |tape.symm U i| ≤ ‖U i.1‖ := by
  change |U i.1 i.2| ≤ _
  rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ (U i.1) i.2]
  simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) (U i.1)

set_option maxHeartbeats 480000 in
private lemma sources (h : J.Branches P.bind G) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=J → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
        ∀ (q : Chi) (d : ℝ),0<d → d ≤ 1 → ∀ (Y : LinkArray G (Frozen A x F)) (i : Receipt G S),
          |source T x V k (shots S x) A F q d Y i| ≤ C := by
  obtain ⟨E,hE,H⟩ := LocalJet.face_global G
  obtain ⟨B,δ,hB,hδ,hQ⟩:= earned J P.bind G h
  obtain ⟨A0,hA,HA⟩:= Work.E04.answer Work.E03.answer P
  let K := max (Real.sqrt P.top.clip.direct) P.top.paths + Real.sqrt P.bind.penalty
  have hK : 0≤K := add_nonneg ((Real.sqrt_nonneg _).trans (le_max_left ..)) (Real.sqrt_nonneg _)
  let Y0:= E*per_cost J 1+B*per_cost J (Next.Fluctuations.predReach J)
  have hY : 0≤Y0 := add_nonneg (mul_nonneg hE.le (per_cost_nonneg ..)) (mul_nonneg hB.le (per_cost_nonneg ..))
  refine ⟨slip*(K*2+A0+K*Y0), by have := slip_pos; positivity,?_⟩
  filter_upwards [(HA J.L (1:ℝ)).late, small_span J,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot J+1),
    Work.E01.fiery_le G (1:Side) (permit J),(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ),
    Work.E01.fiery_le G J.L 1,(Work.E01.largeT_tendsto G J.L).eventually (ge_mem_nhds zero_lt_one)] with x hM hN h he he' ha hb
  intro c f S T hS hs hP F A k V hV q d hd hD Y i
  have h0 : permit J*temp x ≤ δ := by simpa [fiery,betaF] using he.trans he'
  have h1 : fiery G x J.L ≤ 1 := by simpa using ha.trans hb
  have hR := hQ S hS hP.knobs F A V x hV hN (by omega) (by omega) h0
  let D := input x A F (autoShell q d V Y)
  have hz (i : Bond f) : ‖D i‖ ≤ 2 := by
    unfold D input; split
    · rename_i h; split
      · unfold autoShell; exact (patched_small q hd _).trans (by linarith)
      rw [norm_zero]; norm_num
    rw [norm_zero]; norm_num
  let W:=shots S x
  unfold source
  apply le_trans (read_source S _ _)
  unfold Rows.restrict; split
  · rename_i hh
    rw [norm_smul,Real.norm_of_nonneg slip_pos.le]
    apply mul_le_mul_of_nonneg_left _ slip_pos.le
    obtain ⟨⟨s,cell|edge⟩,j⟩:=i
    · apply le_trans (norm_add_le (faceFixed T x s V cell) (faceKick T x V D s cell))
      let V' := pull s 0 V
      obtain ⟨Z,hZ⟩:=free_plot S x (1:ℝ) (1:Config G f) V' k
      have hU : SliceSet S F (1:Config G f) := by intro p _; rfl
      obtain ⟨-, -, hl⟩ := hM c f S (congr_arg RG.Patch.L hS) hs T hP F Z (1:Config G f) k V' hU hZ
      apply add_le_add
      · unfold faceFixed; apply (norm_sub_le ..).trans (add_le_add ?_ ?_)
        · unfold Xf plotted; split
          · obtain ⟨t0,l,h,-⟩:=hP.feeds
            have hz := (fine_cut_pay h cell.1 (facade S s V 0) _ (till x) (show 0<1 by omega)).2.1
            exact hz.trans (by
              have hp : P.top.paths ≤ K := (le_max_right ..).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
              linarith only [hp])
          unfold shoot
          rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hP.high]
          exact mul_le_mul ((le_max_left ..).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))) ((G.curvature_norm _).trans (G.chord_le_two _))
            (norm_nonneg _) hK
        exact (hl.phi cell).trans (by
          rw [hS]; have hL : (1:ℝ)≤ (J.L.val:ℝ)^2 := one_le_pow₀ (by exact_mod_cast J.L.property)
          exact le_trans (mul_le_of_le_one_right (by positivity) h1) (div_le_self hA.le hL))
      have hX (p : Cell f) : ‖plaquetteJet S V s p D‖ ≤ Y0 := by
        rw [plaquetteJet,(Motion.plaquette_turn s V p (face_smooth _ _).contDiffAt).2]
        apply (H S p _ _).trans
        apply le_trans (mul_le_mul_of_nonneg_left (neighborhood S _ _ _ (by intro i; rw [Motion.in_size]; exact hz _)) hE.le)
        rw [hS]; unfold Y0; have := per_cost_nonneg J (Next.Fluctuations.predReach J); nlinarith
      unfold faceKick; split
      · apply (barrel_size P S T hP _ _ _ hY hX _).trans
        have hp : P.top.paths ≤ K := (le_max_right ..).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        exact mul_le_mul_of_nonneg_right hp hY
      rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hP.high]
      exact mul_le_mul ((le_max_left ..).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))) (hX _) (norm_nonneg _) hK
    · apply le_trans (norm_add_le (noiseFixed x V k s edge (T:=T)) (noiseKick V k D s edge))
      let V' := pull s 0 V
      obtain ⟨Z,hZ⟩:=free_plot S x (1:ℝ) (1:Config G f) V' k
      have hU : SliceSet S F (1:Config G f) := by intro p _; rfl
      obtain ⟨-, -, hl⟩ := hM c f S (congr_arg RG.Patch.L hS) hs T hP F Z (1:Config G f) k V' hU hZ
      have hp : Real.sqrt P.bind.penalty ≤ K := le_add_of_nonneg_left ((Real.sqrt_nonneg _).trans (le_max_left ..))
      apply add_le_add
      · unfold noiseFixed Tube.Z
        apply (norm_sub_le ..).trans (add_le_add ?_ ?_)
        · rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hP.knobs]
          exact mul_le_mul hp ((G.curvature_norm _).trans (G.chord_le_two _)) (norm_nonneg _) hK
        exact (hl.hot edge).trans (by rw [hS]; exact mul_le_of_le_one_right hA.le h1)
      unfold noiseKick; rw [norm_neg,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hP.knobs]
      refine mul_le_mul hp ?_ (norm_nonneg _) hK
      obtain ⟨hQ,hT,hG⟩ := hR.noise s k edge hh
      rw [blockJet,(Motion.block_turn s V edge k hT).2]
      apply (hG _).trans
      apply le_trans (mul_le_mul_of_nonneg_left (neighborhood S _ _ _ (by intro i; rw [Motion.in_size]; exact hz _)) hB.le)
      rw [hS]; unfold Y0; have := per_cost_nonneg J 1; nlinarith
  rw [norm_zero]; have := slip_pos; positivity

/-- Post-L *per key* value bound for b, real all-worlds including Y
outside charts. Does NOT yield C-small μ0. -/
lemma root_pay (G : Gauge) (J : Patch) (P : Teller G) (h : J.Branches P.bind G) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=J → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
        ∀ (q : Chi) (d : ℝ),0<d → d ≤ 1 → ∀ (Y : LinkArray G (Frozen A x F)) (i),
          |blame T x V k (shots S x) A F q d Y i| ≤ C := by
  obtain ⟨K,hK,H⟩:=sources J P h
  obtain ⟨M,hM,HM⟩:=common_move J P h
  refine ⟨M*K,mul_nonneg hM hK,?_⟩
  filter_upwards [H,HM] with x hx hh
  intro c f S T hS hR hT F A k V hV q d hd hD Y i
  exact diary (half_pos P.top.width_pos).le hK (hh S T hS hR hT F A k V hV).turn _ (hx S T hS hR hT F A k V hV q d hd hD Y) i
end value
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism
