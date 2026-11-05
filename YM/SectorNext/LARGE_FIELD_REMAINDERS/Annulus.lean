import YM.Push.SECTOR_MEASURE.Bounds
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Collar
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Recovery


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# The actual annulus payment, on ANY selections and all merged owners

Each exterior address or collection, read in its own orientation. Costs per
seed even on one connected packet at local prerequisites with distant choices
arbitrary. β removed, show even all β band prices can be bought before L
(activation after L). Terms included with nonpositive sign in exponent in that
use! No base tails included. To use with the physical a assigned by current
step, supply `Window.charts` on just the selected addresses, also permissible
from retaining extended/frozen charts provided they *give these inputs* on all
needed stencils at the application (not a numerical approximation); e.g., from
caller proof on sector. No postulate on how to compare core overlaps or prove
formal covariance, etc.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}
private lemma uniq {A B : Patch} (h : A.L=B.L) (ht : A.J=B.J) : A=B := by cases A; cases B; congr

set_option maxHeartbeats 800000 in
/-- The quote here for $H_D$, D fixed and paid once. Larger D also with its own
entrance thresholds from this theorem. Can demand alongside Joint order.
`Q.rows` deliberately unrestricted (only nonnegative and no selection needed).
This is before assigning deterministic ownership of terms if doing
reconnection; caller in particular still ensures `charges` requests only on
*exterior* and the same true trees/tags with these same local hypotheses.
Note e allows arbitrary additional B powers while STILL o(1) after multiplication
by β (much smaller than scale required by the grant). This quantifies only the ROW
losses, not costs such as counting frozen $s_g$ at those sites.
-/
lemma annulus_pay (P : Teller G) (L : Side) (W K : ℝ) (hw : 0<W) (D : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℝ → ℝ,
      (∀ᶠ x in atTop, 0 ≤ e x) ∧ (∀ n, Tendsto (fun x => b x^n * y G L x * e x) atTop (𝓝 0)) ∧
      ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L = L → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (O A : Stores S) (F : Forest S.ratio) (U : Config G f) (k : S.Choices) (V : Config G c),
        SliceSet S F U → Wide O A D x W U k V →
        ∃ a : Directions G f, (∀ i∈F.trunks,a i=0) ∧
          ∀ (Q H : Window S), H.selects Q → Q.annulus O A D (radiusB x) → Q.charts U V a C x ∧
            H.written T x k V a ∧ -(e x*O.shares) ≤ Q.work T x U k V - H.extract T x k V a ∧
            ∀ (a' : Directions G f), H.charts U V a' K x →
              H.written T x k V a' ∧ -(e x*O.shares) ≤ Q.work T x U k V - H.extract T x k V a' := by
  obtain ⟨C,hC,H⟩ := cleans_at P L W hw
  obtain ⟨e,he,hl,h⟩ := coat P L C hC W
  let N := (Fintype.card PlaqAxes : ℝ); let M := (Fintype.card Axis:ℝ)
  let X : ℝ := ((L.val:ℝ)^4*N + M + N) * (4*((D+D+1:ℕ):ℝ)^4)
  have hX : 0≤X := by unfold X M N; positivity
  let E x := X*(b x)^4*e x
  refine ⟨C,hC,E,?_,fun n => ?_,?_⟩
  · filter_upwards [he] with x hx; unfold E; positivity
  · have ht := (hl (n+4)).const_mul X; rw [mul_zero] at ht; exact ht.congr fun x => by unfold E; rw [pow_add]; ring
  have h1 : Tendsto (fun x => max K C * fiery G x L) atTop (𝓝 0) := by
    have ht := (tally_g G L 0 1).const_mul (max K C); rw [mul_zero] at ht; exact ht.congr fun x => by rw [fi]; ring
  by_cases hlegal : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap
  · refine Eventually.of_forall fun b c f S T hL hv hT => ?_ -- implicit
    exact (hlegal ⟨S.patch,hL,hT.atStep,hT.kernel⟩).elim
  obtain ⟨P0,hL,hD,-⟩ := hlegal
  filter_upwards [H,h,he,h1.eventually (gt_mem_nhds (Next.Foundations.chart_ok G).patch), (year G L).eventually_gt_atTop 0,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(predReach P0+10))] with x hx hy he hK hY hR
  intro c f S T hL' hh hT O A F U k V hi ha
  obtain ⟨a,h0,H⟩ := hx c f S T hL' hh hT D F O A U k V hi ha
  have h y (h : inSweep O A D (radiusB x) y) := hy c f S T hL' hh hT D F O A U k V y a hi (H y h) h ha
  have hR1 : predReach S.patch≤thin x := by unfold thin; rw [uniq (hL'.trans hL.symm) (hT.atStep.trans hD.symm)]; omega
  rw [← hL'] at hY hK
  have hTY : 0<fiery G x S.patch.L := Work.E09.temp_pos hY
  refine ⟨a,h0,?_⟩; intro Q Z hq hA
  let R := (Q.face.card:ℝ)+(Q.noise.card:ℝ)+(Q.coarse.card:ℝ)
  obtain ⟨hR0,hR'0,hR2⟩ := Q.torus (x:=x) hA
  have hRS : R ≤ X*b x^4 * O.shares := by unfold R; apply (add_le_add (add_le_add hR0 hR'0) hR2).trans_eq; unfold X N M; rw [hL']; ring
  let T0 := replica S.ratio V
  let v := (till x)
  let t := temp x
  let s := fiery G x S.patch.L
  have ha i (hh : i∈Q.face) : Returns T x (e x) U V k a (S.ratio.parent (i:Cell f).1) := h _ (hA.1 _ hh)
  have hb i (hh : i∈Q.noise) : Returns T x (e x) U V k a (i:Bond c).1 := h _ (hA.2.1 _ hh)
  have hz i (hh : i∈Q.coarse) : Returns T x (e x) U V k a (i:Cell c).1 := h _ (hA.2.2 _ hh)
  have Hq i (he : inSweep O A D (radiusB x) i) : PatchInputs (S:=S) U V a C x i := fun b hp =>
    ⟨((H i he).chart b hp).1,((H i he).chart b hp).2.1⟩
  let υ := S.prediction U k
  have hp : -(E x*O.shares) ≤ Q.work T x U k V - Z.extract T x k V a := by
    have hfa : ∑ i∈Q.face, (-e x) ≤ (∑ i∈Q.face,T.workF v U V s t i)-(∑ i∈Z.face,squareP T v t V T0 a i) := by
      apply (Finset.sum_le_sum (s:=Q.face) fun i hi => ((ha i hi).face i rfl).2).trans
      rw [Finset.sum_sub_distrib]; apply sub_le_sub_left
      exact Finset.sum_le_sum_of_subset_of_nonneg hq.1 fun i _ _ => by unfold squareP; positivity
    have hfr : ∑ i∈Q.noise, (-e x) ≤ (∑ i∈Q.noise,T.workI v υ V t i)-(∑ i∈Z.noise,squareQ T v t V T0 k a i) := by
      apply (Finset.sum_le_sum (s:=Q.noise) fun i hi => (hb i hi).noise i rfl).trans
      rw [Finset.sum_sub_distrib]; apply sub_le_sub_left
      exact Finset.sum_le_sum_of_subset_of_nonneg hq.2 fun i _ _ => by unfold squareQ; positivity
    have hfc := Finset.sum_le_sum (s:=Q.coarse) fun i hi => (hz i hi).coarse i rfl
    have hl : 0 ≤ ∑ i∈Q.rows,T.workN v V t i := by unfold workN; positivity
    have hh := mul_le_mul_of_nonneg_right hRS he
    simp only [Finset.sum_neg_distrib,Finset.sum_const,nsmul_eq_mul] at hfa hfr hfc
    unfold Window.work onWindow Window.extract υ v t s T0 E R at *
    linarith only [hh,hl,hfc,hfa,hfr]
  refine ⟨⟨fun i hi => Hq _ (hA.1 _ hi),fun i hi => Hq _ (hA.2.1 _ hi)⟩,?_,hp,?_⟩
  · exact ⟨fun i hi => ⟨((ha i (hq.1 hi)).face i rfl).1,(ha i (hq.1 hi)).cover i rfl⟩, fun i hi => (hb i (hq.2 hi)).Qline i rfl⟩
  intro b hw
  have hV i (f) (H' : inSweep O A D (radiusB x) i) := patch_agreed T U V b a k hTY hK (by unfold till thin; omega) hR1 (funds_branch hT) f (Hq _ H')
  have hF i (hi : i∈Z.face) := (hV (S.ratio.parent i.1) (hw.1 _ hi) (hA.1 _ (hq.1 hi))).1 i rfl
  have hG i (hi : i∈Z.noise) := (hV i.1 (hw.2 _ hi) (hA.2.1 _ (hq.2 hi))).2 i rfl
  have ht : Z.extract T x k V b = Z.extract T x k V a := by
    unfold Window.extract; exact congr_arg₂ (fun (i j : ℝ) => i+j) (Finset.sum_congr (rfl : Z.face=Z.face) (fun i hi => (hF i hi).1)) (Finset.sum_congr (rfl : Z.noise=Z.noise) (fun i hi => (hG i hi).1))
  refine ⟨?_,?_⟩
  swap; rw [ht]; exact hp
  refine ⟨fun i hi => ?_,fun i hi => ?_⟩
  · obtain ⟨h1,h2,h3⟩ := (hF i hi).2
    obtain ⟨h4,h5⟩ := (ha i (hq.1 hi)).cover i rfl
    dsimp only at h2 h3 ⊢; refine ⟨by rw [h1]; exact ((ha i (hq.1 hi)).face i rfl).1, by rw [h2]; exact h4, fun j hj => ?_⟩; rw [h3 j hj]; exact h5 j hj
  obtain hq' := (hb i (hq.2 hi)).Qline i rfl
  dsimp only; unfold qVar; rw [(hG i hi).2]; exact hq'
end YM.SectorNext.Remainder.Affine
