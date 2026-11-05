import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Tariff
import YM.AnalyticNext.CUBIC_MATCH.Ledger.Figures
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Post
import YM.Extra.MULTISOURCE_BOUNDS.Layers
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Cube
import YM.Next.MAXWELL.Det
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.Gas
import YM.Next.WARD_BIN.Wake
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Valve
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Slate
import YM.PhysicalNext.SAME_SERVICE_FRESH_DETERMINANT.Orders
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Infinite
import YM.Progress.DIRECTED_RECIPE.Marks
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Gas
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.LOOP_COEFFICIENT.Guard.Velocity
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Matching
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle

/-!
# Output auxiliary residue labels

Use with value-order perturbative pieces with masks from this
serialization (see Soft.Tissue). Symmetrize the *whole* additive identity
when allotting labels and purchasing anchored cost with transformation
perm at this period. Not caring if it's regular, vanishes at identity, etc.,
since not for producing those data on the real horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Next.Rank RankCovariance Thirst Pump
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι κ : Type} {p : BudgetPoint} {τ a b : ℝ}
structure Piece (G : Gauge) (n : Side) (t : ℝ) where
  atWay : RegularAddress n
  value : Config G n→ℝ
  gauge : GaugeInvariant value
  probes : Measurable value
  look : UsesFinal t atWay.support value
  leave U : value U≠0 → Healthy t atWay.support U
lemma masksLook {f : Config G n→ℝ} {X : Support n} (ht : LocalOn X f) : UsesFinal τ X (masked τ X f):=by
  intro U V h he
  have hs : Healthy τ X U ↔ Healthy τ X V := by
    unfold Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty,he]
  by_cases H : Healthy τ X U
  · rw [masked_eq _ _ _ _ H,masked_eq _ _ _ _ (hs.1 H)]; exact ht U V h
  rw [masked_ne _ _ _ _ H,masked_ne _ _ _ _ (mt hs.2 H)]
structure Pieces (P : ι→ Piece G n p.threshold) (d : ℝ) : Prop where
  worth : ∃ f : ι→ℝ, (∀ i,0≤ f i ∧ ∀ U, ‖(P i).value U‖ ≤ f i) ∧
      ∀ x : Site n, SumBudget (fun i=> if (P i).atWay.site=x then p.mass (P i).atWay.support (f i) else 0) d
variable {X : ι→ Piece G n p.threshold} {Y : κ→ Piece G n p.threshold}
lemma Pieces.all (h : Pieces (p:=p) X a) (U : Config G n) : Summable (fun i => (X i).value U) := by
  obtain ⟨f,hf,ht⟩:= h.worth
  let H (x : Site n) i:= if (X i).atWay.site=x then p.mass (X i).atWay.support (f i) else 0
  have he (x : Site n): Summable (H x):=(ht x).2.1
  refine Summable.of_norm_bounded (summable_sum (s:=univ) (fun i _=> he i)) fun i=>?_ ; unfold H
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]; exact ((hf i).2 U).trans (p.loMass _ _ (hf i).1)
lemma Pieces.combine (h : Pieces (p:=p) X a) (g : Pieces (p:=p) Y b) : Pieces (p:=p) (Sum.elim X Y) (a+b):= by
  obtain ⟨f,hf,hb⟩:= h.worth
  obtain ⟨g,hg,h⟩:= g.worth
  refine ⟨Sum.elim f g,?_,?_⟩
  · rintro (i|i); exact hf _; exact hg _
  intro x; let y (i:ι⊕κ):= if (Sum.elim X Y i).atWay.site=x then p.mass (Sum.elim X Y i).atWay.support (Sum.elim f g i) else 0
  have hU : SumBudget (fun i : ι=> y (.inl i)) a:= hb x
  have hV : SumBudget (fun i : κ=> y (.inr i)) b:= h x
  exact ⟨fun i=> by cases i; exact hU.1 _; exact hV.1 _, Summable.sum y hU.2.1 hV.2.1,(Summable.tsum_sum (f:=y) hU.2.1 hV.2.1).trans_le (add_le_add hU.2.2 hV.2.2)⟩

lemma Pieces.eachAxis [Fintype ι] {W : ι × κ→ Piece G n p.threshold} (f : ι→ℝ) (h : ∀ i,Pieces (p:=p) (fun j=> W (i,j)) (f i)) : Pieces (p:=p) W (∑ i,f i):= by
  choose! g hg hx using fun i=> (h i).worth
  refine ⟨uncurry g, fun i=> hg i.1 i.2, fun x=> ?_⟩
  let b (i:ι × κ):= if (W i).atWay.site=x then p.mass (W i).atWay.support (g i.1 i.2) else 0
  have h (i : ι): SumBudget (fun j=>b (i,j)) (f i):= hx i x
  have hv i:0 ≤ b i:= (h i.1).1 i.2
  have hp := (summable_prod_of_nonneg hv).2 ⟨fun i=> (h i).2.1, (hasSum_fintype _).summable⟩
  exact ⟨hv,hp,hp.tsum_prod.trans_le ((tsum_fintype ..).trans_le (sum_le_sum (fun i _=> (h i).2.2)))⟩

lemma Pieces.across (h : Pieces (p:=p) X a) (ht : a≤b) : Pieces (p:=p) X b:= by
  obtain ⟨f,hf,he⟩:= h.worth; exact ⟨f,hf,fun x=> ⟨(he x).1,(he x).2.1,(he x).2.2.trans ht⟩⟩

def Piece.reweight (A : ℝ) (P : Piece G n τ) : Piece G n τ :=
  {P with
   value:= fun U=> A*P.value U
   gauge:= fun k U=> congr_arg (A*·) (P.gauge k U)
   look:= fun U V ha h=> congr_arg (A*·) (P.look U V ha h)
   probes:= measurable_const.mul P.probes
   leave U h:= P.leave U (fun he=>h (by simp [he])) }
def Piece.turn (e : Wheel n) (P : Piece G n τ): Piece G n τ where
  atWay:=⟨orient e P.atWay.site, swath e.1 e.2 P.atWay.support,mem_image_of_mem _ P.atWay.anchor⟩
  value:=P.value∘pull e.1 e.2
  gauge:= p_invar e.1 e.2 P.gauge
  look:= final_swath e.1 e.2 _ _ P.look
  probes:= P.probes.comp (continuous_pull ..).measurable
  leave _ h:= (s_healthy ..).1 (P.leave _ h)
lemma Pieces.turn (h : Pieces (p:=p) X a) (e : Wheel n) : Pieces (p:=p) (fun i=> (X i).turn e) a:=by
  obtain ⟨f,hf,hx⟩:= h.worth; refine ⟨f,fun i=> ⟨(hf i).1,fun U=> (hf i).2 _ ⟩,fun i=>?_⟩
  obtain ⟨i,rfl⟩:= (orient e).surjective i
  convert! hx i using 1; funext j; simp only [Piece.turn,BudgetPoint.mass,swath_cover,Equiv.apply_eq_iff_eq]
lemma Pieces.scaling (h : Pieces (p:=p) X a) (A : ℝ) : Pieces (p:=p) (fun i=> (X i).reweight A) (|A| *a):= by
  obtain ⟨f,hf,h⟩:= h.worth
  refine ⟨fun i=>|A| *f i,fun i=>⟨mul_nonneg (abs_nonneg _) (hf i).1,fun U=>?_⟩,fun i=>?_⟩
  · exact (abs_mul A _).trans_le (mul_le_mul_of_nonneg_left ((hf i).2 U) (abs_nonneg _))
  let g j := if (X j).atWay.site=i then p.mass (X j).atWay.support (f j) else 0
  have H (j) : (if (X j).atWay.site=i then p.mass (X j).atWay.support (|A| *f j) else 0)=|A| *g j:= by unfold g; split_ifs <;> (try unfold BudgetPoint.mass) <;> ring
  have ht : SumBudget (fun i=> |A| *g i) (|A| *a) := ⟨fun j=> mul_nonneg (abs_nonneg _) ((h i).1 _),((h i).2.1).mul_left |A|, (tsum_mul_left ..).trans_le (mul_le_mul_of_nonneg_left ((h i).2.2) (abs_nonneg _))⟩
  convert! ht using 1; funext j; exact H _
end YM.PhysicalNext.InteractingRank.Soft
