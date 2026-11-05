import YM.UVExtension.Steady.Cinemas
import YM.UVExtension.Reward.Lights

/-!
 Concerted paths for UV steps. Width can be actual.
 Specifying one cutoff and layout through level m and literal HEq across
 normalized paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Pressure Precision Push.AbsoluteSums Finset ConnectedActivityE6
open Reward
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge} {ι κ π : Type*}{v:Filter ι} {R:ι→ PathData G} {σ:ℝ} {g:PathData G}

-- allow all non-bottom/grand filters. accounting
structure Revenues (v:Filter ι)(σ:ℝ)(R:ι→PathData G)(g:PathData G): Prop where
  pos :0<σ
  slots : ∀ (i:ι) j k,((R i).row j k).2=(g.row j k).2
  layout : ∀ i, (∀ k,((R i).loop k).leg=(g.loop k).leg)∧ (∀ k,((R i).cubic k).leg=(g.cubic k).leg)∧∀ k,((R i).quartic k).leg=(g.quartic k).leg
  cops : ∀ i, ∃ W C B,(R i).Bounds W σ C B
  gap : ∀ a:ℝ, 0<a→ ∀ᶠ i in v,
      (∀ j,SumBudget (fun z=>|((R i).row j z).1-(g.row j z).1| * Real.exp (σ*(g.row j z).2.length)) a) ∧ Levies (R i).loop g.loop σ a∧ Levies (R i).cubic g.cubic σ a ∧ Levies (R i).quartic g.quartic σ a
namespace Revenues
variable (p: Revenues v σ R g)
include p
lemma incurs {qq' : Filter κ}{T:κ→ι}(hp:Tendsto T qq' v): Revenues qq' σ (fun n=>R (T n)) g:=
   ⟨p.pos,fun i=>p.slots (T i),fun i=>p.layout (T i),fun i=>p.cops (T i),fun ε h=>hp.eventually (p.gap _ h)⟩
lemma fees (k : PlaqAxes) [NeBot v] : let t i z:=|((R i).row k z).1| *Real.exp (σ*(g.row k z).2.length); let T z:= |(g.row k z).1| * Real.exp (σ*(g.row k z).2.length); Summable T∧Swift v t:=by
  intro t T
  let q n z:= |((R n).row k z).1-(g.row k z).1| * Real.exp (σ*(g.row k z).2.length)
  have he i : Summable (t i) := by
    obtain ⟨W,C,B,H⟩:= p.cops i; unfold t; simp_rw [← p.slots i]; exact (H.rows k).2.1
  obtain ⟨r,hr⟩:= (p.gap 1 zero_lt_one).exists
  have hp : ∃ x, SumBudget T x:= by
    have h:= hr.1 k; have hv : SumBudget (t r) (∑' i,t r i):= ⟨fun i=>by unfold t; positivity,he _,le_rfl⟩
    refine ⟨_,budget_mono (budget_plus h hv) (fun i=>by unfold T; positivity) ?_⟩; intro i; unfold T t; rw [← add_mul]; refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [abs_sub_comm]; exact (norm_le_norm_add_norm_sub' ((g.row k i).1) (((R r).row k i).1)).trans_eq (add_comm ..)
  obtain ⟨s,hs⟩:=hp
  have h n i:t n i≤ T i+ q n i:=by unfold t T q; rw [← add_mul]; exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub' (((R n).row k i).1) ((g.row k i).1)) (Real.exp_pos _).le
  refine ⟨hs.2.1, Swift.absorbs ⟨s+1,(p.gap 1 zero_lt_one).mono fun i hi=> budget_mono (budget_plus hs (hi.1 k)) (fun j=>by unfold t; positivity) (h _)⟩ fun ε hε=> ?_⟩
  exact ⟨_, q, Swift.nil T hs, (p.gap ε hε).mono fun i hi=> hi.1 k, Eventually.of_forall h⟩
lemma fees' (j:PlaqAxes) [NeBot v] : Swift v (fun i z=> |((R i).row j z).1|):= by
    have he:=p.pos; apply (p.fees j).2.le; filter_upwards with i z; exact ⟨abs_nonneg _, le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))⟩
lemma starts (j:PlaqAxes) (k:ℕ): Tendsto (fun i=> ((R i).row j k).1) v (𝓝 ((g.row j k).1)):=by
    rw [Metric.tendsto_nhds]; intro ε he; filter_upwards [p.gap _ (half_pos he)] with i hi
    have hh:=budget_single (hi.1 j) k; have h:=p.pos; apply lt_of_le_of_lt _ (hh.trans_lt (half_lt_self he)); rw [Real.dist_eq]; exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
omit p
section terms
variable [NeBot v] {d:ℕ}{g:ℕ→Atom G d} {R:ι→ℕ→ Atom G d} (h:∀ i, (∀ j, (R i j).leg=(g j).leg)∧ ∃ B, SumBudget (fun j=> (R i j).budget σ) B)
   (q:∀ ε:ℝ,0<ε→∀ᶠ n in v,Levies (R n) g σ ε) (hp:0<σ)
include h q hp
lemma tubs : (∀ i (j:Fin d→G.ColorIndex), Tendsto (fun n=>(R n i).coeff j) v (𝓝 ((g i).coeff j)))∧Swift v (fun n i=> (R n i).budget σ) :=by
  let H i j:={R i j with coeff:= (R i j).coeff-(g j).coeff}
  have hA n i :(H n i).length=(g i).length:= by unfold H Atom.length; dsimp only; rw [(h n).1]
  have hB n i : (R n i).length=(g i).length:= hA n i
  refine ⟨fun i j=>Metric.tendsto_nhds.mpr (fun ε he=> ?_),?_⟩
  · filter_upwards [q _ (half_pos he)] with n hn; refine lt_of_le_of_lt ?_ (((H n i).lower_budget _ hp).trans (budget_single hn i)|>.trans_lt (half_lt_self he)); exact Finset.single_le_sum (f:=fun j=>|(H n i).coeff j|) (fun j _=>abs_nonneg _) (mem_univ j) -- comp
  let f n i:= (R n i).budget σ; let b n i := (H n i).budget σ; let B i:= (g i).budget σ
  obtain ⟨n,hn⟩:= (q 1 zero_lt_one).exists; obtain ⟨r,hr⟩:= (h n).2
  have hZ: SumBudget B (1+r):=by
      apply budget_mono (budget_plus hn hr) (fun i=>by unfold B Atom.budget Atom.magnitude; positivity); intro i; change _ ≤ b n i+ f n i; unfold B b f Atom.budget; rw [hA,hB,← add_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      unfold Atom.magnitude; rw [← Finset.sum_add_distrib]; refine sum_le_sum (fun j _=> ?_); unfold H; dsimp only [Pi.sub_apply]; rw [abs_sub_comm]; exact (norm_le_norm_add_norm_sub' ((g i).coeff j) ((R n i).coeff j)).trans_eq (add_comm ..)
  have he n i: f n i ≤ B i+ b n i:= by
      unfold f B b Atom.budget; rw [hA,hB,← add_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      unfold Atom.magnitude; rw [← Finset.sum_add_distrib]; refine sum_le_sum (fun j _=>?_) ; exact norm_le_norm_add_norm_sub' ((R n i).coeff j) ((g i).coeff j)
  exact Swift.absorbs ⟨(1+r)+1,(q 1 zero_lt_one).mono fun i hi=> budget_mono (budget_plus hZ hi) (fun x=>by unfold Atom.budget Atom.magnitude; positivity) (he _)⟩ fun ε hε=> ⟨_, b, Swift.nil B hZ, q ε hε, Eventually.of_forall he⟩
end terms
include p
variable (g)
def bulk (v:Filter ι)(R:ι→PathData G)(d:ℕ)(L:PathData G→ℕ→Atom G d) : Prop:= (∀ j y,Tendsto (fun n=>(L (R n) j).coeff y) v (𝓝 ((L g j).coeff y)))∧ Swift v (fun i j=> (L (R i) j).budget σ)
variable {g} [NeBot v]
lemma parked₁: bulk (σ:=σ) g v R 2 PathData.loop:=
  tubs (fun i=> ⟨(p.layout i).1,let ⟨_,_,_,H⟩:= p.cops i; ⟨_,H.two⟩⟩) (fun ε he=>(p.gap ε he).mono fun _ hi=>hi.2.1) p.pos
lemma parked₂: bulk (σ:=σ) g v R 3 PathData.cubic:=
  tubs (fun i=> ⟨(p.layout i).2.1, let ⟨_,_,_,H⟩:= p.cops i; ⟨_,H.three⟩⟩) (fun ε he=>(p.gap ε he).mono fun _ hi=>hi.2.2.1) p.pos
lemma parked₃: bulk (σ:=σ) g v R 4 PathData.quartic:=
  tubs (fun i=> ⟨(p.layout i).2.2,let ⟨_,_,_,H⟩:= p.cops i; ⟨_,H.four⟩⟩) (fun ε he=>(p.gap ε he).mono fun _ hi=>hi.2.2.2) p.pos
end Revenues
end YM.UVExtension.Steady
