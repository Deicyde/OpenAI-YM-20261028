import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Gust
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Osmote

/-!
# Joint interval utilities and V derivative receipt on log roots

Here T(X) doesn't inspect away inverse validity. Keep determinant jets grouped
 until one argument known. For derivative values budget with `Brush` weighted
 principal Pad. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen    Vine Tablet Metric Pulse Itinerary
variable {v z r Q s y η γ : ℝ} {j n m B : ℕ} {U : E → Config G c} {x : E}
variable (D : Window (along (G:=G) S) B) (A : E → Pulse.Itinerary.Mat f G)
variable (h : Allow (A x) (along S) m η r Q) (p : Tablet j γ v z A (along S) (along S) x)
variable (he : γ ≤ retain η r Q) (hp : Torch η r Q)

lemma per_entry {E α β ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {k : WithTop ℕ∞} (A : E→ Matrix α ι ℝ) (B : E→ Matrix ι β ℝ) (o : E) (i j)
    (he : ∀ z, ContDiffAt ℝ k (fun x=> A x i z) o) (h : ∀ z, ContDiffAt ℝ k (fun x=> B x z j) o) :
    ContDiffAt ℝ k (fun x=> (A x*B x) i j) o := by simp_rw [Matrix.mul_apply]; exact ContDiffAt.sum fun i _=> (he i).mul (h i)
lemma orbit {k : WithTop ℕ∞} (p : ∀ i j, ContDiffAt ℝ k (fun x=> A x i j) x) (h : ∀ i,
    IsUnit (D.principal (A x) i).det) i j : ContDiffAt ℝ k (fun x=> D.pad (A x) i j) x := by
  unfold Window.pad; simp only [of_apply]; split_ifs with he
  · apply jetBack (A:=fun x=> D.principal (A x) j) (fun i j=> p i.val j.val) (h j)
  exact contDiffAt_const
include h hp p
lemma joyful (q : ℝ) (hk : q∈Set.Icc (0:ℝ) 1) :
    let g (i : E×ℝ):= glide (A i.1) i.2
    ∀ i k, ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun x=>g x i k) (x,q) ∧ ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun x=> D.pad (g x) i k) (x,q) := by
  intro g
  have hh i k : ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun x=>g x i k) (x,q) := by
    have hx:= (p.singular i k).smooth.comp (f:= Prod.fst) (x,q) contDiffAt_fst
    unfold g glide; simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply]
    exact contDiffAt_const.add (contDiffAt_snd.smul (hx.sub contDiffAt_const))
  intro i k; exact ⟨hh i k,orbit D g hh (fun i=> isUnit_det_of_right_inverse (((h.glide hp.hv hp.hQ q hk).sub
    (Embedding.subtype (·∈D.take i))).initial.1)) i k⟩

include he
variable [FiniteDimensional ℝ E]

def crownP (j B m : ℕ) (G : Gauge) (η r Q v : ℝ) := (Fintype.card G.ColorIndex:ℝ)*((v+1)*facePrice j B m (1+(v+1)) (payE η r Q m))
lemma plotsB (i : Bond f) : Brush j (crownP j B m G η r Q v) (z+driftP j z)
    (fun x=> Pulse.Batch.joint (A x) D i) x := by
  unfold Batch.joint
  have hh (u : G.ColorIndex) : Brush j ((v+1)*facePrice j B m (1+(v+1)) (payE η r Q m)) (z+driftP j z)
      (fun x=> localBase D (A x) (i,u)) x := by
    unfold localBase lact; simp only [intensity,pow_zero,mul_one]
    refine yogic (U:=fun x q=> ((A x-1)* D.pad (glide (A x) q)) (i,u) (i,u)) ?_ ?_
    · intro q hq
      obtain hh:= joyful D A h p hp q hq
      exact per_entry (fun z=>A (Prod.fst z)-1) (fun z=> D.pad (glide (A z.1) z.2)) (x,q) _ _
        (fun j=> ((p.singular (i,u) j).smooth.comp (f:=Prod.fst) (x,q) contDiffAt_fst).sub contDiffAt_const)
          (fun j=> (hh _ _).2)
    intro q hq; have hh:= p.joined (Tablet.fixed 1 (one_pay _ _) p.scale zero_le_one p.pos).mirror
    exact (hh.enjoin (padjets D (thunder p _ hq) (h.glide hp.hv hp.hQ q hq) he)).singular ..
  have he : 0 ≤ z+driftP j z := add_nonneg p.pos (mul_nonneg (Nat.cast_nonneg _) p.pos)
  apply (Brush.spree _ _ _ he (fun u _ => hh u)).climb _ le_rfl
  simp [crownP]
end YM.ConnectedActivityE6.Blaze.Vine
