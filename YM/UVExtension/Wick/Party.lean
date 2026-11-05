import YM.UVExtension.Wick.OldGrowth
import YM.UVExtension.Lamppost.Parade

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
variable {ι : Type} [Fintype ι]
-- Axis `none` is the physical β.
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R}
def curtains (x d : ℝ) : Option ι → Set ℂ := Option.elim' (aisle x) (fun _=> Metric.ball 0 d)
abbrev Vines (ι:Type):= Plot (Option ι)
abbrev Drums (ι:Type):= Option ι → ℝ
def parade (x d : ℝ) := Lamppost.Courtyard (ι:=Option ι) (curtains x d)
def grounds (x d : ℝ) : Option ι → Set ℝ := Option.elim' (Complex.ofReal ⁻¹' aisle x) (fun _=> Metric.ball 0 d)
def grown (x q : ℝ) (z : Drums ι) := ∀ i,z i∈grounds x q i
structure Festa (Q : YM.ConnectedActivityE6.Target G P) (L:Side) {R:Rep G f} (H : Cash W x μ L Q o a T R) (V : ι→Juice G f) (ρ B:ℝ) : Prop where
  margin : 0<ρ
  bound : ρ≤B
  known : ∀ t: ℂ, t∈aisle (betaF G x L) → Nonempty (Cash W x μ L Q o a T (flight R t.re))
  kin : ∀ i:ι,∀ t∈ aisle (betaF G x L), Nonempty (Cash W x μ L Q o a T (chunk R (V i) t.re))
  mixture : ∀ z: Drums ι, grown (betaF G x L) ρ z → Nonempty (Cash W x μ L Q o a T (chunk R (blend V (z ∘ some)) (z none)))

lemma connect_aisle (x:ℝ) : Convex ℝ (aisle x):= by
  intro y hy z hz a b ha hb hab
  obtain ⟨ht,hy,hY⟩:=hy; obtain ⟨he,hz,hZ⟩:=hz
  refine ⟨?_,?_,?_⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; rcases lt_or_eq_of_le ha with h|h <;> nlinarith
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; rcases lt_or_eq_of_le ha with h|h <;> nlinarith
  rw [Complex.add_im,Complex.smul_im,Complex.smul_im]; simp only [smul_eq_mul]; calc
    _ ≤ |a| *|y.im|+|b| *|z.im|:= by simp_rw [← abs_mul]; exact abs_add_le ..
    _ < _ := by
      let P := x^(99/100:ℝ); have he : P=a*P+b*P:= by rw [← add_mul,hab,one_mul]
      rw [abs_of_nonneg ha, abs_of_nonneg hb]; change _ < P; rw [he]; rcases lt_or_eq_of_le ha with h|h
      · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hY h) (mul_le_mul_of_nonneg_left hZ.le hb)
      exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hY.le ha) (mul_lt_mul_of_pos_left hZ (by linarith))
lemma seat_in {x : ℝ} (h:0<x): (x:ℂ)∈ aisle x := by unfold aisle; simp; refine ⟨by linarith,by linarith,?_⟩; positivity
omit [Fintype ι] in
lemma marching (t : Vines ι) : t∈parade x B ↔ t none ∈ aisle x∧∀ i:ι, ‖t (some i)‖<B := by
  rw [parade,Lamppost.within]; constructor
  · intro h; exact ⟨h none,fun i=>mem_ball_zero_iff.mp (h (some i))⟩
  rintro ⟨h,ha⟩ (_|i); exact h; exact mem_ball_zero_iff.mpr (ha i)
lemma propagates {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f: Vines ι → A→ E}
    {p:(A→E)→Prop} (hP:Husk p) (hf:∀ y,Bumps (parade x B) (fun z=> f z y)) (hx:0<x) (hg:0<b) (hm:b≤B)
    (h : ∀ z:Drums ι,grown x b z → p (f (hoist z))) : ∀ v∈ parade x B,p (f v) := by
  let c: Drums ι:= Option.elim' x (fun _=>0)
  refine regatta (V:=curtains x B) (c:=c) (grounds x b) ?_ ?_ ?_ ?_ f hP hf h
  · rintro (_|i); exact Complex.continuous_ofReal.continuousAt.preimage_mem_nhds ((open_aisle x).mem_nhds (seat_in hx)); exact Metric.ball_mem_nhds 0 hg
  · rintro (_|i) t ht; exact ht
    apply mem_ball_zero_iff.mpr; rw [Complex.norm_real]; exact lt_of_lt_of_le (mem_ball_zero_iff.mp ht) hm
  · rintro (_|i); exact open_aisle _; exact Metric.isOpen_ball
  rintro (_|i); exact (connect_aisle x).isPreconnected; exact (convex_ball (0:ℂ) B).isPreconnected

lemma equals_hoist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f g: Vines ι → E}
    (hf:Bumps (parade x B) f) (ht:Bumps (parade x B) g) (hx:0<x) (hg:0<b) (hm:b≤B)
    (h:∀ z:Drums ι,grown x b z → f (hoist z)=g (hoist z)) : Set.EqOn f g (parade x B):= by
  let F (z) (u:Bool):E:= if u then f z else g z
  intro z hz; exact propagates (f:=F) (Husk.audit true false) (by rintro (_|_); exact ht; exact hf) hx hg hm h z hz
end YM.UVExtension.Wick
