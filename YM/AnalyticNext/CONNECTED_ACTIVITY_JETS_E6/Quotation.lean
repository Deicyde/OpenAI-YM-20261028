import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Depot

/-!
# Optical Offer: non-packet gas letters

Overlap costs inherit prescribed exponents. b tolerance any strictly looser
half-power; leave station cutoff derivative κ explicit, move to sharp L only
in future E-contraction. Alarm integrated separately; stamp lengths task.
Addresses pricing independent of F,V/Y,z at all points--in particular no
selection-by-hTag. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Coat Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- Sufficient (uniform across matrices and outputs at this T). Can put in
Post heading for service spending. Not assumption about integrated size.
-/
structure Stamped (P : Teller G) (L : Side) (η r Q Y W γ K C E x : ℝ) (T : Tube G S) : Prop where
  serves : ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → X.width=K → X.manifest →
    Port P L η r Q Y X ∧ Tender x W γ K C E X

/-- Dummy at same R, theta. -/
def dum (T : Tube G S) (x K : ℝ) (F : Forest S.ratio) : Coat T F :=
    ⟨⟨∅,∅,∅⟩,x,Chi.canonical,K,1, Classical.arbitrary _,fun _ => 1⟩
lemma dum_lat (T : Tube G S) (x K : ℝ) (F : Forest S.ratio) : (dum T x K F).manifest :=
    (dum T x K F).bowed (temp_nonneg _)

/-- price with ALL ancillary expenses here; hits before quotes combining
transcendental exponents. No loss extracted from changing Beta after this.
Keep *both* raw and Mayer absolute. -/
structure Offer (v ε d d' W a K x : ℝ) (Ñ : ChartRatio G) (T : Tube G S) (R : Rep G f) (l : ℕ) : Prop where
  gifts : ∃ (w : ℕ→ℝ) (y : LogIndex c f→ℝ),
    Sales (radiusB x) v ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) d' ∧
    Sales (radiusB x) v ε (roadway T R (radiusB x) l) y (exCharge T R) d ∧
    ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → X.width=K → X.manifest →
      (∀ i U, |X.bag R a U i| ≤ w i) ∧ ∀ p z, |X.farLog R a Ñ z p| ≤ y p ∧
        |X.raiseAir R a Ñ z p| ≤ y p

/-- May purchase both hopes from actual inputs. b<0. -/
theorem recommends (P : Teller G) {Ñ : ChartRatio G} (h : LocalRatio Ñ) {ε v : ℝ}
    (hp : 4*ε<P.top.supportExponent) (hP : 8*ε<P.top.width) (hQ : 8*ε<P.below.width) (hv : 0≤v) (he : 0<ε)
    (l : ℕ) (hl : 4≤l) {A : ℝ} (hA : 0<A) :
    ∃ n : ℕ,∀ L : Side,n≤L.val→ ∀ (D : Patch), D.Branches P.bind G → ∀ η r Q Y W γ K C a b u : ℝ, 0<C →
      0<a → -(1/2:ℝ) < b → b<0 → ∀ E : ℝ→ℝ, Rate G L (-1) E → Torch η r Q →
      ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → S.patch.L=L → Stamped P L η r Q Y W γ K C (|E x|) x T → Stamp T →
      (∀ w, Maximum A T x w) → ∀ R : Rep G f, Intake P T x R →
        Offer v ε (betaF G x L ^ b) (betaF G x L ^ u) W a K x Ñ T R l := by
  obtain ⟨n,hN⟩ := Raw.inherit_bills G P l he hv hp hP hQ
  refine ⟨n,fun L hL D hd η r Q Y W γ K C a b u hc ha h₁ h₂ E hE hT => ?_⟩
  obtain ⟨M,J,N,h₃,H₁⟩ := dynasty (W:=W) (γ:=γ) (K:=K) (Y:=Y) P L hT l hl ha hc (b:=-(1/2))
    (ε:=ε) (show Rate G L _ _ from hE.weaken (by norm_num)) hv
  obtain ⟨Z,X,h₄,H₂⟩ := minorizes P L D hd A Y a hA ha hT h l v ε hv
  obtain ⟨s,hs,hh⟩ := exists_between h₁
  let T x := betaF G x L ^ s+(X x+N x)
  have ht : Rate G L s T := Rate.power.add ((h₄.add h₃).weaken hs.le)
  filter_upwards [H₁,H₂, hN L hL s hs u, ht.below (hh.trans h₂) 1 zero_lt_one, (ht.mul_left 2) b hh]
    with x hx hy hz hu hh c f S T' hS H hθ hZ hm R hR
  constructor
  obtain ⟨w,hw,hg,k,hk,hf⟩ := hz _ _ _ _ R H hR
  let F := Classical.choice (Tree.select S.ratio S.patch.odd_side)
  let Y' := dum T' x K F
  have hs := hθ.serves F Y' rfl rfl (dum_lat ..)
  have hp := (hx _ _ _ _ F Y' rfl H hs.1 hs.2).1
  have hy' := (hy _ _ _ _ F Y' rfl hS H hs.1 hZ hm).1
  let b₀ := Sum.elim w (Sum.elim (fun _i : Miniature c f=>Z x) (specials G L (radiusB x) η r Q (M x) (J x) S))
  let y i := 2*b₀ i
  have ht : Sales (radiusB x) v ε (roadway T' R (radiusB x) l) b₀ (exCharge T' R) (T x) :=
    hg.together (hy'.together hp)
  refine ⟨k,y,hf, (ht.shift (z:=y) (show 0≤ (2:ℝ) by norm_num) (fun i=>mul_nonneg (by norm_num) (ht.nonneg _))
    (fun _=>le_rfl)).raise ((le_abs_self _).trans hh),fun F X heq hy'' hr => ?_⟩
  obtain ⟨hq,hyx⟩ := hθ.serves F X heq hy'' hr
  have hh {a b c : ℝ} (h : |a|≤b) (hc : c∈Set.Icc 0 1) : |a*c| ≤ b := by rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) ((abs_of_nonneg hc.1).trans_le hc.2)).trans h
  have hβ := hR.window.2; rw [H] at hβ
  refine ⟨fun i U => hh (hk i _) (X.conserve ..), fun i z => ?_⟩
  have hf' : b₀ i≤1 := (ht.atom hv he.le i (exChart ..)).trans ((le_abs_self _).trans hu)
  have hu' : |X.farLog R a Ñ z i| ≤ b₀ i := by
    rcases i with i|i|i
    · have hf i := X.conserve (X.plaza (Raw.space T' 0 X.B R i)) (2*a) (X.liftA R.beta z)
      have H := hw (X.input (X.liftA R.beta z)) X.V i
      rw [← heq] at H; exact hh H (hf i)
    · exact (hy c f S T' F X heq hS H hq hZ hm).2 _ i R.beta hR.positive hβ
    exact (hx c f S T' F X heq H hq hyx).2 R.beta hR.positive hβ z i
  exact ⟨hu'.trans (le_mul_of_one_le_left (ht.nonneg _) (by norm_num)),by
    unfold raiseAir; simpa only [mul_one] using! Raw.mayer_abs hu' hf' (show |(1:ℝ)|≤1 by norm_num)⟩
end YM.ConnectedActivityE6
