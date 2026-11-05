import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cupola

/-!
# Parts of the full Packet envelope

 Jet scalar, permit factors once for K membership; normalize tickets relative
 to assigned positions. d,w Vol inputs NOT raised to β in the stamina; absorb
 polynomial over shares in actual seed capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v : ℝ} {j n l : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}

lemma fever (f : E→ℝ) (p : Brush j b 1 (fun t=> f t-f x) x) (h : Brush j a 1 Real.exp 0) :
    Brush j (Real.exp (f x)) ((1+j.factorial*a)*(1+b)) (fun y=> Real.exp (f y)) x := by
  have he:x=x:=rfl
  let g t:=Real.exp (f t-f x); have hp : g x=1 := by unfold g; rw [sub_self, Real.exp_zero]
  have hh:= p.pine (by rw [sub_self]; exact h : Brush j _ 1 Real.exp (f x-f x)); rw [mul_one] at hh
  have hv:= (hh.exalt (show ‖g x‖≤1 by rw [hp,norm_one])).smul (Real.exp (f x))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,mul_one] at hv; apply hv.shimmy
  refine Eventually.of_forall fun i=>?_ ; change Real.exp (f i)= _ * _; rw [← Real.exp_add]; ring_nf

namespace Silica.Clutch
lemma dynam (G : Gauge) (L : Side) (χ : Chi) (j : ℕ) {V v : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (he : Rate G L (-(1/2)) v) (b W : ℝ) :
    ∃ C, Rate G L 0 C ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
    (Q : Coat T F), Q.x=x → S.patch.L=L → Q.χ=χ → 0 < W*Q.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E)
    (Z: E→ Config G c) (u : E→ Directions G f) (z : Air f G) (w : E → Air f G)
    (R : Rep G f), Mode Z y j (v x) → Clutch Q z b R.beta (V x) y j Z u w →
      ∀ (A: Stores S) (U : Config G f) (k : Finset ℕ), let d:=300*Q.B; let Z':=Q.plaza (A.dome (304*Q.B))
      Brush j (Real.exp (tollFee S.patch (300*Q.B)*A.shares)) (|C x| *A.shares)
        (fun i=> Contract.order R k (vias S A d) U * tickets A d U Q.k * profiles A Q.χ d Q.x W U Q.k (Z i)* Q.enforce b (u i) Z') y := by
  obtain ⟨C,hC,hp⟩:=kernels G L χ h j b
  obtain ⟨Y,hY,hX⟩:=notches G L χ j he W
  let f x:= (Animals.ballCost (300*radiusB x+2):ℝ)*Fintype.card Axis * |Y x|
  let g x:= (Animals.ballCost (304*radiusB x+2):ℝ)*Itinerary.density L* |C x|
  have hz (P : ℝ→ℝ) (p : Rate G L 0 P) := p.compare (v:=fun x=>|P x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  have hf : Rate G L 0 f := by convert (((width_rate G L 300 2).mul_right _).mul (hz _ hY)) using 1; ring
  have hg : Rate G L 0 g := by convert (((width_rate G L 304 2).mul_right _).mul (hz _ hC)) using 1; ring
  refine ⟨_,hf.add hg,?_⟩
  filter_upwards [hp,hX] with x hx hp c f' S T F Q hQ hL hχ hW E _ _ y Z u z w R he hC A U k d Y'
  subst χ; subst x
  have ht := hp _ _ S T F Q rfl rfl hL hW U E Z y he
  have hf := hx _ _ S T F Q rfl hL rfl hC.pulse E z b R.beta y Z u w hC
  have ho : (readBonds (A.dome d)).card ≤ A.shares*Animals.ballCost (300*Q.B+2)*Fintype.card Axis := readBonds_count ..
  have hτ:Y'.card ≤ A.shares*Animals.ballCost (304*Q.B+2)*Itinerary.density L := by rw [← hL]; exact (Finset.card_le_card
    (show Y'⊆ visit A (304*Q.B) from fun i hi=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2.2⟩)).trans (touch_price S ..)
  let t := ∏ i∈readFine (A.dome d) S, fine A Q.χ i Q.t U
  have ht' i : fine A Q.χ i Q.t U∈ Set.Icc 0 1:= fine_range ..
  have hk : 0≤ t := Finset.prod_nonneg fun i _=> (ht' i).1; have ht':t≤1:=Finset.prod_le_one (fun i _=> (ht' i).1) (fun i _=> (ht' i).2)
  let c:= Contract.order R k (vias S A d) U
  have h := Contract.valid_pay R k (vias S A d) U
  have hu : c*tickets A d U Q.k≤ Real.exp (tollFee S.patch d *A.shares) := (mul_le_of_le_one_left (ticket_nonneg ..) h.2).trans
    (Mask.tickets_le ..)
  have he:= Brush.all_prod _ (fun i y=>Q.cone b (u y) i) _ _ (fun i (_:i∈Y')=> hf i)
  simp only [prod_const_one,sum_const,nsmul_eq_mul] at he
  have hX:= Brush.all_prod _ (fun i y => noise A Q.χ i Q.t W U Q.k (Z y)) _ _
    (fun i (_:i∈ readBonds (A.dome d))=> ht i A); simp only [prod_const_one,sum_const,nsmul_eq_mul] at hX
  apply (((Brush.certified (k:=j) (le_refl 0) (c*tickets A d U Q.k)).paints (((Brush.certified (le_refl 0) t).climb (show ‖t‖ ≤ 1 from (Real.norm_of_nonneg hk).trans_le ht') le_rfl).paints hX)).paints he).climb
  · rw [one_mul,mul_one,mul_one,Real.norm_of_nonneg (mul_nonneg h.1 (ticket_nonneg ..))]; exact hu
  rw [zero_add,zero_add]
  refine (add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ho) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hτ) (abs_nonneg _))).trans ((le_of_eq ?_).trans
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)))
  dsimp only [f,g]; unfold Coat.B; push_cast; ring
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
