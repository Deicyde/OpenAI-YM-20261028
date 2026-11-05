import YM.UVExtension.Willow.Stains
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Willow
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
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
lemma birds (G:Gauge) (L:Side) (m:ℝ) (hp:0<m) : ∀ᶠ x:ℝ in atTop, ∀ (k:ℕ) (c f:Side) (S:StepData c f) (X:Support c) (z:ℂ),
    S.patch.L=L→ z∈ aisle (betaF G x L) → 0≤ Real.log (‖z‖/z.re) ∧ Real.log (‖z‖/z.re) ≤ 1 ∧ ‖z‖/z.re ≤2 ∧
    permag z (Fintype.card (↥(podium S G X (radiusB x)))) ≤ Real.exp (m*Copse.cover k (radiusB x) X) := by
  let v x:= softR G L (betaF G x L) (betaF G x L)
  have he:Rate G L (99/100-1) v:= by
    have hh : Rate G L (99/100-1) (fun x=> 2*(betaF G x L)^(99/100-1:ℝ)) := Rate.power.mul_left _
    refine hh.congr ?_; filter_upwards [Delay.shift_pos G L] with x hx
    unfold v softR; rw [Real.rpow_sub hx]; rw [Real.rpow_one]; ring
  have hf : Rate G L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)) := by simpa only [one_mul,add_zero] using! width_rate G L 1 0
  let w x:=((ballCost (radiusB x):ℝ)*Itinerary.density L*Fintype.card G.ColorIndex)/2
  have hW : Rate G L 0 w := by unfold w; simpa only [div_eq_mul_inv] using! (((hf.mul_right _).mul_right _).mul_right _)
  filter_upwards [Delay.shift_pos G L,he.below (by norm_num) 1 zero_lt_one,(hW.mul he).below (by norm_num) m hp] with x hx hv hV k c f S X z hL hz
  let d:= betaF G x L; have hr:= breath hx hz
  let B:=radiusB x
  have hR: 1 ≤ ‖z‖/ z.re := (one_le_div hr).mpr (Complex.re_le_norm z)
  have hD: ‖z‖/ z.re-1 ≤ v x := by
    have hp : ‖z‖-z.re ≤ |z.im|:= by have h:= Complex.norm_le_abs_re_add_abs_im z; rw [abs_of_pos hr] at h; linarith
    unfold v softR
    calc
      _ = (‖z‖-z.re)/z.re := by field_simp
      _ ≤ (betaF G x L ^ (99/100:ℝ))/ z.re := div_le_div_of_nonneg_right (hp.trans hz.2.2.le) hr.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (half_pos hx) hz.1.le
  have ha := Real.log_nonneg hR; have hu : Real.log (‖z‖/ z.re) ≤ v x:= (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hR)).trans hD
  have hv':v x≤1:= (le_abs_self _).trans hv
  refine ⟨ha,hu.trans hv',by linarith,?_⟩
  let I:= edgesM S X B; let Z:= univ.filter fun i:Bond f=> atEdge S i∈X; let n:=Copse.cover k B X
  have hI : I.card≤ X.card *Itinerary.density L:= (Finset.card_le_card (show I ⊆ Z from fun i hi=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 (atEdge S i) (by simp)⟩)).trans (hL ▸ (perch S X))
  have he : podium S G X B=lensS I G:= (chargedU ..).symm
  have hp : (Fintype.card (↥(podium S G X B)):ℝ)≤ n*((Animals.ballCost B:ℝ)*Itinerary.density L*Fintype.card G.ColorIndex) := by
    rw [he]; have h : I.card ≤ n*Animals.ballCost B*Itinerary.density L:= hI.trans (Nat.mul_le_mul_right _ (Copse.size k B X))
    have hh : Fintype.card (↥(lensS I G)) ≤ n*(Animals.ballCost B*Itinerary.density L*Fintype.card G.ColorIndex):= by
      rw [Fintype.card_coe, lensS, card_product,card_univ]; exact (Nat.mul_le_mul_right _ h).trans_eq (by ring)
    exact_mod_cast hh
  apply Real.exp_monotone; apply le_trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 2)) ha)
  have he:w x* Real.log (‖z‖/z.re)≤ m:= (mul_le_mul_of_nonneg_left hu (show 0≤w x from by unfold w; positivity)).trans ((le_abs_self _).trans hV)
  exact (le_of_eq (by unfold w B; ring : _=(n:ℝ)*(w x* Real.log (‖z‖/z.re)))).trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans_eq (mul_comm ..)) -- simplify


structure Pouch (G : Gauge)(L: Side)(x l:ℝ) : Prop where
    step (c f:Side) (S:StepData c f) (Y:Support c)(z:ℂ) : S.patch.L=L → z∈Wick.aisle (betaF G x L) → ∀ d:ℕ, permag z (podium S G Y (radiusB x)).card ≤ Copse.worth d (radiusB x) l Y
lemma mottled (hp:0< u):∀ᶠ x:ℝ in atTop,Pouch G L x u:=by
   filter_upwards [birds G L u hp] with x hx; exact ⟨fun c f S Y z h hz d=> by have h :=hx d c f S Y z h hz|>.2.2.2; rwa [Fintype.card_coe] at h⟩
-- numeric reserve helpers
variable {k:Mixed.Costs}
local notation "d₀"=> H.supportP
local notation "G'"=> radiusB x
lemma rentsTre {Φ:Type*}{n:Side} (X:Φ→Support n)(p:ℕ){f:Φ→ℝ}{γ a δ q:ℝ}(h:Trees.Ready X p f a γ δ q) : (ballCost p:ℝ)*γ≤ δ:=by
    obtain ⟨hL,hU,hq,hx,-⟩:= h; unfold Trees.degreePrice at hq; have ht : Trees.stretch p γ δ ≤ 1:= by linarith only [hq,hx]
    unfold Trees.stretch at ht; linarith only [(div_le_iff₀ hU).mp ht]
-- currency.output per-point array
lemma royalties {Z:Alphabet c f→ℝ}(hp:Mixed.Accounts S Q.halo (radiusB x) k H.birth Z (lengths T R) (steamP S k)) (hK:k.Buy S.patch.L Q.halo (radiusB x)) : let f:= tabs S k (radiusB x) Q.halo Z
  (∀ i,0≤ f i) ∧ Ac.Hit H.supportP (radiusB x) f (k.exponent+k.reserveTree) k.rootHit ∧ (Animals.ballCost (radiusB x):ℝ)*k.rootHit ≤ k.reserveTree:=by
   intro f; have hf i:0≤ f i:= by
      rcases i with i|i; unfold f tabs Mixed.costs; dsimp only [Sum.elim]; split; exact mul_nonneg hK.capture (Real.exp_pos _).le; exact le_rfl; exact hp.holds _
   let v:=Mixed.ready_vertices S _ _ k H.birth Z _ (steamP S k) hK hp
   refine ⟨hf,fun o'=>?_ , rentsTre _ _ v⟩
   apply budget_mono (show SumBudget _ k.rootHit from v.2.2.2.2.2 o')
   · intro i; split; next=>exact mul_nonneg (hf _) (Real.exp_pos _).le
     exact le_rfl
   intro i; split; swap; · exact (v.2.2.2.2.2 o').1 _
   next hx =>
   rw [if_pos (show o'∈ Mixed.foot S Q.halo G' H.birth i from hx)]; apply mul_le_mul _ (Real.exp_monotone _) (Real.exp_pos _).le (v.2.2.2.2.1 _)
   · have hv: 0 ≤ Mixed.lengths S k (lengths T R) i := by rcases i with i|i; exact mul_nonneg hK.extra (by positivity); exact hp.extra _
     have ht':0 ≤ Mixed.stamp S k i:=mul_nonneg hK.marked (by positivity); have he:=hK.eps; exact le_mul_of_one_le_right (hf _) (Real.one_le_exp (add_nonneg (by positivity : 0≤2*k.reservePoly*Mixed.lengths S k (lengths T R) i) ht'))
   exact mul_le_mul_of_nonneg_right (by linarith only [hK.eps]) (Nat.cast_nonneg _)
end YM.UVExtension.Willow
