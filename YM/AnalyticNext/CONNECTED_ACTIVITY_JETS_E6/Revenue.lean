import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.AssignedPrice
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Steam

/-!
# Packet revenue on a sector

Bills before integration, per-V/Stenc hypotheses. `PointCharge` receipt
in THE underlying P,T before entering. Payment on A's assigned stencil
under ITS own local prerequisites, even within a larger Σ. Not credited
with unbound multiplication of factors from those unrelated inputs. Supply
spend schedule slack exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- If putting normalized inactive averaged P when rotations become competitive,
use both ends + chart cost. `W` fixed-L, A pre-L. l may stay at 300 guard etc. -/
def Pack (X : Coat T F) (R : Rep G f) (Ñ : ChartRatio G) (l : Finset ℕ) (W a : ℝ) (A : Stores S) (v : Directions G f) :=
    if X.existSeeds A 300 then X.steam R Ñ l W a A v else 0

lemma ticket_cost (G : Gauge) (P : Patch) (L : Side) : ∃ Q : ℝ, 0<Q ∧
    ∀ x, tollFee P (300*radiusB x) ≤ Q * Delay.bill G L x ^4 := by
  obtain ⟨C,hC,H⟩ := Census.width_bound G L 300 1
  obtain ⟨A,hA,J⟩ := Census.width_bound G L 300 2
  let E : ℝ := Fintype.card P.FrameTag; let K : ℝ := Fintype.card Axis; let W : ℝ := Fintype.card P.Points
  have hE : 0≤ E := by unfold E; positivity
  have hK : 0≤ K := by unfold K; positivity
  have hW : 0≤ W := by unfold W; positivity
  let Q := 1+C*E+A*K*W
  refine ⟨Q,by unfold Q; positivity,fun x=>?_⟩
  unfold tollFee Q
  have ht : 300*radiusB x+1+1=300*radiusB x+2 := by omega
  rw [ht]; apply (add_le_add (mul_le_mul_of_nonneg_right (H _) hE) (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (J _) hK) hW)).trans
  let W' := Delay.bill G L x ^ 4
  have hx : 0≤ W' := by unfold W'; positivity
  nlinarith

lemma sweeps (G : Gauge) (L : Side) (d : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ x,
    swept L ((d*radiusB x+1)+1) ≤ C*Delay.bill G L x ^4 := by
  obtain ⟨A,hA,h⟩ := Census.width_bound G L d 2
  let D : ℝ := Itinerary.density L
  have hh : 0≤D := by unfold D; positivity
  refine ⟨(1+A*D),by positivity,fun x => ?_⟩
  have he := mul_le_mul_of_nonneg_right (h x) hh
  apply he.trans
  nlinarith [sq_nonneg (Delay.bill G L x ^ 2)]

lemma upkeep {Ñ : ChartRatio G} (h : LocalRatio Ñ) (P : Teller G) (D : Patch) (L : Side) (a η r Q Y : ℝ)
    (ha : 0<a) : ∃ K : ℝ, 0<K ∧ ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F),
      X.x=x → S.patch=D → S.patch.L=L → Rotator P L η r Q Y X → Rotator P L η r Q Y X.blank →
        ∀ (R : Rep G f), Intake P T X.x R → ∀ (Z : Stores S) (u : Directions G f),
        X.steamLog R Ñ a Z u + tollFee D (300*X.B)*Z.shares ≤
          -R.beta*X.quoteNear Z u + K*Delay.bill G L x^5*Z.shares := by
  obtain ⟨A,hA,H⟩ := scaled Ñ h L
  obtain ⟨C,hC,h₁⟩ := germ_charge h L ha
  obtain ⟨K,hK,h₂⟩ := ticket_cost G D L
  obtain ⟨M,hM,hm⟩ := sweeps G L 200
  obtain ⟨N,hN,hn⟩ := sweeps G L 304
  obtain ⟨Z,hZ,hz⟩ := sweeps G L 10
  let V := Fintype.card G.ColorIndex*((Q+1)*payE η r Q (tubularPrice G L))
  let U := |V| *M+N+A*Z+K
  refine ⟨U,by unfold U; positivity,?_⟩
  filter_upwards [((Rate.flame (L:=L) (G:=G)).mul_left C).below (by norm_num) _ zero_lt_one,h₁,H]
    with x hv hU hy c f S T F X hh hS hL hr he R hi Y u
  subst x
  let p := Delay.bill G L X.x
  have hP : 1≤p := Delay.bill_ge ..
  have hf := (le_abs_self _).trans hv
  have hh j : |X.gentry Ñ a u j| ≤ 1 := ((hU _ _ S T F X rfl hL hr.room.fiery).2 j u).trans (by
    unfold Coat.t; rw [hL]; exact hf)
  have ht : -Real.log (measure_g Ñ R.beta) ≤ A*p := hy _ hi.positive (hL ▸ hi.window.2)
  have hb : 0 ≤ A*p := by positivity
  have he' := aftermath X u R hi Ñ Y zero_le_one hh (fun j => (X.postedBase hr he j).trans (le_abs_self V)) (abs_nonneg _) ht hb
  rw [hL] at he'
  refine (add_le_add he' (mul_le_mul_of_nonneg_right (h₂ X.x) (Nat.cast_nonneg _))).trans ?_
  have hs : p^4 ≤ p^5 := pow_le_pow_right₀ hP (by norm_num)
  change _ ≤ -R.beta*X.quoteNear Y u+U*p^5*(Y.shares:ℝ); rw [add_assoc,← add_mul]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  change |V| * _+1*_ + A*p*_ + K*p^4 ≤ _
  unfold U
  calc
    _ ≤ |V| *(M*p^4)+1*(N*p^4)+A*p*(Z*p^4)+K*p^4 := by
      gcongr
      · unfold p; exact hm _
      · exact hn _
      exact hz _
    _ = (|V| *M+N+K)*p^4+A*Z*p^5 := by ring
    _ ≤ (|V| *M+N+K)*p^5+A*Z*p^5 := by gcongr
    _ = _ := by ring

lemma steam_prices (P : Teller G) (D : Patch) (L : Side) (hd : D.Branches P.bind G) {Ñ : ChartRatio G} (h : LocalRatio Ñ)
    {a A W : ℝ} (ha : 0<a) (hA : 0<A) (hW : 0<W) (η r Q Y γ k μ : ℝ) (hm : γ*k ≤ a) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
    (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Rotator P L η r Q Y X →
    Rotator P L η r Q Y X.blank → X.width=k → ShellAccess S G X.x W k γ → PointCharge T X.x W μ →
    (∀ v, Maximum A T X.x v) → ∀ R, Intake P T X.x R → ∀ (B : Stores S) (l u),
    |X.Pack R Ñ l W a B u| ≤ Packets.income 1 (C*Delay.bill G L x^5) (R.beta*(μ*X.t^2)) B.shares := by
  let H x := (2*a)*Pressure.fiery G x L
  obtain ⟨E,hE,h₁⟩ := earns P L D hd A hA (w:=H) (Rate.flame.mul_left _) (Eventually.of_forall fun x =>
    mul_nonneg (by positivity) (by unfold Pressure.fiery temp; positivity))
  obtain ⟨K,hK,H₂⟩ := upkeep h P D L a η r Q Y ha
  have hx := ((Rate.hat.mul_left 2).mul hE).below (by norm_num) _ zero_lt_one
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [hx,H₂,h₁] with x hx h hh c f S T F X he hS hL hr ht hi hv hk hp R hR B l u
  subst x
  unfold Pack; split
  swap
  · next h => rw [abs_zero]; unfold Packets.income; positivity
  next hw =>
    unfold Packets.income; rw [one_mul]
    by_cases ha' : X.steam R Ñ l W a B u=0
    · rw [ha',abs_zero]; positivity
    obtain ⟨hz,hG⟩ := hw
    have hF := hR.positive
    have hX := hr.room.fiery
    unfold steam at ha'; dsimp only at ha'
    have hq := left_ne_zero_of_mul ha'
    have hq' := Mask.masks_wide B X.χ (300*X.B) X.x W (X.input u) X.k X.V hW hX
      (right_ne_zero_of_mul hq) (right_ne_zero_of_mul (left_ne_zero_of_mul hq)) hG
    rw [← hi] at hv
    have hU := (h c f S T F X rfl hS hL hr ht R hR B u)
    have hK : γ*(2*(X.width*X.t)) ≤ H X.x := by unfold H; rw [← hL,hi]; nlinarith only [mul_le_mul_of_nonneg_right hm hX.le]
    have he : Controlled X (304*X.B) B u (H X.x) := by
      unfold H; rw [← hL]; exact X.protection_pack (show 0 < a*X.t from mul_pos ha hX) B (304*X.B) u (right_ne_zero_of_mul ha')
    have hh' := hh.2 c f S T F X rfl hS hL hr.room B u W γ μ hz hp hk hv hK he hq'
    have hv : 1 ≤ Delay.bill G L X.x := Delay.bill_ge ..
    have hy : R.beta ≤ 2* betaF G X.x L := hL ▸ hR.window.2
    have hr : R.beta*E X.x ≤ Delay.bill G L X.x^5 := (mul_le_mul_of_nonneg_right hy hh.1).trans
      (((le_abs_self _).trans hx).trans (one_le_pow₀ hv))
    apply (steam_le ..).trans
    rw [hS]; apply Real.exp_monotone; apply hU.trans
    nlinarith only [mul_le_mul_of_nonneg_left hh' hF.le,mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (α:=ℝ) B.shares)]
end YM.ConnectedActivityE6.Coat
