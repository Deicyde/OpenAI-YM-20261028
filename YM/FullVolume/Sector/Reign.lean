import YM.FullVolume.Sector.Dials
/-! Replace root payment in positive tree estimates — using larger post-L income only, no shape change -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
abbrev stella (Q: ConnectedActivityE6.Target G P) : ConnectedActivityE6.Target G P:= {Q with rate := -(2/5), start:=by norm_num, stop:=by norm_num}
-- x powers exactly; choose ε fixed (R≥2 small).
abbrev fire (G:Gauge) (L:Side) (x:ℝ):ℝ := betaF G x L ^ ((1:ℝ)/256)
abbrev thaw (G:Gauge) (L:Side) (x:ℝ):ℝ := betaF G x L ^ (-(1/128:ℝ))
section housing
private lemma worth (G : Gauge) (L: Side) : ∃ y:ℝ, 0≤y∧∀ x:ℝ,↑(L.val^4*Fintype.card Axis)* (Animals.ballCost ((10*radiusB x+1)+1):ℝ) *(Fintype.card G.ColorIndex:ℝ) ≤ y*Delay.bill G L x^5:=by
  let c:ℝ:= (L.val^4*Fintype.card Axis:ℕ); let d:ℝ:= Fintype.card G.ColorIndex
  refine ⟨c*25^4*d,mul_nonneg (mul_nonneg (by positivity:0≤c) (by norm_num)) (by positivity),fun x=>?_⟩
  let t:= Delay.bill G L x; have hp:1≤t:=Delay.bill_ge G L x
  have hb: (radiusB x:ℝ)+1 ≤ t:= by unfold t Delay.bill; linarith [sq_nonneg (Real.log (betaF G x L))]
  have hh: (Animals.ballCost ((10*radiusB x+1)+1):ℝ) ≤ 25^4*t^4 := by
    unfold Animals.ballCost; push_cast; rw [← mul_pow]; gcongr; linarith only [hb,hp]
  -- L cast implicit
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity : 0≤c)) (by positivity : 0≤d)) ?_
  exact (by change c*_ *d ≤ c*25^4*d*t^5; rw [show c*_*d=c*25^4*d*t^4 by ring]; apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by omega)) (by positivity))
lemma crown (G : Gauge) (L : Side) (i : ℕ) (A : ℝ) (D:ℝ) : ∃ C:ℝ, A≤C ∧ D≤C ∧ 0≤C ∧ ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (F:Tree.Forest S.ratio) (X:Coat T F) (Y:Stores S) (x:ℝ) (δ:ℝ) (α:ℝ) (b:ℝ), b ≤ C → b ≤ D → X.x=x → S.patch.L=L → 1 ≤ Y.shares → 0≤δ → δ≤1 →
    FullVolume.Ray.Fold.charge i*(1+δ)^(Tune.count X Y)*Packets.income 1 (b*Delay.bill G L x^5) α Y.shares ≤ Packets.income 1 (C*Delay.bill G L x^5) α Y.shares:=by
  obtain ⟨u,hu,hx⟩:= worth G L
  let v:= FullVolume.Ray.Fold.charge i; have hv:0≤v:= (FullVolume.Ray.ink.pay_pos _).trans (le_max_left ..)
  let C:= max 0 (max A D)+v+u
  refine ⟨C,(by unfold C; have : A ≤ max 0 (max A D):=(le_max_left ..).trans (le_max_right ..); linarith), (by have : D≤ max 0 (max A D):=(le_max_right ..).trans (le_max_right ..); unfold C; linarith), (by unfold C; positivity),?_⟩
  intro c f S T F X Y x δ α b hB hb hy hP hY he hd
  let n:= Tune.count X Y; let t:= Delay.bill G L x; let m := (Y.shares:ℝ)
  have hp : (n:ℝ) ≤ m*(u*t^5) := by
    have hh := (card_le_card (filter_subset (fun i:Bond f=> i∉F.trunks) (visit Y (10*X.B)))).trans (touch_price S (10*X.B) Y)
    refine le_trans (b:=m * ((L.val^4*Fintype.card Axis:ℕ):ℝ)*(Animals.ballCost ((10*radiusB x+1)+1):ℝ)*(Fintype.card G.ColorIndex:ℝ)) ?_ ?_
    · rw [show X.B=radiusB x from congr_arg _ hy,hP] at hh -- dependent
      unfold n Tune.count; push_cast; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold m; exact_mod_cast (by simpa [mul_assoc,mul_comm,mul_left_comm, pens, Coat.B, hy, Itinerary.density] using hh)
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hx x) (by unfold m; positivity)); ring
  have hm : 1≤ m:= by unfold m; exact_mod_cast hY
  have ht : 1 ≤ t^5 := one_le_pow₀ (Delay.bill_ge ..)
  unfold Packets.income; rw [one_mul,one_mul]; refine (mul_le_mul_of_nonneg_right (mul_le_mul (show v≤Real.exp v by linarith [Real.add_one_le_exp v]) (pow_le_pow_left₀ (show 0≤1+δ from (zero_le_one.trans (le_add_of_nonneg_right he))) ((show 1+δ ≤ 2 by linarith).trans (by linarith [Real.add_one_le_exp 1] : 2≤Real.exp 1)) n) (pow_nonneg (by linarith) _) (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; rw [mul_one]; change v+n+(b*t^5-α)*m≤(C*t^5-α)*m
  unfold C; have h : b ≤ max 0 (max A D):=hb.trans ((le_max_right ..).trans (le_max_right ..)); nlinarith only [hp, mul_le_mul_of_nonneg_right h (mul_nonneg (zero_le_one.trans ht) (zero_le_one.trans hm)), le_mul_of_one_le_right hv (one_le_mul_of_one_le_of_one_le ht hm)]
end housing
section trees
variable {Z : ℝ} {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K) (p:Lyre.Signal j)
-- Ξ costs for replacement.C'. Later actual K value separately via raw budget {Γ.κ Quant}
local notation "ψ"=> U.pole
local notation "C₀"=> Q.goal L x₀
local notation "Q'"=> stella Q
local notation "δ'"=> radiusB x₀
structure Clear (Q : Target G P) (L : Side) (μ Y x v:ℝ) (p:Lyre.Signal j) : Prop where
  shill : Lyre.salary p v*(3*Q.goal L x+Q.goal L x) ≤ (stella Q).goal L x
  low : 3*Q.goal L x ≤1/2
  promise : p.B*v^2*(3*Q.goal L x) ≤1
  forcer : ∀ β ∈ Set.Ici (betaF G x L/2), ((stella Q).costs L μ β x Y).Buy L Q.halo (radiusB x)
lemma shows (Q:Target G P) (L: Side) (μ:ℝ) {Y} (hy:0≤Y) (p:Lyre.Signal j) (h:0<μ) (hp : Q.rate ≤ -(7/16)):∀ᶠ x in atTop, Clear Q L μ Y x (fire G L x) p:=by
  let f:= fire G L; have ht : Rate G L (1/256) f:=Rate.power
  let g x:= (3*Q.goal L x); let J : Rate G L Q.rate g:= (Rate.power).mul_left 3
  have hh : Rate G L ((1/256:ℝ)*2) (fun x=> Lyre.salary p (f x)):= (((ht.pow 2).mul_left _).add ((Rate.const _).weaken (by norm_num)))
  have hs := hh.mul (J.add Rate.power); have h' : 1/256*(2:ℝ)+Q.rate < -(2/5):= by linarith
  filter_upwards [hs (-(2/5)) h', J.below Q.stop _ (by norm_num : (0:ℝ)<1/2),((((ht.pow 2).mul_left p.B).mul J)).below (by push_cast; linarith) 1 zero_lt_one, (stella Q).pay_for L h hy] with x hx hv hw hm
  exact ⟨(le_abs_self _).trans hx,(le_abs_self _).trans hv,(le_abs_self _).trans hw,hm⟩
end trees
end YM.ConnectedActivityE6.Empire
