import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc

/-!
# Inherited head jet bills

 Measure at fixed original U; keep true mask on E/numerical cost
 including damping profiles on unturned fields. Turn with FULL path.
 Progress includes OLD halo reads needed to hold U. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
namespace Silica.Clutch

lemma dicers (P : Teller G) (L : Side) {w a ε b : ℝ} (_hb : b≤0) (ha : 0≤a) (he : 0<ε) (hw : 8*ε<P.below.width) {V : ℝ→ℝ}
    (h : Rate G L b V) (j l : ℕ) : ∃ v, Rate G L 0 v ∧ (∀ x,0≤v x) ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L→ Intake P T x R →
    ∃ Z : Pairs c→ℝ, Sales (radiusB x) a ε (bothFoot (atOne _) l (radiusB x) T.down) Z (bothCharge T.down) (betaF G x L^w) ∧
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (U:E→ Config G c), Mode U y j (V x) → ∀ i,
          Brush j (Z i) (v x*(bothCharge T.down i:ℝ)) (fun y=> icicle T.down (U y) (till x) L.val (-(-orientation*R.beta)) i) y := by
  let z := royalty G
  let p x := 2* (|V x| *z)
  let d x := 2*betaF G x L * z^4
  have hz : 1≤z := royalty_ge _
  have hp : Rate G L 0 p := (((h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun x=> (abs_abs _).le)).mul_right _).mul_left 2).weaken _hb
  have hd : Rate G L 1 d := (Rate.hat.mul_left 2).mul_right _
  refine ⟨p,hp,fun x=> by unfold p; positivity,?_⟩
  let t:=w-1
  filter_upwards [tail_bills (s:=P.below.clip) (C:=P.below.paths) G L scaleOne 0 l _ L.property he hw ha hd t,
    (((Rate.power (G:=G) (L:=L) (a:=t)).mul_left (Fintype.card PlaqAxes:ℝ)).mul_left (Fintype.card Signed:ℝ)) w
    (by unfold t; linarith)] with x hx ht c f S T R hS hP
  obtain ⟨_,b,-,he⟩:= hP.ready.feeds
  have hβ:= hP.window.2; rw [hS] at hβ
  have hh : 0≤ 2*betaF G x L := hP.positive.le.trans hβ
  let b i (s : Site c × ℕ×ℕ) := d x* pairPrice T.down (till x) L.val i s.2
  let W i : ℝ := b (i:Pairs c).2.1 i.2.2
  have hD : 0≤ d x := mul_nonneg hh (by positivity)
  have hW (i : PlaqAxes) := hx c c (atOne c) rfl T.down _ he i (b i) hD (fun u=> by
    simp only [b,pow_zero,mul_one]; exact ⟨mul_nonneg hD (pairPrice_nonneg ..), le_rfl⟩)
  -- tensor Sales
  refine ⟨W,(Sales.price_fst W _ _ (fun _ : Signed=> ∑ _ : PlaqAxes,betaF G x L ^ t)
    (fun s=> Sales.price_fst _ _ _ _ (fun i=> (hW i).rotated s 0 ha))).raise ?_,?_⟩
  · simp only [sum_const,nsmul_eq_mul,card_univ]; exact (le_abs_self _).trans ht
  intro E _ _ y U m i
  let Z y:= pull i.1 0 (U y); let s:= (i.2.2.1,i.2.1); let v:= V x
  have hO:= Blaze.turn m i.1; let j':= i.2.2.2
  let W' k:= T.down.row i.2.1 k; let q(k):= W' k|>.2; let C k := |(W' k).1| *z^2
  have hk k : Brush j (C k) (p x*(q k).length) (fun y=> T.down.ellTerms s k (Z y)) y := by
    apply ((slot_cost (q k) (U:=Z) (k:=j) s.1 hO.pos hO.atLink).smul ((W' k).1)).climb le_rfl
    unfold p z; rw [abs_of_nonneg hO.pos]; exact le_of_eq (by ring)
  unfold icicle Polar.twin; split_ifs with hi
  · apply (((semi (stroke (hk j'.1) (hk j'.2)))).smul (-(-orientation*R.beta))).climb
    · rw [Real.norm_eq_abs,abs_neg,abs_mul,abs_neg,abs_of_nonneg (orientation_range.1.le),abs_of_nonneg hP.positive.le]
      have hβ' : orientation *R.beta ≤ 2*betaF G x L := (mul_le_of_le_one_left hP.positive.le orientation_range.2).trans hβ
      unfold W; dsimp only [b,d]; rw [pairPrice,if_pos (by exact hi)]
      apply (mul_le_mul_of_nonneg_right hβ' (by unfold C; positivity)).trans
      calc
        _ = d x*Paths.mate T.down i.2.1 i.2.2.2 := by unfold C d W' j' Paths.mate; ring
        _ ≤ d x*(2*Paths.mate T.down i.2.1 i.2.2.2) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by unfold Paths.mate; positivity) (by norm_num)) hD
    unfold bothCharge; rw [Paths.duplex_price,Nat.cast_add,mul_add]
  · simp only [mul_zero]; apply Brush.zi EventuallyEq.rfl (mul_nonneg hD (pairPrice_nonneg ..)) (by unfold p; positivity)
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
