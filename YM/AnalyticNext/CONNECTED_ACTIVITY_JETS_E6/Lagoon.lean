import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Interpolate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Modes
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Outer

/-!
# Flat tests and all-order charge on the probed chart

Unit physical window may exceed probe. Angular comparisons checked even from
closed ball. Extend AFTER laying out, but bound before x period chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes Quill Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side}
open Brush

-- Hatted scales for probing. Need Rate **with inverse** too
abbrev boil (G : Gauge) (L : Side) (x : ℝ) := Pressure.betaF G x L ^ (1/2:ℝ)
def mist (G : Gauge) (L : Side) x := (boil G L x)⁻¹
lemma mist_rate (G : Gauge) (L : Side) : Rate G L (-(1/2)) (mist G L) := by
  apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]; rfl
lemma softly (G : Gauge) (L : Side) : ∀ᶠ x : ℝ in atTop, 0 < mist G L x ∧ mist G L x ≤ Pressure.temp x := by
  filter_upwards [Delay.shift_pos G L,eventually_gt_atTop (0:ℝ)] with x hx hv
  have hs : (Real.sqrt x)⁻¹ ≤ Pressure.temp x := le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) <|
    Real.one_le_exp (sq_nonneg _)
  unfold mist boil; rw [← Real.sqrt_eq_rpow]; constructor
  · positivity
  apply le_trans _ hs; apply inv_anti₀ (Real.sqrt_pos.mpr hv); apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right (Work.E04.shift_nonneg G L)

lemma probe_window (G : Gauge) (L : Side) : ∃ q : ℝ, 0<q ∧ ∀ᶠ x in atTop, ∀ (c : Side) (V : Directions G c),
    ‖V‖ ≤ 3*(q*mist G L x) → ∀ o : Site c, Clean (increment 1 V) x o (radiusB x) := by
  obtain ⟨C,r,hC,hr,h⟩:= chord_chart_cost G
  let u := 1/(12*C); have hu : 0<u := by unfold u; positivity
  refine ⟨u,hu,?_⟩
  filter_upwards [(((mist_rate G L).mul_left u).mul_left 3).below (by norm_num) _ hr, softly G L]
    with x hx hp c V hV z hz _ hf
  let U:= increment 1 V
  obtain ⟨p,-,he⟩:= (flags_spec (temp x) U _).mp hf
  have hF (i : Bond c) : G.chord (U i)≤ C*(3*(u*mist G L x)) := by
    have hi := (norm_le_pi_norm V i).trans hV
    unfold U increment; rw [Pi.one_apply,mul_one]; exact (h _ (hi.trans ((le_abs_self _).trans hx))).trans
      (mul_le_mul_of_nonneg_left hi hC.le)
  have hv : toll U p≤4*(C*(3*(u*mist G L x))) := travel_chord U (square p.2.val.1 p.2.val.2) p.1 _ hF
  have hc' : 4*(C*(3*(u*mist G L x)))=mist G L x := by unfold u; field_simp; ring
  exact (not_lt_of_ge (show toll U p ≤ Pressure.temp x from hv.trans (hc'.trans_le hp.2))) he

lemma ivy_windows (P : Teller G) (L : Side) (D : Patch) (he : D.Branches P.bind G) {a : ℝ→ℝ}
    (hv : Rate G L (-(1/2)) a) (ha : ∀ᶠ x : ℝ in atTop,0≤a x) : ∃ E : ℝ→ℝ, Rate G L (-(3/2)) E ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S),S.patch=D → Works P L x S T→ ∀ (k : S.Choices) (p : Spot c f)
    (z : ZipP G c f), ‖z‖≤a x → Clean (increment 1 z.1) x (lead S p) (radiusB x) → |ivy T x k p z| ≤ E x := by
  obtain ⟨M,C,hM,hC,hW⟩:= max_prices P
  obtain ⟨X,hX,hF⟩:= SliceRows.soft_bills P L D he M hM hv ha
  obtain ⟨N,hN,hG⟩:= letters_N P L
  obtain ⟨L',hY,hL⟩:= letters_LD P L D he M hM hv ha
  obtain ⟨Z,hz,HZ⟩:= letters_C P L
  refine ⟨fun x=>X x+N x+L' x+Z x,((hX.add (hN.weaken (by norm_num))).add hY).add (hz.weaken (by norm_num)),?_⟩
  filter_upwards [hW L,hF,hG,hL,HZ,room G P L] with x hw H K hQ hZ hp c f S T hS hR k p u ht hh
  have hx:= hp c f S T hR
  let V:= increment (1:Config G c) u.1; let U:= shaft S u; let Q := S.prediction U k; let y:=Pressure.temp x; let R:=till x
  have hH: Grafted V U u.2 (lead S p) (radiusB x/2) (a x) S := ⟨fun _ _=> rfl,fun i _=>
    (norm_le_pi_norm u.2 i).trans ((le_max_right ..).trans (show max _ _ ≤ a x from ht))⟩
  have hb : Clean V x (lead S p) (radiusB x/2) := hh.shrink (by rw [separation_self]; omega)
  have hl:=hR.length_eq
  have hy : Bid.Maximum M T x V := ((hw c f S T hR).2 V).1
  have he := H.2 c f S T hS hl hx U k V _ u.2 hy hh hH
  have hX i (hi:i∈parents p) : Scroll.freely T x V k i+straightened T R V u.2 i=reply T x V k u.2 i := by
    unfold freely reply request; rw [frameCost hx i ?_]
    rw [cost_is_here i,(parent_iff (S:=S) i p).1 hi]; exact hh.shrink (by rw [separation_self]; omega)
  let g i:= ‖reply T x V k u.2 i‖^2/2
  unfold ivy squarepot
  rw [← (Scroll.yields hx p hb U k).1, Finset.sum_congr rfl (show ∀ i∈parents p, _ = g i from fun i hi=> by rw [show _=_ from hX i hi])]
  have h₁ := H.1; have h₂:=K.1; have h₃ := hQ.1; have h₄:=hZ.1
  rcases p with p|p|p|p
  · refine le_trans (b:=X x) ?_ (by linarith)
    have he := he.1 p rfl; rw [Fintype.sum_bool] at he
    change |soft T x U V k p-_| ≤ _
    simpa [parents,g] using he
  · refine le_trans (b:=X x) ?_ (by linarith)
    change |T.workI R Q V y _-_|≤_
    have h : T.workI R Q V y p=softI T x U V k p:=splitI ..; simpa only [parents, Finset.sum_singleton,h] using! he.2 p rfl
  · have hv := hQ.2 _ _ S T hl hS hx U V p k hy hh u.2 hH
    have hf := hZ.2 _ _ S T hl hx V p (hh.toll (b:=p) (by change separation p.1 p.1≤_; simp))
    simp only [parents,sum_empty,sub_zero]
    change |T.workC R V _ _+(T.workL R U Q _ _ _+_)|≤ _
    apply ((abs_add_le ..).trans (add_le_add hf ((abs_add_le ..).trans hv))).trans
    linarith
  simp only [parents,sum_empty,sub_zero]
  exact (K.2 c f S T hl hx V p (hh.shrink (by change separation p.1 p.1+_≤ _; rw [separation_self]; have hp:=hx.sight; omega))).trans (by linarith)

lemma evokes (P : Teller G) (L : Side) (D : Patch) (h : D.Branches P.bind G) (j : ℕ) {V : ℝ→ℝ}
    (hv : Rate G L (-(1/2)) V) (hu : ∀ᶠ x in atTop, 0 ≤ V x) :
    ∃ a Q : ℝ→ℝ, Rate G L (-(3/2)) Q ∧ Rate G L (1/2) a ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T →
    ∀ (k : S.Choices) (p : Spot c f) (u : ZipP G c f), ‖u‖ ≤ V x → Brush j (Q x) (a x) (ivy T x k p) u := by
  obtain ⟨r,hr,hR,E,hE,H⟩:= growth P L D h (j+3)
  obtain ⟨q,hq,hQ⟩:= probe_window G L
  let d x:= q*mist G L x
  let B x := V x+3*d x
  have he : Rate G L (-(1/2)) d := (mist_rate G L).mul_left _
  obtain ⟨Z,hZ,HZ⟩ := ivy_windows P L D h (he.mul_left 3) ((softly G L).mono (fun x hx=> show 0≤3*d x from mul_nonneg (by norm_num) (mul_nonneg hq.le hx.1.le)))
  have ha : Rate G L (1/2) (fun x=> (d x)⁻¹) := by simpa only [d,mist,mul_inv_rev,inv_inv] using!
    (Rate.mul_right (Rate.power (G:=G) (L:=L) (a:=1/2)) q⁻¹)
  have hB : Rate G L (-(1/2)) B := hv.add (he.mul_left 3)
  refine ⟨_,_,recover_price he hB hZ hE (by rfl) ha,ha,?_⟩
  filter_upwards [H,hQ,softly G L,room G P L,HZ, hu,hB.below (by norm_num) r hr] with x Hb hx hp hb H hv hU c f S T hS hY k p u he'
  have hE := hb _ _ _ _ hY
  have hr (i : ZipP G c f) (hi : i∈Metric.closedBall 0 (B x)) := Hb c f S T hS hY.length_eq hE p k i
    ((mem_closedBall_zero_iff.mp hi).trans ((le_abs_self _).trans hU))
  have hy : 0 < d x := mul_pos hq hp.1
  have hD : 3*d x ≤ B x := le_add_of_nonneg_left hv
  have hF (i : ZipP G c f) (hi : i∈Metric.closedBall 0 (3*d x)) := H c f S T hS hY k p i (mem_closedBall_zero_iff.mp hi)
    (hx c i.1 ((le_max_left ..).trans (show max _ _ ≤ _ from mem_closedBall_zero_iff.mp hi)) (lead S p))
  have hO : (0 : ZipP G c f) ∈ Metric.closedBall 0 (3*d x) := Metric.mem_closedBall_self (by positivity)
  exact (ascend (by omega : 3≤ j+3) ((abs_nonneg _).trans (hF 0 hO)) hy (by linarith only [hR, hD, (le_abs_self _).trans hU,hy]) hD
    (hr 0 (closedBall_subset_closedBall hD hO)).nonneg hr hF u (mem_closedBall_zero_iff.mpr (he'.trans
      (le_add_of_nonneg_right (show 0 ≤ 3*d x by positivity))))).smaller (by omega)
end YM.ConnectedActivityE6.Blaze.Frond
