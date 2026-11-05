import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.TrueFaces
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Upgrade
import YM.Next.FREE_KERNELS.Amend
import YM.Next.SCHEDULE.GridCost
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Patch
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils
import YM.Work.F05.Actions

/-!
# Joint chart cost on *actual* Q tangents needed by one/two sectors

Take the union of retained noise rows for the two trees, before restriction
in columns at true `Active`. Later `skip_bump` will allow using the same
matrix for both. Each used Q can be computed on an extension of one output
patch dressed by a local held gauge. Apply the forward `gaugeQ` budgets on
small fields there, NOT an affine inverse-gap or a stationary-price claim
on the extended system. Undress the whole directed group predictor before
linearizing, not a signed adjoint read of a positive tangent. Holds all
readouts k fixed (no resampling). Delay is crucial. No differentiability
claim about discarded Q or about recomputed branch masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations
  YM.Pressure FreeResolvent Affine Mark TestD Push.Uniform
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Patch} {n : ℕ}

def reaction (k : S.Choices) (V : Config G c) (s : Signed) (i : Bond c) (z : pair G c f) :=
  G.curvature (predictorTurn (increment V (paint G c z.1)) k s i (paint G f z.2))

def shared (x : ℝ) (A : Stores S) (T U : Forest S.ratio) (s : Signed) (i : Bond c) :=
    curb (shots S x) A T x s (.inr i) ∨ curb (shots S x) A U x s (.inr i)

def contacts (x : ℝ) (A : Stores S) (T U : Forest S.ratio) (k : S.Choices) (V : Config G c) (s : Signed) (z : pair G c f) : Vec G c 1 :=
  fun i => if shared x A T U s (edge i) then reaction k V s (edge i) z i.2.2 else 0

variable {K : KernelChoices} {k : S.Choices} {V : Config G c} {x : ℝ} {A : Stores S} {T U : Forest S.ratio}
  {s : Signed} {i : Bond c}

lemma contacts_local (h : S.patch.Branches S.kernel G) (z : pair G c f) (j : raw G c) :
    contacts x A T U k V s (stopAt S (namedCo s j) (predReach S.patch+1) z) j = contacts x A T U k V s z j := by
  have ho : namedCo s j = s.act (edge j).1 := add_zero _
  let o := s.act (edge j).1
  let r := predReach S.patch
  let y := stopAt S o (r+1) z
  rw [ho]; unfold contacts; split
  swap; · rfl
  have hb := pulled_near (S:=S) _ _ s (edge j).1 _ (landscape_local S V o (r+1) z)
  have hf := pulled_near (S:=S) _ _ s (edge j).1 _ (forward_local S V o (r+1) z)
  simp only [reaction,predictorTurn,predictGroup,facade,Motion.increment_zero]
  change G.curvature (S.prediction (pull s 0 (forward S V y)) _ (edge j) * (S.prediction (pull s 0 (landscape S V y.1)) _ (edge j))⁻¹) j.2.2 = _
  rw [prediction_near_eq h _ _ _ _ hf,prediction_near_eq h _ _ _ _ hb]; rfl

private lemma clear_ball {o : Site c} {r : ℕ} (h : A.flags=RG.flags (temp x) V) (hr : o∉ A.dome r) :
    ∀ i : Site c, separation o i ≤ r → ∀ p : PlaqAxes, toll V (i,p) ≤ temp x := by
  intro i hi p; by_contra! hx
  have he : i∈ A.flags := h.symm ▸ (flags_spec ..).2 ⟨(i,p), by exact YM.Work.E01.base_touched (i,p), hx⟩
  exact hr (halo_spec.mpr ⟨i, Finset.mem_union_right _ he, (separation_comm ..).trans_le hi⟩)

lemma release_gauge (h : A.flags=RG.flags (temp x) V) (hS : S.patch=P) (hr : span P x ≤ radiusB x/50)
    (ht : LocalJet.allot P+1 ≤ 9*radiusB x) (hp : 2*(LocalJet.allot P+1)<c.val) (hi : shared x A T U s i) :
    ∃ w : Site c → G.El, ∃ W : Config G c, (∀ e : Bond c, separation (s.act i.1) e.1 ≤ predReach S.patch+1 → W e=Lattice.gauge w V e) ∧
      (∀ e : Bond c, G.chord (W e) ≤ LocalJet.permit P * temp x) := by
  let r := LocalJet.allot P; let o := s.act i.1
  have hh : o∉ A.dome (9*radiusB x+9*radiusB x/10) := (hi.elim (fun h => (guarded (hS ▸ hr) h).1) (fun h => (guarded (hS ▸ hr) h).1))
  obtain ⟨w,H⟩ := Work.E08.axial_patch o V r (r+1) (by omega) hp (temp x) (Push.SectorMeasure.temp_nonneg x)
    (fun i hi => clear_ball h hh _ (hi.trans (ht.trans (by omega))))
  refine ⟨w,fun e => if separation o e.1 ≤ r then Lattice.gauge w V e else 1, fun e he => if_pos ?_,fun e => ?_⟩
  · rw [hS] at he; unfold r LocalJet.allot; exact he.trans (by omega)
  dsimp only; split
  · apply H e; assumption
  rw [G.chord_one]; exact mul_nonneg (by unfold LocalJet.permit; positivity) (Push.SectorMeasure.temp_nonneg _)

lemma turn_swing (h : S.patch.Branches S.kernel G) (w : Site c → G.El) (k : S.Choices) (V : Config G c)
    (s : Signed) (i : Bond c) (a : Directions G f) :
    let v := constantGauge w S.ratio (affine s 0 (S.ratio.embed i.1))
    G.curvature (predictorTurn (Lattice.gauge w V) k s i (Motion.swing (constantGauge w S.ratio) a)) =
      G.adjoint v (G.curvature (predictorTurn V k s i a)) := by
  intro v
  let W := fun j : Site f => constantGauge w S.ratio (affine s 0 j)
  have eh (a : Directions G f) : facade S s (Lattice.gauge w V) (Motion.swing (constantGauge w S.ratio) a) =
      Lattice.gauge W (facade S s V a) := by
    rw [facade,← copied _ S.patch.odd_side,Motion.swing_increment,Work.F05.pull_gauge_zero]; rfl
  have he (a : Directions G f) : predictGroup (Lattice.gauge w V) k s i (Motion.swing (constantGauge w S.ratio) a) =
      v * predictGroup V k s i a * (W (S.ratio.embed (i.1+step i.2)))⁻¹ := by
    rw [predictGroup,eh,(Push.SectorMeasure.choice_gauge h _ _ W).2]; rfl
  rw [predictorTurn,he,← map_zero (Motion.swing (constantGauge w S.ratio)),he,← G.curvature_conjugate]
  congr 1; unfold predictorTurn; group

lemma turn_local (h : S.patch.Branches S.kernel G) {V' : Config G c}
    (hv : ∀ e : Bond c, separation (s.act i.1) e.1 ≤ predReach S.patch+1 → V e=V' e) (b : Directions G c) (a : Directions G f) :
    predictorTurn (increment V b) k s i a=predictorTurn (increment V' b) k s i a := by
  have he (y : Directions G f) : predictGroup (increment V b) k s i y=predictGroup (increment V' b) k s i y := by
    unfold predictGroup; refine prediction_near_eq h _ _ _ _ (pulled_near (S:=S) _ _ _ _ _ ?_); intro e hh
    unfold increment replica; split
    · rfl
    dsimp only; rw [hv (S.ratio.parent e.1,e.2) hh]
  exact congr_arg₂ (fun a b : G.El => a*b⁻¹) (he a) (he 0)

open YM.Push.SectorMeasure.Oriented in
lemma entire_turn (h : S.patch.Branches S.kernel G) (k : S.Choices) (s : Signed) (i : Bond c) (z : pair G c f) :
    paint G c (gaugeQ S s k z) i = reaction k 1 s i z := by
  ext j
  rw [reaction,curvature_project,paint_apply,gaugeQ,castNoise]
  simp only [predictorTurn,predictGroup,facade,(carry s h k _).2,Motion.increment_zero]
  have he : which ( (hue (G:=G) i j).1, (hue (G:=G) i j).2.1)=i := edge_hue (G:=G) i j
  rw [he]; rfl

lemma transferTurn (h : S.patch.Branches S.kernel G) {B : Vec G c 1} (w : Site c → G.El)
    (hr : ∀ e, ‖paint G c B e‖ < radius G n)
    (hv : ∀ e : Bond c, separation (s.act i.1) e.1 ≤ predReach S.patch+1 → Lattice.gauge w V e=increment 1 (paint G c B) e) :
    reaction k V s i =ᶠ[𝓝 0] fun z => G.adjoint (constantGauge w S.ratio (affine s 0 (S.ratio.embed i.1)))⁻¹
      (paint G c (gaugeQ S s k (routing S n B w z)) i) := by
  filter_upwards [routing_effect S hr w] with z hz
  rw [entire_turn h]; unfold reaction; rw [hz.1,hz.2,← turn_local h hv,Motion.swing_increment,turn_swing h,
    ← G.adjoint_mul, inv_mul_cancel,G.adjoint_one]

def transmit (G : Gauge) (n : ℕ) (C : ℝ) := filePrice G * composeCost n C (routeCost n G)
lemma transmit_nn (G : Gauge) (n : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ transmit G n C := by
  unfold transmit composeCost; have := route_nn n G; have := file_pos G; positivity

lemma transmit_pay (h : S.patch.Branches S.kernel G) {B : Vec G c 1} (w : Site c → G.El)
    (hr : ∀ e, ‖paint G c B e‖ < radius G n)
    (hv : ∀ e : Bond c, separation (s.act i.1) e.1 ≤ predReach S.patch+1 → Lattice.gauge w V e=increment 1 (paint G c B) e)
    {C : ℝ} (hQ : Allows n (gaugeQ S s k) (B,0) C) (j : G.ColorIndex) :
    Allows n (fun z => reaction k V s i z j) 0 (transmit G n C) := by
  let u := constantGauge w S.ratio (affine s 0 (S.ratio.embed i.1))
  have hz := routing_allows S hr w
  rw [← routing_zero S hr w] at hQ
  have he := ((((hQ.comp hz).linear _ (paint_size G c)).linear _ (allows_at (E:=G.Color) i)).linear _ (adjoint_size (G:=G) u⁻¹)).linear _ (tint_size (G:=G) j)
  simp only [one_mul] at he
  exact he.germ ((transferTurn h w hr hv).symm.fun_comp fun t : G.Color => t j)

lemma contacts_pay (G : Gauge) (P : Patch) (K : KernelChoices) (hp : P.Branches K G) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → 100*(1+radiusB x) ≤ c.val →
    ∀ (A : Stores S) (T U : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V → ∀ s (i : raw G c),
    Allows n (fun z => contacts x A T U k V s z i) 0 C := by
  obtain ⟨r,C,hr,hC,-,H⟩ := Small.vicinity_cost P G K hp n
  obtain ⟨δ,hδ,he⟩ := Small.obtain_log G (lt_min hr (show 0 < radius G n /filePrice G from div_pos (radius_pos ..) (zero_lt_one.trans_le (file_pos G))))
  have ht : ∀ᶠ x : ℝ in atTop, LocalJet.permit P * temp x ≤ δ := by
    have h0 := Work.E01.fiery_le G (1:Side) (LocalJet.permit P)
    filter_upwards [h0,(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx h
    simpa [fiery,betaF] using hx.trans h
  refine ⟨_, transmit_nn G n hC,?_⟩
  filter_upwards [ht,small_span P, Work.E01.radiusB_tendsto.eventually_ge_atTop (LocalJet.allot P+1)] with x hx hS hx'
  intro c f S hP hK hR A T U k V hV s i
  have h : S.patch.Branches S.kernel G := by rwa [hP,hK]
  unfold contacts; split
  swap; · exact allows_const _ ((norm_zero.le).trans (transmit_nn G n hC))
  rename_i hi
  obtain ⟨w,W,h,hW⟩ := release_gauge hV hP hS (by omega) (by omega) hi
  obtain ⟨B,hB,hB'⟩ := he W (fun i => (hW i).trans hx)
  have hy : ‖((B,(0:Vec G f 1)):pair G c f)‖<r := by rw [Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _)]; exact hB.trans_le (min_le_left ..)
  apply transmit_pay (G:=G) (B:=B) (by rwa [hP,hK]) w
    (fun e => (norm_le_pi_norm _ _).trans_lt (((paint G c).toContinuousLinearMap.le_opNorm B).trans_lt ((mul_le_mul_of_nonneg_right (paint_size G c) (norm_nonneg B)).trans_lt ?_)))
    (fun e he => (h e he).symm.trans (congr_fun hB'.symm e))
  · subst P K
    have hQ := (H (h:=S.sizes) (by omega) s k (B,0) hy).2
    exact allows_pi hC (fun i => ⟨contDiffAt_pi.mp hQ.1 i,hQ.2 i⟩)
  rw [mul_comm,← lt_div_iff₀ (zero_lt_one.trans_le (file_pos G))]; exact hB.trans_le (min_le_right ..)
end YM.SelectedOrderedKernels.Selected
