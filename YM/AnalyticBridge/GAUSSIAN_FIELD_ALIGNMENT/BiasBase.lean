import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations

set_option warningAsError false

/-!
# Actual affine bias in the two mean-window conventions: base row inputs

Bound selected `base` by local rotations with slack around its whole queried
stencil (not assuming all V globally small). Use prediction of the same
`Choices`, on whichever channel the row lives. , after-L, real
zero external derivatives. Does NOT authorize enlarging to all fine or
noise rows under the weighted label costs in E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.BiasBase
open Filter Function Set Lattice RG Precision Wilson Pressure Tube Stores Bid Exterior Bloch Matrix
open Push.SectorMeasure Oriented Next.Fluctuations Next.SectorChange Rows LocalJet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ} {T : Tube G S}

def smallPrice (P : Patch) : ℝ := 16*(2*((allot P+1:ℕ):ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)
lemma small_nn (P : Patch) : 0 ≤ smallPrice P := by unfold smallPrice; positivity
lemma delay_temp (G : Gauge) {E δ : ℝ} (h : 0 < δ) : ∀ᶠ x : ℝ in atTop, E*temp x ≤ δ := by
  have he := YM.Work.E01.largeT_tendsto G (1:Side)
  filter_upwards [YM.Work.E01.fiery_le G (1:Side) E,he.eventually (ge_mem_nhds h)] with y hy hY
  simpa [fiery,betaF] using hy.trans hY

def Origin {c f} (S : StepData c f) (x : ℝ) (V : Config G c) (i : Site c) := ∃ z : Site c → G.El,
    ∀ e : Bond c,separation i e.1 ≤ allot S.patch → G.chord (Lattice.gauge z V e) ≤ smallPrice S.patch*temp x

/-- Readable even just on the table. -/
lemma at_origin (s : Signed) (i : Where S) (p : Site c) {V : Config G c} {A : Stores S} {F : Tree.Forest S.ratio}
    (h : A.flags=RG.flags (temp x) V) (hc : 100*(1+radiusB x) ≤ c.val) (hl : allot S.patch+1 ≤ radiusB x)
    (hx : span S.patch x ≤ radiusB x/50) (he : curb (shots S x) A F x s i)
    (hp : separation (roots S i) p ≤ till x) : Origin S x (pull s 0 V) p := by
  let R := allot S.patch
  have hh (j : Site c) (hy : separation p j ≤ R+1) : j ∉ RG.flags (temp x) (pull s 0 V) := fun h' => by
    have ht := Finset.mem_image_of_mem (affine s 0) h'; rw [YM.Work.H03.flags_send,← h,affine,add_zero] at ht
    apply (guarded hx he).1
    refine halo_spec.mpr ⟨s.act j, Finset.mem_union_right _ ht, ?_⟩
    rw [separation_comm,separation_signed]; have hi := separation_triangle (roots S i) p j
    unfold till at hp; unfold R at *; omega
  exact YM.Work.E08.axial_patch p (pull s 0 V) R _ le_rfl (by unfold R; omega) _ (Work.E04.temp_nonneg _) fun j hy q =>
    le_of_not_gt (fun ht => hh j hy ((RG.flags_spec ..).2 ⟨(j,q),Work.E01.base_touched _,ht⟩))

lemma face_price (i : Cell f) (s : Signed) (V : Config G c) (hp : Origin S x (pull s 0 V) (S.ratio.parent i.1)) :
    ‖G.curvature (faceValue (facade S s V 0) i)‖ ≤ (4*smallPrice S.patch)*temp x := by
  obtain ⟨z,hz⟩ := hp
  let W := pull s 0 V; let U := replica S.ratio (Lattice.gauge z W); let p := S.ratio.parent i.1
  let Y (e : Bond f) := if separation p (S.ratio.parent e.1) ≤ 4 then U e else 1
  have hi : ‖G.curvature (faceValue (facade S s V 0) i)‖=‖G.curvature (faceValue U i)‖ := by
    unfold U
    rw [fixed_facade,← copied S.ratio S.patch.odd_side, face_gauge,G.curvature_conjugate,G.norm_adjoint,
      Locations.replica_move, show S.ratio.embed (0:Site c)=0 from S.ratio.root.map_zero]
  have he : faceValue U i=faceValue Y i := travel_near _ (Work.E03.parent_step S) U Y _ _ 4 le_rfl (fun e he => (if_pos he).symm)
  rw [hi,he]; apply (G.curvature_norm _).trans
  have ht (e : Bond f) : G.chord (Y e) ≤ smallPrice S.patch*temp x := by
    have hn := G.chord_one.trans_le (mul_nonneg (small_nn S.patch) (Work.E04.temp_nonneg x))
    unfold Y U replica; split_ifs with ht hh
    · exact hn
    · exact hz (S.ratio.parent e.1,e.2) (ht.trans (by unfold allot; omega))
    exact hn
  exact (travel_chord Y _ _ _ ht).trans_eq (mul_assoc (4:ℝ) ..).symm

set_option maxHeartbeats 800000 in
/-- Keep actual branch prediction at replica. Local gauge then transplant
*fields* at that same stencil; no inference from smoothness on a torus whose
size determined the derivative cost. -/
lemma pred_price (P : Patch) (K : KernelChoices) (G : Gauge) (hP : P.Branches K G) : ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f} (S : StepData c f) (V : Config G c), S.patch=P → S.kernel=K → ∀ (s : Signed) (i : Bond c) (k : S.Choices),
    Origin S x (pull s 0 V) i.1 → ‖Tube.Z S (S.prediction (facade S s V 0) (choice s k)) (pull s 0 V) i‖ ≤ C*temp x := by
  obtain ⟨D,δ,hD,hδ,Hd⟩ := extend_interior G
  obtain ⟨A,r,hA,hr,HA⟩ := z_chart_cost P K G hP
  have hm := small_nn P
  refine ⟨2*A*D*smallPrice P+1,by positivity,?_⟩
  filter_upwards [delay_temp (G:=G) (E:=smallPrice P) hδ, delay_temp (G:=G) (E:=D*smallPrice P) (lt_min hr zero_lt_one)] with x hδ hr
  intro c f S V hS hK s i k hw
  let V' := pull s 0 V
  obtain ⟨z,hz⟩ := hw
  let t := smallPrice P * temp x
  rw [hS] at hz
  have ht := Work.E04.temp_nonneg x; have hv : 0 ≤ t := mul_nonneg hm ht
  let W := Lattice.gauge z V'
  obtain ⟨a,ha,H⟩ := Hd id i.1 (allot P) W t hv hδ hz
  let U := replica S.ratio W
  obtain ⟨b,hb,I⟩ := Hd S.ratio.parent i.1 (allot P) U t hv hδ (fun i hi => by
    unfold U replica; split <;> first | exact G.chord_one.trans_le hv | exact hz (_,i.2) hi)
  have hh : ‖(b,a)‖ ≤ D*t := (max_le hb ha)
  have h1 : D*t ≤ 1 := by unfold t; rw [← mul_assoc]; exact hr.trans (min_le_right ..)
  have h2 : D*t ≤ r := by unfold t; rw [← mul_assoc]; exact hr.trans (min_le_left ..)
  have hbr : S.patch.Branches S.kernel G := hS.symm ▸ hK.symm ▸ hP
  have H1 : S.prediction (Lattice.gauge (constantGauge z S.ratio) (replica S.ratio V')) (choice s k) = Lattice.gauge z (S.prediction (replica S.ratio V') (choice s k)) := by rw [(choice_gauge hbr _ _ _).2,show constantGauge z S.ratio ∘ S.ratio.embed=z from funext fun j => congr_arg _ (S.ratio.embed_parent j)]
  have h0 : ‖Tube.Z S (S.prediction (facade S s V 0) (choice s k)) V' i‖ = ‖zTest S (choice s k) i (b,a)‖ := by
    have he := Gauges.Z_turn (S:=S) (S.prediction (replica S.ratio V') (choice s k)) V' z i
    rw [← H1,copied S.ratio S.patch.odd_side] at he
    have hh : Tube.Z S (S.prediction U (choice s k)) W i = zTest S (choice s k) i (b,a) := by
      unfold Tube.Z zTest
      rw [prediction_near_eq hbr U (represent b) _ i (fun e he => I e (by rw [hS] at he; unfold allot; exact he.trans (by omega))), H i (by simp)]; rfl
    rw [show facade S s V 0=replica S.ratio V' from by rw [fixed_facade, show replica S.ratio V'=_ from Locations.replica_move (S:=S) s 0 V, show S.ratio.embed (0:Site c)=0 from S.ratio.root.map_zero], ← hh,show Tube.Z S (S.prediction U _) W i = _ from he,G.norm_adjoint]
  obtain ⟨hl,hq⟩ := HA c f S hS hK (choice s k) i (b,a)
  rw [h0]
  apply (show ‖zTest S (choice s k) i (b,a)‖ ≤ ‖zTest S (choice s k) i (b,a)-zLin S b a i‖ + ‖zLin S b a i‖ from by simpa only [sub_add_cancel] using! norm_add_le (zTest S (choice s k) i (b,a)-zLin S b a i) (zLin S b a i)).trans
  have he : ‖(b,a)‖^2 ≤ ‖(b,a)‖ := by have hn := norm_nonneg (b,a); nlinarith [hh.trans h1]
  calc
    _ ≤ A*‖(b,a)‖^2 + A*‖(b,a)‖ := add_le_add (hq (hh.trans h2)) hl
    _ ≤ (2*A*D*smallPrice P+1)*temp x := by dsimp only [t] at hh; linarith only [mul_le_mul_of_nonneg_left he hA.le, mul_le_mul_of_nonneg_left hh hA.le,ht]

lemma barrel_cost {n : Side} (W : PathData G) {p σ E Λ} (hb : W.Bounds p σ E Λ) (r : ℕ) (U : Config G n)
    (a : Cell n → G.Color) (i : Cell n) {C : ℝ} (hC : 0 ≤ C) (h : ∀ s : RG.Slot, s.length ≤ r → ‖a (Work.F03.slotFace s i.1)‖ ≤ C) :
    ‖barrel W r U a i‖ ≤ E*C := by
  have he := (barrel_summed W r U a i hb).norm
  rcases hb.rows i.2 with ⟨hn,hs,ht⟩
  calc
    _ ≤ _ := norm_tsum_le_tsum_norm he
    _ ≤ _ := he.tsum_le_tsum (fun j => ?_) (hs.mul_right C)
    _ ≤ _ := by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ht hC
  dsimp only; split
  next hk =>
    rw [norm_smul,Real.norm_eq_abs,G.norm_adjoint]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by have hw := hb.width; positivity))) (h _ hk) (norm_nonneg _) (hn _)
  rw [norm_zero]; exact mul_nonneg (hn _) hC

lemma allowances (P : Teller G) (d : Patch) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f} (S : StepData c f) (T : Tube G S), S.patch=d → P.Funds S T → ∀ (V : Config G c),
      (∀ i, ‖T.Mv (till x) (temp x) V i‖ ≤ C*temp x) ∧ ∀ i, ‖T.Mw (till x) (temp x) V i‖ ≤ C*temp x := by
  let L : ℝ := d.L.val
  let A := Work.E04.capacity P.below; let E : ℝ := Fintype.card Layers2
  have he : 0 ≤ E := Nat.cast_nonneg _
  have hL : 0 < L := Nat.cast_pos.mpr d.L.property
  let D := E*|P.C|+E*(|P.C|/L^2)
  have ha := Work.E04.capacity_pos P.below
  refine ⟨D*A+1,by have : 0≤D := by unfold D; positivity
                   have : 0<A := ha
                   positivity,?_⟩
  filter_upwards [Work.E04.eventually_room 0 P.below.clip.relaxation P.below.clip.radius_pos] with x hx
  intro c f S T hd ht V
  obtain ⟨a,b,hf,hc⟩ := ht.feeds
  obtain ⟨hm,ho,hM,hA⟩ := ht.crosses
  have hs := Work.E04.temp_nonneg x
  have H := Work.E04.lanes (q:=id (α:=Site c)) (a:=P.below) hc le_rfl hs S.patch.L.property (fun i j => Nat.le_succ _) (by simpa using hx)
  have hB (i : Twin c) : ‖T.vision (till x) (temp x) V i‖ ≤ A*temp x := by
    unfold Tube.vision; rw [ht.low]; exact Work.E04.thinned_le (Work.E04.capacity_ge _).2.2 hs H V i
  have hn := mul_nonneg ha.le hs
  have Hy : D*(A*temp x) ≤ (D*A+1)*temp x := by linarith
  constructor <;> intro i
  all_goals apply (Work.E04.zip_le _ _ hn hB i (C:=D) ?_).trans Hy
  · have h := (Work.E03.leap_anchored S T.R (radiusB x) V P.width.le hM).rows i
    apply h.trans; unfold D L; rw [hd]; have h := le_abs_self P.C
    exact le_add_of_nonneg_of_le (by positivity) (by gcongr)
  have h := (Work.E03.lane_anchored T.R.mn (Work.E03.poleEquiv c) (Work.E03.meshEquiv c) (radiusB x) S.patch.L.val S.patch.L.property V P.width.le hm).rows i
  exact h.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) he).trans (le_add_of_nonneg_right (by positivity)))

def Knob (P : Teller G) := max P.top.paths (Real.sqrt P.top.clip.direct)

lemma Xf_cost {P : Teller G} (hT : P.Funds S T) {V : Config G c} {A : Stores S} {F : Tree.Forest S.ratio}
    (s : Signed) (i : Twin f) (hA : A.flags = RG.flags (temp x) V) (h : keep x (shots S x) A F (s,Sum.inl i)) (hc : 100*(1+radiusB x) ≤ c.val) (hl : allot S.patch+1 ≤ radiusB x) (hx : span S.patch x ≤ radiusB x/50) :
    ‖T.Xf (till x) (facade S s V 0) i‖ ≤ Knob P * (4*smallPrice S.patch)*(temp x) := by
  let p := S.ratio.parent i.1.1; let C := 4*smallPrice S.patch*temp x
  have he (j : Cell f) (he : separation p (S.ratio.parent j.1) ≤ till x) : ‖G.curvature (faceValue (facade S s V 0) j)‖ ≤ C :=
    face_price j s V (at_origin s _ _ hA hc hl hx (show curb _ A F x s (Sum.inl i.1) from h) he)
  have hn : 0≤C := by unfold C; have := small_nn S.patch; have := Work.E04.temp_nonneg x; positivity
  unfold Tube.Xf plotted; rw [mul_assoc]; split
  · obtain ⟨l,m,hh,-⟩ := hT.feeds
    rw [← barrel_term]
    refine (barrel_cost T.up hh _ _ _ i.1 hn (fun s hs => ?_)).trans (by gcongr; exact le_max_left ..)
    apply he; exact (slot_distance s (S:=S) _).trans (by unfold RG.Slot.length at hs; omega)
  unfold shoot; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hT.high]
  exact mul_le_mul (le_max_right ..) (he _ (by unfold p; simp)) (norm_nonneg _) ((Real.sqrt_nonneg _).trans (le_max_right ..))

lemma bases (P : Teller G) (d : Patch) (h : d.Branches P.bind G) : ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f} (S : StepData c f) (T : Tube G S), S.patch=d → P.Funds S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (V : Config G c) (A : Stores S) (F : Tree.Forest S.ratio), A.flags=RG.flags (temp x) V → ∀ (k : S.Choices) (i : Slots S),
        keep x (shots S x) A F i → ‖base T x V k i‖ ≤ C*temp x := by
  obtain ⟨C,hC,H⟩ := pred_price d _ _ h
  obtain ⟨D,hD,H'⟩ := allowances P d
  let B := Knob P * (4*smallPrice d); have hB : 0 ≤ B := by unfold B Knob; have := small_nn d; have := Real.sqrt_nonneg P.top.clip.direct; positivity
  refine ⟨C+D+B,by positivity,?_⟩
  filter_upwards [H,H',small_span d, Work.E01.radiusB_tendsto.eventually_ge_atTop (allot d+1)] with x hu hv hx hy
  intro c f S T he hT hc V A F hA k i hi
  rw [← he] at hx hy
  obtain ⟨s,i|i⟩ := i
  · unfold base faceFixed; refine (norm_sub_le ..).trans ?_; have h := Xf_cost hT s i hA hi hc hy hx; rw [he] at h
    have hh := (hv S T he hT (pull s 0 V)).1 i
    linarith only [show ‖_‖ ≤ B*temp x from h,hh,mul_nonneg hC.le (Work.E04.temp_nonneg x)]
  have h := hu S V he hT.knobs s i k (at_origin s (.inr i) _ hA hc hy hx (show curb _ A F x s (.inr i) from hi) (by change separation i.1 i.1 ≤ _; simp))
  unfold base noiseFixed; refine (norm_sub_le ..).trans ?_
  have hh := (hv S T he hT (pull s 0 V)).2 i
  linarith only [hh,h,mul_nonneg hB (Work.E04.temp_nonneg x)]
end YM.AnalyticBridge.GaussianFieldAlignment.BiasBase
