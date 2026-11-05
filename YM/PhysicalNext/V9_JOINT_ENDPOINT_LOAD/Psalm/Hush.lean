import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton

/-!
# Actual strict test plateaus and their variable-Z germ regions

Uses continuation mean with frozen geometry (NOT a
formula for stereotyping a changed closure/test neighborhood); equality
with true hard at V where the compulsory output flags on these reads permit
it.

All continuation integrand and localization identities to call the
neighboring V statements on after chart/Assembly are a dictionary obligation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Planned.AtomRegular.Foliage AnalyticBridge.LocalGaussianLaws
   AnalyticBridge.LocalGaussian Heir
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {d : Desk G S}
    {I : Type} [Fintype I] {X X' : Support f} {Y : Support c} {n : ℕ} {Pt : Teller G} {C : Libretto G n} {D : Record} {Bt : Baton G}
    {r : ℝ} {V : Config G c}

structure Sounded (Pt : Teller G) (C : Libretto G n) (D : Record) (Bt : Baton G) (r : ℝ) (d : Desk G S) : Prop extends Plays C D d.out d.input.p Pt d.tube d.betaHat,
    Peace C Bt S.patch S.kernel d.W r d.betaHat where
  heat : 0<d.g
  price : d.radius = r*d.input.p.threshold

abbrev cap (D : Record) (d : Desk G S) := D.ε*d.input.p.threshold
abbrev Score (a : Museum F d.betaHat A X Y I) (D : Record) (Z : Set (Site f)) (z : Prices G I) := Guarded a Z d.g (cap D d) z
abbrev field (k : S.Choices) (a : Museum F d.betaHat A X Y I) (U : Config G c → Config G f) (w : Config G c → Prices G I) (W : Config G c) :=
    a.received k d.tube d.broadCut d.radius d.g W (U W) (w W)
abbrev liftU (k : S.Choices) (a : Museum F d.betaHat A X Y I) (U : Config G c → Config G f) (w : Config G c → Prices G I) (W : Config G c) (i : I) :=
    a.deposited k d.tube d.broadCut d.radius d.g W (U W) (w W) (a.seat i)
omit [Fintype I] in
private lemma fine_quiet (a : Museum F d.betaHat A X Y I) {j : Cell f} (hx : Tests X j) : j∉A.costs := fun h =>
    Finset.disjoint_left.mp a.away (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j,h,Finset.mem_image_of_mem _ (Work.E01.base_touched _)⟩))) (a.asks j.1 (hx.retain (Work.E01.base_touched _)) (halo_subset _ _ (Finset.mem_singleton_self _)))
omit [Fintype I] in
private lemma noise_quiet (a : Museum F d.betaHat A X Y I) {j : Bond c} (hx : predictorUses S j ⊆ inspected X) : j∉A.aisles := fun h =>
    Finset.disjoint_left.mp a.away (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j,h,taps_first (S:=S) _⟩))) ((S.ratio.embed_parent j.1) ▸ a.asks (S.ratio.embed j.1) (hx (Or.inl (Push.GridApprox.window_home ..))) (halo_subset _ _ (Finset.mem_singleton_self _)))
private lemma share_one (q : Chi) {r t : ℝ} (hr : 0≤r) (he : r<t) : q.innerShare t r=1 := sub_eq_zero.mp (Classical.not_not.mp (fun h => he.not_gt (q.exterior_gt _ _ hr (hr.trans_lt he) h))) |>.symm
private lemma frame_gated (u : Spot d) (i : Site c) (U : Config G f) (h : uses S i U) : u.frameBit i U=1 := by
  rw [Spot.frameBit,Patch.frameMass,if_pos h, mul_inv_cancel₀ (show (Fintype.card S.patch.FrameTag:ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)]
private lemma sound_bits (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (i : Bond c) {U : Config G f} (h : Conduct S k U V i (d.W*fiery G d.betaHat S.patch.L/2)) (ha : i∉A.aisles) :
    let s:=spectacle d A F k
    s.connectorBit i U=1 ∧ s.noiseBit i V U=1 := by
  intro s; refine ⟨?_,?_⟩
  · change (Fintype.card S.patch.Points:ℝ)* S.patch.predictorMass S.kernel (S.connector U k.1 i) (k.2 i) = 1
    rw [Patch.predictorMass,if_pos h.branch,mul_inv_cancel₀ (show (Fintype.card S.patch.Points:ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)]
  change (if i∈A.aisles then _ else d.profile.innerShare _ _)=_; rw [if_neg ha]
  exact share_one _ (G.chord_nonneg _) (h.sound.trans (half_lt_self (mul_pos d.paidW d.paidScale)))

variable (h : Sounded Pt C D Bt r d) (a : Museum F d.betaHat A X Y I) (U : Config G c → Config G f) (w : Config G c → Prices G I)
    (hw : ContinuousAt w V) (hV : Healthy d.out.threshold Y V)
namespace Sounded
include h
lemma large : 0 < d.radius := h.price ▸ mul_pos ((mul_pos zero_lt_two (storeCost_pos C)).trans_le h.aperture) d.input.p.threshold_pos
include hV hw
lemma quiet_link (i : I) (hz : d.g * ‖tape (w V) i‖ ≤ cap D d) :
    ‖liftU k a U w V i‖ ≤ d.radius/2 ∧ ∀ᶠ W in 𝓝 V, let b := liftU k a U w W i
      ‖b‖ < d.radius ∧ broad d.broadCut d.radius b = 1 ∧ broad d.broadCut (2*d.radius) b = 1 := by
  have hh : ‖liftU k a U w V i‖ ≤ d.radius/2 := (displacement a U h.toPlays hV h.heat.le i hz).trans (by
    rw [h.price]; linarith only [mul_le_mul_of_nonneg_right h.aperture d.input.p.threshold_pos.le])
  refine ⟨hh,?_⟩; have ht := h.large
  filter_upwards [(deposit_cont (k:=k) (q:=d.broadCut) (d:=d.radius) (u:=d.g) a U w h.toPlays hV hw i).norm.eventually (gt_mem_nhds (hh.trans_lt (half_lt_self ht)))] with W he
  exact ⟨he,broad_one _ ht he.le,broad_one _ (by positivity) (he.le.trans (by linarith))⟩

abbrev movie (k : S.Choices) (a : Museum F d.betaHat A X Y I) := replay d.tube d.betaHat k d.broadCut d.radius d.g a
omit h hw hV in
lemma toll_match {p : Cell f} (hp : Tests X p) (V) : toll (field k a U w V) p=toll (movie k a U w V) p := congr_arg G.chord (travel_local _ _ _ _ (fun i hi hj => replay_agrees a U w i (hp.retain (List.mem_toFinset.mpr hi)) (hp.retain (List.mem_toFinset.mpr hj))))

lemma quiet_face {p : Cell f} (hp : Tests X p) (hz : Score a D (touched p) (w V)) : ∀ᶠ W in 𝓝 V,
    let t := fiery G d.betaHat S.patch.L; let s:=spectacle d A F k
    toll (field k a U w W) p < t/8 ∧ s.fineBit p (field k a U w W) = 1 := by
  let t := fiery G d.betaHat S.patch.L; have ht := h.rehearsed.fiery_eq
  have hh : toll (movie k a U w V) p<t/8 := by rw [← toll_match a U w hp V]; unfold t; rw [← ht]; exact inspected_toll a U h.toPlays hV p hp h.heat hz
  have he : ContinuousAt (fun W => toll (movie k a U w W) p) V := (show Continuous (fun U : Config G f => toll U p) by unfold toll faceValue; fun_prop).continuousAt.comp (replay_cont a U w h.toPlays hV hw)
  filter_upwards [he.eventually (gt_mem_nhds hh)] with W hw
  rw [← toll_match a U w hp W] at hw
  refine ⟨hw,?_⟩; change (if p∈A.costs then _ else _) = 1; rw [if_neg (fine_quiet a hp)]
  exact share_one _ (G.chord_nonneg _) (by change _ < t/4; linarith only [hw, (d.paidScale : 0<t)])
lemma quiet_good (he : X'⊆X) (hz : ∀ p : Cell f, Tests X' p → Score a D (touched p) (w V)) : ∀ᶠ W in 𝓝 V, Healthy d.input.p.threshold X' (field k a U w W) := by
  filter_upwards [eventually_all.mpr (fun p : {p : Cell f // Tests X' p} => h.quiet_face (k:=k) a U w hw hV (show Tests X p.val from let ⟨i,hi,h⟩ := p.property; ⟨i,he hi,h⟩) (hz p.val p.property))] with W hh
  rw [h.rehearsed.fiery_eq]; refine Finset.disjoint_left.mpr (fun i hi h => ?_)
  obtain ⟨p,hp,hp'⟩ := (flags_spec ..).mp h
  have h := (hh ⟨p,i,hi,hp⟩).1; change _ < toll (field k a U w W) p at hp'; linarith only [h,d.paidScale,hp']
lemma quiet_frame (o : Site c) (hE : frameUses S o ⊆ inspected X) (hz : Score a D (frameUses S o) (w V)) : ∀ᶠ W in 𝓝 V, uses S o (field k a U w W) ∧ (spectacle d A F k).frameBit o (field k a U w W)=1 := by
  have he W := uses_same S o (show Agrees (frameUses S o) (field k a U w W) (movie k a U w W) from fun i h h' => replay_agrees a U w i (hE h) (hE h'))
  have hh := (he V).1 (frame_pass a U w h.toPlays hV h.toPeace h.heat o hE hz)
  filter_upwards [(replay_cont a U w h.toPlays hV hw).eventually (uses_open o hh)] with W hW
  exact ⟨(he W).2 hW,frame_gated _ _ _ ((he W).2 hW)⟩
lemma quiet_noise (e : Bond c) (hE : predictorUses S e ⊆ inspected X) (hz : Score a D (predictorUses S e) (w V)) : ∀ᶠ W in 𝓝 V,
    let Q := field k a U w W; let s := spectacle d A F k
    Conduct S k Q W e (d.W * fiery G d.betaHat S.patch.L / 2) ∧ s.connectorBit e Q=1 ∧ s.noiseBit e W Q = 1 := by
  have he := baton (k:=k) (d:=d.radius) (q:=d.broadCut) a U w h.toPlays hV h.toPeace h.heat e hE hz; rw [h.rehearsed.fiery_eq] at he
  have hh W := (show Agrees (predictorUses S e) (field k a U w W) (movie k a U w W) from fun i hi hj => replay_agrees a U w i (hE hi) (hE hj))
  have hp := h.bulletin.priced; have hS : S.patch.Branches S.kernel G := hp.knobs.symm ▸ hp.kernel
  have hc := he.read hS (hh V)
  filter_upwards [((replay_cont a U w h.toPlays hV hw).prodMk continuousAt_id).eventually (hc.opened hS)] with W hW
  have hW := hW.read hS (show Agrees _ (movie k a U w W) (field k a U w W) from fun i hi hj => (hh W i hi hj).symm)
  exact ⟨hW,sound_bits A F k e hW (noise_quiet a hE)⟩
end Sounded
end YM.PhysicalNext.JointLoad.Psalm
