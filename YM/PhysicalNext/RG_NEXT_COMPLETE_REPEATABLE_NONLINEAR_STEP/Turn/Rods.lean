import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels

/-! Literal E6 flat-carrier tilted D rotations (not reusing Syl.
orientation on a curved Hessian D); real rows including boundary values. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
open ConnectedActivityE6 Shell Coat SliceRows
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}

lemma incremental_detect (U : Config G f) (a v : Directions G f) (h : ∀ t : ℝ, increment U (t • a)=increment U (t • v)) : a=v := by
  funext i
  have hh (c : G.Color): Tendsto (fun t : ℝ=>t • c) (𝓝 0) (𝓝 0) := by simpa only [zero_smul] using (show Continuous (fun t:ℝ=>t • c) by fun_prop).tendsto 0
  have he := (((hh (a i)).eventually G.plog_left).and ((hh (v i)).eventually G.plog_left)).filter_mono (nhdsWithin_le_nhds (s:=Set.Ioi 0))
  obtain ⟨t,⟨hx,hv⟩,ht⟩ := (he.and self_mem_nhdsWithin).exists
  have hp : G.lieExp (t • a i) = G.lieExp (t • v i) := mul_right_cancel (congr_fun (h t) i)
  exact (smul_right_injective G.Color (show t≠0 from (Set.mem_Ioi.mp ht).ne')) (hx.symm.trans ((congr_arg (G.plog ∘ G.mat) hp).trans hv))

section translate
variable (S) (s b) (U : Config G f) (V : Config G c) (w : Directions G f)
-- reindex in the channel
abbrev march (x : Site f) (w : Directions G f) := w ∘ Channels.shift x _
lemma pays_displacement (t : ℝ) (i : Signed) : ConnectedActivityE6.Channel.displacement i (t • w) U=t • ConnectedActivityE6.Channel.displacement i w U := by
  funext x; cases h : i.flip x.2 <;> simp [ConnectedActivityE6.Channel.displacement,h]
lemma pasted (x : Site f) : increment (translate x U) (march x w)=translate x (increment U w) := rfl
lemma posts (i : Signed) :
    ConnectedActivityE6.Channel.displacement i (wheels (S:=S) s b V w) (replica S.ratio (pull s b V)) =
      march (S.ratio.embed (offset s b i)) (ConnectedActivityE6.Channel.displacement (s*i) w (replica S.ratio V)) := by
  apply incremental_detect (pull i 0 (replica S.ratio (pull s b V))); intro t
  rw [← pays_displacement, ← map_smul (wheels s b V), ← ConnectedActivityE6.Channel.pull_increment, wheels,Channels.lift_turn,
    channel_turn, Locations.replica_move, Channels.channel_turn,Channels.offset_fine]
  let u := ConnectedActivityE6.Channel.displacement (s*i) w (replica S.ratio V)
  rw [show t • march (S.ratio.embed _) u = march (S.ratio.embed (offset s b i)) (t • u) from rfl,pasted,← pays_displacement, ConnectedActivityE6.Channel.pull_increment]

lemma shifted_knot (p : Cell f) (x : Site f) : Work.F03.faceCurl p (toLog (march x w))=Work.F03.faceCurl (Channels.shift x _ p) (toLog w) := by
  rw [curl_eq,curl_eq]; simp [march,Channels.shift,add_right_comm]

lemma shifted_volt (hb : S.patch.Branches S.kernel G) (i : Bond c) : zLin S (toLog (march (S.ratio.embed b) w)) 0 i =
    zLin S (toLog w) 0 (Channels.shift b _ i) := by
  let k : S.Choices := Classical.ofNonempty
  let a := toLog (march (S.ratio.embed b) w)
  let f (t : ℝ) := zTest S k i (t • (a,(0:LogField G c)))
  have reps (t : ℝ) : represent (t • a)=pull (1:Signed) (S.ratio.embed b) (represent (t • toLog w)) := by
    rw [pull_one]; funext i
    let j:= Channels.shift (S.ratio.embed b) Axis i
    change represent (t • a) i = represent (t • toLog w) j
    rw [Work.F03.represent_link,Work.F03.represent_link,Pi.smul_apply,Pi.smul_apply]
    change G.lieExp (t • toLog (march _ w) (pole i))=G.lieExp (t • toLog w (pole j))
    rw [at_pole,at_pole]; rfl
  have h (t : ℝ) : f t=zTest S (S.withinChoice 1 b k) (Channels.shift b _ i) (t • (toLog w,(0:LogField G c))) := by
    simp only [f,zTest, Prod.smul_fst, Prod.smul_snd, smul_zero,link_one]
    have hp (Z : Config G c) : Tube.Z S (translate b Z) (1:Config G c) i = Tube.Z S Z 1 (Channels.shift b _ i) := rfl
    rw [reps,S.prediction_channel hb,pull_one, hp]
  have he : HasDerivAt f (zLin S a 0 i) 0 := zTest_deriv hb k i _
  rw [funext h] at he; exact he.unique (zTest_deriv hb (S.withinChoice 1 b k) _ _)

variable {S}
lemma straight_tilt (T : Tube G S) (p : Rod c f) (q : Signed) (R : ℕ) (h : S.patch.Branches S.kernel G) :
    barField T R (march (S.ratio.embed (Channels.offset s b q)) w) p=barField T R w (shiftSlot s b q S.ratio p) := by
  rcases p with i|i
  · change bareCut _ _ _ (toLog (march _ w)) i=bareCut _ _ _ _ (twin _ i)
    unfold bareCut; rw [show (twin _ i).2=i.2 from rfl]; split
    · unfold ellCut
      let t := S.ratio.embed (offset s b q)
      refine tsum_congr fun j=> ?_
      change (if (T.up.row i.1.2 j).snd.length ≤ _ then _ else _ ) = if (T.up.row i.1.2 j).snd.length ≤ _ then _ else _
      split
      · rw [shifted_knot]; change _ • Work.F03.faceCurl (Channels.shift t _ _) (toLog w)=_ • _; rw [slot_shift]; rfl
      rfl
    congr 1; exact shifted_knot ..
  exact shifted_volt S (offset s b q) w h i
lemma circled (p y : Site c) (z : Site c) : carrier p (translate z V) y = carrier (p+z) V (y+z) := by
  simp only [carrier, translated_travel,carriage,add_sub_add_right_eq_sub]
lemma rolls_D (T : Tube G S) (q : Signed) (p : Rod c f) (R : ℕ) (h : S.patch.Branches S.kernel G) :
    orientedRow T R q p (pull s b V) (wheels (S:=S) s b V w)=orientedRow T R (s*q) (shiftSlot s b q S.ratio p) V w := by
  unfold orientedRow straightened; rw [posts, Channels.channel_turn, show spinRow _ _ (march _ _) = march _ _ from ?_, straight_tilt]; exact h
  let p' := offset s b q; let j:=shiftSlot s b q S.ratio p
  have he : focus S j=focus S p+p' := by rw [cost_is_here,show j=_ from rfl,rod_honors,partner,← cost_is_here]
  funext i; change G.adjoint _ _=G.adjoint _ _; unfold march; congr 1; rw [circled,← he]; congr 2; simpa only [affine,Signed.act_one] using! (Locations.parent_map (S:=S) 1 p' i.1).symm
end translate

lemma requested {F : Forest S.ratio} {T : Tube G S} (X : Coat T F) (p : Mention c f) :
    SliceRows.request T X.x (choice p.1 X.k) (pull p.1 0 X.V) p.2=Rows.base T X.x X.V X.k p := by
  rcases p with ⟨u,i|i⟩
  · unfold Rows.base; dsimp only [Sum.elim]; rw [Rows.faceFixed,fixed_facade, ConnectedActivityE6.Channel.pulls_replica]; rfl
  unfold Rows.base; dsimp only [Sum.elim]; rw [Rows.noiseFixed,fixed_facade, ConnectedActivityE6.Channel.pulls_replica]; rfl

namespace Parked
variable {F : Forest S.ratio} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    (h : Parked s b X Y) (hp : S.patch.Branches S.kernel G)
include h hp
lemma strands (p : Mention c f) (u : Directions G f) : Y.motion (wheels (S:=S) s b X.V u) p=X.motion u (perChannel s b S p) := by
  unfold Coat.motion; rw [if_congr (h.panel p) rfl rfl]; split
  · rw [h.pans, h.v,h.aligned.2.2]; exact rolls_D s b _ _ T _ _ _ hp
  rfl
end Parked
namespace Tuned
variable {F : Forest S.ratio} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    (h : Tuned s b X Y) (hp : S.patch.Branches S.kernel G) {W C : ℝ} (ht : ShellAccess S G X.x W X.width C)
include h hp ht
lemma footing (p : Mention c f) (u : Directions G f) : let p' := perChannel s b S p
    Y.realPath p.1 p.2 (wheels (S:=S) s b X.V u)=X.realPath p'.1 p'.2 u := by
  intro p'; unfold Coat.realPath
  rw [h.signal ht, requested Y p, requested X p', h.v,h.x,h.way,h.toParked.aligned.2.2]; apply congr_arg₂ (·+·)
  · exact Channels.rotated_base s b X.V X.k T X.x hp p
  exact rolls_D s b _ _ T _ _ _ hp
end Tuned
end YM.PhysicalNext.Repeat.Turn
