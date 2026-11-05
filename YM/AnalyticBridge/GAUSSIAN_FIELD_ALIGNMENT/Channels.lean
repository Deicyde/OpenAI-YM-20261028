import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations


set_option warningAsError false

/-!
# Signed permutations and step translations of the two covariance prescriptions

Compare channel by channel only AFTER permuting the whole stack,
never making the generally wrong identification of the reversal basis on Q
term with reversal on V. Pay attention even to nonzero-bar background and to
those fixed cut transports in the frozen affine terms. This is not symmetry
of a varying path-choice procedure, Allocation, extents of every prerequisite
or labeling scheme under which these values occur. Uses the SAME numerical
path/horizon witnesses at every turn. No argument from symmetry to selection
of a compatible physical family across steps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Channels
open Function Filter Set Lattice RG Wilson Precision Exterior Tree Pressure Pressure.Stores Pressure.Tube Bloch Matrix
open Next.SectorChange Rows Push.SectorMeasure Oriented Orthogonal Tensor Locations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {α β : Type} {G : Gauge} {c f n : Side} {S : StepData c f}

def shift (b : Site n) (α : Type*) : Equiv.Perm (Site n × α) := (Equiv.addRight b).prodCongr (Equiv.refl _)
def twin (b : Site n) : Equiv.Perm (Twin n) := (shift b PlaqAxes).prodCongr (Equiv.refl Bool)
lemma translated_travel (b : Site n) (U : Config G n) (i : Site n) (w : Walk) : travel (translate b U) i w = travel U (i+b) w := by rw [← pull_one,travel_pull]; simp [affine]
lemma translated_face (b : Site n) (U : Config G n) (i : Cell n) : faceValue (translate b U) i = faceValue U (shift b _ i) := translated_travel ..
lemma slot_shift (b : Site n) (i : Site n) (s : RG.Slot) : shift b _ (Work.F03.slotFace s i) = Work.F03.slotFace s (i+b) := by unfold shift Work.F03.slotFace; simp [add_assoc]
lemma translated_barrel (b : Site n) (P : PathData G) (r : ℕ) (U : Config G n) (z : Cell n → G.Color) (i : Cell n) : barrel P r (translate b U) (fun j => z (shift b _ j)) i = barrel P r U z (shift b _ i) := by unfold barrel; simp_rw [translated_travel,slot_shift]; rfl
lemma translated_shoot (b : Site n) (p : Clip) (U : Config G n) (i : Cell n) : shoot p (translate b U) i = shoot p U (shift b _ i) := by unfold shoot; rw [translated_face]
lemma translated_shorten (b : Site n) (P : PathData G) (r d : ℕ) (U : Config G n) (i : Cell n) : shorten P r d (translate b U) i = shorten P r d U (shift b _ i) := by unfold shorten shortenTerm PathData.ellTerms; simp_rw [Work.F03.atSite_path, translated_travel, translated_face,slot_shift]; rfl
lemma translated_plot (b : Site n) (P : PathData G) (p : Clip) (r d : ℕ) (U : Config G n) (i : Twin n) : plotted P p r d (translate b U) i = plotted P p r d U (twin b i) := by unfold plotted; rw [translated_shoot,translated_shorten]; rfl
lemma translated_thinned (b : Site n) (P : PathData G) (p : Clip) (t : ℝ) (r d : ℕ) (U : Config G n) (i : Twin n) : thinned P p t d r (translate b U) i = thinned P p t d r U (twin b i) := by
  have h : PathData.kept p t i.1.1 (translate b U) ↔ PathData.kept p t (twin b i).1.1 U := by
    unfold PathData.kept; conv_rhs => rw [← (shift b PlaqAxes).forall_congr_right]
    simp_rw [translated_face]; simp [shift,twin,separation_translate]
  unfold thinned; rw [show (twin b i).2=i.2 from rfl,toll, translated_face, if_congr h rfl rfl, translated_shorten, translated_shoot]; rfl
lemma translated_Z (b : Site c) (U V : Config G c) (i : Bond c) : Tube.Z S (translate b U) (translate b V) i = Tube.Z S U V (shift b _ i) := rfl

lemma translated_lane {α β : Type*} (A : Row α β) (r d : ℕ) (b : Site n) (U : Config G n) (i j) :
    lane r d (translate b U) A i j = lane r d U A (shift b _ i) (shift b _ j) := by
  unfold lane priced rated; simp_rw [translated_travel]; simp only [shift,Equiv.prodCongr_apply,Prod.map,Equiv.coe_addRight,Equiv.refl_apply]
  apply tsum_congr; intro z; split <;> (next h => split <;> first | rfl | simp_all [add_right_comm _ b _])

lemma translated_leap (M : Towers S.patch.L) (b : Site c) (V : Config G c) (r : ℕ) (i j) :
    leap S M r (translate b V) i j = leap S M r V (twin (S.ratio.embed b) i) (twin b j) := by
  unfold leap casted; apply tsum_congr; intro z
  let g := S.ratio
  have hp : replica g (translate b V)=translate (g.embed b) (replica g V) := by simp_rw [← pull_one]; exact replica_move ..
  have he (i : Site f) : g.parent (i+g.embed b) = g.parent i + b := by simpa only [affine,Signed.act_one] using! parent_map (S:=S) 1 b i
  have h₁ : mesh (twin (g.embed b) i) = shift (g.embed b) _ (mesh i) := rfl
  have h₂ : mesh (twin b j)= shift b _ (mesh j) := rfl
  rw [hp,h₁,h₂]; simp only [shift,Equiv.prodCongr_apply,Prod.map,Equiv.refl_apply,Equiv.coe_addRight,map_add]
  rw [rated,rated,translated_travel]; -- conditions
  simp [g,he (mesh i).1,add_right_comm _ b _]
lemma translated_Mv (b : Site c) (T : Tube G S) (r : ℕ) (t : ℝ) (V : Config G c) (i : Twin f) : T.Mv r t (translate b V) i = T.Mv r t V (twin (S.ratio.embed b) i) := by
  unfold Mv vision zip; simp_rw [translated_thinned, Φ,translated_leap]; exact Equiv.sum_comp (twin b) (fun j : Twin c => (T.Φ r V (twin (S.ratio.embed b) i) j) (T.vision r t V j))
lemma translated_Mw (b : Site c) (T : Tube G S) (r : ℕ) (t : ℝ) (V : Config G c) (i : Bond c) : T.Mw r t (translate b V) i = T.Mw r t V (shift b _ i) := by
  unfold Mw vision Φ' kick zip; simp_rw [translated_thinned,translated_lane]; exact Equiv.sum_comp (twin b) (fun j : Twin c => (T.Φ' r V (shift b _ i) j) (T.vision r t V j))

section edges
variable (s : Signed) (t : Site n) (U : Config G n)
def flip (i : Bond n) : G.Color →ₗᵢ[ℝ] G.Color := { -G.adjoint (U (sendEdge s t i))⁻¹ with norm_map' := fun _ => by simp }
def scatter : ColorOrtho G (Bond n) := fun i => if s.flip i.2 then flip s t U i else LinearIsometry.id
lemma read_back (i : Bond n) : pull s t U i = if s.flip i.2 then (U (sendEdge s t i))⁻¹ else U (sendEdge s t i) := by unfold pull Step.read sendEdge; simp [posDir,Step.rotate]
lemma insert_turn (a : Directions G n) : increment (pull s t U) (lifting (scatter s t U) (StepData.sendBonds s t) a)=pull s t (increment U a) := by
  funext i; rw [read_back]; unfold increment; rw [read_back,lifting_apply]; unfold scatter; split
  next he => change G.lieExp (-G.adjoint _ _) * _ = _; rw [exp_negative,exp_adjoint]; change ((U _)⁻¹ * G.lieExp (a (sendEdge s t i)) * ((U _)⁻¹)⁻¹)⁻¹ * _ = _; group
  rfl
end edges

variable (s : Signed) (b : Site c) (q : Signed) (V : Config G c) (k : S.Choices) (T : Tube G S) (x : ℝ)
def offset := (s*q)⁻¹.act b
lemma offset_fine (g : Ratio c f) : offset s (g.embed b) q = g.embed (offset s b q) := by rw [offset,offset,g.signed]
lemma channel_turn (V : Config G c) : pull q 0 (pull s b V) = translate (offset s b q) (pull (s*q) 0 V) := by rw [pull_pull,← pull_one, pull_pull, mul_one]; simp only [offset,affine,Signed.act_inv,add_zero,Signed.act_zero,zero_add]
def ticket := (S.withinChoice s b).symm k
def diagram (S : StepData c f) := StepData.sendBonds s (S.ratio.embed b)
def fiber (S : StepData c f) := scatter s (S.ratio.embed b) (replica S.ratio V)

lemma lift_turn (a : Directions G f) : increment (replica S.ratio (pull s b V)) (lifting (fiber s b V S) (diagram s b S) a) = pull s (S.ratio.embed b) (increment (replica S.ratio V) a) := by rw [replica_move]; exact insert_turn ..
lemma facade_move (a : Directions G f) : facade S q (pull s b V) (lifting (fiber s b V S) (diagram s b S) a) = translate (S.ratio.embed (offset s b q)) (facade S (s*q) V a) := by unfold facade; rw [lift_turn,channel_turn,offset_fine]
lemma facade_zero : facade S q (pull s b V) 0 = translate (S.ratio.embed (offset s b q)) (facade S (s*q) V 0) := by simpa only [map_zero] using facade_move (S:=S) s b q V 0

variable (h : S.patch.Branches S.kernel G)
include h
lemma prediction_move (a : Directions G f) :
    S.prediction (facade S q (pull s b V) (lifting (fiber s b V S) (diagram s b S) a)) (choice q (ticket s b k)) =
    translate (offset s b q) (S.prediction (facade S (s*q) V a) (choice (s*q) k)) := by
  unfold facade; rw [(carry q h (ticket s b k) _).2,(carry (s*q) h k _).2, lift_turn,S.prediction_channel h,ticket,Equiv.apply_symm_apply, channel_turn]
lemma prediction_zero : S.prediction (facade S q (pull s b V) 0) (choice q (ticket s b k)) = translate (offset s b q) (S.prediction (facade S (s*q) V 0) (choice (s*q) k)) := by simpa only [map_zero] using prediction_move s b q V k h 0
lemma predicts_turn (a : Directions G f) (i : Bond c) : predictorTurn (pull s b V) (ticket s b k) q i (lifting (fiber s b V S) (diagram s b S) a) = predictorTurn V k (s*q) (shift (offset s b q) _ i) a := by unfold predictorTurn predictGroup; rw [prediction_move s b q V k h, prediction_zero s b q V k h]; rfl

omit h in
lemma faceJet_turn (a : Directions G f) (p : Cell f) :
    plaquetteJet S (pull s b V) q p (lifting (fiber s b V S) (diagram s b S) a) = plaquetteJet S V (s*q) (shift (S.ratio.embed (offset s b q)) _ p) a := by
  unfold plaquetteJet; refine derives _ (ContinuousLinearEquiv.refl ℝ G.Color) (fun a => ?_) a; rw [facade_move,translated_face]; rfl
lemma blockJet_turn (a : Directions G f) (i : Bond c) : blockJet (pull s b V) (ticket s b k) q i (lifting (fiber s b V S) (diagram s b S) a) = blockJet V k (s*q) (shift (offset s b q) _ i) a := by
  unfold blockJet; refine derives _ (ContinuousLinearEquiv.refl ℝ G.Color) (fun a => ?_) a; rw [predicts_turn s b q V k h]; rfl

omit h in
def shiftSlot (g : Ratio c f) : Equiv.Perm (Twin f ⊕ Bond c) := Equiv.sumCongr (twin (g.embed (offset s b q))) (shift (offset s b q) _)
def perChannel (S : StepData c f) : Equiv.Perm (Slots S) where
  toFun i := (s*i.1,shiftSlot s b i.1 S.ratio i.2)
  invFun i := (s⁻¹*i.1,(shiftSlot s b (s⁻¹*i.1) S.ratio).symm i.2)
  left_inv i := by simp
  right_inv i := by simp

def unchanged (G : Gauge) (S : StepData c f) : ColorOrtho G (Slots S) := fun _ => LinearIsometry.id
lemma rotated_bump (a : Directions G f) (i : Slots S) : bump T x (pull s b V) (ticket s b k) (lifting (fiber s b V S) (diagram s b S) a) i = unchanged G S i (bump T x V k a (perChannel s b S i)) := by
  obtain ⟨q,p|i⟩ := i
  · change faceKick T x (pull s b V) (lifting (fiber s b V S) (diagram s b S) a) q p = faceKick T x V a (s*q) (twin _ p)
    unfold faceKick; rw [show (twin _ p).2=p.2 from rfl]; split
    next he => simp_rw [facade_zero,faceJet_turn]; exact translated_barrel (S.ratio.embed (offset s b q)) T.up _ _ (fun i => plaquetteJet S V (s*q) i a) _
    next he => rw [faceJet_turn]; rfl
  change -(Real.sqrt S.kernel.penalty • blockJet (pull s b V) (ticket s b k) q i _) = noiseKick ..
  rw [noiseKick,blockJet_turn s b q V k h]; rfl
lemma rotated_base (i : Slots S) : base T x (pull s b V) (ticket s b k) i = unchanged G S i (base T x V k (perChannel s b S i)) := by
  obtain ⟨q,i|i⟩ := i
  · change faceFixed T _ q _ i=faceFixed T _ (s*q) _ (twin _ i); rw [faceFixed,facade_zero,channel_turn,Tube.Xf,translated_plot, translated_Mv]; rfl
  change noiseFixed T _ _ _ q i=noiseFixed T _ _ _ (s*q) _; rw [noiseFixed,prediction_zero s b q V k h,channel_turn,translated_Z,translated_Mw]; rfl

variable (A : Stores S) (F : Forest S.ratio)

theorem turned_cov {σ E Λ : ℝ} (hT : T.up.Bounds T.high σ E Λ) : Equivalent T V (pull s b V) k (ticket s b k) (Locations.active s b A F x) (onBond (fiber s b V S)) := gram_motion (diagram s b S) _ _ _ _ h hT (fun _ => rfl) (rotated_bump s b V k T x h) (geometry _ s b (fun _ => rfl))

def rollY (Y : LinkArray G (Frozen A x F)) : LinkArray G (Frozen (book s b A) x (Locations.forest s b F)) := fun i => if s.flip i.val.val.2 then (Y (frozen s b A F x i))⁻¹ else Y (frozen s b A F x i)
omit h in
lemma rollY_shell (Y : LinkArray G (Frozen A x F)) (q : Chi) (d : ℝ) (i) : autoShell q d (pull s b V) (rollY s b x A F Y) i = fiber s b V S i.val.val (autoShell q d V Y (frozen s b A F x i)) := by
  unfold autoShell rollY; rw [replica_move, read_back]; unfold fiber scatter; split
  next he =>
    let v := replica S.ratio V (sendEdge s (S.ratio.embed b) i.val.val)
    let u := Y (frozen s b A F x i)
    change patched q d (u⁻¹*v⁻¹⁻¹)= -G.adjoint v⁻¹ (patched q d (u*v⁻¹))
    rw [show u⁻¹*v⁻¹⁻¹ = (v⁻¹*(u*v⁻¹)*v⁻¹⁻¹)⁻¹ by group,patched_inv,patched_covary]
  rfl

theorem turned_mean {σ E Λ : ℝ} (hT : T.up.Bounds T.high σ E Λ) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) :
    Means (V:=V) (V':=pull s b V) (k:=k) (k':=ticket s b k) (T:=T) (Locations.active s b A F x) q d (onBond (fiber s b V S)) Y (rollY s b x A F Y) := by
  refine means _ q d _ _ _ (turned_cov s b V k T x h A F hT) ?_
  exact blame_motion (diagram s b S) _ _ (frozen s b A F x) _ _ h hT (fun _ => rfl) (rotated_bump s b V k T x h) _ _ _ _ (fun _ => rfl) (rollY_shell s b V x A F Y q d) (rotated_base s b V k T x h)
end YM.AnalyticBridge.GaussianFieldAlignment.Channels
