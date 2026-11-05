import YM.Branch.Channel

/-! Transport of frames and masses under gauging and patches. -/

set_option autoImplicit false
noncomputable section
namespace YM.RG.Patch
open Lattice Wilson Function Finset
open scoped Matrix.Norms.Frobenius BigOperators

variable (P : Patch) {G : Gauge}

/-- Offset about patch center -/
def permBox (r : ℕ) (s : Signed) : Equiv.Perm ↥(box r) :=
  let b (q : Signed) := fun (x : ↥(box r)) => (⟨q.act x.val,(Axial.aff_mem q _ (box_covariant r q) _).mp x.property⟩:↥(box r))
  ⟨b s,b s⁻¹, fun _ => Subtype.ext (s.inv_act _),fun _ => Subtype.ext (s.act_inv _)⟩

def offset (s : Signed) : Equiv.Perm P.Points := permBox _ s

def orient (s : Signed) : Equiv.Perm P.FrameTag := Equiv.prodCongr (P.offset s) (orderEquiv s)

@[simp] lemma coord (s : Signed) (x : P.Points) : (P.offset s x).val=s.act x.val := rfl

@[simp] lemma at_zero (s : Signed) : P.offset s P.center=P.center := Subtype.ext (map_zero s.actEquiv)

lemma via_channel (s : Signed) (U : CoverConfig G) (h : P.Frame G) (x y : P.Points) (o : Lattice.Order) :
    P.via (h ∘ P.offset s) (pull s 0 U) x y o = P.via h U (P.offset s x) (P.offset s y) (orderEquiv s o) := by
  unfold via; rw [travel_pull, send_route _ _ _ s 0]; simp [affine]

lemma axial_channel (s : Signed) (U : CoverConfig G) (t : P.FrameTag) :
    P.axial (pull s 0 U) t=P.axial U (P.orient s t) ∘ P.offset s := by
  funext x; unfold axial; rw [travel_pull, send_route _ _ _ s 0]; simp [affine]; rfl

lemma min_channel (s : Signed) (U : CoverConfig G) (C : KernelChoices) :
    P.usesMin C (pull s 0 U) ↔ P.usesMin C U := by
  unfold usesMin
  conv_rhs => rw [(orderEquiv s).surjective.forall]; intro l; rw [(orderEquiv s).surjective.forall]; intro k; rw [(P.offset s).surjective.forall]; intro x; rw [(P.offset s).surjective.forall]
  simp_rw [axial_channel,via_channel]; simp only [orient,Equiv.prodCongr_apply,Prod.map_apply,at_zero]

lemma chooses_channel (s : Signed) (U : CoverConfig G) (h : P.Frame G) :
    P.minimizing (pull s 0 U) (h ∘ P.offset s) ↔ P.minimizing U h := by
  have he (h : P.Frame G) : P.score (pull s 0 U) (h ∘ P.offset s)=P.score U h := by
    simp_rw [score,via_channel,average]
    conv_rhs => rw [← Equiv.sum_comp (P.offset s)]
    apply congr_arg
    refine sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Equiv.sum_comp (P.offset s)]
    apply congr_arg
    refine sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← Equiv.sum_comp (orderEquiv s)]
  have hs : Surjective (fun h : P.Frame G => h ∘ P.offset s) := fun f =>
    ⟨f ∘ (P.offset s).symm, by funext; simp⟩
  unfold minimizing
  rw [hs.forall]; simp only [Function.comp_apply,P.at_zero,he]

lemma selected_channel {C : KernelChoices} (hb : P.Branches C G) (s : Signed) (U : CoverConfig G) (h : P.usesMin C U) :
    P.selected (pull s 0 U)=P.selected U ∘ P.offset s :=
  (hb.frame_unique _ ((P.min_channel s U C).mpr h)).unique (P.min_exists _).choose_spec ((P.chooses_channel s U _).mpr (P.min_exists _).choose_spec)

lemma axial_cost_channel (s : Signed) (U : CoverConfig G) (t : P.FrameTag) :
    P.axialCost (pull s 0 U) t=P.axialCost U (P.orient s t) := by
  rw [Axial.edge_cost,Axial.edge_cost]
  let q := P.orient s t
  let T := Axial.traveller (allAxes q.2) U q.1.val
  have he : Axial.traveller (allAxes t.2) (pull s 0 U) t.1.val = fun i => T (affine s 0 i) := by
    funext i; change travel _ _ (route _ _ _) = travel _ _ (route _ _ _)
    rw [travel_pull,send_route _ _ _ _ 0]; simp only [affine,add_zero]; rfl
  rw [he, show Lattice.gauge (fun i => T (affine s 0 i)) (pull s 0 U)=pull s 0 (Lattice.gauge T U) by
    funext ⟨x,i⟩; change _=((posDir i).rotate s).read (Lattice.gauge T U) (affine s 0 x)
    rw [Step.gauge_read]; simp only [Lattice.gauge,Step.vec_rotate,Step.vec_pos]; simp only [pull,affine, Signed.act_add, add_zero]]
  exact (Axial.channels _ _ s (box_covariant _ _)).2

lemma good_channel (s : Signed) (U : CoverConfig G) (t : P.FrameTag) (C : KernelChoices) :
    t ∈ P.eligible C (pull s 0 U) ↔ P.orient s t ∈ P.eligible C U := by
  simp only [eligible,mem_filter,mem_univ,true_and, axial_cost_channel, Axial.face_cost]; rw [(Axial.channels _ _ s (box_covariant _ _)).1]

lemma frames_channel {C : KernelChoices} (hb : P.Branches C G) (s : Signed) (U : CoverConfig G) (t : P.FrameTag) :
    P.frameMass C (pull s 0 U) t = P.frameMass C U (P.orient s t) ∧
    P.frame C (pull s 0 U) t=P.frame C U (P.orient s t) ∘ P.offset s := by
  classical
  by_cases h : P.usesMin C U
  · simp only [frameMass, frame, if_pos h,if_pos ((P.min_channel s U C).mpr h), P.selected_channel hb s U h,and_self]
  have h' : ¬ P.usesMin C (pull s 0 U) := by rwa [P.min_channel]
  have hi : (P.eligible C (pull s 0 U)).map (P.orient s).toEmbedding=P.eligible C U := by
    ext i
    obtain ⟨j,rfl⟩ := (P.orient s).surjective i
    simp [P.good_channel]
  constructor
  · have he : (P.eligible C (pull s 0 U)).card = (P.eligible C U).card := by rw [← hi,card_map]
    by_cases hz : t∈ P.eligible C (pull s 0 U)
    · simp only [frameMass, if_neg h',if_neg h,if_pos hz, if_pos ((P.good_channel ..).mp hz),he]
    have hx : P.orient s t∉ P.eligible C U := fun e => hz ((P.good_channel ..).mpr e)
    simp only [frameMass,if_neg h,if_neg h',if_neg hz,if_neg hx]
  simp only [frame,if_neg h',if_neg h,axial_channel,Function.comp_def,at_zero]

/-- without `s` for gauge version. -/
def changed (k : Cover → G.El) (h : P.Frame G) : P.Frame G := fun i => k P.center.val * h i * (k i.val)⁻¹

@[simp] lemma via_gauged (U : CoverConfig G) (k : Cover → G.El) (h : P.Frame G) (x y i) :
    P.via (P.changed k h) (Lattice.gauge k U) x y i=k P.center.val*P.via h U x y i*(k P.center.val)⁻¹ := by
  simp only [via,changed,travel_gauge,route_end]; group

lemma axial_gauged (U : CoverConfig G) (k : Cover → G.El) (t : P.FrameTag) (x : P.Points) :
    P.axial (Lattice.gauge k U) t x=k t.1.val * P.axial U t x * (k x.val)⁻¹ := by simp only [axial,travel_gauge,route_end]

lemma min_gauged (U : CoverConfig G) (k : Cover → G.El) (C : KernelChoices) :
    P.usesMin C (Lattice.gauge k U) ↔ P.usesMin C U := by
  have hx (i : Lattice.Order) : P.axial (Lattice.gauge k U) (P.center,i)=P.changed k (P.axial U (P.center,i)) := by funext x; exact P.axial_gauged U k _ x
  simp only [usesMin,hx,via_gauged,G.chord_conj]

lemma frame_gauged {C : KernelChoices} (hb : P.Branches C G) (k : Cover → G.El) (U : CoverConfig G) (t : P.FrameTag) :
    P.frameMass C (Lattice.gauge k U) t = P.frameMass C U t ∧
    P.frame C (Lattice.gauge k U) t = P.changed k (P.frame C U t) := by
  classical
  by_cases h : P.usesMin C U
  · simp only [frameMass,frame, if_pos h,if_pos ((P.min_gauged U k C).mpr h),true_and]
    refine (hb.frame_unique _ ((P.min_gauged U k C).mpr h)).unique (P.min_exists _).choose_spec ?_
    have hs : Surjective (P.changed k) := fun f => ⟨P.changed (fun i => (k i)⁻¹) f,by funext; simp [changed,mul_assoc]⟩
    have he (i) : P.changed k i P.center=1 ↔ i P.center=1 := by simp [changed]
    unfold minimizing
    rw [hs.forall]; simp only [he,score,via_gauged,G.price_conj]; exact (P.min_exists _).choose_spec
  have h' : ¬ P.usesMin C (Lattice.gauge k U) := by rwa [P.min_gauged]
  constructor
  · have hh (a : P.FrameTag) : P.axialCost (Lattice.gauge k U) a=P.axialCost U a := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [axial_gauged,axial_gauged]; simp only [Lattice.gauge]; refine Eq.trans (congr_arg G.chord (show _ = k a.1.val * (P.axial U a i * U (i.val,j) * _⁻¹)*(k a.1.val)⁻¹ from ?_)) (G.chord_conj ..)
        group
      rfl
    have he : P.eligible C (Lattice.gauge k U)=P.eligible C U := by simp only [eligible,hh,Axial.face_cost,Axial.faces_gauge_symm]
    by_cases hs : t ∈ P.eligible C U <;> simp [frameMass,h,h',he,hs]
  funext x
  simp only [frame,if_neg h',if_neg h,changed, axial_gauged]; group

lemma weight_invariant (s : Signed) (x : P.Points) : P.weight (P.offset s x)=P.weight x := by
  let r : Equiv.Perm P.Rolls := Equiv.piCongrRight (fun _ => permBox (P.L.val/2) s)
  have he (i : P.Rolls) : P.addRoll (r i)=P.offset s (P.addRoll i) := by
    apply Subtype.ext
    change ∑ j, s.act (i j).val = s.act (∑ j, (i j).val)
    exact (map_sum s.actEquiv ..).symm
  unfold weight; rw [← Equiv.sum_comp r]; simp_rw [he,(P.offset s).injective.eq_iff]
end YM.RG.Patch
