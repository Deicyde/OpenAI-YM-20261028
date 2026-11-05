import YM.Branch.Transport
import YM.RG.History

/-!
# Predictor transport

Under symmetry transform positive bond may invert. Preserve frame tags at
shared sites (coarse-labelled), and transform bond point once for the WHOLE
bond. Gauge transforms do not change ranges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG

open Function Lattice Wilson
open scoped Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

namespace Patch
variable (P : Patch) {C : KernelChoices}

lemma predicts {h : P.Branches C G} {T X : P.Connector G} (f : Equiv.Perm P.Points) (j : Equiv.Perm G.El)
    (hf : ∀ x, P.weight (f x)=P.weight x) (he : ∀ x, T x=j (X (f x)))
    (hs : ∀ u, P.bondCost T (j u)=P.bondCost X u) (x : P.Points) :
    P.predictorMass C T x=P.predictorMass C X (f x) ∧ P.predict C T x=j (P.predict C X (f x)) := by
  have eq (Y : P.Connector G) : P.usesBest C Y ↔ ∃ u, P.bondCost Y u < C.predictor_cut :=
    ⟨fun hx ↦ ⟨_,hx⟩, fun ⟨t,hx⟩ ↦ ((P.bond_min Y).choose_spec t).trans_lt hx⟩
  have hh : P.usesBest C T ↔ P.usesBest C X := by
    rw [eq,eq,j.surjective.exists]; simp only [hs]
  by_cases ha : P.usesBest C X
  · simp only [predictorMass, predict, if_pos ha,if_pos (hh.mpr ha),true_and]
    refine (h.predictor_unique T (hh.mpr ha)).unique (P.bond_min T).choose_spec fun i => ?_
    obtain ⟨b,rfl⟩ := j.surjective i; rw [hs,hs]; exact (P.bond_min X).choose_spec b
  simp only [predictorMass, predict, if_neg ha,if_neg (mt hh.mp ha),he,hf,and_self]

lemma bond_pull {h : P.Branches C G} (s : Signed) (X : P.Connector G) (x : P.Points) :
    P.predictorMass C (X ∘ P.offset s) x=P.predictorMass C X (P.offset s x) ∧
    P.predict C (X ∘ P.offset s) x=P.predict C X (P.offset s x) := by
  refine P.predicts (T:=X ∘ P.offset s) (h:=h) (P.offset s) (Equiv.refl _) (P.weight_invariant s) (fun _ => rfl) (fun u => ?_) x
  unfold bondCost; conv_rhs => rw [← Equiv.sum_comp (P.offset s)]
  simp_rw [weight_invariant]; rfl

lemma bond_inv {h : P.Branches C G} (s : Signed) (X : P.Connector G) (x : P.Points) :
    P.predictorMass C (X⁻¹ ∘ P.offset s) x=P.predictorMass C X (P.offset s x) ∧
    P.predict C (X⁻¹ ∘ P.offset s) x=(P.predict C X (P.offset s x))⁻¹ := by
  refine P.predicts (T:=X⁻¹ ∘ P.offset s) (h:=h) (P.offset s) (Equiv.inv _) (P.weight_invariant s) (fun _ => rfl) (fun u => ?_) x
  unfold bondCost; conv_rhs => rw [← Equiv.sum_comp (P.offset s)]
  have ht (k : G.El) : G.price (k⁻¹ * u) = G.price (k * u⁻¹) := by
    rw [← G.price_inv (k*u⁻¹), show (k*u⁻¹)⁻¹=k*(k⁻¹*u)*k⁻¹ by -- actually k*(k⁻¹*u)*k⁻¹=u*k⁻¹
      group,G.price_conj]
  simp only [weight_invariant, Function.comp_apply,Pi.inv_apply, Equiv.inv_apply, inv_inv, ht]

lemma bond_gauge {h : P.Branches C G} (u v : G.El) (X : P.Connector G) (x : P.Points) :
    P.predictorMass C (fun i => u * X i * v) x=P.predictorMass C X x ∧
    P.predict C (fun i => u * X i * v) x=u*P.predict C X x*v := by
  refine P.predicts (T:=(fun i => u * X i * v)) (h:=h) (Equiv.refl _) ((Equiv.mulLeft u).trans (Equiv.mulRight v))
    (fun _ => rfl) (fun _ => rfl) (fun j => ?_) x
  unfold bondCost
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change _ * G.price (u * X i * v * (u*j*v)⁻¹) = _
  rw [show u * X i * v * (u*j*v)⁻¹=u*(X i*j⁻¹)*u⁻¹ by group,G.price_conj]
end Patch

namespace StepData
variable {c f : Side} (S : StepData c f)

private lemma add (y x : Site c) : S.ratio.embed (x+y)=S.ratio.embed x + S.ratio.embed y := S.ratio.root.map_add x y
lemma port (s : Signed) (y x : Site c) : affine s (S.ratio.embed y) (S.ratio.embed x)=S.ratio.embed (affine s y x) := by
  rw [affine,affine,add, Ratio.signed]

lemma leap (x : Site c) (i : Axis) : S.ratio.embed (x+step i)=S.ratio.embed x+S.patch.L.val • step i := by
  have he : S.ratio.embed (step i)=_ := calc
    S.ratio.embed (step i)=S.ratio.embed (wrap _ (step i)) := by rw [wrap_step]
    _ = _ := S.ratio.embed_wrap (step i)
  rw [S.add,he,map_nsmul,wrap_step]; rfl

abbrev sendSites (s : Signed) (b : Site c) : Equiv.Perm (Site c) := s.actEquiv.toEquiv.trans (Equiv.addRight b)
abbrev sendBonds (s : Signed) (b : Site c) : Equiv.Perm (Edge (Site c)) := Equiv.ofBijective _ ⟨sendEdge_injective s b,
    Finite.injective_iff_surjective.mp (sendEdge_injective s b)⟩

def withinSites (s : Signed) (b : Site c) : Equiv.Perm S.SitesChoice :=
    Equiv.arrowCongr (sendSites s b) (S.patch.orient s)

def withinBond (s : Signed) (b : Site c) : Equiv.Perm S.BondChoice :=
    Equiv.arrowCongr (sendBonds s b) (S.patch.offset s)

def withinChoice (s : Signed) (b : Site c) : Equiv.Perm S.Choices := Equiv.prodCongr (S.withinSites s b) (S.withinBond s b)

lemma port_site (s : Signed) (b : Site c) (t : S.SitesChoice) (x : Site c) :
    S.withinSites s b t (affine s b x)=S.patch.orient s (t x) := by
  change S.withinSites s b t (((sendSites s b) x)) = _
  simp only [withinSites,Function.comp_apply,Equiv.arrowCongr_apply, Equiv.symm_apply_apply]

lemma port_bond (s : Signed) (b : Site c) (t : S.BondChoice) (x : Edge (Site c)) :
    S.withinBond s b t (sendEdge s b x)=S.patch.offset s (t x) := by
  change S.withinBond s b t (((sendBonds s b) x)) = _
  simp only [withinBond,Function.comp_apply,Equiv.arrowCongr_apply,Equiv.symm_apply_apply]

def repath (i : Axis) := List.replicate S.patch.L.val (posDir i)

lemma stop_repath (i : Axis) {A : Type*} [AddCommGroup A] [One A] (x : Four A) :
    stop x (S.repath i) = x + S.patch.L.val • step i := by
  unfold repath
  generalize S.patch.L.val = M; induction M generalizing x with
  | zero => simp [stop]
  | succ m ih => rw [List.replicate_succ, stop, ih,succ_nsmul,Step.vec_pos]; abel

lemma frames_match (h : S.patch.Branches S.kernel G) (s : Signed) (b : Site c) (U : Config G f) (t : S.SitesChoice) (x : Site c) :
    S.frames (pull s (S.ratio.embed b) U) t x=S.frames U (S.withinSites s b t) (affine s b x) ∘ S.patch.offset s := by
  unfold frames; rw [expandAt_pull,S.port,S.port_site]; exact (S.patch.frames_channel h s _ _).2

lemma negsite (s : Signed) (b : Site c) (x : Site c) (i : Axis) (he : s.flip i=true) :
    affine s b (x+step i) = affine s b x-step (s.perm i) := by
  have hh : s.act (step i : Site c) = -step (s.perm i) := by
    have ht := (Step.vec_rotate (R:=Per c) (posDir i) s).symm
    rw [Step.vec_pos] at ht
    exact ht.trans (by simp [Step.rotate,posDir,he,Step.vec])
  unfold affine; rw [Signed.act_add,hh]; abel

lemma possite (s : Signed) (b : Site c) (x : Site c) (i : Axis) (he : s.flip i=false) :
    affine s b (x+step i) = affine s b x+step (s.perm i) := by
  have ht := (Step.vec_rotate (R:=Per c) (posDir i) s).symm
  rw [Step.vec_pos] at ht
  unfold affine; rw [Signed.act_add,ht]; simp [Step.rotate,Step.vec,posDir,he,add_right_comm]

lemma positive (h : S.patch.Branches S.kernel G) (s : Signed) (b : Site c) (U : Config G f) (t : S.SitesChoice)
    (x : Site c) (i : Axis) (hs : s.flip i=false) : S.connector (pull s (S.ratio.embed b) U) t (x,i)=
      (S.connector U (S.withinSites s b t) (sendEdge s b (x,i))) ∘ S.patch.offset s := by
  funext y; unfold connector; simp only [Function.comp_apply]
  rw [S.frames_match h,S.frames_match h, expandAt_pull,S.port, travel_pull]
  have hh : sendEdge s b (x,i)=(affine s b x,s.perm i) := by simp [sendEdge,Step.rotate,posDir,Step.used,hs]
  simp only [hh,Function.comp_apply, possite s b x i hs,Patch.coord]
  simp [affine,Step.rotate,posDir,hs]

lemma negative (h : S.patch.Branches S.kernel G) (s : Signed) (b : Site c) (U : Config G f) (t : S.SitesChoice)
    (x : Site c) (i : Axis) (hs : s.flip i=true) : S.connector (pull s (S.ratio.embed b) U) t (x,i)=
      (S.connector U (S.withinSites s b t) (sendEdge s b (x,i)))⁻¹ ∘ S.patch.offset s := by
  funext y; unfold connector; simp only [Function.comp_apply,Pi.inv_apply]
  rw [S.frames_match h,S.frames_match h, expandAt_pull,S.port, travel_pull, travel_at,travel_at]
  have hh : sendEdge s b (x,i)=(affine s b x-step (s.perm i),s.perm i) := by simp [sendEdge,Step.rotate,posDir,Step.used,hs]
  -- inverse occurs around whole product before inverse-path
  rw [hh]; simp only [Function.comp_apply, sub_add_cancel, Patch.coord, negsite s b x i hs, mul_inv_rev, inv_inv]
  let X := affine s b x-step (s.perm i)
  have he : S.ratio.embed X + S.patch.L.val • step (s.perm i) = S.ratio.embed (affine s b x) := by rw [← S.leap, show X+step (s.perm i)=_ by unfold X; abel]
  rw [show List.replicate S.patch.L.val (posDir (s.perm i))=S.repath _ from rfl, ← travel_reverse _ U, S.stop_repath, add_assoc,he]
  simp only [affine,add_zero,List.map_replicate,repath,reverse,List.reverse_replicate, Step.rotate,posDir,hs,Bool.false_xor,mul_assoc]
  rfl

lemma updateGauged (h : S.patch.Branches S.kernel G) (t : Site f → G.El) (U : Config G f) (i : S.SitesChoice) (e : Edge (Site c)) :
    S.connector (Lattice.gauge t U) i e=fun x => t (S.ratio.embed e.1)*S.connector U i e x*(t (S.ratio.embed (e.1+step e.2)))⁻¹ := by
  have ht (x y) : S.frames (Lattice.gauge t U) i x y = t (S.ratio.embed x)*S.frames U i x y*(t (wrap f y.val +S.ratio.embed x))⁻¹ := by
    rw [frames,expandAt_gauge,(S.patch.frame_gauged h ..).2, Patch.changed, show S.patch.center.val=0 from rfl,map_zero,zero_add]; rfl
  funext x; unfold connector
  rw [ht,ht,travel_at,travel_at,travel_gauge,show List.replicate S.patch.L.val (posDir e.2)=S.repath e.2 from rfl,S.stop_repath]
  rw [add_assoc (wrap f x.val) (S.ratio.embed e.1),← S.leap]
  group
end StepData
end YM.RG
