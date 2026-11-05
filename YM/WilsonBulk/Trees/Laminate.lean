import YM.WilsonBulk.Trees.Rows

/-! Compatible heights & exact tree matrix bridge.
`Genuine active heights` bound uniform in earlier cuts. Any repeated forest model, no comparisons
asserted BETWEEN different models here. Tree covariance has no zeros-mode exemption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open Work.F08 Lifted Primitives.TwoWave
open scoped Topology BigOperators Matrix Classical

variable {c f : Side} {P : Patch} {K : KernelChoices} {σ η C W : ℝ}
-- branch before sizes
section paper
variable (G : Gauge) (T : Model P K)
def projectedSheet : Row (Co P.L (Loc G 1)) (Co P.L (Loc G 1)) :=
  plusRows (unitRow _) (fineColor G (composeRows (rectangle P.L (cobound 0)) (hikeRows T))) -- clashes
lemma Stamped.projected : Stamped (projectedSheet G T) :=
  Stamped.unit.plus (Stamped.painted _ _ _ _ ((rect_paid _ (Stamped.cobound 0)).product (Stamped.hikeRows T)))
def rootSheet (P : Patch) := marketColor G (FreeResolvent.rootRow P)
lemma Stamped.root (P : Patch) : Stamped (rootSheet G P) := Stamped.painted _ _ _ _ (fun v _ => FreeResolvent.ready_rootRow P v)
def shiftSheet (L : Side) := bondColor G (composeRows (rectangle L (cobound 0)) (copyRow L))
lemma Stamped.shift (L : Side) : Stamped (shiftSheet G L) :=
  Stamped.painted _ _ _ _ ((rect_paid _ (Stamped.cobound 0)).product (Stamped.site _))
def collapseSheet (P : Patch) := minusRows (leftBound G P.L)
  (composeRows (shiftSheet G P.L) (plusRows (rightBound G P.L) (composeRows (rootSheet G P) (leftBound G P.L))))
lemma Stamped.left (L : Side) : Stamped (leftBound G L):= Stamped.site _
lemma Stamped.right (L : Side) : Stamped (rightBound G L):= Stamped.site _
lemma Stamped.collapseSheet (P : Patch) : Stamped (collapseSheet G P) := Stamped.sub (Stamped.left G _) (Stamped.product (Stamped.shift G _) ((Stamped.right G _).plus ((Stamped.root G _).product (Stamped.left G _))))
def aimed : Row (Co P.L (Loc G 1)) (ParcelG G P.L) := composeRows (projectedSheet G T) (collapseSheet G P)
lemma Stamped.aimed : Stamped (aimed G T) := (Stamped.projected G T).product (Stamped.collapseSheet G P)

variable (v : f.val=c.val*P.L.val)
lemma sees_aimed :
    let S := data v K; let U:=spreadForest T v
    Seen c (splitCo S.ratio _) (clothe G S) (aimed G T) (casting G S U) := by -- binder shadow
  intro S U
  let X : Loc G 1 ⊕ Loc G 0→Prop:= fun _=>True
  have h0 : Seen c (splitCo S.ratio _) (splitCo S.ratio _) (rectangle P.L (cobound 0)) (d 0 f):= rect_embedded S.ratio (Stamped.cobound 0)
  have hw : Seen c (splitCo S.ratio _) (splitCo S.ratio _) (projectedSheet G T) (projectFull G S U) :=
    (see_unit _).plus (Seen.fine G (h0.chain' (hike_seen G T v) (rect_paid _ (Stamped.cobound _)) (Stamped.hikeRows _))) Stamped.unit
         (Stamped.painted _ _ _ _ ((rect_paid _ (Stamped.cobound _)).product (Stamped.hikeRows _)))
  have hz : Seen c (Equiv.refl _) (splitCo S.ratio _) (rootSheet G P) (patron G (fixRoot S)) := Seen.fromFine G (show Seen c (Equiv.refl _) _ _ _ from FreeResolvent.block_root S)
  have hk : Seen c (splitCo S.ratio _) (Equiv.refl _) (shiftSheet G P.L) (patron G (HGrad S)) := Seen.coarse G (h0.chain' (copy_acts S) (rect_paid _ (Stamped.cobound _)) (Stamped.site _)) -- h0 d: row of grad
  have hL:= sees_left G S; have hR:= sees_right G S
  exact hw.chain' (hL.minus (hk.chain' (hR.plus (hz.chain' hL (Stamped.root G P) (Stamped.left G P.L)) (Stamped.right G _) ((Stamped.root G _).product (Stamped.left G _)))
    (Stamped.shift G _) ((Stamped.right G _).plus ((Stamped.root G _).product (Stamped.left G _))))
     (Stamped.left G _) ((Stamped.shift G _).product ((Stamped.right G _).plus ((Stamped.root G _).product (Stamped.left G _))))) (Stamped.projected G T) (Stamped.collapseSheet G P)
end paper

-- actual coherence over all c,f as explicitly announced
variable (G : Gauge) (T : Model P K) (B : Bed)
def fluct : Row (Co P.L (Loc G 1)) (Co P.L (Loc G 1)) :=
  composeRows (composeRows (aimed G T) (jointInverse G P K B)) (transRows (aimed G T))
lemma fluct_ready (h : (jointInverse G P K B).strip σ W) (hs : 0 ≤ σ)
    (hb : (aimed G T).strip σ C) : (fluct G T B).strip σ ((Fintype.card (ParcelG G P.L):ℝ)*(Fintype.card (ParcelG G P.L)*(C*W)*C)) :=
  strip_compose hs (strip_compose hs hb h) (strip_trans hb)
lemma fluct_poses (h : (jointInverse G P K B).strip σ W) (hs : 0 ≤ σ) {b : ℝ} {p : Clip}
    (hη : 0< η) (hB : Floor B p f η b) (v : f.val=c.val*P.L.val) (hP : Bid.Larger (G:=G) (data v K))
    (t : (data v K).Choices) (hT : completedM G B (data v K) t * (jointInverse G P K B).acts c=1) :
    let S:= data v K; let U:=spreadForest T v
    Seen c (splitCo S.ratio _) (splitCo S.ratio _) (fluct G T B) (covariance G S U B.metric) := by
  intro S U; have hx : Seen c (clothe G S) (clothe G S) (jointInverse G P K B)
      (repackM (clothe G S).symm (clothe G S).symm ((jointInverse G P K B).acts c)) := rfl
  rw [driven (S:=S) t U B p η b hB hη hP ((jointInverse G P K B).acts c) hT]
  obtain ⟨M,hu,hM⟩:= Stamped.aimed G T |>.bound σ
  have he := sees_aimed G T v
  exact (Seen.chain he hx hM h hs).chain (Seen.trans he) (strip_compose hs hM h) (strip_trans hM) hs
end YM.WilsonBulk
