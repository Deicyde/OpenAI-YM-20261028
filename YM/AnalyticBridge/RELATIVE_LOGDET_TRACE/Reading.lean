import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Corners
import YM.Next.FOUNDATIONS.JetReads

/-!
# Address of a full precision entry

Checks at the original tag sites, both endpoint requirements, and *both*
positive and negative answers for holes. V tests do not move with any
interpolated mask. In particular when a rotated row of Q is used its read uses
the actual original physical choices. No support assumption about a truncated
path entering through a covariant matrix derivative; prove it below for the
true branch jet. We treat the trunk mask bits as data here: a local agreement
condition, not a test that those bits constitute a valid global forest.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Function Filter Set Matrix Lattice RG Wilson Pressure Tree Precision
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side}

def Shields (Z : Support c) (o : Site c) (t : ℕ) := ∀ s : Site c,separation o s ≤ t → s∈Z
namespace Shields
variable {Z : Support c} {o i : Site c} {d t : ℕ}
lemma shift (h : Shields Z o t) (he : separation o i+d ≤ t) : Shields Z i d :=
  fun j hj => h j ((separation_triangle o i j).trans ((Nat.add_le_add_left hj _).trans he))
lemma shrink (h : Shields Z o t) (he : d ≤ t) : Shields Z o d := fun i hh => h i (hh.trans he)
lemma center (h : Shields Z o t) : o∈Z := h _ (by simp)
lemma full {ι : Type} (p : ι → Site c) (i : ι) (l B : ℕ) (h : lens p l B i ⊆ Z) : Shields Z (p i) (l*B) :=
  fun _ hx => h ((lens_spec _).2 hx)
end Shields

namespace Physical
open Next.SectorChange Next.Fluctuations YM.Push.SectorMeasure.Oriented
open Work.E03
variable {G : Gauge} {S : StepData c f} {F H : Forest S.ratio} {A A' : Stores S} {k k' : S.Choices} {x : ℝ}

lemma pin_diam (i : Bond c) {x y : Site c} (hx : x∈pinPos i) (hy : y∈pinPos i) : separation x y ≤ 2 := by
  have ht (z : Site c) (hz : z∈pinPos i) : separation i.1 z ≤ 1 := by
    simp only [pinPos,Finset.mem_singleton,Finset.mem_insert] at hz; rcases hz with hz|hz <;> rw [hz]
    · simp
    exact sep_step i.1 i.2
  exact (separation_triangle x i.1 y).trans (Nat.add_le_add ((separation_comm ..).trans_le (ht _ hx)) (ht _ hy))

private lemma touch {c f : Side} (p : Site f → Site c) (hp : ∀ i (a : Axis), separation (p i) (p (i+Lattice.step a)) ≤ 1)
    (i : Cell f) (x : Site f) (hx : x∈touched i) : separation (p i.1) (p x) ≤ 4 := by
  have h (w : Walk) (v : Site f) (hv : x∈visits v w) : separation (p v) (p x) ≤ w.length := by
    induction w generalizing v with
    | nil => rw [show x=v from List.mem_singleton.mp hv]; simp
    | cons d w ih =>
      simp only [visits,List.mem_cons] at hv
      rcases hv with h|h
      · rw [h]; simp
      have he : separation (p v) (p (v+d.vec)) ≤ 1 := sep_walk p hp _ [d]
      have hf := ih (v+d.vec) h
      exact (separation_triangle _ (p (v+d.vec)) _).trans ((Nat.add_le_add he hf).trans (by simp [Nat.add_comm]))
  exact h _ _ (List.mem_toFinset.mp hx)
lemma inspect_shield {Z : Support c} {x : Site c} (he : Shields Z x 8) : inspected {x} ⊆ Z := by
  intro y hy
  rw [inspected, Finset.mem_union] at hy
  rcases hy with h|h
  · rw [Finset.mem_singleton.mp h]; exact he.center
  obtain ⟨q,-,hq⟩ := Finset.mem_biUnion.mp h
  split at hq
  next hg => simp at hq
  next hg =>
    have hs : x∈touched q := by simpa using hg
    exact he y ((separation_triangle _ q.1 _).trans (Nat.add_le_add ((separation_comm ..).trans_le (touch id sep_step q _ hs)) (touch id sep_step q _ hq)))
lemma start_diam (i : Cell f) {x y} (hx : x∈startPos S i) (hy : y∈startPos S i) : separation x y ≤ 8 := by
  obtain ⟨x,hx',rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y,hy',rfl⟩ := Finset.mem_image.mp hy
  have he := touch _ (parent_step S) i
  exact (separation_triangle _ (S.ratio.parent i.1) _).trans (Nat.add_le_add
    ((separation_comm ..).trans_le (he _ hx')) (he _ hy'))



variable {V V' : Config G c} {Z : Support c}

/-- Precise agreement of the data used by determinant letters. Does
not include the extra tests for producing a *full* K packet. No
v-condition needed for any frozen HOLD value. Endpoints included. -/
structure Reads (Z : Support c) (A A' : Stores S) (F H : Forest S.ratio) (V V' : Config G c) (k k' : S.Choices) : Prop where
  configuration : Agrees Z V V'
  frame (v : Site c) : v∈Z → k.1 v=k'.1 v
  bond (i : Bond c) : pinPos i ⊆ Z → k.2 i=k'.2 i
  tree (i : Bond f) : S.ratio.parent i.1∈Z → S.ratio.parent (i.1+Lattice.step i.2)∈Z → (i∈F.trunks ↔ i∈H.trunks)
  flags (v : Site c) : inspected {v}⊆Z → (v∈A.flags ↔ v∈A'.flags)
  cost (i : Cell f) : startPos S i⊆Z → (i∈A.costs ↔ i∈A'.costs)
  aisle (i : Bond c) : pinPos i⊆Z → (i∈A.aisles ↔ i∈A'.aisles)

namespace Reads
variable (h : Reads Z A A' F H V V' k k')
include h
lemma seed {v : Site c} (he : Shields Z v 8) : v∈A.place ↔ v∈A'.place := by
  have hc (i : Cell f) : i∈A.costs ∧ v∈startPos S i ↔ i∈A'.costs ∧ v∈startPos S i := by
    by_cases hx : v∈startPos S i
    · rw [h.cost i (fun y hy => he y (start_diam i hx hy))]
    simp [hx]
  have ha (i : Bond c) : i∈A.aisles ∧ v∈pinPos i ↔ i∈A'.aisles ∧ v∈pinPos i := by
    by_cases hx : v∈pinPos i
    · rw [h.aisle i (fun y hy => he y ((pin_diam i hx hy).trans (by omega)))]
    simp [hx]
  simp only [Stores.place,Finset.mem_union,Finset.mem_biUnion,hc,ha,h.flags v (inspect_shield he)]

lemma dome_agrees (t : ℕ) (v : Site c) (he : Shields Z v (t+8)) : v∈ A.dome t ↔ v ∈ A'.dome t := by
  rw [Stores.dome, Stores.dome, halo_spec, halo_spec]
  refine exists_congr fun i => ?_
  by_cases hx : separation i v ≤ t
  · rw [h.seed (he.shift (by rw [separation_comm]; omega))]
  simp [hx]

lemma frozen_bits (hb : 120 ≤ radiusB x) (e : Bond f) (he : Shields Z (S.ratio.parent e.1) (12*radiusB x)) :
    openBond A F x e ↔ openBond A' H x e := by
  have hv := parent_step S e.1 e.2
  rw [mask A F, mask A' H,h.tree e he.center (he _ (hv.trans (by omega))),
    h.dome_agrees _ _ (he.shrink (by omega)), h.dome_agrees _ _ (he.shift (by omega))]

lemma patch_view {a : Directions G f} (s : Signed) (o : Site c) (n : ℕ)
    (hp : Shields Z (s.act o) (n+2)) :
    AgreeNear S.ratio.parent o n (facade S s V a) (facade S s V' a) := by
  have he (i : Bond f) (hi : separation (s.act o) (S.ratio.parent i.1) ≤ n+1) : replica S.ratio V i=replica S.ratio V' i := by
    unfold replica; split
    · rfl
    exact h.configuration (S.ratio.parent i.1,i.2) (hp _ (hi.trans (by omega))) ((hp.shift (Nat.add_le_add_right hi 1)) _ (sep_step _ _))
  apply pulled_near
  intro e h; unfold increment; rw [he _ h]

lemma plaquette_view (s : Signed) (i : Cell f) (hp : Shields Z (s.act (S.ratio.parent i.1)) 6) :
    plaquetteJet S V s i = plaquetteJet S V' s i := by
  refine congr_arg (fun u : Directions G f → G.Color => fderiv ℝ u 0) ?_
  funext a
  exact congr_arg G.curvature (travel_near _ (parent_step S) _ _ _ _ 4 le_rfl (h.patch_view s _ 4 hp))

lemma choices_local (i : Bond c) (hp : pinPos i ⊆ Z) (U : Config G f) : S.prediction U k i=S.prediction U k' i := by
  unfold StepData.prediction StepData.connector StepData.frames
  simp only [h.frame i.1 (hp (by simp [pinPos])),h.frame (i.1+Lattice.step i.2) (hp (by simp [pinPos])),h.bond i hp]

omit h in
private lemma pins_rot (s : Signed) (i : Bond c) (hp : Shields Z (s.act i.1) 3) : pinPos (sendEdge s 0 i) ⊆ Z := by
  have hi : separation (s.act i.1) (sendEdge s 0 i).1 ≤ 1 := by
    unfold sendEdge Step.used; split
    next he =>
      simp only [affine, add_zero]; rw [separation_comm]
      have ht := sep_step (s.act i.1-Lattice.step ((posDir i.2).rotate s).dir) ((posDir i.2).rotate s).dir
      rwa [sub_add_cancel] at ht
    next he => simp [affine]
  intro x hx; exact hp x ((separation_triangle _ _ _).trans
    (Nat.add_le_add hi (pin_diam _ (Finset.mem_insert_self _ _) hx)))

lemma branch_query (i : Bond c) (hS : S.patch.Branches S.kernel G) (s : Signed)
    (hp : Shields Z (s.act i.1) (predReach S.patch + 3)) (a : Directions G f) :
    predictGroup V k s i a=predictGroup V' k' s i a := by
  have hi := prediction_near_eq hS _ _ (choice s k) i (h.patch_view s i.1 _ (hp.shrink (by omega)) (a:=a))
  have ht := pins_rot s i (hp.shrink (by omega))
  unfold predictGroup; rw [hi]
  unfold facade; rw [(carry s hS k _).2,(carry s hS k' _).2]
  rw [Motion.turn_read, Motion.turn_read,h.choices_local (sendEdge s 0 i) ht _]
lemma predictor_view (i : Bond c) (hS : S.patch.Branches S.kernel G) (s : Signed)
    (hp : Shields Z (s.act i.1) (predReach S.patch+3)) : blockJet V k s i=blockJet V' k' s i := by
  refine congr_arg (fun u : Directions G f → G.Color => fderiv ℝ u 0) (funext fun a => ?_)
  simp only [predictorTurn,h.branch_query i hS s hp]

lemma clue_agrees (hS : S.patch.Branches S.kernel G) (T : Tube G S)
    (r : Rows.Receipt G S) (i : Key G f) (he : Shields Z (Wisps.down S r) (Next.SectorChange.span S.patch x+2)) :
    clue T k V x i r=clue T k' V' x i r := by
  suffices hh : Rows.bump T x V k (axisPrice i) r.1 = Rows.bump T x V' k' (axisPrice i) r.1 by
    unfold clue; rw [Pi.smul_apply,Pi.smul_apply,hh]
  rcases r with ⟨⟨s,t|t⟩,r⟩
  · change Rows.faceKick T x V _ _ t=Rows.faceKick T x V' _ _ _
    let R := Stores.till x; let o:=S.ratio.parent t.1.1
    change Shields Z (s.act o) _ at he
    unfold Rows.faceKick; split
    next hi =>
      apply tsum_congr; intro j; dsimp only; split
      next hv =>
        let P := (T.up.row t.1.2 j).2
        let l := Work.F03.slotFace P t.1.1
        have hx : P.length ≤ R := hv
        have hm : P.walk.length ≤ R := by unfold Slot.length at hx; omega
        have hf : separation (s.act o) (s.act (S.ratio.parent l.1)) ≤ R := by rw [separation_signed]; exact (slot_distance P _).trans hm
        have ha := h.plaquette_view s l (he.shift (by change _ ≤ R+5+predReach S.patch+2; omega))
        have ht := h.patch_view s o R (a:=(0:Directions G f)) (he.shrink (by change _ ≤ R+5+predReach S.patch+2; omega))
        have hu := travel_near _ (parent_step S) _ _ _ P.walk R hm (show AgreeNear _ (S.ratio.parent t.1.1) R _ _ from ht)
        change _ • G.adjoint (travel (facade S s V 0) t.1.1 P.walk) (plaquetteJet S V s l _) = _ • G.adjoint _ (plaquetteJet S V' s l _)
        rw [ha, hu]
      next hv => rfl
    rw [h.plaquette_view s t.1 (he.shrink (by unfold Next.SectorChange.span; omega))]
  change -(_ • blockJet V k s t _)=-(_ • blockJet V' k' s t _)
  rw [h.predictor_view _ hS s (he.shrink (by unfold Next.SectorChange.span; omega))]

/-- Row itself, including holes & all-cost path data, on the original V. -/
lemma same_row (hS : S.patch.Branches S.kernel G) (T : Tube G S) (i : Key G f)
    (hb : 120 ≤ radiusB x) (hy : Next.SectorChange.span S.patch x ≤ radiusB x/50)
    (hx : Shields Z (place S i) (14*radiusB x)) (j : Key G f) :
    AFull T A F x V k i j=AFull T A' H x V' k' i j := by
  let B:=radiusB x
  by_cases he : nearby (place S) B i j
  · have hi := h.frozen_bits hb i.1 (hx.shrink (by omega))
    have ht := h.frozen_bits hb j.1 (hx.shift (by change separation (place S i) (place S j) +12*B ≤ 14*B; unfold nearby at he; omega))
    rw [read_kernel _ _ _ _ _ _ hS,read_kernel T k' V' A' H x hS,hi,ht]; split
    next hp =>
      unfold unpaired; apply Finset.sum_congr rfl
      intro r _
      by_cases ha : separation (Wisps.down S r) (place S i) ≤ Next.SectorChange.span S.patch x
      · have hs : Shields Z (Wisps.down S r) (Next.SectorChange.span S.patch x+2) := hx.shift (by rw [separation_comm]; omega)
        rw [h.clue_agrees hS _ r i hs,h.clue_agrees hS _ r j hs]
      rw [clue_zero T _ _ hS _ _ ha,clue_zero T k' _ hS _ _ ha,zero_mul,zero_mul]
    rfl
  rw [(kernel_reach T k V hS _ A F).trans (by dsimp only [B]; omega) i j he,
    (kernel_reach T k' V' hS _ A' H).trans (by dsimp only [B]; omega) i j he]
end Reads
end Physical
end YM.AnalyticBridge.RelativeLogdet
