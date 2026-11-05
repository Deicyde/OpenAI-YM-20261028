import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Addresses
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Force
import YM.Next.PHASE.Assembly

/-!
Affine *primitive* read receipt at fixed horizon and x, before patching or
expanding or regrouping. Track thinned selector (including equality), tagged
choices, ℓ-path costs and rotated physical frame for every query. Does NOT
say the `fderiv` at an arbitrary compared field here exists.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.PatchReads
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier Next.SectorChange.Motion
  Next.SectorChange.LocalJet Next.SectorChange.Rows Next.Fluctuations Bid FiniteMatrix Gaussian Exterior Bloch
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {x : ℝ} {k k' : S.Choices} {o : Site c} {r : ℕ}

private lemma face_close {R : ℕ} {i : Cell c} (h : AgreeNear id o (R+4) V V') (hi : separation o i.1 ≤ R) : faceValue V i = faceValue V' i :=
  travel_near id (fun i e => Work.E03.sep_step i e) _ _ i.1 (square i.2.val.1 i.2.val.2) 4 le_rfl (h.shrink (Nat.add_le_add_right hi _))
private lemma kept_close (ha : Ready T x) (h : AgreeNear id o (radiusB x / 50+4) V V') (hk : PathData.kept T.low (temp x) o V) : PathData.kept T.low (temp x) o V' := by
  intro p
  by_contra! hx
  exact hx.not_ge ((face_close h (ha.mask _ _ p hx)) ▸ (hk p))
private lemma vision_close (ha : Ready T x) {i : Twin c} (h : AgreeNear id i.1.1 (radiusB x/50+4) V V') : T.vision (till x) (temp x) V i=T.vision (till x) (temp x) V' i := by
  have he := face_close h (i:=i.1) (by simp)
  have hh : PathData.kept T.low (temp x) i.1.1 V ↔ PathData.kept T.low (temp x) i.1.1 V' := ⟨kept_close ha h,kept_close ha (fun i hi => (h i hi).symm)⟩
  unfold Tube.vision thinned
  split
  · simp_rw [hh]; split
    · let p : Twin c := (i.1,true)
      have hx := ha.inputs; unfold span at hx
      exact plotted_near id (fun i e => Work.E03.sep_step i e) _ _ T.low T.down _ _ p S.patch.L.property
        (h.shrink (show separation i.1.1 i.1.1 + _ ≤ _ by rw [separation_self]; omega))
    rfl
  unfold toll shoot; rw [he]

section rows
variable {X : Type} (T : Tube G S) (R : ℕ)
/-- Private analog of Fluctuations.RowNear for forward zip on the changed
clipped field (can't call `local_gaps`, which holds an independent field w).
-/
private structure TurnCost (g : Config G c → X → Twin c → Pay G) (p : X → Site c) : Prop where
  band (V : Config G c) (i : X) (j : Twin c) : R < separation (p i) j.1.1 → g V i j = 0
  seen (V W : Config G c) (i : X) (j : Twin c) : AgreeNear id (p i) R V W → g V i j = g W i j
variable {T R}
private lemma mv_step : TurnCost R (T.Φ R) (S.ratio.parent ∘ fun i : Twin f => i.1.1) := by
  constructor <;> intro V
  · intro i j h
    have hf (u : Cover) : casted S T.R R V (mesh i) (mesh j) u = 0 := by
      dsimp only [casted]; split
      next hv =>
        let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • u) 1
        have hp := Work.E03.sep_walk S.ratio.parent (Work.E03.parent_step S) (mesh i).1 w
        rw [show stop _ w = _ from Work.E03.casted_endpoint S (mesh i).1 u, S.ratio.embed_parent, ← hv.2] at hp
        exact (h.not_ge (hp.trans hv.1)).elim
      rfl
    simp only [Tube.Φ,leap,hf,tsum_zero]
  intro W i j h
  apply tsum_congr; intro u; dsimp only [casted]; split
  next ht => rw [rated,rated,travel_near _ (Work.E03.parent_step S) _ _ (mesh i).1 _ R ht.1 (rep_share h)]
  rfl
private lemma mw_step : TurnCost R (T.Φ' R) Prod.fst := by
  have hl k (h : k*S.patch.L.val ≤ R) : k ≤ R := le_trans (le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property) h
  constructor <;> intro V
  · intro i j h
    have hf (u : Cover) : priced R S.patch.L.val V T.R.mn (pole i) (mesh j) u = 0 := by
      unfold priced; split
      next hv =>
        have hx : stop (pole i).1 (route 0 u 1) = (mesh j).1 := by
          rw [hv.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route (pole i).1 0 u
        have he : separation (pole i).1 (mesh j).1 ≤ R := by
          rw [← hx]; exact (Work.E03.sep_walk (fun x : Site c => x) Work.E03.sep_step ..).trans (hl _ hv.1)
        exact (h.not_ge he).elim
      rfl
    simp [Tube.Φ',Pressure.kick,lane,hf]
  intro W i j h
  apply tsum_congr; intro u; unfold priced; split
  next ht => rw [rated,rated,travel_near id (fun i e => Work.E03.sep_step i e) _ _ (pole i).1 _ R (hl _ ht.1) h]
  rfl




private lemma TurnCost.zip {g : Config G c → X → Twin c → Pay G} {p : X → Site c}
    (ha : TurnCost R g p) (hx : Ready T x) {i : X} (h : AgreeNear id (p i) (R+radiusB x/50+4) V V') :
    zip (g V) (T.vision (till x) (temp x) V) i = zip (g V') (T.vision (till x) (temp x) V') i := by
  have he := h.shrink (q':=p i) (D':=R) (by rw [separation_self]; omega)
  unfold Pressure.zip; refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha.seen V V' i j he]; by_cases ho : separation (p i) j.1.1 ≤ R
  · rw [vision_close hx (i:=j) (h.shrink (by omega))]
  rw [ha.band V' i j (lt_of_not_ge ho),_root_.zero_apply,_root_.zero_apply]
end rows

def mark (S : StepData c f) (i : Slots S) := i.1.act (roots S (i.2.elim (fun i => Sum.inl i.1) Sum.inr))
variable {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')}
lemma cover_eq {i : Slots S} (h : Scan S x (mark S i) (span S.patch x) A A' F F' k k' V V' Y Y') (hk : Rows.keep x (shots S x) A F i) : Rows.keep x (shots S x) A' F' i := by
  rcases i with ⟨s,t|t⟩
  all_goals
    obtain ⟨i,hi⟩ := hk
    obtain ⟨j,hj⟩ := h.switch i ((contains ..).mp hi)
    rw [hj] at hi; exact ⟨j,hi⟩
lemma base_eq (hr : Ready T x) {i : Slots S} (h : Scan S x (mark S i) (radiusB x/10) A A' F F' k k' V V' Y Y') : Rows.base T x V k i = Rows.base T x V' k' i := by
  have hk := hr.length; have hx := hr.inputs; unfold span at hx
  rcases i with ⟨s,t|t⟩
  · let p := S.ratio.parent t.1.1
    change Scan _ _ (s.act p) .. at h
    change faceFixed T x s V t = faceFixed T x s V' t
    unfold faceFixed
    rw [show T.Xf _ _ t = T.Xf _ _ t from plotted_near _ (Work.E03.parent_step S) _ _ _ _ _ _ _ le_rfl (facade_read (h.lower (show till x+4+1 ≤ _ by omega)).outer 0),
      show T.Mv (till x) (temp x) _ t = T.Mv (till x) (temp x) _ t from TurnCost.zip mv_step hr (coarse_turn (h.lower (r':=(till x+radiusB x/50+4)+1) (by omega)).outer)]
  change Scan _ _ (s.act t.1) .. at h
  change noiseFixed x V k s t (T:=T) = noiseFixed T x V' k' s t
  unfold noiseFixed Tube.Z
  rw [show (pull s 0 V) t = (pull s 0 V') t from coarse_turn ((h.lower (show 0+1 ≤ _ by omega)).outer) t (show separation t.1 t.1 ≤ 0 by simp),
    show S.prediction (facade S s V 0) (Oriented.choice s k) t = _ from predict_read (i:=t) hr.rules (h.lower (by omega)) 0]
  rw [show T.Mw (till x) (temp x) _ t = T.Mw (till x) (temp x) _ t from TurnCost.zip mw_step hr (coarse_turn (h.lower (r':=(till x+radiusB x/50+4)+1) (by omega)).outer)]
  rfl

lemma bump_eq (hr : S.patch.Branches S.kernel G) {i : Slots S} (a : Directions G f)
    (h : Scan S x (mark S i) (span S.patch x) A A' F F' k k' V V' Y Y') : Rows.bump T x V k a i = Rows.bump T x V' k' a i := by
  obtain ⟨s,j|j⟩ := i
  · change Scan _ _ (s.act (S.ratio.parent j.1.1)) .. at h
    change Rows.faceKick T x V a s j = Rows.faceKick T x V' a s j
    unfold Rows.faceKick
    split
    · apply tsum_congr; intro i; dsimp only; split
      next hi =>
        let u := (T.up.row j.1.2 i).2
        have he := slot_distance (S:=S) u j.1.1
        have hh : u.length ≤ till x := hi
        unfold Slot.length at hh
        have hl : separation (s.act (S.ratio.parent j.1.1)) (s.act (S.ratio.parent (Work.F03.slotFace u j.1.1).1))+5 ≤ span S.patch x := by
          rw [separation_signed]; unfold span; omega
        rw [show travel (facade S s V 0) .. = travel (facade S s V' 0) j.1.1 u.walk from travel_near _ (Work.E03.parent_step S) _ _ _ _ u.walk.length le_rfl (facade_read (h.lower (by unfold span; omega)).outer 0),
          face_share _ (Work.F03.slotFace u j.1.1) (h.outer.shrink hl)]
      rfl
    rw [face_share _ j.1 (h.lower (by unfold span; omega)).outer]
  change Scan _ _ (s.act j.1) .. at h
  change noiseKick V k a s j = noiseKick V' k' a s j
  have he := predict_read hr (h.lower (show predReach S.patch+1 ≤ _ by unfold span; omega)) (i:=j)
  have ht : blockJet V k s j = blockJet V' k' s j := congr_arg (fun f : Directions G _ → G.Color => fderiv ℝ f 0) (funext fun a => congr_arg G.curvature (congr_arg₂ (fun i j : G.El => i*j⁻¹) (he a) (he 0)))
  unfold noiseKick; rw [ht]

abbrev Full (_S : StepData c f) (G : Gauge) := Bond f × G.ColorIndex
def lift (j : Rows.In x A F (G:=G)) : Full S G := (j.1.val.val,j.2)
lemma lifting_injective (A : Stores S) (x : ℝ) (F : Forest S.ratio) : Injective (lift (x:=x) (G:=G) (F:=F) (A:=A)) :=
  fun i j h => Prod.ext (Subtype.ext (Subtype.ext (congr_arg Prod.fst h))) (show (lift i).2=(lift j).2 from congr_arg Prod.snd h)
lemma fresh_basis {i : Rows.In x A F (G:=G)} (e : Bond f) (W : Stencils S) : fresh x W A F (axisPrice i) e =
    if e=i.1.val.val then (EuclideanSpace.basisFun G.ColorIndex ℝ) i.2 else 0 := by
  rw [on_axis]; by_cases he : e=i.1.val.val
  · subst e; rw [fresh,dif_pos i.1.val.2, dif_pos i.1.2,Pi.single_eq_same,if_pos rfl]
  rw [if_neg he,fresh]; split
  · split
    · exact Pi.single_eq_of_ne (fun hh => he (congr_arg (fun i : Active A x F => i.val.val) hh)) _
    rfl
  rfl
lemma move_range (h : S.patch.Branches S.kernel G) {i : Rows.Receipt G S} {j : Rows.In x A F (G:=G)} (hi : span S.patch x < separation (down S i) (front A F j)) :
    move T x V k (shots S x) A F i j=0 := by
  let W := shots S x
  let a := fresh x W A F (axisPrice j)
  have he : bump T x V k a i.1=0 := by
    obtain ⟨⟨s,i'⟩,ι⟩ := i
    change bump T x V k a (s,i')=0
    rw [bump_dep T x V k s i' a 0 h ?_]
    · unfold bump; rcases i' with j|j
      · dsimp only [Sum.elim_inl]; unfold faceKick; simp [barrel]
      dsimp only [Sum.elim_inr]; simp [noiseKick]
    intro i hh
    have he : separation (down S (G:=G) ((s,i'),ι)) (S.ratio.parent i.1) ≤ span S.patch x := (contains ..).mp hh
    have ht : i ≠ j.1.val.val := fun hx => hi.not_ge (show separation (down S (G:=G) ((s,i'),ι)) (S.ratio.parent j.1.val.val.1) ≤ _ from hx ▸ he)
    exact (fresh_basis i W).trans (if_neg ht)
  change tape.symm (Rows.restrict x W A F (bump T x V k a)) i = 0
  change (Rows.restrict x W A F (bump T x V k a) i.1) i.2 = 0
  unfold Rows.restrict; split
  · rw [he,smul_zero]; rfl
  rfl
lemma move_eq {i : Rows.Receipt G S} {j : Rows.In x A F (G:=G)} {j' : Rows.In x A' F' (G:=G)}
    (hr : S.patch.Branches S.kernel G) (h : Scan S x (down S i) (span S.patch x) A A' F F' k k' V V' Y Y') (he : lift j=lift j') :
    move T x V k (shots S x) A F i j=move T x V' k' (shots S x) A' F' i j' := by
  let W := shots S x
  let a := fresh x W A F (axisPrice j)
  have ha : a=fresh x W A' F' (axisPrice j') := by 
    funext e; unfold a; rw [fresh_basis, fresh_basis]
    have h₁ : (lift j).1=(lift j').1 := congr_arg Prod.fst he
    have h₂ : (lift j).2=(lift j').2 := congr_arg Prod.snd he
    change _ = if e=(lift j').1 then _ else _
    rw [show j.1.val.val=(lift j').1 from h₁, show j.2=j'.2 from h₂]
  have hh : keep x W A F i.1 ↔ keep x W A' F' i.1 := ⟨cover_eq h,cover_eq h.turn⟩
  change (Rows.restrict x W A F (bump T x V k a) i.1) i.2 = (Rows.restrict x W A' F' (bump T x V' k' (fresh x W A' F' (axisPrice j'))) i.1) i.2
  unfold Rows.restrict; simp_rw [hh]
  split
  · rw [bump_eq hr a h, ha]
  rfl

variable {d : ℝ} {q : Chi} {i : Rows.Receipt G S}
lemma input_eq {e : Bond f} (h : Scan S x o r A A' F F' k k' V V' Y Y') (hi : separation o (S.ratio.parent e.1) ≤ r) :
    input x A F (autoShell q d V Y) e=input x A' F' (autoShell q d V' Y') e := by
  by_cases he : e∈F.trunks
  · rw [input,input,dif_neg (not_not.mpr he),dif_neg (not_not.mpr ((h.trunks e hi).1 he))]
  let j : F.Free := ⟨e,he⟩; let j' : F'.Free := ⟨e,mt (h.trunks e hi).2 he⟩
  rw [input,input,dif_pos j.2,dif_pos j'.2]
  by_cases hj : chill A x F j
  · have hj' := (h.freeze_same (i:=j) (j:=j') hi (show j.val=j'.val from rfl)).mp hj
    rw [dif_pos hj,dif_pos hj',autoShell,autoShell,h.held ⟨j,hj⟩ ⟨j',hj'⟩ hi rfl, rep_share (S:=S) h.outer e hi]
  rw [dif_neg hj,dif_neg (mt ((h.freeze_same (i:=j) (j:=j') hi (show j.val=j'.val from rfl)).mpr) hj)]
lemma source_eq (hr : Ready T x) (h : Scan S x (down S i) (radiusB x/10) A A' F F' k k' V V' Y Y') :
    source T x V k (shots S x) A F q d Y i=source T x V' k' (shots S x) A' F' q d Y' i := by
  let W:=shots S x; let a := input x A F (autoShell q d V Y); let a' := input x A' F' (autoShell q d V' Y')
  have hx := hr.inputs
  have h := h.lower (r':=span S.patch x) (by omega)
  have hh : keep x W A F i.1 ↔ keep x W A' F' i.1 := ⟨cover_eq h,cover_eq h.turn⟩
  change (Rows.restrict x W A F (base T x V k+bump T x V k a) i.1) i.2=(Rows.restrict x W A' F' (base T x V' k'+bump T x V' k' a') i.1) i.2
  unfold Rows.restrict; simp_rw [Pi.add_apply, hh]; split
  · rw [base_eq hr ‹Scan _ _ _ (_/10) ..›,bump_eq hr.rules a h,
      show bump T x V' k' a i.1 = bump T x V' k' a' i.1 from bump_dep T x V' k' i.1.1 i.1.2 a a' hr.rules (fun e he => input_eq h ((contains ..).mp he))]
  rfl
end YM.AnalyticBridge.MarginalMultiplier3b1d.PatchReads
