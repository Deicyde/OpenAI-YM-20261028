import YM.Push.STATIONARY_UNIFORM.Array

/-! # Distances retained by the literal scores: periodic, native-fine-site
Use no injectivity of the stencil after projecting to the torus. (Admitted
period may need to be sufficiently large elsewhere.) This is just equality of
reads, not independence. All on the SAME tree and tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side}

lemma letter_position (x : Site f) (d : Step) : separation x (d.used x).1 ≤ 1 := by
  unfold Step.used; split
  · simp only [separation,sub_sub_cancel]; apply pdist_step
  simp only [separation_self,zero_le]
lemma letter_step (x : Site f) (d : Step) : separation x (x+d.vec) ≤ 1 := by
  rw [separation_comm,separation,add_comm,add_sub_cancel_right]; unfold Step.vec; split
  · rw [pdist_neg]; exact pdist_step _
  exact pdist_step _
lemma stop_length (x : Site f) (w : Walk) : separation x (stop x w) ≤ w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons i l ih =>
    rw [stop,List.length_cons, Nat.add_comm]
    exact (separation_triangle x (x+i.vec) _).trans (Nat.add_le_add (letter_step ..) (ih _))
lemma path_same {x : Site f} {w : Walk} {U V : Config G f} (he : ∀ i : Bond f, separation x i.1 ≤ w.length → U i=V i) :
    travel U x w=travel V x w := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih =>
    have hm : U (d.used x) = V (d.used x) := he _ ((letter_position x d).trans (by rw [List.length_cons]; omega))
    rw [travel,travel, Step.read, Step.read, hm, ih]
    intro i hi; apply he; apply (separation_triangle x (x+d.vec) _).trans
    rw [List.length_cons, Nat.add_comm w.length 1]; exact Nat.add_le_add (letter_step ..) hi

section Fine
variable {p : Ratio c f} (B : Forest p)
variable {u v : Positions (Joint B G)} {y : Site f} {R : ℕ}

def together {ιₛ : Type} (l : ιₛ → Site f) (y : Site f) (R : ℕ) (u v : Positions ιₛ) := ∀ i, separation y (l i) ≤ R → u i=v i
lemma co_read (he : together (address B G) y R u v) (i : Bond c) (hi : separation y (p.embed i.1) ≤ R) :
    outer G B u i=outer G B v i := by
  unfold outer; rw [Work.F03.represent_link, Work.F03.represent_link]; apply congr_arg G.lieExp
  ext j; rw [pinA,pinA]; exact he _ hi

lemma fine_read (he : together (address B G) y R u v) (i : Bond f) (hi : separation y i.1 + p.count.val ≤ R) :
    fine G B u i=fine G B v i := by
  by_cases ht : i ∈ B.trunks
  · exact (B.on_tree _ ⟨i,ht⟩).trans (B.on_tree _ ⟨i,ht⟩).symm
  let j : B.Free := ⟨i,ht⟩
  have h (u : Positions (Joint B G)) : fine G B u i=G.lieExp ((paint B G u).2 j)*replica p (outer G B u) i := B.off_tree _ j
  have hv : replica p (outer G B u) i=replica p (outer G B v) i := by
    unfold replica; split; next _ => rfl
    next _ =>
      apply co_read B he
      apply (separation_triangle y i.1 _).trans
      have hc : separation i.1 (p.embed (p.parent i.1)) ≤ p.count.val := by
        have hs := Corona.near p i.1; omega
      exact (Nat.add_le_add_left hc (separation y i.1)).trans hi
  rw [h u,h v,hv]; congr 2
  ext k; rw [pinB,pinB]; apply he
  change separation y i.1 ≤ _; omega

def signedFine (u : Positions (Joint B G)) (s : Signed) := pull s 0 (fine G B u)

def signedCost (L : Side) (r : ℕ) := (r+1+L.val)
lemma signed_read (s : Signed) (x : Site f) (w : Walk)
    (h : signedCost p.count w.length ≤ R) (he : together (address B G) (affine s 0 x) R u v) :
    travel (signedFine B u s) x w=travel (signedFine B v s) x w := by
  apply path_same; intro i hi
  let t : Step := (posDir i.2).rotate s
  let j := affine s 0 i.1
  have ha : separation (affine s 0 x) (t.used j).1 ≤ w.length+1 := (separation_triangle _ j _).trans
    (Nat.add_le_add (by simpa [j,affine] using hi) (letter_position ..))
  have hw : fine G B u (t.used j)=fine G B v (t.used j) := fine_read B he _ ((Nat.add_le_add_right ha p.count.val).trans h)
  change t.read _ j = t.read _ j
  unfold Step.read; rw [hw]

lemma slot_read (s : Signed) (x : Site f) (a : Slot)
    (h : signedCost p.count (2*a.length) ≤ R) (he : together (address B G) (affine s 0 x) R u v) :
    a.atSite (signedFine B u s) x=a.atSite (signedFine B v s) x := by
  have ht : (Work.F02.slotWalk a).length ≤ 2*a.length := by
    simp only [Work.F02.slotWalk,List.length_append,Lattice.reverse,List.length_map,List.length_reverse]
    change a.walk.length+4+_ ≤ 2*(a.walk.length+4); omega
  rw [Work.F02.atSite_curvature, Work.F02.atSite_curvature, signed_read B s x _ ((show signedCost p.count _ ≤ signedCost p.count (2*a.length) from by unfold signedCost; omega).trans h) he]
end Fine

section Noise
variable {S : StepData c f}

lemma orbit (S : StepData c f) (x : Site c) (i : S.patch.Points) :
    separation (S.ratio.embed x) (Precision.atPoint S x i) ≤ 8*S.patch.radius := by
  have he := Precision.reach S x S.patch.center i 1
  rw [show Precision.atPoint S x S.patch.center = S.ratio.embed x from by rw [Precision.atPoint,
    show S.patch.center.val=0 from rfl,map_zero,zero_add]] at he
  rw [← he]; exact (stop_length ..).trans (routeLe ..)

-- ALL pairs agree -> any min frame used by prediction agrees, assuming uniqueness on branch.
-- Could restrict to open ball and re-use our uniform min-estimate instead.
lemma obey (P : Patch) (Q : KernelChoices) (h : P.Branches Q G) (U V : CoverConfig G)
    (he : ∀ (i j : P.Points) l, travel U i.val (route i.val j.val l)=travel V i.val (route i.val j.val l)) (t : P.FrameTag) :
    P.frame Q U t=P.frame Q V t := by
  have hx (t : P.FrameTag) : P.axial U t = P.axial V t := funext fun i => he _ i _
  have hu (w : P.Frame G) : P.via w U = P.via w V := by unfold Patch.via; simp_rw [he]
  have hv : P.score U=P.score V := by unfold Patch.score; simp_rw [hu]
  have hs : P.usesMin Q U ↔ P.usesMin Q V := by simp only [Patch.usesMin,hx,hu]
  unfold Patch.frame; split
  next hm =>
    rw [if_pos (hs.mp hm)]
    apply (h.frame_unique U hm).unique (P.min_exists U).choose_spec
    have ht : P.minimizing V (P.selected V) := (P.min_exists V).choose_spec
    simpa only [Patch.minimizing,hv] using ht
  next hm => rw [if_neg (fun hi => hm (hs.mpr hi)), hx]

def noiseCost (P : Patch) := P.L.val+8*P.radius+8*P.radius+P.L.val+P.L.val

lemma noise_read (B : Forest S.ratio) {u v : Positions (Joint B G)} (h : S.patch.Branches S.kernel G)
    (t : S.Choices) (b : Bond c)
    (he : together (address B G) (S.ratio.embed b.1) (noiseCost S.patch) u v) :
    S.prediction (fine G B u) t b=S.prediction (fine G B v) t b := by
  let P := S.patch; let y := S.ratio.embed b.1
  have hN : P.L.val=S.ratio.count.val := rfl
  have hh (z : Site c) (hz : separation y (S.ratio.embed z) ≤ P.L.val) (i : P.Points) :
      separation y (Precision.atPoint S z i) ≤ P.L.val+8*P.radius := (separation_triangle y (S.ratio.embed z) _).trans
    (Nat.add_le_add hz (orbit ..))
  have hV (z : Site c) (hz : separation y (S.ratio.embed z) ≤ P.L.val) : S.frames (fine G B u) t.1 z=S.frames (fine G B v) t.1 z := by
    apply obey P _ h
    intro i j l; rw [travel_at,travel_at]; apply path_same
    intro x hx; apply fine_read _ he
    have he : separation y x.1 ≤ P.L.val+8*P.radius+8*P.radius := (separation_triangle _ (Precision.atPoint S z i) _).trans
      (Nat.add_le_add (hh z hz i) (hx.trans (routeLe ..)))
    change separation y x.1+ S.ratio.count.val ≤ noiseCost P; unfold noiseCost; omega
  have hs : separation y (S.ratio.embed b.1) ≤ P.L.val := by rw [show S.ratio.embed b.1=y from rfl, separation_self]; omega
  have ht : separation y (S.ratio.embed (b.1+step b.2)) ≤ P.L.val := by
    rw [S.leap, ← StepData.stop_repath]
    simpa only [P,y,StepData.repath, List.length_replicate] using stop_length y (S.repath b.2)
  unfold StepData.prediction
  apply congr_arg (fun q => S.patch.predict _ q _)
  unfold StepData.connector; rw [hV b.1 hs, hV _ ht]
  funext i; rw [travel_at,travel_at]; congr 2
  apply path_same; intro x hx
  apply fine_read _ he
  have hw : separation y x.1 ≤ P.L.val+8*P.radius+P.L.val := (separation_triangle y (Precision.atPoint S b.1 i) _).trans
    (Nat.add_le_add (hh _ hs i) (by rw [List.length_replicate] at hx; exact hx))
  change separation y x.1+ S.ratio.count.val ≤ noiseCost P; unfold noiseCost; omega
end Noise
end YM.Push.Uniform
