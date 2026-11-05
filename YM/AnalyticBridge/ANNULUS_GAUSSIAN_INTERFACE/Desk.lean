import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Meter
import YM.Next.SCHEDULE.Blocks

set_option warningAsError false

/-! # Affine row footprint, both dyes

At unchanged $F,A$. This is a location property of the exact fd
functions, extends even to zero coefficients. It proves no growth or
Taylor price for an expanded activity. E:7019 radius checks, looking
only at the numerical/guard use in the current cost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus.Map
open Function Filter Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree Finset
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.Fluctuations Next.SectorChange Bid
open YM.SectorNext.Remainder.Affine
open Work.E03 (sep_step parent_step sep_walk stop_route)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} (S : StepData c f)

def slipAt (i : Slots S) : Where S := i.2.elim (fun j => .inl j.1) Sum.inr

def spot (i : Slots S) := i.1.act (roots S (slipAt S i))

def portOf (e : Bond f) := S.ratio.parent e.1

variable {S} (T : Tube G S) (x : ℝ) (A : Stores S) (k k' : S.Choices) (V V' : Config G c)
    (F : Forest S.ratio)

lemma orient_view (o : Site c) (r : ℕ) (s : Signed) (h : AgreeNear id (s.act o) (r+1) V V') :
    ∀ a : Directions G f, AgreeNear S.ratio.parent o r (facade S s V a) (facade S s V' a) := by
  intro a; apply pulled_near
  intro i hi; unfold increment replica; split
  · rfl
  rw [h (S.ratio.parent i.1,i.2) hi]

variable (hA : Aperture S T x)
include hA

/-- Bump kernel, still with an arbitrary unchanged input. -/
theorem drawn (i : Slots S) (h : AgreeNear id (spot S i) (4*radiusB x) V V')
    (he : TagNe S (spot S i) (4*radiusB x) k k') :
    Rows.base T x V k i=Rows.base T x V' k' i ∧
      ∀ u : Directions G f, Rows.bump T x V k u i=Rows.bump T x V' k' u i := by
  let B := radiusB x; let R := till x
  have hB : 120 ≤ B := hA.scale
  have hr : R ≤ B := by unfold R B till; omega
  have hi0 : R+4≤B := by unfold R till; unfold B at *; omega
  obtain ⟨s,i⟩ := i
  let o := roots S (slipAt S (s,i))
  have hv := orient_view (S:=S) V V' o (3*B) s (anchored h (by change 3*B+1≤4*B; omega))
  have ht : TagNe S o (3*B) (choice s k) (choice s k') :=
    TagNe.pull s o (3*B) k k' (TagNe.close _ _ _ _ he (by change separation (s.act o) (s.act o)+(3*B+1)≤4*B; rw [separation_self]; omega))
  let V0 := pull s 0 V; let W := pull s 0 V'
  have hf : AgreeNear id o (3*B) V0 W := read_turn s _ (3*B) V V'
    (anchored h (by change 3*B+1 ≤4*B; omega))
  rcases i with p|p
  · refine ⟨?_,fun u => ?_⟩
    · have he1 := plotted_near _ (parent_step S) (facade S s V 0) (facade S s V' 0) T.high T.up R 1 p le_rfl (anchored (hv 0) (by omega))
      have he2 := received T x V0 W hA p (anchored hf (by unfold B; omega))
      unfold V0 W R at *; change Rows.faceFixed T x s V p= Rows.faceFixed T x s V' p
      unfold Rows.faceFixed Xf; rw [he1,he2]
    have hJ j (he : separation o (S.ratio.parent (j:Cell f).1) ≤ R) :
        plaquetteJet S V s j = plaquetteJet S V' s j := by
      unfold plaquetteJet; apply congr_arg (fderiv ℝ · 0); refine funext fun a => ?_
      rw [face_near (parent_step S) j _ _ ((hv a).shrink (by omega))]
    change Rows.faceKick T x V u s p=Rows.faceKick T x V' u s p
    let r := p.1
    have hb : o=S.ratio.parent r.1 := rfl
    have hp : separation o (S.ratio.parent p.1.1) ≤ R := by rw [hb]; unfold r; simp
    unfold Rows.faceKick; split
    · refine tsum_congr fun i => ?_; dsimp only; split
      next h =>
        let k := (T.up.row p.1.2 i).2
        have h0 : k.walk.length ≤ R := Nat.le_trans (show k.walk.length ≤ k.length by unfold Slot.length; omega) h
        rw [hJ _ ((show separation o _ ≤ k.walk.length from slot_distance k p.1.1).trans h0),
          travel_near _ (parent_step S) (facade S s V 0) _ _ k.walk R h0
            (anchored (hv 0) (by omega))]
      rfl
    rw [hJ p.1 hp]
  have hQ a : predictGroup V k s p a = predictGroup V' k' s p a :=
    transmission T x (facade S s V a) (facade S s V' a) (choice s k) _ hA p
      (anchored (hv a) (by unfold B; omega)) (TagNe.close _ _ _ _ ht (by change separation p.1 p.1+B≤3*B; simp; omega))
  constructor
  · change Rows.noiseFixed _ _ _ _ _ _ = Rows.noiseFixed _ _ _ _ _ _
    have hi := side_received T x V0 W hA p (anchored hf (by unfold B; omega))
    unfold V0 W at hi
    have hv1 : pull s 0 V p = pull s 0 V' p := hf p (by change separation o o ≤ _; simp)
    have hv2 := hQ 0; unfold predictGroup at hv2
    unfold Rows.noiseFixed Z; rw [hi,hv1,hv2]
  intro u; change Rows.noiseKick _ _ _ _ _ = Rows.noiseKick _ _ _ _ _
  unfold Rows.noiseKick blockJet predictorTurn; simp_rw [hQ]

theorem bump_with (i : Slots S) (a b : Directions G f) (h : AgreeNear id (spot S i) (4*radiusB x) V V')
    (he : TagNe S (spot S i) (4*radiusB x) k k')
    (hi : ∀ j, separation (spot S i) (portOf S j) ≤ radiusB x → a j=b j) :
    Rows.bump T x V k a i=Rows.bump T x V' k' b i := by
  rw [(drawn T x k k' V V' hA i h he).2 a]; apply bump_dep _ _ V' k' i.1 i.2 a b hA.branched
  intro j hj; have hz := (contains ..).mp hj; have ht := hA.spans
  exact hi j (hz.trans (ht.trans (Nat.div_le_self ..)))

variable (Y Y' : LinkArray G (Frozen A x F)) (q : Chi) (d : ℝ)

/-- At fixed active/frozen lists. -/
def notesAt (o : Site c) (b : ℕ) :=
    ∀ i : Frozen A x F, separation o (portOf S i.val.val) ≤ b → Y i=Y' i



omit hA in
lemma input_note {o : Site c} {b : ℕ} (ht : notesAt x A F Y Y' o b) (he : AgreeNear id o b V V') (j : Bond f)
    (h : separation o (portOf S j) ≤ b) :
    Rows.input x A F (autoShell q d V Y) j=Rows.input x A F (autoShell q d V' Y') j := by
  unfold Rows.input; split
  · split
    next hz hl =>
      unfold autoShell; rw [ht ⟨⟨j,hz⟩,hl⟩ h]; unfold replica; dsimp only; split
      · rfl
      rw [he (S.ratio.parent j.1,j.2) h]
    rfl
  rfl






end YM.AnalyticBridge.Annulus.Map
