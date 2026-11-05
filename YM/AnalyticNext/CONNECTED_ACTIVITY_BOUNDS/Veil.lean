import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.DCompare
import YM.Push.ABSOLUTE_SUMS.Mixed


/-!
# Stencil to remove clamps and work in a patch

Uses true thresholds and data on a halo, all orientations including away
from holes. Query when a V selector outside is determined by universal
distance and compact-group chords, not assuming payload locations at
which it returns nonzero automatically determine all decisions. Again some
public read lemmas adapted from the working private localities; here also
publish/use on the projected F and on the affines.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section prices

/-- E04 receipts pre-L in support, obtain unconditionally on any
operation funded by Teller. Plot at empty halo is locally valid for
this use. Don't deduce a global default slice from that Plot. -/
def blank (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩

lemma blank_dome (S : StepData c f) (r) : (blank S).dome r=∅ := by
  ext; simp [dome,place,halo_spec,blank]

structure Reserve (P : Teller G) (C : ℝ) : Prop where
  price : 0<C
  receipt (L : Side) : ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
    P.Funds S T → S.patch.L=L → 100*(1+radiusB x) ≤ c.val → (∀ (_ : Forest S.ratio) (V : Config G c),
      Bid.LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent ∧
      Bid.LaneCounts T.down x (temp x) T.low C S.patch.L.val (id:Site c → Site c) ∧ Bid.Maximum C T x V)

lemma reserves (P : Teller G) : ∃ C, Reserve P C := by
  obtain ⟨C,hC,h⟩ := Work.E04.answer Work.E03.answer P
  refine ⟨C,hC,fun L => ?_⟩
  filter_upwards [(h L 0).late] with x hx c f S T hh hS hm F V
  let k : S.Choices := Classical.ofNonempty
  have hF : Plot (blank S) (1:Config G f) k V x 0 := by
    refine ⟨fun p hp => ?_,fun b hb => ?_,fun i hi => ?_,fun i hi => ?_⟩
    all_goals simp [blank_dome] at *
  rw [hS]; exact hx c f S hS hm T hh F (blank S) 1 k V (fun _ _ => rfl) hF

lemma honor {W : Config G n} {t : ℝ} {y : Site n} {p : PlaqAxes} (h : y ∉ RG.flags t W) :
    toll W (y,p) ≤ t := by
  apply le_of_not_gt; intro he; exact h ((RG.flags_spec ..).mpr ⟨(y,p),Work.E01.base_touched (y,p),he⟩)

lemma veil (T : Tube G S) {C : ℝ} (x : ℝ) (V : Config G c) (i : Twin c)
    (h : Bid.LaneCounts T.down x (temp x) T.low C S.patch.L.val (id:Site c → Site c))
    (hv : ∀ y : Site c,separation i.1.1 y ≤ radiusB x/50 → y∉ RG.flags (temp x) V) :
    T.vision (till x) (temp x) V i=T.Xn (till x) V i := by
  let t := temp x
  unfold Tube.vision Tube.Xn thinned plotted
  have he : toll V i.1 ≤ t := honor (hv _ (by simp))
  split
  next =>
    rw [if_pos]
    intro p; apply le_of_not_gt; intro H
    let V' := h.dropped V i.1.1 p H; have hz : toll V p ≤ t := honor (hv _ V')
    have hm : t ≤ t * Real.exp (↑(separation i.1.1 p.1)/ T.low.relaxation) := le_mul_of_one_le_right
      (temp_nonneg _) (Real.one_le_exp (div_nonneg (by positivity) T.low.radius_pos.le))
    exact H.not_ge (hz.trans hm)
  next =>
    split
    next => rw [one_smul]
    next hh =>
      have ht : 0<toll V i.1 := lt_of_le_of_ne (G.chord_nonneg _) (Ne.symm hh)
      rw [min_eq_left (by rw [le_div_iff₀ ht, one_mul]; exact he),one_smul]
end prices

-- Numerical stencils, reads with model/tag parameters kept fixed. No freedom to
-- use an eigenvalue-cap based st instead.
section extents
variable {ι κ : Type*} (M : Config G c→ι→κ→Pay G) (p : ι→Site c) (q : κ→Site c)
open Work.E03
structure Unseen (R : ℕ) : Prop where
  view i j (V W : Config G c) : AgreeNear id (p i) R V W → M V i j=M W i j
  zero i j V : R < separation (p i) (q j) → M V i j=0

lemma Unseen.pay [Fintype κ] {V W : Config G c} {v w : κ→G.Color} {R i}
    (h : Unseen M p q R) (hp : AgreeNear id (p i) R V W) (hv : ∀ j, separation (p i) (q j) ≤ R → v j=w j) :
    zip (M V) v i=zip (M W) w i := by
  unfold zip; refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : separation (p i) (q j)≤R
  · rw [hv j hi,h.view i j V W hp]
  rw [h.zero i j V (lt_of_not_ge hi), h.zero i j W (lt_of_not_ge hi), _root_.zero_apply, _root_.zero_apply]

lemma laneSight {α β : Type*} (N : Row α β) (d R : ℕ) (hd : 1 ≤ d) (a : ι → Co c α) (b : κ → Co c β) :
    Unseen (fun (V : Config G c) i j => lane R d V N (a i) (b j)) (Prod.fst∘a) (Prod.fst∘b) R := by
  have hh r (hr : r*d≤R) : r≤R := (by nlinarith)
  constructor
  · intro i j V W H; apply tsum_congr; intro y; unfold priced; split
    next h => rw [rated,rated, travel_near id (fun _ _ => sep_step ..) _ _ _ _ R (hh _ h.1) H]
    next h => rfl
  intro i j V ht
  have he (u) : priced R d V N (a i) (b j) u=0 := by
    unfold priced; split
    next h =>
      let w := route 0 u 1
      have he : stop (a i).1 w = (b j).1 := by rw [h.2]; simpa only [map_zero, add_zero] using Work.E03.stop_route (a i).1 0 u
      have hv := Work.E03.sep_walk (fun x : Site c => x) Work.E03.sep_step (a i).1 w
      rw [he] at hv; exact (ht.not_ge (hv.trans (hh _ h.1))).elim
    next => rfl
  simp only [lane,he,tsum_zero]

lemma river (T : Tube G S) (R : ℕ) : Unseen (T.Φ R)
    (fun i : Twin f => S.ratio.parent (mesh i).1) (fun i : Twin c => (mesh i).1) R := by
  constructor
  · intro i j V W ht; apply tsum_congr; intro k; dsimp only [casted]; split
    next h =>
      rw [rated,rated, travel_near S.ratio.parent (parent_step S) _ _ _ _ R h.1 ?_]
      intro e he; unfold replica; split
      next => rfl
      next => exact ht _ he
    next => rfl
  intro i j V ht
  have he u : casted S T.R R V (mesh i) (mesh j) u = 0 := by
    dsimp only [casted]; split
    next h =>
      let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • u) 1
      have hp := sep_walk S.ratio.parent (parent_step S) (mesh i).1 w
      rw [show stop _ w = _ from casted_endpoint S (mesh i).1 u,S.ratio.embed_parent,← h.2] at hp
      exact (ht.not_ge (hp.trans h.1)).elim
    next => rfl
  unfold Tube.Φ leap; simp only [he, tsum_zero]
end extents

-- raw (unclipped, not analytic on all U,V)
section raw
variable (T : Tube G S) (R : ℕ)
open Work.E03

def primalF (V : Config G c) := zip (T.Φ R V) (T.Xn R V)
def primalI (V : Config G c) := zip (T.Φ' R V) (T.Xn R V)
def primalN (V : Config G c) := zip (T.N R V) (T.Xn R V)

def primal (i : Pos S) (k : S.Choices) (V : Config G c) (U : Config G f) : G.Color :=
    let X := pull i.1 0 V; let W := pull i.1 0 U
    i.2.elim (fun p => T.Xf R W p - primalF T R X p)
      (fun b => Pressure.Tube.Z S (S.prediction W (choice i.1 k)) X b - primalI T R X b)

-- coordinate shift allowance on V

def radial (D : Patch) := 2*R+predReach D+10

lemma plots_within (i : Twin c) (w : Site c) (r : ℕ) (V W : Config G c) (he : AgreeNear id w r V W)
    (ht : separation w (mesh i).1 + (R+4) ≤ r) : T.Xn R V i=T.Xn R W i :=
  plotted_near id (fun x i => sep_step x i) V W T.low T.down R S.patch.L.val i S.patch.L.property (he.shrink ht)

lemma primalF_local (i : Twin f) (V W : Config G c) (he : AgreeNear id (S.ratio.parent (mesh i).1) (2*R+4) V W) :
    primalF T R V i=primalF T R W i := Unseen.pay _ _ _ (river T R) (he.shrink (by simp; omega))
      (fun j hj => plots_within T R j _ _ V W he (by omega))

lemma primalI_local (i : Bond c) (V W : Config G c) (he : AgreeNear id i.1 (2*R+4) V W) :
    primalI T R V i=primalI T R W i := Unseen.pay _ _ _
      (i:=i) (laneSight (G:=G) T.R.mn S.patch.L.val R S.patch.L.property pole mesh)
      (he.shrink (show separation i.1 i.1 + R ≤ _ by simp; omega)) (fun j hj => plots_within T R j _ _ V W he (by
      change separation i.1 (mesh j).1≤ _ at hj; omega))

lemma primalN_local (i : Co c Gain) (V W : Config G c) (he : AgreeNear id i.1 (2*R+4) V W) :
    primalN T R V i=primalN T R W i := Unseen.pay _ _ _
      (i:=i) (laneSight (G:=G) T.R.o S.patch.L.val R S.patch.L.property id mesh)
      (he.shrink (show separation i.1 i.1 + R ≤ _ by simp; omega)) (fun j hj => plots_within T R j _ _ V W he (by
      change separation i.1 (mesh j).1≤ _ at hj; omega))

lemma pull_agreesFine (S : StepData c f) {u v : Config G f} (p : Pos S) {D : ℕ}
    (hu : AgreeNear S.ratio.parent (base S p) (D+1) u v) :
    AgreeNear S.ratio.parent (center S p.2) D (pull p.1 0 u) (pull p.1 0 v) := by
  intro i hi; simp only [step_transport,hu (edgeP p.1 i)
    ((along_home p.1 (center S p.2) S i).trans (Nat.add_le_add_right hi _))]

lemma pull_agreesCoarse (s : Signed) (x : Site c) {u v : Config G c} {D : ℕ}
    (hu : AgreeNear id (s.act x) (D+1) u v) : AgreeNear id x D (pull s 0 u) (pull s 0 v) := by
  intro i hi; simp only [step_transport,hu (edgeP s i) ((directed_climb s x i).trans (Nat.add_le_add_right hi _))]

lemma primal_local (p : Pos S) (k : S.Choices) {U W : Config G f} {V X : Config G c} (hb : S.patch.Branches S.kernel G)
    (he : AgreeNear S.ratio.parent (base S p) (radial R S.patch) U W)
    (hd : AgreeNear id (base S p) (radial R S.patch) V X) : primal T R p k V U = primal T R p k X W := by
  let D := radial R S.patch-1
  have hD : D+1=radial R S.patch := by unfold D radial; omega
  rw [← hD] at he hd
  have hu := pull_agreesFine S p he; have hv := pull_agreesCoarse p.1 (center S p.2) hd
  have hel : 2*R+4 ≤ D := by unfold D radial; omega
  have hy : predReach S.patch ≤ D := by unfold D radial; omega
  rcases p with ⟨s,i|i⟩
  · change _-_=_-_
    exact congr_arg₂ Sub.sub
      (plotted_near _ (parent_step S) _ _ T.high T.up R 1 i le_rfl
        (hu.shrink (show separation (S.ratio.parent i.1.1) (S.ratio.parent i.1.1)+(R+4)≤D by simp; omega)))
      (primalF_local T R i _ _ (hv.shrink (show separation (S.ratio.parent i.1.1) (S.ratio.parent i.1.1)+(2*R+4)≤D by simp; exact hel)))
  unfold primal; dsimp only [Sum.elim_inr]; apply congr_arg₂ Sub.sub
  · unfold Tube.Z; rw [hv i (by change separation i.1 i.1 ≤ _; simp),prediction_near_eq hb _ (pull s 0 W) _ i
        (hu.shrink (show separation i.1 i.1 + _ ≤ D by rw [separation_self]; omega))]
  apply primalI_local; exact hv.shrink (show separation i.1 i.1+(2*R+4)≤D by rw [separation_self]; omega)

-- Only through the outward halo. The `φ` path stencil lives in R, don't
-- use R to pay the kept-row tests; for that enlarge to R+B/50 etc.
lemma target_unveiled (x : ℝ) (p : Pos S) (k : S.Choices) (V : Config G c) (U : Config G f)
    {C : ℝ} (h : Bid.LaneCounts T.down x (temp x) T.low C S.patch.L.val (id:Site c → Site c))
    (he : ∀ y : Site c,separation (base S p) y ≤ radiusB x → y∉RG.flags (temp x) V) :
    target T (till x) (temp x) p k V U = primal T (till x) p k V U := by
  let W := pull p.1 0 V
  have ht i (hg : separation (center S p.2) (mesh i).1 ≤ till x) :
      T.vision (till x) (temp x) W i=T.Xn (till x) W i := by
    apply veil T x W i h; intro j hj hp
    have hy : p.1.act j ∈ RG.flags (temp x) V := by
      rw [← Work.H03.flags_send p.1 0]; simpa only [affine,add_zero] using Finset.mem_image_of_mem (affine p.1 0) hp
    apply he (p.1.act j) _ hy
    unfold base; rw [separation_signed]; apply le_trans (separation_triangle _ (mesh i).1 _)
    refine le_trans (Nat.add_le_add hg hj) ?_; unfold till; omega
  rcases p with ⟨a,i|i⟩
  · unfold target primal; dsimp only [Sum.elim_inl]; congr 1
    apply Unseen.pay _ _ _ (river T _) (fun _ _ => rfl) ht
  unfold target primal; dsimp only [Sum.elim_inr]; congr 1
  apply Unseen.pay _ _ _ (laneSight (G:=G) T.R.mn S.patch.L.val (till x) S.patch.L.property pole mesh)
    (fun _ _ => rfl) ht
end raw
end YM.AnalyticNext.ConnectedActivity.Aff
