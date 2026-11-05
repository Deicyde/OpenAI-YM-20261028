import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Guards
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Post
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical

set_option warningAsError false

/-!
# A location ticket, pre-integration and at fixed F,A

`Aperture` is bought after L and may require boosting
further BEFORE stages. Don't claim that all `Payment`-calendars
automatically admit it just from their type. No finite norm of the
unknown remaining integrands asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus.Map
open Function Filter Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree Finset
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.Fluctuations Next.SectorChange Bid
open YM.SectorNext.Remainder.Affine
open Work.E03 (sep_step parent_step sep_walk stop_route)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n m : Side} {S : StepData c f}

/-- Locationwise k-neighbor equality. -/
structure TagNe (S : StepData c f) (o : Site c) (r : ℕ) (k j : S.Choices) : Prop where
  sites i : separation o i ≤ r → k.1 i=j.1 i
  paths (i : Bond c) : separation o i.1 ≤ r → k.2 i=j.2 i

section chain
variable (s : Signed) (o : Site c) (r : ℕ) (k j : S.Choices)

lemma TagNe.close {u : Site c} {v : ℕ} (ht : TagNe S o r k j) (hr : separation o u+v ≤r) : TagNe S u v k j := by
  have hl (q : Site c) (h : separation u q ≤ v) := (separation_triangle o u q).trans ((Nat.add_le_add_left h _).trans hr)
  exact ⟨fun i hi => ht.sites i (hl _ hi),fun i hi => ht.paths i (hl _ hi)⟩

lemma spin_cost (e : Bond c) : separation (s.act o) (sendEdge s 0 e).1 ≤ separation o e.1 + 1 := by
  cases ht : s.flip e.2
  · rw [edge_positive s e ht]; dsimp only; rw [separation_signed]; omega
  rw [edge_negative s e ht,← step_negative s _ ht e.1]; dsimp only; rw [separation_signed]
  exact (separation_triangle ..).trans (Nat.add_le_add_left (sep_step ..) _)

lemma TagNe.pull (ht : TagNe S (s.act o) (r+1) k j) : TagNe S o r (choice s k) (choice s j) := by
  constructor
  · intro i hi
    have he : StepData.sendSites s 0 i=s.act i := by change s.act i + 0=_; rw [add_zero]
    have hh := ht.sites _ (show separation (s.act o) (s.act i) ≤ r+1 by rw [separation_signed]; omega)
    apply (S.patch.orient s).injective
    -- leg choice has one inverse, use port theorem
    have hv b : S.patch.orient s ((choice s b).1 i) = (b:S.Choices).1 (s.act i) := by
      rw [← S.port_site s 0, show (S.withinSites s 0 (choice s b).1)=b.1 from congr_arg Prod.fst ((S.withinChoice s 0).apply_symm_apply b)]
      exact congr_arg _ he
    rw [hv,hv,hh]
  intro i hi
  have hv b : S.patch.offset s ((choice s b).2 i) = (b:S.Choices).2 (sendEdge s 0 i) := by
    rw [← S.port_bond s 0, show (S.withinBond s 0 (choice s b).2)=b.2 from congr_arg Prod.snd ((S.withinChoice s 0).apply_symm_apply b)]
  have hy := ht.paths _ ((spin_cost s o i).trans (Nat.add_le_add_right hi _))
  apply (S.patch.offset s).injective; rw [hv,hv,hy]

lemma read_turn (V V' : Config G c) (ht : AgreeNear id (s.act o) (r+1) V V') :
    AgreeNear id o r (pull s 0 V) (pull s 0 V') := by
  intro i hi; have he := ht _ ((spin_cost s o i).trans (Nat.add_le_add_right hi _))
  rw [Motion.turn_read,Motion.turn_read,he]
lemma same_tags (o : Bond c) (i : S.Choices) (V : Config G f) (hh : TagNe S o.1 1 k i) : S.prediction V k o=S.prediction V i o := by
  have hp := hh.paths o (by simp)
  unfold StepData.prediction; rw [hp]
  have hj : S.connector V k.1 o=S.connector V i.1 o := by
    funext p; unfold StepData.connector StepData.frames; rw [hh.sites _ (by simp),hh.sites _ (sep_step ..)]
  rw [hj]
end chain

section likelihood
-- cover queries here before choosing torus. Use also for any tagged fallback.
variable (P : Patch)

def ratesPatch : Finset Lattice.Cover := univ.biUnion fun i : P.Points =>
  (((univ.biUnion fun j : P.Points => univ.biUnion fun l : Lattice.Order => (visits i.val (route i.val j.val l)).toFinset) ∪
      univ.biUnion fun j : PlaqAxes => (visits i.val (square j.val.1 j.val.2)).toFinset) ∪
      (univ.biUnion fun j : Axis => (visits i.val (List.replicate P.L.val (posDir j))).toFinset)) ∪ {i.val}

def pitCost := (ratesPatch P).sup fun i => (route 0 i 1).length

lemma admit_rate (o : Site c) (i : Lattice.Cover) (h : i∈ratesPatch S.patch) :
    separation o (S.ratio.parent (wrap f i + S.ratio.embed o)) ≤ pitCost S.patch := by
  have he : stop (S.ratio.embed o) (route 0 i 1) = wrap f i+S.ratio.embed o := by
    simpa only [map_zero, add_zero, add_comm] using stop_route (S.ratio.embed o) 0 i
  nth_rw 1 [← S.ratio.embed_parent o]
  rw [← he]
  exact (sep_walk _ (parent_step S) ..).trans (le_sup (f:=fun i=>(route 0 i 1).length) h)

private lemma pit (Q : KernelChoices) (h : P.Branches Q G) (p : P.FrameTag)
    (V W : CoverConfig G) (hl : ∀ i : Edge Lattice.Cover, i.1∈ratesPatch P → V i=W i) :
    P.frameMass Q V p=P.frameMass Q W p ∧ P.frame Q V p=P.frame Q W p ∧
      ∀ (i : P.Points) (j : Axis), travel V i.val (List.replicate P.L.val (posDir j)) =
        travel W i.val (List.replicate P.L.val (posDir j)) := by
  have he {i : P.Points} (v : Lattice.Cover) (hp : v∈(fun i : P.Points =>
    (((univ.biUnion fun j : P.Points => univ.biUnion fun l : Lattice.Order => (visits i.val (route i.val j.val l)).toFinset) ∪
      univ.biUnion fun j : PlaqAxes => (visits i.val (square j.val.1 j.val.2)).toFinset) ∪
      (univ.biUnion fun j : Axis => (visits i.val (List.replicate P.L.val (posDir j))).toFinset)) ∪ {i.val}) i) : v∈ratesPatch P :=
      mem_biUnion.mpr ⟨_,mem_univ i,hp⟩
  have hR i j l : travel V (i:P.Points).val (route i.val (j:P.Points).val l)=travel W i.val (route i.val j.val l) := by
    refine travel_local _ _ _ _ ?_; intro u hu _; apply hl u; apply he (i:=i)
    simp only [mem_union,mem_biUnion,mem_univ,true_and,List.mem_toFinset]; exact Or.inl (Or.inl (Or.inl ⟨j,l,hu⟩))
  have hs (x : P.FrameTag) : P.axial V x=P.axial W x := funext fun _ => hR ..
  have hv (f : P.Frame G) : P.via f V = P.via f W := by funext x y l; rw [via,via,hR]
  have hc : P.score V = P.score W := by funext f; simp only [score,hv]
  have hm : P.usesMin Q V ↔ P.usesMin Q W := by simp only [usesMin, hs, hv]
  refine ⟨?_,?_,?_⟩
  · have ht : P.eligible Q V=P.eligible Q W := by
      have hx (t : P.FrameTag) : P.axialCost V t=P.axialCost W t := by
        have ht i j : V ((i:P.Points).val,j)=W (i.val,j) := hl (i.val,j) (he (i:=i) _ (mem_union_right _ (mem_singleton_self _)))
        simp only [axialCost,hs,ht]
      have hb i j : faceValue V ((i:P.Points).val,j) = faceValue W (i.val,j) := by
        refine travel_local _ _ _ _ ?_; intro a ha _; apply hl; apply he (i:=i)
        simp only [mem_union,mem_biUnion,mem_univ,true_and,List.mem_toFinset]; exact Or.inl (Or.inl (Or.inr ⟨j,ha⟩))
      simp only [eligible,hx,facesum,hb]
    simp [frameMass,ht,hm]
  · unfold Patch.frame; by_cases hh : P.usesMin Q W
    · rw [if_pos hh, if_pos (hm.mpr hh)]
      have he : P.minimizing W (P.selected V) := by simp only [minimizing, ← hc]; exact (P.min_exists V).choose_spec
      exact (h.frame_unique W hh).unique he (P.min_exists W).choose_spec
    rw [if_neg hh, if_neg (mt hm.mp hh)]; simp only [hs]
  intro i j; refine travel_local _ _ _ _ ?_; intro u hu _; apply hl; apply he (i:=i)
  simp only [mem_union,mem_biUnion,mem_univ,true_and,List.mem_toFinset]; exact Or.inl (Or.inr ⟨j,hu⟩)

lemma rates_local (h : S.patch.Branches S.kernel G) (k j : S.Choices) (V W : Config G f) (p : Bond c)
    (hp : TagNe S p.1 1 k j)
    (hs : AgreeNear S.ratio.parent p.1 (pitCost S.patch+1) V W) :
    frameRate S k V p.1=frameRate S j W p.1 ∧ bondRate S k V p=bondRate S j W p := by
  have he (i : Site c) (hx : separation p.1 i ≤ 1) (b : Edge Lattice.Cover) (hb : b.1∈ratesPatch S.patch) :
      expandAt (S.ratio.embed i) V b=expandAt (S.ratio.embed i) W b := by
    refine hs _ ((separation_triangle p.1 i _).trans ?_)
    exact le_trans (Nat.add_le_add hx (admit_rate (S:=S) i b.1 hb)) (Nat.add_comm 1 _).le
  have hi (i : Site c) (hx : separation p.1 i≤1) := pit S.patch S.kernel h (j.1 i) _ _ (he i hx)
  have ht : separation p.1 p.1 ≤ 1 := by simp
  have hh := sep_step p.1 p.2
  have ha := hp.sites p.1 ht; have hh' := hp.sites _ hh
  refine ⟨?_,?_⟩
  · unfold frameRate; rw [ha,(hi _ ht).1]
  have hu : S.connector V k.1 p = S.connector W j.1 p := by
    funext v; unfold StepData.connector StepData.frames
    rw [ha, hh',(hi _ ht).2.1,(hi _ hh).2.1,(hi _ ht).2.2]
  unfold bondRate; rw [hu,hp.paths p ht]
end likelihood

/-- Includes even witness range for masks. Priced separately for this
exercise. -/
structure Aperture (S : StepData c f) (T : Tube G S) (x : ℝ) : Prop where
  visits : pitCost S.patch+10≤ radiusB x/50
  branched : S.patch.Branches S.kernel G
  spans : span S.patch x ≤ radiusB x/50
  scale : 120≤radiusB x
  fine : ∃ a, LaneCounts T.up x (fiery G x S.patch.L) T.high a 1 S.ratio.parent
  coarse : ∃ a, LaneCounts T.down x (temp x) T.low a S.patch.L.val (id : Site c → Site c)

lemma aperture (Q : Teller G) (P : Patch) : ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=P → Q.Funds S T → Aperture S T x := by
  let a := G.slopeConstant * Real.log P.L.val
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (50*(pitCost P+120)),
    small_span P,Work.E04.eventually_room a Q.top.clip.relaxation Q.top.clip.radius_pos,
    Work.E04.eventually_room 0 Q.below.clip.relaxation Q.below.clip.radius_pos] with x hx hv he hh
  intro c f S T hq hp
  obtain ⟨b,w,hb,h⟩ := hp.feeds
  simp only [add_zero] at hh
  refine ⟨by rw [hq]; omega, funds_branch hp,hq.symm ▸ hv,by omega,?_,?_⟩
  · rw [hp.high]
    refine ⟨_,Work.E04.lanes hb le_rfl (Work.E04.temp_nonneg _) (by decide) (Work.E04.parent_separation _) ?_⟩
    rw [hq]; exact he
  rw [hp.low]; exact ⟨_,Work.E04.lanes h le_rfl (Work.E04.temp_nonneg x) S.patch.L.property (fun i j => Nat.le_succ _) hh⟩
end YM.AnalyticBridge.Annulus.Map
