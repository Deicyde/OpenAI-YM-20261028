import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Nooks

/-!
# Share prerequisites. Short and Packet

X·zone suffices even when off-path stores changed. Keep q, mandatory
intersections. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {x : Site c} {X X' : Coat T F} {a d : ℕ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G}

namespace Borough
variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x)
include H p
lemma marksHere (i : Site f) (h : Cleanroom Z (30*X.B) (S.ratio.parent i)) :
    i∈RG.flags R.p.threshold (X.input (X.liftA R.beta w)) ↔ i∈RG.flags R.p.threshold (X'.input (X'.liftA R.beta v)) := by
  rw [flags_spec,flags_spec]
  refine exists_congr fun j => and_congr_right (fun hj=>?_)
  rw [LocalRows.facesight _ (parent_step S) _ _ j ((H.intake p h).shrink (by
    have he := Work.E01.sep_touched j i hj; rw [separation_comm] at he
    have hv := Work.E04.parent_separation S.ratio i j.1; have hx : 100 ≤ X.B := p.sight.1; omega))]

lemma marksOut (t : ℝ) (i : Site c) (h : Cleanroom Z (30*X.B) i) : i∈RG.flags t X.V ↔ i∈RG.flags t X'.V := by
  have hx : 100 ≤ X.B := p.sight.1
  rw [flags_spec,flags_spec]; refine exists_congr fun j => and_congr_right fun hj=> ?_
  have hv := (H.social (x:=i) (a:= 20*X.B) (fun l hl=> h _ (hl.trans (by omega)))).pay
  rw [LocalRows.facesight id sep_step _ _ j (hv.shrink (by
    have he := Work.E01.sep_touched j i hj; rw [separation_comm] at he; change separation i j.1+4≤_; omega))]

abbrev won (i : Panic c f) (A A' : Stores S) :=
    i.elim (fun i=> i∈A.costs ↔ i∈A'.costs) (Sum.elim (fun i=> i∈A.aisles ↔ i∈A'.aisles) (fun _=> True))

lemma ushers (A A' : Stores S) (i : Panic c f) (he : won i A A') (b : ℝ) (h : Cleanroom Z (30*X.B) (focus_alarms S i)) :
    X.rawStorm (X.liftA R.beta w) b A R k i=X'.rawStorm (X'.liftA R.beta v) b A' R k' i := by
  let U:=X.input (X.liftA R.beta w); let Y:=X'.input (X'.liftA R.beta v)
  let o:= focus_alarms S i
  have hp : 100 ≤ X.B ∧ 4*X.R+4+predReach S.patch ≤ X.B/100 := p.sight
  have hg : Zone X X' o (25*X.B) := H.social (x:=o) (fun j hj=> h j (by change separation o j ≤_; omega))
  have hq : AgreeNear id o X.B (S.prediction U X.k) (S.prediction Y X'.k) := H.targeting p h
  have hu : AgreeNear _ o _ U Y := H.intake p h
  unfold rawStorm; rcases i with i|i|i|i|i
  · simp only [Sum.elim, Mask.fine]; unfold Pressure.toll
    rw [← H.chi, ← H.flame,facesight _ (parent_step S) U Y i (hu.shrink (by change separation o o+4≤_; rw [separation_self]; omega))]
    change i∈A.costs ↔ _ at he; simp_rw [he]; rfl
  · have hz : X.V i=X'.V i := hg.pay i (show separation i.1 i.1 ≤_ by rw [separation_self]; omega)
    have hv := hq i (by change separation i.1 i.1 ≤ _; rw [separation_self]; omega)
    simp only [Sum.elim, Mask.noise,wire]; rw [H.chi,H.flame,hz]; unfold U Y at hv; rw [hv]
    change i∈A.aisles ↔ _ at he; simp_rw [he]
  · have hh : o=i.1 := rfl
    
    exact (Emblems.choices U Y i X.k X'.k (funds_branch p.accepted) (hg.site _ (by rw [hh,separation_self]; omega)) (hg.site _
      (by rw [hh]; have ht := sep_step i.1 i.2; omega)) (hg.bond i (by rw [hh,separation_self]; omega))
      (hu.shrink (by rw [hh,separation_self]; omega))).2.1
  · exact (Emblems.frames_agree U Y i X.k X'.k (funds_branch p.accepted) (hg.site _ (by change separation i i ≤ _; rw [separation_self]; omega))
      (hu.shrink (by change separation i i+_ ≤ _; rw [separation_self]; omega))).2
  have ht := H.marksHere p i h
  have hv := H.covering i (h _ (by change separation o o≤_; rw [separation_self]; omega))
  unfold Contract.charges; simp_rw [Sum.elim,hv,ht]
end Borough

lemma alarm_base (S : StepData c f) (i : Panic c f) (y : Site c) (he : y∈districts S i) :
    separation (focus_alarms S i) y ≤ 1 := by
  have h := Coat.sigh S (Sum.inl i) y 0 0 (by change y∈halo _ _; exact halo_subset _ _ he)
  exact h
private lemma awards (S : StepData c f) (l : ℕ) (b : Stores S) (p : Packets.Seed S) (h : p∈Packets.seeds S b) :
    anchor S p∈b.dome l := by
  rw [dome,←place_reads]; apply halo_subset
  exact mem_biUnion.mpr ⟨p,h,contains ..⟩

namespace Borough
variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x)
include H p
omit H p in
private lemma neither (i : Panic c f) (ha : ¬ mandatory X.seeds X.B i) (hb : ¬ mandatory X'.seeds X'.B i) : won i X.seeds X'.seeds := by
  rcases i with i|i|i
  · have hh (Z : Coat T F) (hp : ¬ mandatory Z.seeds Z.B (.inl i)) : i ∉ Z.seeds.costs := fun he => hp <|
      Finset.not_disjoint_iff.mpr ⟨_, awards S _ Z.seeds (.inl i) (mem_disjSum.mpr (Or.inl ⟨i,he,rfl⟩)),contains S (.inl i)⟩
    exact iff_of_false (hh X ha) (hh X' hb)
  · have hh (Z : Coat T F) (hp : ¬ mandatory Z.seeds Z.B (.inr (.inl i))) : i∉ Z.seeds.aisles := fun he => hp <|
      Finset.not_disjoint_iff.mpr ⟨_, awards S _ Z.seeds (.inr (.inl i)) (by simp [Packets.seeds,he]), contains S (.inr (.inl i))⟩
    exact iff_of_false (hh X ha) (hh X' hb)
  exact True.intro
lemma mayorL (l : ℕ) (hl : 500≤l) (i : Panic c f) (he : field_support S X.B l (.inl i) ⊆ Z) (a b : ℝ) :
    X.mayor (X.liftA R.beta w) b a R k i=X'.mayor (X'.liftA R.beta v) b a R k' i := by
  let o := focus_alarms S i
  have hk u (hu : u ∈ districts S i) : Cleanroom Z (l*X.B) u := fun j hj=> he <| halo_spec.mpr ⟨u,hu,hj⟩
  have hv : 500*X.B≤l*X.B := Nat.mul_le_mul_right _ hl
  have h1 : 100 ≤ X.B := p.sight.1
  have hT (u) (hu : u∈districts S i) : Zone X X' u (350*X.B) := H.social fun j hj=> hk u hu j (by omega)
  have hG : mandatory X.seeds X.B i ↔ mandatory X'.seeds X'.B i := by
    have hp u (hu : u∈districts S i) := (hT _ hu).covert u (b:=300*X.B) (by rw [separation_self]; omega)
    unfold mandatory; rw [← H.B]; simp only [not_disjoint_iff]; constructor
    · rintro ⟨j,hg,hu⟩; exact ⟨j,(hp j hu).1 hg,hu⟩
    rintro ⟨j,hg,hu⟩; exact ⟨j,(hp j hu).2 hg,hu⟩
  unfold mayor; by_cases hx : mandatory X.seeds X.B i
  · rw [if_pos hx,if_pos (hG.1 hx)]
  have hy := hG.not.mp hx
  rw [if_neg hx,if_neg hy,H.ushers p X.seeds X'.seeds i (neither i hx hy) b (fun j hj => hk o (home_storm S i) j (hj.trans (by omega))),← H.B,H.enforces p]
  intro j hj; obtain ⟨v,hv,hh⟩ := halo_spec.mp hj
  apply fans (hk v hv); omega
lemma warning (l : ℕ) (hl : 500 ≤ l) (i : WarningAt c f) (he : field_support S X.B l i⊆ Z) (a b : ℝ) :
    X.detect (X.liftA R.beta w) b a R k i=X'.detect (X'.liftA R.beta v) b a R k' i := by
  rcases i with i|i
  · exact H.mayorL p l hl i he ..
  have hp : 500*X.B≤l*X.B := Nat.mul_le_mul_right _ hl
  obtain ⟨hv,hz⟩ := H.occupied p i (fun j hj=> town_circle he j (hj.trans (by omega)))
  unfold detect aura; simp only [Sum.elim]; simp_rw [H.coin p (p:=i) (fun j hj=> town_circle he j (hj.trans (by omega))),hz,hv]
end Borough
end YM.ConnectedActivityE6
