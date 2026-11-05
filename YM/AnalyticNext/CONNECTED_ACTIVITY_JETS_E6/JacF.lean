import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District


/-!
# Tree transition for the vacuum determinant

 Integer cochain basis change (on FULL dozing + active completion). No
 assumptions on the reach of supported rotations; does not yet retag K families.
 Complements between any two forests have same cardinal. Not claiming positivity
 generally -- see Rotator prices. Used with F external to word.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.TreeColor
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Bid  Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} (F H : Forest S.ratio) {P : Teller G}

private lemma leaf_distinct (i j : Site f) (hi : leaf S.ratio i) (hj:leaf S.ratio j) (h : (F.up i).used i=(F.up j).used j) : i=j := by
  have hp:= F.rise i hi; have hq:=F.rise j hj
  cases he : F.up i with
  | mk a b =>
    rw [he] at h hp
    cases hz : F.up j with
    | mk k d =>
      rw [hz] at h hq
      cases b <;> cases d <;> simp only [Lattice.Step.used,Bool.false_eq_true,↓reduceIte,Prod.mk.injEq] at h
      · exact h.1
      · have ha:=h.1; rw [h.2] at hp; change F.height (i+step k)<_ at hp; rw [show i+step k=j from by rw [ha,sub_add_cancel]] at hp
        change F.height (j+ -step k) < _ at hq; rw [← sub_eq_add_neg,← ha] at hq; omega
      · have ha:=h.1; rw [← h.2] at hq; change F.height (j+step a)<_ at hq; rw [show j+step a=i from by rw [← ha,sub_add_cancel]] at hq
        change F.height (i+ -step a) < _ at hp; rw [← sub_eq_add_neg,ha] at hp; omega
      have hh := h.1; rw [h.2] at hh; exact sub_left_injective hh

def tallyF : (↥F.trunks)≃(↥H.trunks) := by
  let K : ∀F:Forest S.ratio, {i//leaf S.ratio i}≃↥F.trunks := by
    intro F
    refine Equiv.ofBijective (fun i=> ⟨(F.up i.val).used i.val,(F.trunk_mem_iff _).mpr ⟨i.val,i.2,rfl⟩⟩) ⟨fun i j he=>?_,fun i=>?_⟩
    · exact Subtype.ext (leaf_distinct _ _ _ i.2 j.2 (congr_arg Subtype.val he))
    obtain ⟨x,h,hx⟩:= (F.trunk_mem_iff _).mp i.2; exact ⟨⟨x,h⟩,Subtype.ext hx⟩
  exact (K F).symm.trans (K H)
lemma freed : Fintype.card F.Free=Fintype.card H.Free := by
  have hp:= Fintype.card_congr (tallyF F H); rw [Fintype.card_subtype_compl,Fintype.card_subtype_compl,hp]

section rods
variable {A : Type} [AddCommGroup A]
local notation "dir" => Bond f → A

def gradient (u : Site f→ A) : Bond f → A := fun i=> u (i.1+step i.2)-u i.1
-- use arbitrary scalars / linear CL
private lemma telescoping (u: Site f→A) (x : Site f) (p : Walk) : linkSum (gradient u) x p=u (stop x p)-u x := by
  induction p generalizing x with
  | nil => simp [linkSum,stop]
  | cons d p ih => rw [linkSum,stop,ih]; rcases d with ⟨i,h|h⟩ <;> simp [Step.used,Step.vec,gradient,sub_eq_add_neg] <;> abel

lemma lane_plus (u v: Bond f →A) (x : Site f) (p : Walk) : linkSum (u+v) x p=linkSum u x p+linkSum v x p := by
  induction p generalizing x with
  | nil => simp [linkSum]
  | cons d p ih => rw [linkSum,linkSum,linkSum,ih]; split <;> simp [*] <;> abel

def aligns (v : Bond f → A) : Site f→ A := fun i=> linkSum v i (F.hike i)
def bundled (v : Bond f → A) := v+gradient (aligns F v)
lemma numbered (v : Bond f → A) (i : Bond f) (h : i∈F.trunks) : bundled F v i=0 := by
  obtain ⟨x,hx,rfl⟩ := (F.trunk_mem_iff _).mp h
  have hh:= F.stays x hx
  have ht : aligns F v x=(if (F.up x).neg then -v ((F.up x).used x) else v ((F.up x).used x))+aligns F v (x+(F.up x).vec) := by
    unfold aligns; nth_rw 1 [Forest.hike, dif_pos hx]; rfl
  cases he : F.up x with
  | mk i val =>
    rw [he] at ht
    cases val <;> simp only [Step.used,Bool.false_eq_true,↓reduceIte,Step.vec] at *
    · unfold bundled; rw [Pi.add_apply,gradient]; dsimp only; rw [ht]; abel
    unfold bundled; rw [Pi.add_apply,gradient]; dsimp only; rw [sub_add_cancel,ht,sub_eq_add_neg]; abel
lemma vacates {u:Bond f→A} (hp : ∀ i∈F.trunks,u i=0) : bundled F u=u := by
  have he (x : Site f) : aligns F u x=0 := by
    unfold aligns; induction x using Forest.hike.induct F with
    | case1 x hx ih => rw [Forest.hike,dif_pos hx, Exterior.linkSum, hp _ ((F.trunk_mem_iff _).mpr ⟨x,hx,rfl⟩),ih]; simp
    | case2 x hx => rw [Forest.hike, dif_neg hx]; rfl
  funext i; unfold bundled gradient; rw [Pi.add_apply]; simp only [he,sub_zero,add_zero]
lemma evaporates (v : Site f → A) (h : ∀ i,v (S.ratio.embed i)=0) : bundled F (gradient v)=0 := by
  unfold bundled aligns; simp_rw [telescoping,F.hike_root,h]; funext i; unfold gradient; simp
lemma aligns_embed (u : Bond f → A) (p : Site c) : aligns F u (S.ratio.embed p)=0 := by
  unfold aligns; rw [Forest.hike,dif_neg]; rfl
  apply Not.intro; unfold leaf; dsimp only; rw [Ratio.embed_parent]; simp
lemma bundle_sum (u v : Bond f → A) : bundled F (u+v)=bundled F u+bundled F v := by
  funext i; simp only [bundled,gradient, aligns, lane_plus, Pi.add_apply]; abel

def directF (u : Bond f → A) : Bond f → A := fun i=> if i∈F.trunks then 0 else u i
lemma trunkless (u : Bond f→A) (i) (hi : i∈F.trunks) : directF F u i=0:=if_pos hi

def surgery (t : (↥F.trunks) ≃ (↥H.trunks)) (u : Bond f→A) : Bond f → A := fun i=> if h:i∈ H.trunks then
    u ((t.symm ⟨i,h⟩).val) else bundled H (directF F u) i
lemma enwrap (t : (↥F.trunks) ≃ (↥H.trunks)) (u : Bond f→A) : directF H (surgery F H t u)=bundled H (directF F u) := by
  funext i; unfold directF surgery; by_cases h:i∈H.trunks
  · rw [if_pos h,numbered H _ i h]
  rw [if_neg h,dif_neg h]; rfl
lemma stays_all (t : (↥F.trunks) ≃ (↥H.trunks)) (u : Bond f→A) : surgery H F t.symm (surgery F H t u)=u := by
  let v:=surgery F H t u
  have he: directF F (surgery H F t.symm v)=directF F u := by unfold v; rw [enwrap, enwrap, show bundled H (directF F u)=directF F u+gradient (aligns H _) from rfl,bundle_sum,evaporates F _ (aligns_embed H (directF F u)),add_zero]; exact vacates F (trunkless F u)
  funext i
  by_cases h:i∈F.trunks
  · unfold surgery; rw [dif_pos h, dif_pos];
    · simp
    exact (t ⟨i,h⟩).2
  simpa only [v,directF, if_neg h] using congr_fun he i
end rods
end YM.ConnectedActivityE6.TreeColor
