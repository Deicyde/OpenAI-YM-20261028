import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsZone

/-! Trees: generalize E6/ColumnL reasoning to **changing forests**, including active, lens and invitations. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.WoodZone
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n d : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {x : Site c} {X : Coat T F} {X' : Coat T F'} {a d k : ℕ}
variable (H : WoodZone X X' x a) (h : Room P S T X.x)
include H
lemma B : X'.B=X.B := congr_arg radiusB H.temp.symm
lemma R : X'.R=X.R := congr_arg till H.temp.symm

lemma shifting (s : Signed) (p : Spot c f) (he : x=X.addr s p) (ha : 6*X.B≤a) :
    X.selected s p ↔ X'.selected s p := by
  unfold Coat.selected; rw [H.B]; change ¬Inside _ _ _ ↔ ¬ Inside (X.addr s p) _ _
  subst x; exact (H.covert _ (by rw [separation_self,zero_add]; exact ha)).not

include h in
lemma real (s : Signed) (p : Rod c f) (he : x=s.act (focus S p)) (ha : 12*X.B ≤ a)
    (u u' : Directions G f) (hh : ∀ i, distAt S i x ≤ X.B → X.Hot i → u i=u' i) :
    X.realPath s p u=X'.realPath s p u' := by
  subst x; unfold realPath; rw [H.patrol s p rfl (by omega) h,H.R,raw_near T h ..];
  · exact H.pay.shrink (by rw [separation_self]; change 0+X.B/4≤ a; omega)
  intro i hi; change distAt S i _ ≤ X.B/4 at hi
  exact (H.reports i (by have h : 100 ≤ X.B:=h.sight.1; omega) (hh _ (by omega))).2

include h in
lemma billing (i : Mention c f) (he : x=root S i) (ha : 12*X.B ≤ a) : X.priced 0 i=X'.priced 0 i := by
  have hz : X.selected i.1 (spot S i.2) ↔ X'.selected i.1 (spot S i.2) := H.shifting _ _
    (by unfold Coat.addr; rw [← cost_is_here]; exact he) (by omega)
  unfold Coat.priced; rw [hz,H.real h i.1 i.2 he ha 0 0 (fun _ _ _=>rfl)]

include h in
lemma motionL (i : Mention c f) (u : Directions G f) (he : x=root S i) (ha : 12*X.B≤a) :
    X.motion u i=X'.motion u i := by
  have hz := H.shifting i.1 (spot S i.2) (by unfold Coat.addr; rw [← cost_is_here]; exact he) (by omega)
  unfold Coat.motion; rw [hz,H.R, raw_near T h _ X'.V (X.lens u) (X'.lens u) i.2 i.1]
  · exact H.pay.shrink (by change separation x (root S i)+X.B/4≤_; rw [he,separation_self]; omega)
  intro b hb
  have hh := H.tides b (by
    have hv : distAt S b x ≤ X.B/4 := by rw [he]; exact hb
    have hr : 100 ≤ X.B:=h.sight.1; omega)
  unfold Coat.lens; rw [hh]

include h in
lemma coupling (p : Tubular f G) (he : x=along S p) (ha : 13*X.B≤a) (j : Coat.Target c f G) :
    let v := separation x (aim S j) ≤ X.B/4
    (v → ∀ q : Tubular f G, X.form j q=X'.form j q) ∧ (¬v → X.form j p=0 ∧ X'.form j p=0) := by
  intro v; constructor
  · intro hi q; simp only [Coat.form,of_apply,stand,(H.tune_down (q:=root S j.1) (b:=12*X.B)
      (by change separation x (aim S j)+_ ≤ _; unfold v at hi; omega)).motionL h j.1 (sing q) rfl (Nat.le_refl _)]
  intro hi; unfold v at hi; rw [he,separation_comm] at hi
  refine ⟨X.plume h j p (lt_of_not_ge hi), X'.plume (H.temp ▸ h) j p (by rw [H.B]; exact lt_of_not_ge hi)⟩

include h in
lemma plateL (p : Tubular f G) (he : x=along S p) (ha : 13*X.B≤a) (q : Tubular f G) : X.plate p q=X'.plate p q := by
  unfold plate; simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
  refine congrArg₂ (·+·) ?_ ?_
  · refine sum_congr rfl fun j _=> ?_
    by_cases h' : separation x (aim S j) ≤ X.B/4
    · simp only [(H.coupling h p he ha j).1 h']
    obtain ⟨hk,hz⟩ := (H.coupling h p he ha j).2 h'
    rw [hk,hz,zero_mul,zero_mul]
  have hf := H.tides p.1 (by
    change separation x (along S p)+1+_≤_; rw [he,separation_self]; have hr : 100 ≤ X.B:=h.sight.1; omega)
  unfold sleepy; by_cases hi : p=q
  · subst q; rw [diagonal_apply_eq,diagonal_apply_eq,hf]
  rw [diagonal_apply_ne _ hi,diagonal_apply_ne _ hi]

include h in
lemma billL (p : Tubular f G) (he : x=along S p) (ha : 13*X.B≤a) : X.linearBill p=X'.linearBill p := by
  unfold linearBill Matrix.mulVec dotProduct; refine sum_congr rfl fun j _=> ?_
  simp only [Matrix.transpose_apply,stand]
  by_cases hi : separation x (aim S j) ≤ X.B/4
  · have hF := (H.tune_down (q:= aim S j) (b:=12*X.B) (by omega)).billing h j.1 rfl (Nat.le_refl _)
    rw [hF,(H.coupling h p he ha j).1 hi]
  obtain ⟨hk,hh⟩ := (H.coupling h p he ha j).2 hi
  rw [hk,hh,zero_mul,zero_mul]
end YM.ConnectedActivityE6.WoodZone
