import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Meters
import YM.SectorNext.LARGE_FIELD_REMAINDERS.CorePacket


/-!
# Restriction and assignment of the drows and affvd parts

Typed packets, with the actual geometry (no obligation here on other
row selections or derivative/locality estimates), for applying the
dyadics local charge. Partition both sets of rows without duplicate
indices. `hot D O...`: anchor in H_D at the orientations read, and both
Twins through the same plaquette. This will leave an actual complement
at that integrand under the Gaussian, not be subtracting two
independently averaged Reps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix Bloch
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

/-- Typed isolation; model  using l=500. Every old seed through
its full 500B halo either present in O or disjoint from the packet
support. No claim on geometry of any optional activity, just this packet.
This version is even stable under turning. -/
structure Isle (O A : Stores S) (l B : ℕ) : Prop where
  hasCost : O.costs ⊆ A.costs
  hasAisles : O.aisles ⊆ A.aisles
  hasFlags : O.flags ⊆ A.flags
  lockedF (i : Cell f) : i∈A.costs → i∉O.costs → Disjoint (halo (l*B) (startPos S i)) (O.dome (l*B))
  lockedB (i : Bond c) : i∈A.aisles → i∉O.aisles → Disjoint (halo (l*B) (pinPos i)) (O.dome (l*B))
  locked (i : Site c) : i∈A.flags → i∉O.flags → Disjoint (halo (l*B) {i}) (O.dome (l*B))

variable {O A : Stores S} {l B : ℕ}



lemma Isle.owns (h : Isle O A l (radiusB x)) (hx : 5 ≤ l) : Owns O A x := by
  have ht : O.dome (5*radiusB x) ⊆ O.dome (l*radiusB x) := Corona.halo_mono (by gcongr) (fun _ h => h)
  refine ⟨h.hasCost,h.hasAisles,h.hasFlags,fun i hi ht' =>
    Disjoint.mono (halo_subset _ _) ht (h.lockedF i hi ht'), fun i hi ht' =>
    Disjoint.mono (halo_subset _ _) ht (h.lockedB i hi ht'),?_⟩
  intro i hi ht' hu
  exact Finset.disjoint_left.mp (h.locked i hi ht') (halo_subset _ _ (Finset.mem_singleton_self _)) (ht hu)

lemma turn_halo (s : Signed) {x : Site c} {R Q : Support c} (h : ∀ x, x∈Q ↔ s.act x∈R) (b : ℕ) :
    x∈halo b Q ↔ s.act x∈halo b R := by
  simp_rw [halo_spec]
  constructor
  · rintro ⟨i,hi,he⟩; exact ⟨s.act i,(h i).mp hi,(separation_signed ..).trans_le he⟩
  rintro ⟨i,hi,he⟩; obtain ⟨j,rfl⟩ := s.actEquiv.surjective i
  exact ⟨j,(h j).mpr hi,(separation_signed j x s) ▸ he⟩

lemma Isle.turn (h : Isle O A l B) (s : Signed) : Isle (turnStore s O) (turnStore s A) l B := by
  constructor
  · intro i hi; exact (cost_turn ..).mpr (h.hasCost ((cost_turn ..).mp hi))
  · intro i hi; exact (aisle_turn ..).mpr (h.hasAisles ((aisle_turn ..).mp hi))
  · intro i hi; exact (flag_turn ..).mpr (h.hasFlags ((flag_turn ..).mp hi))
  · intro i hi ht; exact (turn_incidence s _ _ _ _ (fun x => turn_halo s (fun x => (turn_start s x i).symm) _) (fun x => turn_dome s ..)).mpr
      (h.lockedF _ ((cost_turn ..).mp hi) (mt (cost_turn ..).mpr ht))
  · intro i hi ht; exact (turn_incidence s _ _ _ _ (fun x => turn_halo s (fun x => (turn_pin s x i).symm) _) (fun x => turn_dome s ..)).mpr
      (h.lockedB _ ((aisle_turn ..).mp hi) (mt (aisle_turn ..).mpr ht))
  intro i hi ht
  refine (turn_incidence s _ _ _ _ (fun x => turn_halo s (fun x => by simp [s.act_injective.eq_iff]) _) (fun x => turn_dome s ..)).mpr
      (h.locked (s.act i) ((flag_turn ..).mp hi) (mt (flag_turn ..).mpr ht))

lemma Isle.cleared (h : Isle O A l B) {R t : ℕ} {x : Site c} (hR : R≤l*B) (ht : t≤l*B) (hx : x∈O.dome R) :
    x∈A.dome t → x∈O.dome t := by
  have hl : x∈O.dome (l*B) := Corona.halo_mono hR (fun _ h => h) hx
  intro hs
  rw [dome,halo_spec] at hs ⊢
  obtain ⟨y,h1,h2⟩ := hs
  unfold place at h1
  simp only [Finset.mem_union,Finset.mem_biUnion] at h1
  rcases h1 with ( ⟨p,hq,hP⟩|⟨p,hq,hP⟩ ) |hq
  · have he : x∈halo (l*B) (startPos S p) := halo_spec.mpr ⟨y,hP,h2.trans ht⟩
    by_cases hr : p∈O.costs
    · exact ⟨y,Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p,hr,hP⟩)),h2⟩
    exact (Finset.disjoint_left.mp (h.lockedF p hq hr) he hl).elim
  · have he : x∈halo (l*B) (pinPos p) := halo_spec.mpr ⟨y,hP,h2.trans ht⟩
    by_cases hr : p∈O.aisles
    · exact ⟨y,Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hr,hP⟩)),h2⟩
    exact (Finset.disjoint_left.mp (h.lockedB p hq hr) he hl).elim
  have he : x∈halo (l*B) ({y}:Support c) := halo_spec.mpr ⟨y,Finset.mem_singleton_self y,h2.trans ht⟩
  by_cases hr : y∈O.flags
  · exact ⟨y,Finset.mem_union_right _ hr,h2⟩
  exact (Finset.disjoint_left.mp (h.locked y hq hr) he hl).elim

lemma Isle.place (h : Isle O A l B) : O.place ⊆ A.place := by
  intro i hi
  unfold Stores.place at hi ⊢
  simp only [Finset.mem_union,Finset.mem_biUnion] at hi ⊢
  rcases hi with ( ⟨p,hp,he⟩|⟨p,hp,he⟩ ) |hf
  · exact Or.inl (Or.inl ⟨p,h.hasCost hp,he⟩)
  · exact Or.inl (Or.inr ⟨p,h.hasAisles hp,he⟩)
  exact Or.inr (h.hasFlags hf)
lemma Isle.burn (h : Isle O A l B) {t r : ℕ} (hr : t ≤ r) : O.dome t ⊆ A.dome r := Corona.halo_mono hr h.place

namespace Harvest

/-- Arguments here already channel rotated. -/
def hot (O : Stores S) (D B : ℕ) : Window S where
  face := Finset.univ.filter fun i => S.ratio.parent i.1 ∈ O.dome (D*B)
  noise := Finset.univ.filter fun i => i.1∈ O.dome (D*B)
  coarse := Finset.univ.filter fun i => i.1∈ O.dome (D*B)
  rows := Finset.univ.filter fun i => i.1∈ O.dome (D*B)

def inner (O : Stores S) (x : ℝ) := hot O 2 (radiusB x)

def remove (M J : Window S) : Window S := ⟨M.face \ J.face,M.noise \ J.noise,M.coarse \ J.coarse,M.rows \ J.rows⟩

/-- open on the 2B edge, closed through `D*B`. -/
def corona (O : Stores S) (D : ℕ) (x : ℝ) := remove (hot O D (radiusB x)) (inner O x)



lemma in_face {i : Cell f} {D : ℕ} : i∈(hot O D B).face ↔ S.ratio.parent i.1∈O.dome (D*B) := by simp [hot]
lemma in_noise {i : Bond c} {D : ℕ} : i∈(hot O D B).noise ↔ i.1∈O.dome (D*B) := by simp [hot]
lemma in_coarse {i : Cell c} {D : ℕ} : i∈(hot O D B).coarse ↔ i.1∈O.dome (D*B) := by simp [hot]
lemma in_row {i : Co c Gain} {D : ℕ} : i∈(hot O D B).rows ↔ i.1∈O.dome (D*B) := by simp [hot]

lemma mono (O : Stores S) (D d B : ℕ) (h : D≤d) :
    (hot O D B).face ⊆ (hot O d B).face ∧ (hot O D B).noise ⊆ (hot O d B).noise ∧
      (hot O D B).coarse ⊆ (hot O d B).coarse ∧ (hot O D B).rows ⊆ (hot O d B).rows := by
  have hh : O.dome (D*B) ⊆ O.dome (d*B) := Corona.halo_mono (by gcongr) (fun _ h => h)
  exact ⟨fun i ht => in_face.mpr (hh (in_face.mp ht)),fun i ht => in_noise.mpr (hh (in_noise.mp ht)),
    fun i ht => in_coarse.mpr (hh (in_coarse.mp ht)),fun i ht => in_row.mpr (hh (in_row.mp ht))⟩

lemma earns {D : ℕ} (hD : D≤l) (ht : 2≤l) (h : Isle O A l (radiusB x)) :
    (corona O D x).annulus O A D (radiusB x) := by
  unfold Window.annulus inSweep
  have hi {y : Site c} (hy : y∈O.dome (D*radiusB x)) (hx : y∉O.dome (2*radiusB x)) : y∉A.dome (2*radiusB x) :=
    fun hs => hx (h.cleared (Nat.mul_le_mul_right _ hD) (Nat.mul_le_mul_right _ ht) hy hs)
  refine ⟨fun i he => ?_,fun i he => ?_,fun i he => ?_⟩ <;>
    simp only [corona,remove,Finset.mem_sdiff,inner,in_face,in_noise,in_coarse] at he
      <;> exact ⟨hi he.1 he.2,he.1⟩

section regions
variable (T : Tube G S) (U : Config G f) (V : Config G c) (k : S.Choices)

lemma already (O : Stores S) (x : ℝ) :
    (inner O x).work T x U k V = O.assessed T x U (S.prediction U k) V := by
  unfold inner hot assessed tally talli talll tallc talln limit intern outs coordN Window.work onWindow
  simp only [Finset.sum_add_distrib]
  abel

lemma sum_work (O : Stores S) (D : ℕ) (x : ℝ) (hD : 2≤D) :
    (corona O D x).work T x U k V + (inner O x).work T x U k V = (hot O D (radiusB x)).work T x U k V := by
  obtain ⟨h1,h2,h3,h4⟩ := mono O 2 D (radiusB x) hD
  unfold corona Window.work onWindow remove; dsimp only
  have ha {ι : Type} [DecidableEq ι] (f : ι → ℝ) (A B : Finset ι) (h : B⊆A) : ∑ i∈A\B, f i = ∑ i∈A,f i - ∑ i∈B,f i := by
    rw [eq_sub_iff_add_eq]; exact Finset.sum_sdiff h
  unfold inner
  simp only [ha _ _ _ h1, ha _ _ _ h2,
    ha _ _ _ h3, ha _ _ _ h4]
  abel

end regions

lemma clear_core {F : Forest S.ratio} {s : Signed} (hx : span S.patch x ≤ radiusB x/50) (h : Isle O A l (radiusB x)) {i : Where S}
    (he : roots S i ∈ (turnStore s O).dome (2*radiusB x)) : ¬ curb (shots S x) A F x s i := by
  have hl := (turn_dome s O (roots S i) _).mp he
  intro hs
  apply (guarded hx hs).1
  exact h.burn (show 2*radiusB x ≤ 9*radiusB x+9*radiusB x/10 by omega) hl

lemma coronate {F : Forest S.ratio} (s : Signed) (D : ℕ) (hx : span S.patch x ≤ radiusB x/50) (h : Isle O A l (radiusB x)) :
    emitted x (shots S x) A F (hot (turnStore s O) D (radiusB x)) s = emitted x (shots S x) A F (corona (turnStore s O) D x) s := by
  unfold emitted corona remove
  congr 1
  · ext i; simp only [Finset.mem_filter,Finset.mem_sdiff,inner,in_face]
    constructor
    · rintro ⟨ha,hb⟩; exact ⟨⟨ha,fun he => clear_core (i:=Sum.inl i) hx h he hb⟩,hb⟩
    rintro ⟨⟨h,_⟩,ha⟩; exact ⟨h,ha⟩
  ext i; simp only [Finset.mem_filter,Finset.mem_sdiff,inner,in_noise]
  constructor
  · rintro ⟨ha,hb⟩; exact ⟨⟨ha,fun he => clear_core (i:=Sum.inr i) hx h he hb⟩,hb⟩
  rintro ⟨⟨h,_⟩,ha⟩; exact ⟨h,ha⟩

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (W : Stencils S) (A : Stores S) (F : Forest S.ratio)
  (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F))

def debit (M : Window S) (s : Signed) (U : Config G f) (a : Prices G (Active A x F)) : ℝ :=
  M.work T x (pull s 0 U) (choice s k) (pull s 0 V) - extraction T x V k W A F q d Y M a s

/-- The (row) charge in a compulsory packet. `a` here GAUSSIAN active
log-link arguments, so the `dyed` residual of interest uses `a=m+gz` in
these. C in that case will be fixed through the application and the proof
does not require switching it to charge by a different one. -/
def debt (O : Stores S) (D : ℕ) (U : Config G f) (a : Prices G (Active A x F)) (s : Signed) : ℝ :=
  debit T x V k W A F q d Y (hot (turnStore s O) D (radiusB x)) s U a

def crown (O : Stores S) (D : ℕ) (s : Signed) : Window S := corona (turnStore s O) D x

def clipping (O : Stores S) (D : ℕ) (s : Signed) := emitted x (shots S x) A F (crown x O D s) s

/-- Identify all rows of the displayed debt with the ones paid by LFR's CorePacket.
Use exact annulus common a. -/
lemma debited {O A : Stores S} {D : ℕ} (hI : Isle O A l (radiusB x)) (ht : 2≤D)
    (hx : span S.patch x ≤ radiusB x/50)
    {P : Teller G} (h : P.Funds S T) {Y : LinkArray G (Frozen A x F)} (s : Signed)
    (he : Issued x V k (shots S x) A F (hot (turnStore s O) D (radiusB x)) s) (a : Prices G (Active A x F)) (U : Config G f) :
    debt T x V k (shots S x) A F q d Y O D U a s = credits U V O (crown x O D) (clipping x A F O D) T x k
      (orientedLog x V (shots S x) A F q d Y a) s := by
  unfold debt credits debit boost
  rw [← sum_work T _ _ _ _ D x ht, already, transported T x V k (shots S x) A F q d Y h s _ a he, coronate s D hx hI]
  unfold clipping crown; abel



end Harvest
end YM.AnalyticBridge.AnnulusRatioInsertions
