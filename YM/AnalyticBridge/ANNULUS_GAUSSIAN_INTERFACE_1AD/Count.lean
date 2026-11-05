import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Guard
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Read


/-!
# Halo anchor counts

Diameter measured in output units. No covariance or activity estimates
hidden here: just counting distinct locations of applied losses. These
bounds *do not* enumerate supports of views or connected terms, only
prices actually applied at one link/anchor in the compulsory product.
 fixed-L. We may also renormalize likelihoods per tag inside
such a number of addresses (for use with uniform probability on tags).
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- nat counts first, b x uses 1+radiusB.
def plotBill (O : Stores S) (D B : ℕ) := (4*(2*D+1)^4)*(B+1)^4*O.shares
lemma dome_count (O : Stores S) (D B : ℕ) : (O.dome (D*B)).card ≤ plotBill O D B := by
  apply (Corona.halo_size _ _).trans
  apply (Nat.mul_le_mul_right _ (Work.E01.place_card O)).trans
  calc
    _ ≤ 4*O.shares*(((2*D+1)*(B+1))^4) := by
      gcongr
      ring_nf; omega
    _ = _ := by unfold plotBill; ring

/-- Post-L multiplicity (no uniform L claim). -/
lemma fine_count {α : Type} [Fintype α] (s : Finset (Site f × α)) (N : Support c)
    (h : ∀ i∈s,S.ratio.parent (i:Site f × α).1∈N) : s.card ≤ Fintype.card α*S.patch.L.val^4*N.card := by
  let e : Site f × α ≃ (Site c × Site S.ratio.count) × α := Equiv.prodCongr S.ratio.splitSites (.refl _)
  have he : s.map e.toEmbedding ⊆ (N ×ˢ (univ:Finset (Site S.ratio.count))) ×ˢ (univ:Finset α) := by
    intro i hi; obtain ⟨p,hp,rfl⟩ := mem_map.mp hi
    exact mem_product.mpr ⟨mem_product.mpr ⟨h _ hp,mem_univ _⟩,mem_univ _⟩
  have hh := card_le_card he
  simp only [card_map,card_product,card_univ,site_card] at hh
  apply hh.trans_eq; change N.card*S.patch.L.val^4*Fintype.card α=_; ring

lemma coarse_count {α : Type} [Fintype α] (s : Finset (Site c × α)) (N : Support c)
    (h : ∀ i∈s,(i:Site c × α).1∈N) : s.card ≤ N.card*Fintype.card α :=
  calc
    _ ≤ (N ×ˢ (univ:Finset α)).card := card_le_card (fun i hi => mem_product.mpr ⟨h _ hi,mem_univ _⟩)
    _ = _ := by simp

lemma projection_visit (S : StepData c f) (x y : Site f) (w : Walk) (h : y∈(visits x w).toFinset) :
    separation (S.ratio.parent x) (S.ratio.parent y)≤w.length := by
  induction w generalizing x with
  | nil => have hg : y=x := by simpa only [visits,List.mem_toFinset,List.mem_singleton] using h
           simp [hg]
  | cons d w ih =>
    simp only [visits,List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl|hx
    · simp
    have hi := ih (x+d.vec) (List.mem_toFinset.mpr hx)
    have he : separation (S.ratio.parent x) (S.ratio.parent (x+d.vec)) ≤ 1 := Work.E03.sep_walk S.ratio.parent (Work.E03.parent_step S) _ [d]
    exact (separation_triangle ..).trans ((Nat.add_le_add he hi).trans (by simp; omega))

lemma next_place {O : Stores S} {N M} {p i : Site c} (h : separation i p≤N) (he : i∈O.dome M) :
    p∈O.dome (N+M) := by
  obtain ⟨q,hq,hm⟩ := halo_spec.mp he
  exact halo_spec.mpr ⟨q,hq,(separation_triangle ..).trans ((Nat.add_le_add hm h).trans (by omega))⟩
lemma one_step (i : Site n) (a : Axis) : separation i (i+step a) ≤ 1 := by
  exact Work.E01.sep_step_le i a

lemma noise_near (O : Stores S) (R : ℕ) (p : Bond c) (h : p∈nearNoise (O.dome R)) :
    p.1∈O.dome (1+R) := by
  have he:= (mem_filter.mp h).2
  simp only [Finset.disjoint_left] at he; push Not at he
  obtain ⟨y,hy,hh⟩:=he
  simp only [pinPos,mem_insert,mem_singleton] at hy
  rcases hy with hd|hd
  · subst y; exact farther (by omega) hh
  subst y
  exact next_place ((separation_comm ..).trans_le (one_step ..)) hh

lemma face_near (O : Stores S) (R : ℕ) (p : Cell f) (h : p∈nearFace S (O.dome R)) :
    S.ratio.parent p.1∈ O.dome (4+R) := by
  have he := (mem_filter.mp h).2
  simp only [Finset.disjoint_left] at he; push Not at he
  obtain ⟨y,hy,hh⟩ := he
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
  refine next_place ((separation_comm ..).trans_le ?_) hh
  exact projection_visit S _ _ (Lattice.square p.2.val.1 p.2.val.2) hz

def everyLink (S : StepData c f) (O : Stores S) (R : ℕ) : Finset (Bond f) := univ.filter (witnesses O R)

lemma link_near (O : Stores S) (R : ℕ) (p : Bond f) (h : p∈everyLink S O R) :
    S.ratio.parent p.1∈ O.dome (1+R) := by
  obtain h|h := (show witnesses O R p from (mem_filter.mp h).2)
  · exact farther (by omega) h
  exact next_place ((separation_comm ..).trans_le (Work.E03.parent_step S ..)) h

lemma counts_torus (O : Stores S) (D B : ℕ) (he : 1≤B) :
    let C := plotBill O (D+1) B; let L:= S.patch.L.val
    (nearNoise (O.dome (D*B))).card ≤ C*Fintype.card Axis ∧
    (everyLink S O (D*B)).card ≤ Fintype.card Axis * L^4 * C ∧
    (nearFace S (O.dome (D*B))).card ≤ Fintype.card PlaqAxes*L^4*(plotBill O (D+4) B) := by
  intro C L
  have h (a) {i : Site c} (h : i∈O.dome (a+D*B)) : i∈O.dome ((D+a)*B) := by
    apply farther _ h; rw [Nat.add_mul]; have := Nat.mul_le_mul_left a he; omega
  exact ⟨(coarse_count _ _ (fun i hi => h 1 (noise_near O _ i hi))).trans (Nat.mul_le_mul_right _ (dome_count ..)),
    (fine_count (S:=S) _ _ (fun i hi => h 1 (link_near O _ i hi))).trans (Nat.mul_le_mul_left _ (dome_count ..)),
    (fine_count (S:=S) _ _ (fun i hi => h 4 (face_near O _ i hi))).trans (Nat.mul_le_mul_left _ (dome_count ..))⟩

def driftwood (A O : Stores S) (x : ℝ) (F : Forest S.ratio) : Finset (Frozen A x F) := univ.filter fun i =>
  chill O x F i.val



lemma frozen_count (A O : Stores S) (x : ℝ) (F : Forest S.ratio) (he : 1≤radiusB x) :
    let C := plotBill O 11 (radiusB x); let L:= S.patch.L.val
    (driftwood A O x F).card ≤ Fintype.card Axis*L^4*C := by
  intro C L; apply le_trans (b:=(everyLink S O (10*radiusB x)).card) _ (counts_torus O 10 _ he).2.1
  refine card_le_card_of_injOn (fun i => i.val.val) ?_ (fun _ _ _ _ h => Subtype.ext (Subtype.ext h))
  intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩

end YM.AnalyticBridge.Annulus1AD
