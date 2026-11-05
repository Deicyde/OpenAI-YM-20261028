import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Bulkhead
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Catkin
/-! # F-averaged restoration (port of Melt/Bulkhead, using integrated average and actual K support).
 Existing terms are single-F; they are not multiplicative across average! Use this version.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (χ : Chi) (V : Config G c)
variable (p : Renewed j a δ e H)

def statesPool (r : H.Chainbook) := H.inventory r.1.toLeft= RG.flags (Pressure.temp α) V∩H.library r

def smilesPool (r : H.Chainbook) := if H.Fresh r ∧ Ac.Spark H.bookFoot r.1 ∧ H.statesPool V r then
    manyW (H.colognePool χ V) r else 0

def eruptedPool (U : Finset H.Chainbook) := U.biUnion (fun r=> H.inventory r.1.toLeft)=RG.flags (Pressure.temp α) V

def canopyPool (U : Finset H.Chainbook) := if Letter.Valid H.bookFoot U ∧ H.eruptedPool V U then ∏ r∈U,H.smilesPool χ V r else 0

private lemma ties (U : Finset H.Chainbook) (h : Letter.Valid H.bookFoot U) : H.Fresh (openRep U) ↔ ∀ r∈U,H.Fresh r := by
  let b:= openRep U
  have hu (i) (hi : i∈U) : i.fst⊆ b.fst := fun j hj=> (Letter.stages _ U).mpr ⟨i,hi,hj⟩
  have hx (i j) (hi : i∈U) (hj : j∈U) (p) (hh : p∈H.library i) (hi' : p∈H.library j) : i=j := by
    by_contra H; exact Finset.disjoint_left.mp (h.disjoint hi hj H) hh hi'
  constructor
  · intro he i hi
    refine ⟨fun a ha=> (Letter.lifting U h.addresses i hi _ ha).symm.trans (he.1 a (hu i hi ha)), ?_, ?_⟩
    · exact fun j hj k hk=> he.2.1 j ((H.orbiting U j).2 ⟨i,hi,hj⟩) k ((H.orbiting U k).2 ⟨i,hi,hk⟩)
    intro j hj
    obtain ⟨v,hv,hj'⟩ := not_disjoint_iff.mp (he.2.2 j (mem_toRight.mpr <| hu i hi (mem_toRight.mp hj)))
    obtain ⟨u,hU,hv⟩ := mem_biUnion.mp hv; obtain ⟨m,hm,hv'⟩ := (H.orbiting U u).1 hU
    have ht : v∈H.library i := mem_biUnion.mpr ⟨Sum.inr j,mem_toRight.mp hj,hj'⟩
    have hb : i=m := hx i m hi hm v ht (H.arching hv' hv)
    exact not_disjoint_iff.mpr ⟨v,mem_biUnion.mpr ⟨u,hb.symm ▸ hv',hv⟩,hj'⟩
  intro hp; refine ⟨?_,?_,?_⟩
  · intro i hi; obtain ⟨z,hz,hZ⟩ := (Letter.stages _ U).mp hi
    exact (Letter.lifting U h.addresses z hz _ hZ).trans ((hp _ hz).1 i hZ)
  · intro i hi j hj hk
    obtain ⟨u,hu,hU⟩ := (H.orbiting _ i).1 hi
    obtain ⟨v,hv,hV⟩ := (H.orbiting _ j).1 hj
    by_cases hf : u=v
    · exact (hp u hu).2.1 i hU j (hf.symm ▸ hV) hk
    apply not_or.mpr; refine ⟨hk,?_⟩
    rintro ⟨s,hs,ht⟩; exact hf (hx u v hu hv s (H.arching hU hs) (H.arching hV ht))
  intro i hi; obtain ⟨u,hu,hx⟩ := (Letter.stages _ U).mp (mem_toRight.mp hi)
  obtain ⟨j,hj,hi'⟩ := Finset.not_disjoint_iff.mp ((hp u hu).2.2 i (mem_toRight.mpr hx))
  obtain ⟨x,hj,hz⟩ := mem_biUnion.mp hj
  exact not_disjoint_iff.mpr ⟨j,mem_biUnion.mpr ⟨x,(H.orbiting ..).2 ⟨u,hu,hj⟩,hz⟩, hi'⟩

lemma book_associatedPool (U : Finset H.Chainbook) (h : Letter.Valid H.bookFoot U) :
    H.canopyPool χ V U=H.truthfulPool χ V (openRep U) := by
  unfold canopyPool truthfulPool; simp_rw [← show H.eruptedPool V U ↔ H.inventory (openRep U).1.toLeft= RG.flags (Pressure.temp α) V from H.allotment (prism T α χ o.K V (Classical.choice (Tree.select S.ratio S.patch.odd_side))) U, H.ties U h]
  by_cases he : H.eruptedPool V U
  · rw [if_pos ⟨h,he⟩]; split
    next hx => rw [prices_union h.addresses]; apply prod_congr rfl; intro i hi
               exact if_pos ⟨hx.1 i hi,h.classified i hi,H.colonies (prism T α χ o.K V (Classical.choice (Tree.select S.ratio S.patch.odd_side))) U h he i hi⟩
    next hx =>
      by_contra hp; exact hx ⟨fun i hi=> by
        by_contra hg; exact hp <| prod_eq_zero hi (show H.smilesPool χ V i=0 from if_neg fun h=> hg h.1), he⟩
  rw [if_neg (fun h=>he h.2),if_neg (fun h=>he h.2)]

variable (O : Tree.Forest S.ratio)
include p
lemma convoyPool : HasSum
    (fun U => overhead (prism T α χ o.K V O) R Q.table * H.homesteadPool χ V * H.canopyPool χ V U)
    (S.push R.beta R.eval V) := by
  let f U:= overhead (prism T α χ o.K V O) R Q.table * H.homesteadPool χ V * H.canopyPool χ V U
  let b (c) := shard H.bookFoot c
  have hx : Injective b := LeftInverse.injective (show LeftInverse openRep b from fun r=> inflates H.bookFoot r)
  apply (hx.hasSum_iff (f:=f) ?_).1; swap
  · intro x ht; unfold f canopyPool; rw [if_neg (fun h=>ht ⟨openRep x,Letter.includes H.bookFoot x h.1⟩),mul_zero]
  have hv c : f (b c)=overhead (prism T α χ o.K V O) R Q.table * H.homesteadPool χ V * H.truthfulPool χ V c := by
    unfold f b; rw [H.book_associatedPool χ V (Letter.shard H.bookFoot c) (sharding H.bookFoot c), inflates]
  simp_rw [Function.comp_def,hv]; exact H.bouquetPool χ V p O
omit p
lemma excel_boundsPool (j : ℕ) (p : H.Chainbook) : ‖H.smilesPool χ V p‖ ≤ H.excels j p := by
  unfold smilesPool; split
  next h=> unfold excels; rw [if_pos ⟨h.1,h.2.1⟩, abs_bill]; apply Finset.prod_le_prod
           · exact fun _ _=> div_nonneg (pow_nonneg (norm_nonneg _) _) (by positivity)
           intro i hi; apply div_le_div_of_nonneg_right _ (by positivity); refine pow_le_pow_left₀ (norm_nonneg _) ((?_ : ∀ q:H.Chapter, ‖H.colognePool χ V q‖ ≤ grade H.seam (H.thinPay j) (H.broadPay j) q) i.val) _
           intro f; rcases f with f|f
           · exact (H.renew χ V j).2 f
           change ‖-(Gas.term H.seam (H.entriesPool χ V) f)‖ ≤ clusters H.seam (H.thinPay j) f.2
           rw [norm_neg,term_nonneg]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
             (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun _ _=> (H.renew χ V j).1 _)) (abs_nonneg _)) (by positivity)
  rw [norm_zero]; exact H.excels_nn ..


end YM.ConnectedActivityE6.Cash
