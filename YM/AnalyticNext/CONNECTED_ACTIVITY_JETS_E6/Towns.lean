import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch
import YM.Push.ABSOLUTE_SUMS.Copies

/-! # Components of restored occurrences, counts shared -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Letter
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel  Footprint Raw ProbabilityTheory Poll  
open  Ursell Trees Multiple 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ : Type} {a : Side}

def liftRep (p : Reps ι) (i : Finset ι) : Reps ι := ⟨i,fun j=> if h : j.val∈ p.fst then p.2 ⟨j.val,h⟩ else 0⟩

def openRep (V : Finset (Reps ι)) : Reps ι :=
    ⟨V.biUnion Sigma.fst, fun i=> ∑ y∈ V, (liftRep y (V.biUnion Sigma.fst)).2 (show ↥(liftRep y _).1 from i)⟩

lemma lifting (V : Finset (Reps ι)) (h : (V:Set (Reps ι)).PairwiseDisjoint Sigma.fst) (p : Reps ι) (hp : p∈V) (i : ι) (hi : i∈p.1) :
    (openRep V).2 ⟨i, mem_biUnion.mpr ⟨p,hp,hi⟩⟩=p.2 ⟨i,hi⟩ := by
  let b:= openRep V
  unfold openRep; dsimp only [liftRep]; rw [Finset.sum_eq_single p]
  · simp [hi]
  · intro q hq he; exact dif_neg (show i ∉ q.1 from fun h' => Finset.disjoint_left.mp (h hq hp he) h' hi)
  simp [hp]

def shard (X : ι → Support a) (p : Reps ι) := (Ac.Parts X p.1).image (liftRep p)

structure Valid (X : ι → Support a) (V : Finset (Reps ι)) : Prop where
  addresses : (V:Set (Reps ι)).PairwiseDisjoint Sigma.fst
  classified p : p∈V → Ac.Spark X p.1
  disjoint : (V:Set (Reps ι)).PairwiseDisjoint (fun y=> y.fst.biUnion X)


lemma sharding (X : ι → Support a) (p : Reps ι) : Valid X (shard X p) := by
  constructor
  · intro i hi j hj hp; obtain ⟨i₀,h_i',h_i⟩ := mem_image.mp hi; obtain ⟨j₀,h_j',h_j⟩ := mem_image.mp hj; subst i j
    exact Ac.different X p.1 h_i' h_j' (fun h=>hp (congr_arg _ h))
  · rintro i hi; obtain ⟨v,hv,rfl⟩ := mem_image.mp hi; exact (Ac.lives X p.1 hv).2
  intro i hi j hj hp; obtain ⟨v,hv,rfl⟩:= mem_image.mp hi; obtain ⟨w,hw,rfl⟩:=mem_image.mp hj
  exact Ac.separate X p.1 hv hw (fun h=>hp (congr_arg _ h))

lemma inflates (X : ι → Support a) (p : Reps ι) : openRep (shard X p)=p := by
  let A:= openRep (shard X p)
  have hp : A.fst=p.fst := by
    calc
      _ = (Ac.Parts X p.fst).biUnion id := by ext; simp [A,openRep,shard,liftRep,mem_biUnion]
      _ = _ := Ac.reconstruct ..
  refine Sigma.ext hp ?_
  have hv i (hi : i∈p.1) : A.snd ⟨i, hp.symm ▸ hi⟩=p.2 ⟨i,hi⟩ := by
    have hx := (show i∈ (Ac.Parts X p.1).biUnion id from by rw [Ac.reconstruct]; exact hi)
    obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hx
    have ht := Letter.lifting _ (sharding X p).addresses (liftRep p b) (mem_image_of_mem _ hb) i hx
    change A.snd _=_ at ht
    exact ht.trans (dif_pos hi)
  change HEq A.snd p.snd
  generalize hg : A=q at *; obtain ⟨s,k⟩:=p; obtain ⟨q,g⟩:=q
  change q=s at hp; subst q
  exact heq_of_eq (funext fun i=> hv _ i.2)

lemma includes (X : ι → Support a) (V : Finset (Reps ι)) (h : Valid X V) : shard X (openRep V)=V := by
  let p:= openRep V
  have hp : Ac.Parts X p.1=V.image Sigma.fst := by
    let U := V.image Sigma.fst
    have hu : U.biUnion id=V.biUnion Sigma.fst := by ext; simp [U]
    rw [show p.1=U.biUnion id from hu.symm]
    apply Ac.separates
    · intro y hy; obtain ⟨t,ht,rfl⟩:=mem_image.mp hy; exact h.classified t ht
    intro i hi j hj hp; obtain ⟨v,hv,rfl⟩:= mem_image.mp hi; obtain ⟨w,hw,rfl⟩:=mem_image.mp hj
    exact h.disjoint hv hw (fun he=>hp (congr_arg Sigma.fst he))
  have he i (hi : i∈V) : liftRep p i.1=i := by
    refine Sigma.ext rfl (heq_of_eq ?_); funext j
    exact (dif_pos (show j.val∈p.1 from mem_biUnion.mpr ⟨i,hi,j.2⟩)).trans (lifting V h.addresses i hi j.val j.2)
  unfold shard; rw [hp,image_image]; ext i; constructor
  · intro hi; obtain ⟨j,hj,hq⟩:=mem_image.mp hi
    exact ((he j hj).symm.trans hq) ▸ hj
  intro hi; exact mem_image.mpr ⟨i,hi,he i hi⟩

lemma prices_union {V : Finset (Reps ι)} (h : (V:Set (Reps ι)).PairwiseDisjoint Sigma.fst) (w : ι→ℝ) :
    manyW w (openRep V)=∏ i∈V, manyW w i := by
  let p:= openRep V
  let f (j : ι) := if h : j∈p.1 then w j^(p.snd ⟨j,h⟩+1)/(p.snd ⟨j,h⟩+1).factorial else 0
  have he (q : Reps ι) (hg : q.fst⊆ p.fst) (hv : ∀ i : ↥q.fst,q.snd i=p.snd ⟨i.1,hg i.2⟩) :
      manyW w q= ∏ i∈q.1,f i := by
    rw [← Finset.prod_coe_sort]; unfold manyW; apply prod_congr rfl; intro i _
    unfold f; rw [hv, dif_pos (hg i.2)]
  rw [he p (Finset.Subset.refl _) (fun i=>rfl),show p.1=V.biUnion _ from rfl, prod_biUnion h]; apply prod_congr rfl
  intro i hi; exact (he i (subset_biUnion_of_mem Sigma.fst hi) (fun j=> (lifting V h i hi j.val j.2).symm)).symm
lemma stages (i : ι) (U : Finset (Reps ι)) : i∈(openRep U).fst ↔ ∃j∈U,i∈ j.fst := mem_biUnion
end YM.ConnectedActivityE6.Letter
