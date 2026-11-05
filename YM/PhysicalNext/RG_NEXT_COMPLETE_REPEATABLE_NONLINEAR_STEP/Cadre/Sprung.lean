import YM.Further.THRESHOLD_SOURCE_RESTART.ClusterLong
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt

/-! # F-averaged restoration (port of Colony, using integrated average and actual K support).
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


-- actual lower values
def spawn (_H : Cash W α μ L Q o C T R) (χ : Chi) (V : Config G c) := poolA T α χ o.K Q.table V R W o.a Q.halo
lemma resident (i : Molecule S) (h : H.spawn χ V i≠0) :
    Ac.Spark H.supportP i ∧ troupe T R Q.halo (radiusB α) i ∧ (H.unionP i).Nonempty ∧ (roster i).flags=RG.flags (Pressure.temp α) V ∩ H.unionP i := by
  have hz : ∃ r: Reserve S,H.emerging (prism T α χ o.K V (Greenbelt.allot r)) i ≠ 0 := by
    by_contra! he
    apply h; unfold spawn poolA Pond.likely; unfold emerging at he; simp only [he,sum_const_zero,mul_zero]
  obtain ⟨r,hr⟩ := hz; exact H.residency (prism T α χ o.K V (Greenbelt.allot r)) rfl i hr
def entriesPool (i : H.ThinP) := H.spawn χ V i.val
def depositsPool (i : H.ThickP) := H.spawn χ V i.val
def bankedPool (A : Finset H.ThickP) := if H.inventory A=RG.flags (Pressure.temp α) V then Gas.value
    (blocked H.largeAt) (H.depositsPool χ V) A else 0

def ignoresPool (A : Finset H.ThickP) := Gas.cut H.smallAt (H.tall A) (H.entriesPool χ V)

def inletPool (p : Finset H.ThickP × Finset H.ThinP) := H.bankedPool χ V p.1 * Gas.value (blocked H.smallAt) (H.ignoresPool χ V p.1) p.2

lemma family_pool (p : Finset H.ThickP × Finset H.ThinP) :
    H.inletPool χ V p=festival T α χ o.K Q.table V R W o.a Q.halo (H.binders p) := by
  rcases p with ⟨A,U⟩; let M:= H.binders (A,U); let t := Pressure.temp α
  let S':=H.stave A; let U':= H.sword U
  have Hh (x) (hx : x∈M) (hv : H.spawn χ V x≠0) := (H.resident χ V _ hv).1
  have HE : areas R T Q.halo (radiusB α)=H.supportP := rfl
  have Hp : (M:Set (Molecule S)).PairwiseDisjoint H.unionP → ∀ i∈M,H.spawn χ V i≠0 → Ac.Spark H.supportP i := fun _=> Hh
  have he : permitsA (S:=S) α V M ↔ H.inventory A=RG.flags t V := by
    unfold permitsA; change ((S' ∪ U').biUnion _)=_ ↔ _
    rw [union_biUnion]
    have ht : S'.biUnion (fun i=> (roster i).flags)=H.inventory A := by ext; simp [S',stave,inventory]
    have hu : U'.biUnion (fun i=> (roster i).flags)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=> by
      obtain ⟨j,hj,h⟩ := mem_biUnion.mp hi; obtain ⟨p,hp,rfl⟩ := mem_map.mp hj; exact p.2.2 ▸ (show i∈(roster p.val).flags from h) |> Finset.notMem_empty _)
    rw [ht,hu,union_empty]
  have hh : (∏ i∈ M,H.spawn χ V i)=(∏ i∈ A,H.depositsPool χ V i)*∏ i∈ U,H.entriesPool χ V i := by
    unfold M binders; rw [prod_union (H.rent_split (A,U)),sword,stave,prod_map,prod_map]; rfl
  have hm : (M:Set (Molecule S)).PairwiseDisjoint H.unionP ↔ separated (blocked H.largeAt) A ∧
      separated (blocked H.smallAt) U ∧ ∀ i∈U, Disjoint (H.tall A) (H.smallAt i) := by
    constructor
    · intro hz; constructor
      · intro i hi j hj hg; have hw := hz (mem_union_left U' (show i.val∈ S' from mem_map_of_mem _ hi))
          (mem_union_left U' (show j.val∈ S' from mem_map_of_mem _ hj)) (fun h=>hg <| Subtype.ext h)
        exact not_or_intro hg (fun h=> Finset.not_disjoint_iff.mpr h hw)
      constructor
      · intro i hi j hj hg; have hw:= hz (mem_union_right S' (show i.val∈ U' from mem_map_of_mem _ hi))
          (mem_union_right S' (show j.val∈U' from mem_map_of_mem _ hj)) (fun h=>hg <| Subtype.ext h)
        exact not_or_intro hg (fun h=> Finset.not_disjoint_iff.mpr h hw)
      intro i hi
      refine Finset.disjoint_left.mpr fun p hp ha=> ?_
      obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
      exact Finset.disjoint_left.mp (hz (mem_union_left U' (show j.val∈ S' from mem_map_of_mem _ hj))
        (mem_union_right S' (show i.val∈U' from mem_map_of_mem _ hi)) (fun h=> j.2.2.ne_empty (h.symm ▸ i.2.2))) hp ha
    rintro ⟨hw,hv,hx⟩ v hi y hj ht
    have hw' : (S':Set _).PairwiseDisjoint H.unionP := by
      rintro i hi j hj hn
      obtain ⟨i,h_i,rfl⟩ := mem_map.mp hi; obtain ⟨j,h_j,rfl⟩ := mem_map.mp hj
      exact Finset.disjoint_left.mpr fun p hp hq=> hw i h_i j h_j (fun h=>hn (h ▸ rfl)) (Or.inr ⟨p,hp,hq⟩)
    have hv' : (U':Set _).PairwiseDisjoint H.unionP := by
      rintro i hi j hj hn; obtain ⟨i,h_i,rfl⟩ := mem_map.mp hi; obtain ⟨j,h_j,rfl⟩ := mem_map.mp hj
      exact Finset.disjoint_left.mpr fun p hp hq=> hv i h_i j h_j (fun h=>hn (h ▸ rfl)) (Or.inr ⟨p,hp,hq⟩)
    have he i j (hi : i∈S') (hj : j∈U') : Disjoint (H.unionP i) (H.unionP j) := by
      obtain ⟨i,h_i,rfl⟩ := mem_map.mp hi; obtain ⟨j,h_j,rfl⟩ := mem_map.mp hj
      exact (hx j h_j).mono_left (show H.largeAt i⊆H.tall A from subset_biUnion_of_mem _ h_i)
    rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
    · exact hw' hi hj ht
    · exact he v y hi hj
    · exact (he y v hj hi).symm
    · exact hv' hi hj ht
  unfold inletPool bankedPool festival
  let F' := ∏ i∈ M,H.spawn χ V i; let P := (M:Set (Molecule S)).PairwiseDisjoint H.unionP
  have hz : joints T R Q.halo (radiusB α) M ↔ (∀ i∈M,Ac.Spark H.supportP i)∧P := by unfold joints ground; rw [HE]; exact Iff.rfl
  change (if H.inventory A=RG.flags t V then _ else _) * _ = if _ then F' else 0
  by_cases hs : permitsA (S:=S) α V M
  swap; · rw [if_neg (he.not.1 hs), if_neg (fun h=>hs h.2),zero_mul]
  rw [if_pos (he.1 hs)]; unfold Gas.value; split_ifs with hA hU HK
  next =>
    have hg := (hm.mp (hz.mp HK.1).2).2.2
    unfold F'; rw [hh]; apply congr_arg _; refine prod_congr rfl fun i hi=> ?_; exact if_pos (hg i hi)
  next =>
    by_cases hx : ∀ i∈U,Disjoint (H.tall A) (H.smallAt i)
    · rw [show (∏ i∈U,H.ignoresPool χ V A i)=(∏ i∈U,H.entriesPool χ V i) from ?_]
      · rw [← hh]; by_contra h
        exact HK ⟨hz.mpr ⟨fun i hi=> Hp (hm.2 ⟨hA,hU,hx⟩) i hi (fun he'=>h (prod_eq_zero hi he')),
          hm.2 ⟨hA,hU,hx⟩⟩,hs⟩
      exact prod_congr rfl fun i hi=> (if_pos (hx i hi))
    push Not at hx
    obtain ⟨i,hi,hp⟩ := hx; rw [prod_eq_zero hi (show H.ignoresPool χ V A i=0 from if_neg hp),mul_zero]
  next Hh => exact (hU (hm.mp (hz.mp Hh.1).2).2.1).elim
  next => rw [mul_zero]
  next _ Hh => exact (hA (hm.mp (hz.mp Hh.1).2).1).elim
  next => rw [zero_mul]
  next _ Hh => exact (hA (hm.mp (hz.mp Hh.1).2).1).elim
  next => rw [zero_mul]
end YM.ConnectedActivityE6.Cash
