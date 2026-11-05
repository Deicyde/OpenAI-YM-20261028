import YM.Further.THRESHOLD_SOURCE_RESTART.ClusterLong
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt
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



variable (u : Molecule S→ℝ)
def TaggedW := ∀ i,u i≠0→ Ac.Spark H.supportP i ∧ (H.unionP i).Nonempty
def festo (V:Config G c) (u : Molecule S→ℝ) (s:Finset (Molecule S)):= let _:=H; if joints T R Q.halo (radiusB α) s ∧ permitsA α V s then ∏ i∈s,u i else 0
-- needs H mention for fields

def entriesMill (i : H.ThinP) := u i.val
def depositsMill (i : H.ThickP) := u i.val
def bankedMill (A : Finset H.ThickP) := if H.inventory A=RG.flags (Pressure.temp α) V then Gas.value
    (blocked H.largeAt) (H.depositsMill u) A else 0

def ignoresMill (A : Finset H.ThickP) := Gas.cut H.smallAt (H.tall A) (H.entriesMill u)

def inletMill (p : Finset H.ThickP × Finset H.ThinP) := H.bankedMill V u p.1 * Gas.value (blocked H.smallAt) (H.ignoresMill u p.1) p.2

lemma family_mill (hu : TaggedW H u) (p : Finset H.ThickP × Finset H.ThinP) :
    H.inletMill V u p=H.festo V u (H.binders p) := by
  rcases p with ⟨A,U⟩; let M:= H.binders (A,U); let t := Pressure.temp α
  let S':=H.stave A; let U':= H.sword U
  have Hh (x) (hx : x∈M) (hv : u x≠0) := (hu _ hv).1
  have HE : areas R T Q.halo (radiusB α)=H.supportP := rfl
  have Hp : (M:Set (Molecule S)).PairwiseDisjoint H.unionP → ∀ i∈M,u i≠0 → Ac.Spark H.supportP i := fun _=> Hh
  have he : permitsA (S:=S) α V M ↔ H.inventory A=RG.flags t V := by
    unfold permitsA; change ((S' ∪ U').biUnion _)=_ ↔ _
    rw [union_biUnion]
    have ht : S'.biUnion (fun i=> (roster i).flags)=H.inventory A := by ext; simp [S',stave,inventory]
    have hu : U'.biUnion (fun i=> (roster i).flags)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=> by
      obtain ⟨j,hj,h⟩ := mem_biUnion.mp hi; obtain ⟨p,hp,rfl⟩ := mem_map.mp hj; exact p.2.2 ▸ (show i∈(roster p.val).flags from h) |> Finset.notMem_empty _)
    rw [ht,hu,union_empty]
  have hh : (∏ i∈ M,u i)=(∏ i∈ A,H.depositsMill u i)*∏ i∈ U,H.entriesMill u i := by
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
  unfold inletMill bankedMill festo
  let F' := ∏ i∈ M,u i; let P := (M:Set (Molecule S)).PairwiseDisjoint H.unionP
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
    · rw [show (∏ i∈U,H.ignoresMill u A i)=(∏ i∈U,H.entriesMill u i) from ?_]
      · rw [← hh]; by_contra h
        exact HK ⟨hz.mpr ⟨fun i hi=> Hp (hm.2 ⟨hA,hU,hx⟩) i hi (fun he'=>h (prod_eq_zero hi he')),
          hm.2 ⟨hA,hU,hx⟩⟩,hs⟩
      exact prod_congr rfl fun i hi=> (if_pos (hx i hi))
    push Not at hx
    obtain ⟨i,hi,hp⟩ := hx; rw [prod_eq_zero hi (show H.ignoresMill u A i=0 from if_neg hp),mul_zero]
  next Hh => exact (hU (hm.mp (hz.mp Hh.1).2).2.1).elim
  next => rw [mul_zero]
  next _ Hh => exact (hA (hm.mp (hz.mp Hh.1).2).1).elim
  next => rw [zero_mul]
  next _ Hh => exact (hA (hm.mp (hz.mp Hh.1).2).1).elim
  next => rw [zero_mul]

end YM.ConnectedActivityE6.Cash
