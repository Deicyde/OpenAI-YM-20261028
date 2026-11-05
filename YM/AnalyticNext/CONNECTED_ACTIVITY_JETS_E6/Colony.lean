import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Expenses
import YM.Push.ABSOLUTE_SUMS.Absence


/-!
# Separating U and D labels on the SAME alphabet

Use incidence as cost. HasSum conditional in V. Payments rely on H invariants,
not predicate guesses. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)

abbrev ThinP := { p : Molecule S // (H.unionP p).Nonempty ∧ (roster p).flags=∅ }
abbrev ThickP := { p : Molecule S // (H.unionP p).Nonempty ∧ (roster p).flags.Nonempty }

def sword (U : Finset H.ThinP) := U.map (Embedding.subtype _)
def stave (A : Finset H.ThickP) := A.map (Embedding.subtype _)
def binders (U : Finset H.ThickP × Finset H.ThinP) := H.stave U.1 ∪ H.sword U.2

def largeAt (i : H.ThickP) := H.unionP i.val
def smallAt (i : H.ThinP) := H.unionP i.val

def entries (i : H.ThinP) := H.emerging X i.val
def deposits (i : H.ThickP) := H.emerging X i.val

def tall (u : Finset H.ThickP) := u.biUnion H.largeAt

def inventory (A : Finset H.ThickP) := A.biUnion fun i=> (roster i.val).flags

def banked (A : Finset H.ThickP) := if H.inventory A=RG.flags (Pressure.temp X.x) X.V then Gas.value
    (blocked H.largeAt) (H.deposits X) A else 0

def ignores (A : Finset H.ThickP) := Gas.cut H.smallAt (H.tall A) (H.entries X)

def inlet (p : Finset H.ThickP × Finset H.ThinP) := H.banked X p.1 * Gas.value (blocked H.smallAt) (H.ignores X p.1) p.2

lemma rent_split (p : Finset H.ThickP × Finset H.ThinP) : Disjoint (H.stave p.1) (H.sword p.2) := by
  refine Finset.disjoint_left.mpr fun z hz hu=> ?_
  obtain ⟨i,h_i,rfl⟩ := mem_map.mp hz
  obtain ⟨j,hj,he⟩ := mem_map.mp hu; have ht := j.2.2; change j.val=i.val at he
  exact i.2.2.ne_empty (he ▸ ht)
lemma bindInj : Injective H.binders := by
  have hh p i : i∈Prod.snd p ↔ Subtype.val i ∈ H.binders p := by
    rw [binders,mem_union]; refine ⟨fun h=> Or.inr (Finset.mem_map_of_mem _ h), ?_⟩
    rintro (hp|hp)
    · obtain ⟨j,hj,hq⟩ := mem_map.mp hp; change j.val=i.val at hq
      exact (j.2.2.ne_empty (hq.symm ▸ (i:H.ThinP).2.2)).elim
    obtain ⟨j,hj,hq⟩ := mem_map.mp hp; exact Subtype.ext (show j.val=i.val from hq) ▸ hj
  have hg p i : i∈Prod.fst p ↔ Subtype.val i∈ H.binders p := by
    rw [binders,mem_union]; refine ⟨fun h=> Or.inl (Finset.mem_map_of_mem _ h),?_⟩
    rintro (hp|hp)
    · obtain ⟨j,hj,hq⟩ := mem_map.mp hp; exact Subtype.ext (show j.val=i.val from hq) ▸ hj
    obtain ⟨j,hj,hq⟩ := mem_map.mp hp; change j.val=i.val at hq
    exact False.elim ((i:H.ThickP).2.2.ne_empty (hq ▸ j.2.2))
  intro p q he; exact Prod.ext (Finset.ext fun i=> by rw [hg,hg,he]) (Finset.ext fun i=> by rw [hh,hh,he])

include hk in
lemma family_neat (p : Finset H.ThickP × Finset H.ThinP) :
    H.inlet X p=ejections R X W o.a Q.halo Q.table (H.binders p) := by
  rcases p with ⟨A,U⟩; let M:= H.binders (A,U); let t := Pressure.temp X.x
  let S':=H.stave A; let U':= H.sword U
  have Hh (x) (hx : x∈M) (hv : H.emerging X x≠0) := (H.residency X hk _ hv).1
  have HE : areas R T Q.halo X.B=H.supportP := by unfold Coat.B; rw [hk]; rfl
  have Hp : (M:Set (Molecule S)).PairwiseDisjoint H.unionP → ∀ i∈M,H.emerging X i≠0 → Ac.Spark H.supportP i := fun _=> Hh
  have he : Matter.covers X M ↔ H.inventory A=RG.flags t X.V := by
    unfold Matter.covers; change ((S' ∪ U').biUnion _)=_ ↔ _
    rw [union_biUnion]
    have ht : S'.biUnion (fun i=> (roster i).flags)=H.inventory A := by ext; simp [S',stave,inventory]
    have hu : U'.biUnion (fun i=> (roster i).flags)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=> by
      obtain ⟨j,hj,h⟩ := mem_biUnion.mp hi; obtain ⟨p,hp,rfl⟩ := mem_map.mp hj; exact p.2.2 ▸ (show i∈(roster p.val).flags from h) |> Finset.notMem_empty _)
    rw [ht,hu,union_empty]
  have hh : (∏ i∈ M,H.emerging X i)=(∏ i∈ A,H.deposits X i)*∏ i∈ U,H.entries X i := by
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
  unfold inlet banked ejections
  let F' := ∏ i∈ M,H.emerging X i; let P := (M:Set (Molecule S)).PairwiseDisjoint H.unionP
  have hz : joints T R Q.halo X.B M ↔ (∀ i∈M,Ac.Spark H.supportP i)∧P := by unfold joints ground; rw [HE]; exact Iff.rfl
  change (if H.inventory A=RG.flags t X.V then _ else _) * _ = if _ then F' else 0
  by_cases hs : Matter.covers X M
  swap; · rw [if_neg (he.not.1 hs), if_neg (fun h=>hs h.2),zero_mul]
  rw [if_pos (he.1 hs)]; unfold Gas.value; split_ifs with hA hU HK
  next =>
    have hg := (hm.mp (hz.mp HK.1).2).2.2
    unfold F'; rw [hh]; apply congr_arg _; refine prod_congr rfl fun i hi=> ?_; exact if_pos (hg i hi)
  next =>
    by_cases hx : ∀ i∈U,Disjoint (H.tall A) (H.smallAt i)
    · rw [show (∏ i∈U,H.ignores X A i)=(∏ i∈U,H.entries X i) from ?_]
      · rw [← hh]; by_contra h
        exact HK ⟨hz.mpr ⟨fun i hi=> Hp (hm.2 ⟨hA,hU,hx⟩) i hi (fun he'=>h (prod_eq_zero hi he')),
          hm.2 ⟨hA,hU,hx⟩⟩,hs⟩
      exact prod_congr rfl fun i hi=> (if_pos (hx i hi))
    push Not at hx
    obtain ⟨i,hi,hp⟩ := hx; rw [prod_eq_zero hi (show H.ignores X A i=0 from if_neg hp),mul_zero]
  next Hh => exact (hU (hm.mp (hz.mp Hh.1).2).2.1).elim
  next => rw [mul_zero]
  next _ Hh => exact (hA (hm.mp (hz.mp Hh.1).2).1).elim
  next => rw [zero_mul]
  next _ Hh => exact (hA (hm.mp (hz.mp Hh.1).2).1).elim
  next => rw [zero_mul]
end YM.ConnectedActivityE6.Cash
