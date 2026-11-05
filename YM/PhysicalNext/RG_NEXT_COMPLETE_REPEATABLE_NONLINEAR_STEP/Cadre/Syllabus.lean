import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Juveniles

/-! # K gas reindex for actual output. Same representation not just
cluster sum of unfrozen log. Alpha and Pricing irrelevant to valid if labels
retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Refrain
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open Extra.Iteration Greenbelt Match
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q α a δ e C : ℝ} {b j n : ℕ} {F : Tree.Forest S.ratio}
variable (p : BudgetPoint) (H : Cash W α μ L Q o C T I) {J : Cash W α μ L Q o C T R}
    (X : Match.Alliance H J 1 0) (χ : Chi)

-- from NEW Chainbook positive to uniform annual indices.
def visa : Leaf J ↪ ℕ := Embedding.trans ((gate H X).symm.toEmbedding.trans Embedding.inl) (badge H).symm.toEmbedding
lemma visited (i : Leaf J) : badge H (visa H X i)=.inl ((gate H X).symm i) := (badge H).apply_symm_apply _
lemma admitted (i : Leaf J) :
    (reserve H (badge H (visa H X i))).support=J.library i.val ∧
    (reserve H (badge H (visa H X i))).inventory=J.inventory i.val.1.toLeft := by
  rw [visited]
  have hp := crew H X ((gate H X).symm i)
  rw [Equiv.apply_symm_apply] at hp; exact ⟨hp.1.symm,hp.2.symm⟩
lemma crowned (V : Config G c) (i : Leaf J) : fuse H X χ (badge H (visa H X i)) V=J.smilesPool χ V i.val := by rw [visited,flowering,Equiv.apply_symm_apply]
lemma resides (V : Config G c) (n : ℕ) (hn : fuse H X χ (badge H n) V ≠ 0) : ∃ i, visa H X i=n := by
  rcases he : badge H n with i|i
  · refine ⟨(gate H X) i, (badge H).injective ?_⟩
    rw [visited,he,Equiv.symm_apply_apply]
  rw [he,barren] at hn; exact False.elim (hn rfl)

lemma chapter_ne (i : H.Chapter) : (H.bookFoot i).Nonempty := by
  rcases i with i|i
  · exact i.2.1
  exact Finset.Nonempty.mono (subset_biUnion_of_mem (H.smallAt ∘ i.2) (mem_univ none)) (i.2 none).2.1
lemma parted {U : Finset H.Chainbook} (h : (U:Set H.Chainbook).PairwiseDisjoint H.library) : (U:Set H.Chainbook).PairwiseDisjoint Sigma.fst := by
  intro i hi j hj hn; refine Finset.disjoint_left.mpr fun p hp hq=>?_ ; obtain ⟨x,hx⟩ := chapter_ne H p
  exact Finset.disjoint_left.mp (h hi hj hn) (show x∈H.library i from mem_biUnion.mpr ⟨p,hp,hx⟩) (show x∈H.library j from mem_biUnion.mpr ⟨p,hq,hx⟩)

variable (E : ℕ → RegularAddress c) (A : ℕ → Config G c → ℝ)
    (V : Config G c)
local notation "R°" => read H X χ E A

lemma present (U : Finset (Leaf J)) (hp : p.threshold=Pressure.temp α) :
    R°.admissible p V (U.map (visa H X)) ↔
      let s := U.map (Embedding.subtype _)
      (s : Set J.Chainbook).PairwiseDisjoint J.library ∧ J.eruptedPool V s := by
  let Z := U.map (Embedding.subtype _)
  change _ ↔ (Z:Set _).PairwiseDisjoint J.library ∧ J.eruptedPool V Z
  let T:= U.map (visa H X)
  have hf i : (R°.forced (visa H X i)).support=J.library i.val := (admitted H X i).1
  have hg i : (R°.forced (visa H X i)).inventory=J.inventory i.val.1.toLeft := (admitted H X i).2
  have hi : T.biUnion (fun i=> (R°.forced i).inventory)=Z.biUnion (fun i=> J.inventory i.1.toLeft) := by
    ext x; constructor
    · intro he; obtain ⟨p,hp,hx⟩:= mem_biUnion.mp he; obtain ⟨p,hq,rfl⟩:=mem_map.mp hp
      exact mem_biUnion.mpr ⟨p.val,show p.val ∈ Z from mem_map_of_mem (Embedding.subtype _) hq, hg p ▸ hx⟩
    intro he; obtain ⟨p,hp,hx⟩ := mem_biUnion.mp he; obtain ⟨p,hq,rfl⟩ := mem_map.mp hp; exact mem_biUnion.mpr ⟨_,mem_map_of_mem (visa H X) hq,(hg p).symm ▸ (show x∈J.inventory p.val.1.toLeft from hx)⟩
  unfold Activities.admissible; rw [hi,hp]; apply and_congr _ Iff.rfl
  constructor
  · intro h i hi j hj he
    obtain ⟨i,h_i,rfl⟩ := mem_map.mp hi; obtain ⟨j,h_j,rfl⟩:=mem_map.mp hj
    change Disjoint (J.library i.val) (J.library j.val); rw [← hf,← hf]
    exact h (show visa H X i∈ T from mem_map_of_mem _ h_i) (show visa H X j ∈ T from mem_map_of_mem _ h_j) ((visa H X).injective.ne (fun hz=> he (hz ▸ rfl)))
  intro h i hi j hj he; obtain ⟨i,h_i,rfl⟩ := mem_map.mp hi; obtain ⟨j,h_j,rfl⟩:=mem_map.mp hj; rw [hf,hf]
  exact h (show i.val∈ Z from mem_map_of_mem (Embedding.subtype _) h_i) (show j.val∈ Z from mem_map_of_mem (Embedding.subtype _) h_j) (fun hb=>he (congr_arg (visa H X) (Subtype.ext hb)))

lemma occupied (U : Finset (Leaf J)) (hp : p.threshold=Pressure.temp α) :
    R°.gasOccurrence p (U.map (visa H X)) V= J.canopyPool χ V (U.map (Embedding.subtype _)) := by
  let T:=U.map (visa H X); let Z := U.map (Embedding.subtype _)
  have he : R°.admissible p V T ↔ (Z:Set (J.Chainbook)).PairwiseDisjoint J.library ∧ J.eruptedPool V Z := present p H X χ E A V U hp
  have hq : (∏ i∈T,R°.K i V)=∏ i∈ Z,J.smilesPool χ V i := by unfold T Z; rw [prod_map,prod_map]; exact prod_congr rfl fun i _=> crowned H X χ V i
  change R°.gasOccurrence p T V=J.canopyPool χ V Z
  unfold Activities.gasOccurrence Cash.canopyPool
  by_cases hb : R°.admissible p V T
  swap; · rw [if_neg hb,if_neg (fun h=> hb (he.2 ⟨h.1.disjoint,h.2⟩))]
  rw [if_pos hb,hq]; obtain ⟨ht,hv⟩:= he.1 hb; split
  next => rfl
  next hx =>
    by_contra hn; exact hx ⟨⟨parted J ht,fun i hi=> (emits χ i V (fun hz=> hn (prod_eq_zero hi hz))).2.2,ht⟩,hv⟩

-- filtered addresses regardless of admission, applies HasSum without asserting global tsum rearrangements from zeros
lemma canopy_range {V : Finset J.Chainbook} (U : Config G c) (hu : J.canopyPool χ U V≠0) : V ∈ Set.range (fun X:Finset (Leaf J)=> X.map (Embedding.subtype _)) := by
  unfold Cash.canopyPool at hu; split at hu
  next he =>
    have h i (hi : i∈ V): (J.inventory i.1.toLeft).Nonempty := (emits χ i U (fun hz=> hu (prod_eq_zero hi hz))).2.1
    let X:=V.subtype fun p=> (J.inventory p.1.toLeft).Nonempty
    refine ⟨X,?_⟩; ext i; constructor
    · intro hi; obtain ⟨x,hx,rfl⟩:=mem_map.mp hi; exact mem_subtype.mp hx
    intro hi; exact Finset.mem_map.mpr ⟨⟨i,h _ hi⟩,mem_subtype.mpr hi,rfl⟩
  exact False.elim (hu rfl)
lemma output_range {U : Finset ℕ} (hu : R°.gasOccurrence p U V≠0) : U∈ Set.range (fun Z:Finset (Leaf J)=> Z.map (visa H X)) := by
  unfold Activities.gasOccurrence at hu; split at hu
  next =>
    refine ⟨Finset.preimage U (visa H X) (visa H X).injective.injOn,?_⟩
    ext i; constructor
    · intro hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp hi; exact mem_preimage.mp hj
    intro hi; obtain ⟨i,rfl⟩ := resides H X χ V i (fun h=>hu (prod_eq_zero hi h)); exact mem_map.mpr ⟨_,mem_preimage.mpr hi,rfl⟩
  exact False.elim (hu rfl)
lemma inundated (h : Cash.Renewed j a δ e J) (hp : p.threshold=Pressure.temp α) : R°.gas p V=∑' i,J.canopyPool χ V i := by
  let a (X : Finset (Leaf J)) := X.map (Embedding.subtype _)
  let b (X' : Finset (Leaf J)) := X'.map (visa H X)
  let f := J.canopyPool χ V
  let F' := Classical.choice (Tree.select S.ratio S.patch.odd_side)
  let Y := overhead (prism T α χ o.K V F') R Q.table; let z := J.homesteadPool χ V
  have he : Y*z ≠ 0 := mul_ne_zero (overhead_pos (prism ..) J).ne' (((J.threshold_logPool χ V h).2 ▸ Real.exp_pos _).ne')
  have hm : Summable f := by
    have hh := ((J.convoyPool χ V h F').summable).mul_left (Y*z)⁻¹; change Summable (fun i=> (Y*z)⁻¹*(Y*z*f i)) at hh; simp_rw [show ∀ i,(Y*z)⁻¹*(Y*z*f i)=f i from fun i=> inv_mul_cancel_left₀ he _] at hh; exact hh
  let g (d) := R°.gasOccurrence p d V
  have hF : Injective a := Finset.map_injective _
  have hK : Injective b := Finset.map_injective _
  have hh := (hF.hasSum_iff (f:=f) (fun t ht=> by by_contra h; exact ht (canopy_range χ V h))).2 hm.hasSum
  rw [show (f∘a)= (g ∘ b) from funext fun i=> (occupied p H X χ E A V i hp).symm] at hh
  exact ((hK.hasSum_iff (f:=g) (fun t ht=> by by_contra h; exact ht (output_range p H X χ E A V h))).1 hh).tsum_eq
end YM.PhysicalNext.Repeat.Refrain
