import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tournament

/-!
# Compulsory outputs in standard family format
 Use *all* restored molecules, even agreeing-support different counts.
 Keep exactly full-support tested flags, preserve hard dependence in `K`.
 Need to prove ordinary gas equality even though Library has custom
 `Valid` requiring disjoint underlying letters (also true). -/
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

abbrev Leaf := {p : H.Chainbook// (H.inventory p.1.toLeft).Nonempty}

def gate {s : Signed} {t : Site c} (X : Alliance H J s t) : Leaf H≃ Leaf J := Equiv.subtypeEquiv X.tongs fun i=> by rw [X.fireplaces]; simp

def cannon (i : Leaf H) : ForcedAddress G c := ⟨H.library i.val,H.inventory i.val.1.toLeft,i.property,H.shelf _,fun _=>True⟩
lemma stem {s : Signed} {t : Site c} (X : Alliance H J s t) (i : Leaf H) :
    (cannon J (gate H X i)).support=(cannon H i).support.image (affine s t) ∧
    (cannon J (gate H X i)).inventory=(cannon H i).inventory.image (affine s t) := ⟨X.hearth i.val,X.fireplaces i.val⟩
lemma crew (i : Leaf H) : (cannon J (gate H X i)).support=(cannon H i).support ∧ (cannon J (gate H X i)).inventory=(cannon H i).inventory := by
  have h := stem H X i; rw [show affine 1 (0:Site c)=id from funext fun y=> by simp [Lattice.affine],image_id,image_id] at h; exact h

-- pad by Nat copies of ZERO K with orbit of all sites. Don't repeat real K.
abbrev Blank := ℕ × Site c
abbrev Annual := Leaf H ⊕ Blank (c:=c)

def reserve : Annual H → ForcedAddress G c := Sum.elim (cannon H) (fun i=> ⟨{i.2},{i.2},Finset.singleton_nonempty _,Finset.Subset.refl _,fun _=>False⟩)
def fuse (u : Annual H) (V : Config G c) := u.elim (fun i=> J.smilesPool χ V (X.tongs i.val)) fun _=>0

scoped instance countSeeds : Countable (Head S) := by
  haveI : Countable (LogIndex c f) := Function.Injective.countable (f:=fun i : LogIndex c f=> ((∅,{i}): ListsAt c f)) (by intro i j h; simpa using h)
  haveI : Countable (WarningAt c f) := Finite.to_countable
  haveI : Countable (Stores S) := Finite.to_countable
  unfold Head ConnectedActivityE6.Alphabet Mixed.Alphabet; infer_instance
scoped instance : Countable (Annual H) := by
  have : Countable (Head S) := inferInstance
  unfold Annual Leaf Blank; infer_instance
scoped instance : Infinite (Annual H) := Infinite.of_injective (fun i : ℕ=> (Sum.inr (i,(0:Site c)):Annual H)) (by intro i j h; simpa using h)

def badge : ℕ≃ Annual H := numbering _

def read (E : ℕ → RegularAddress c) (V : ℕ → Config G c → ℝ) : Activities G c := ⟨E,reserve H ∘ badge H,V, fuse H X χ ∘ badge H⟩

lemma emits (u : J.Chainbook) (V) (h : J.smilesPool χ V u ≠ 0) : J.statesPool V u ∧ (J.inventory u.1.toLeft).Nonempty ∧ Ac.Spark J.bookFoot u.1 := by
  unfold Cash.smilesPool at h; split at h
  next he => obtain ⟨i,hx⟩ := J.regains _ he.2.1 he.1
             exact ⟨he.2.2,Nonempty.mono (subset_biUnion_of_mem (fun i:J.ThickP=> (roster i.val).flags) (mem_toLeft.mpr hx)) i.2.2,he.2.1⟩
  exact (h rfl).elim
lemma dolls (hp : p.threshold=Pressure.temp α) (i : Leaf H) (U) (he : fuse H X χ (.inl i) U ≠ 0) : (cannon H i).eligible p.threshold U := by
  obtain ⟨hz,hP,hq⟩ := emits (J:=J) χ (gate H X i).val U he
  unfold ForcedAddress.eligible; rw [← (crew H X i).1, ← (crew H X i).2, hp, inter_comm]
  exact ⟨hz.symm,True.intro⟩
lemma flowering (i : Leaf H) : fuse H X χ (.inl i)=(fun V => J.smilesPool χ V (gate H X i).val) := rfl
lemma collateral (hp : p.threshold=Pressure.temp α) (i : Leaf H) : GaugeInvariant (fuse H X χ (Sum.inl i)) ∧ Measurable (fuse H X χ (Sum.inl i)) ∧ UsesFinal p.threshold (cannon H i).support (fuse H X χ (Sum.inl i)) := by
  rw [flowering,← (crew H X i).1,hp]
  let a:= gate H X i; have he:= bloom J χ a.val; change GaugeInvariant (fun V=> J.smilesPool χ V a.val) ∧ Measurable _ ∧ UsesFinal _ (J.library a.val) _
  exact ⟨he.2,he.1,boughs J χ a.val⟩
lemma barren (i : Blank (c:=c)) : fuse H X χ (Sum.inr i)=(fun _=>0) := rfl
lemma collated (hp : p.threshold=Pressure.temp α) (i : Annual H) : GaugeInvariant (fuse H X χ i) ∧ Measurable (fuse H X χ i) ∧ UsesFinal p.threshold (reserve H i).support (fuse H X χ i) ∧ ∀ U,fuse H X χ i U≠0 → (reserve H i).eligible p.threshold U := by
  rcases i with i|i
  · have hh:= collateral p H X χ hp i
    exact ⟨hh.1,hh.2.1,hh.2.2,dolls p H X χ hp i⟩
  rw [barren]
  exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun _ h=> (h rfl).elim⟩

def congo {A B : Type} (p : A≃B) (q : Equiv.Perm B) := (p.trans q).trans p.symm
lemma perch {A B : Type} (p : A≃B) (q : Equiv.Perm B) (i : A) : p (congo p q i)=q (p i) := p.apply_symm_apply _
theorem buoyant (s : Signed) (t : Site c) (π : R.activities.Moves s (S.ratio.embed t)) (f : Equiv.Perm (Leaf H)) (i : Leaf H) (U)
    (hk : gate H X (f i)=gate J (swing J π) (gate H X i)) :
    (cannon H (f i)).support=(cannon H i).support.image (affine s t) ∧ (cannon H (f i)).inventory=(cannon H i).inventory.image (affine s t) ∧
      fuse H X χ (.inl (f i)) U=fuse H X χ (.inl i) (pull s t U) := by
  have hz := stem J (swing J π) (gate H X i)
  rw [← (crew H X (f i)).1,← (crew H X i).1,← (crew H X (f i)).2,← (crew H X i).2,flowering,flowering]
  dsimp only; rw [hk]
  exact ⟨hz.1,hz.2,(blossom J χ π U (gate H X i).val).symm⟩
lemma settles (s : Signed) (t : Site c) (π : R.activities.Moves s (S.ratio.embed t)) : ∃ z : Equiv.Perm (Annual H), ∀ i,
    (reserve H (z i)).support=(reserve H i).support.image (affine s t) ∧ (reserve H (z i)).inventory=(reserve H i).inventory.image (affine s t) ∧
      ∀ U, ((reserve H (z i)).extraTest U↔(reserve H i).extraTest (pull s t U)) ∧ fuse H X χ (z i) U=fuse H X χ i (pull s t U) := by
  have hout (A B : Type) (p:A≃B) (q:Equiv.Perm B) : ∃ u:Equiv.Perm A,∀ i,p (u i)=q (p i) := ⟨congo p q, perch p q⟩
  obtain ⟨f,hf⟩ := hout _ _ (gate H X) (gate J (swing J π))
  refine ⟨Equiv.sumCongr f (Equiv.prodCongr (Equiv.refl ℕ) (StepData.sendSites s t)),?_⟩
  rintro (i|⟨i,b⟩)
  · have hk U := buoyant H X χ s t π f i U (hf i)
    simp only [Equiv.sumCongr_apply,Sum.map_inl]
    exact ⟨(hk 1).1,(hk 1).2.1,fun U=> ⟨Iff.rfl,(hk U).2.2⟩⟩
  simp only [Equiv.sumCongr_apply,Sum.map_inr]
  simp [reserve,fuse,Lattice.affine]; rfl
lemma chargesOut (z : Cash.Renewed j a δ e J) (hB : p.B=radiusB α)
    (hp : p.supportExponent+1≤a) : ∃ k, (∀ i,0 ≤ k i ∧ ∀ U, ‖fuse H X χ (badge H i) U‖ ≤ k i) ∧ Ac.Hit (fun i=> (reserve H (badge H i)).support) p.B k
      (p.supportExponent+1) (Cash.armK Q L μ α 0 j) := by
  let f i := J.excels j (X.tongs (Subtype.val (i:Leaf H)))
  let k:=Sum.elim f fun _ : Blank (c:=c)=>0
  have h i : 0 ≤ k i ∧ ∀ U, ‖fuse H X χ i U‖ ≤ k i := by
    rcases i with i|i
    · exact ⟨J.excels_nn ..,fun U=> J.excel_boundsPool χ U ..⟩
    exact ⟨le_rfl,fun U=> by simp [fuse,k]⟩
  refine ⟨k ∘ badge H,fun i=>h _,fun y=> ?_⟩
  let f' i:= if y∈(reserve H i).support then k i *Real.exp ((p.supportExponent+1)*coverNumber p.B (reserve H i).support) else 0
  have ha : SumBudget (fun i=> f' (Sum.inl i)) (Cash.armK Q L μ α 0 j) := by
    have hk:= J.bulkhead z 0 y; simp only [Nat.zero_le,↓reduceIte] at hk
    let g:=gate H X
    have hl:= budget_pull (Subtype.val ∘ g) (Subtype.val_injective.comp g.injective) hk
    refine budget_mono hl (fun i=> ?_) fun i=> ?_
    · unfold f'; split
      · exact mul_nonneg (h _).1 (Real.exp_pos _).le
      exact le_rfl
    unfold f'; split
    next hx=> have hz : (reserve H (Sum.inl i)).support=J.library (g i).val := (crew H X i).1.symm
              simp only [hB,hz,Function.comp_apply]; rw [if_pos (hz ▸ hx)]
              exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (h _).1
    exact hl.1 i
  have hz : SumBudget f' ((Cash.armK Q L μ α 0 j)+0) := Cost.sum (f:=f') ha (show SumBudget (fun i=> f' (.inr i)) 0 from by unfold f'; simp [k,SumBudget]);
  rw [add_zero] at hz; exact Cost.equiv (badge H) hz

variable (E : ℕ → RegularAddress c) (V : ℕ → Config G c → ℝ)
lemma qualified (hp : p.threshold=Pressure.temp α) : (read H X χ E V).ForcedFamily p := by
  have ht:= collated p H X χ hp
  have hh i k U : (reserve H i).extraTest (Lattice.gauge k U) ↔ (reserve H i).extraTest U:= by cases i <;> exact Iff.rfl
  have hg i : MeasurableSet {U | (reserve H i).extraTest U} := by cases i <;> simp [reserve,cannon]
  have ha i : UsesFinal p.threshold (reserve H i).support (reserve H i).extraTest := by cases i <;> exact fun _ _ _ _=>rfl
  exact ⟨fun i=>(ht _).1, fun i=>hh _, fun i=>(ht _).2.1, fun i=>hg _, fun i=>(ht _).2.2.1, fun i=>ha _, fun i=>(ht _).2.2.2⟩
end YM.PhysicalNext.Repeat.Refrain
