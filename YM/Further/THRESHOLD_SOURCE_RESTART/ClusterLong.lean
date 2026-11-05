import YM.Further.THRESHOLD_SOURCE_RESTART.ClusterCurrent

/-!
# Infinite histories, actual marked logarithm identity

At value order, over entire (possibly infinite) unforced alphabet. Combine
finite log version, radius margin and absolute estimates. Given per-site hit
test, can therefore divide by QUIET coefficient, and read nilpotent part as
in `Grey`. Nothing about being able to divide in any such way on the forced or
whole-determinant system.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Clusters
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi Repeated
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {α V : Type*} [Fintype V] [DecidableEq V] {n : Side}
variable (X : α → Support n) (W : α → Marks.Algebra V)

-- This coefficient system respects restriction to any finite subalphabet.
private def append (D : Finset α) (z : Tuple ↥D) : Tuple α := ⟨z.1,Subtype.val ∘ z.2⟩
private lemma append_inj (D : Finset α) : Injective (append D) := by
  rintro ⟨k,f⟩ ⟨i,g⟩ h
  have he : k=i := congr_arg Sigma.fst h
  subst i
  have he : Subtype.val ∘ f = Subtype.val ∘ g := (Sigma.mk.inj h).2 |> eq_of_heq
  have ht : f=g := funext fun i => Subtype.ext (congr_fun he i)
  rw [ht]
private lemma processed (D : Finset α) (z : Tuple ↥D) :
    ink X W (append D z)=ink (fun i : ↥D => X i.val) (fun i : ↥D => W i.val) z := by
  open Push.AbsoluteSums.Ursell in
    suffices coefficient (blocked X) (Subtype.val ∘ z.2) =
        coefficient (blocked (fun i : D => X i.val)) z.2 by
      unfold ink append; dsimp only; congr 2; rw [this]
  open Push.AbsoluteSums.Ursell in
    refine congr_arg (fun P => Push.AbsoluteSums.Graph.mass P) (show _ = _ from Finset.ext (fun i => ?_))
  open Push.AbsoluteSums.Ursell in
    simp only [potential_mem]; simp only [blocked,Ac.meets]; simp [comp_apply]

private def push (D : Finset α) (s : Finset ↥D) : Finset α := s.image Subtype.val
private lemma push_inj (D : Finset α) : Injective (push D) := Finset.image_injective Subtype.val_injective
private lemma contributed (D : Finset α) (s : Finset ↥D) :
    formed X W (push D s)=formed (fun i : ↥D => X i.val) (fun i : ↥D => W i.val) s := by
  let R := Push.AbsoluteSums.Ursell.blocked X
  let Q := Push.AbsoluteSums.Ursell.blocked fun i : D => X i.val
  have hf (i j : D) : R i.val j.val ↔ Q i j := by simp only [R,Q,Push.AbsoluteSums.Ursell.blocked,Subtype.val_inj,Ac.meets]
  have he : Push.AbsoluteSums.Gas.separated R (push D s) ↔ Push.AbsoluteSums.Gas.separated Q s := by
    constructor
    · intro h i hi j hj H
      exact fun he => h _ (Finset.mem_image_of_mem _ hi) _ (Finset.mem_image_of_mem _ hj)
        (fun w => H (Subtype.ext w)) ((hf ..).2 he)
    intro h i hi j hj H; obtain ⟨i,hI,rfl⟩ := Finset.mem_image.mp hi; obtain ⟨j,hJ,rfl⟩ := Finset.mem_image.mp hj
    exact fun he => h i hI j hJ (fun e => H (congr_arg _ e)) ((hf ..).1 he)
  unfold formed; split
  next H => rw [if_pos (he.mp H)]; unfold push; rw [Finset.prod_image Subtype.val_injective.injOn]
  next H => rw [if_neg (mt he.mpr H)]

lemma live (h : Summable fun i => ‖ink X (fun i => (2:ℂ) • W i) i‖) (hp : Summable fun s => ‖formed X W s‖) :
    electric (∑' i, ink X W i)=∑' s,formed X W s := by
  let L (D : Finset α) := (range (append D)).indicator (ink X W)
  let H (D : Finset α) := (range (push D)).indicator (formed X W)
  have he (D : Finset α) : electric (∑' i, L D i)=∑' s,H D s := by
    let S := fun i : D => X i.val
    let V := fun i : D => W i.val
    have ht (i : Tuple ↥D) : L D (append D i)=ink S V i := by
      unfold L; rw [indicator_of_mem (mem_range_self _)]; exact processed ..
    have hh (i) : H D (push D i)=formed S V i := by
      unfold H; rw [indicator_of_mem (mem_range_self _)]; exact contributed ..
    simp_rw [← (append_inj D).tsum_eq (f:=L D) support_indicator_subset,ht,
      ← (push_inj D).tsum_eq (f:=H D) support_indicator_subset,hh]
    apply authorized S V
    apply (h.comp_injective (append_inj D)).congr
    intro i; exact congr_arg Norm.norm (processed X (fun i => (2:ℂ) • W i) ..)
  have hf : Tendsto (fun D => ∑' i,L D i) atTop (𝓝 (∑' i,ink X W i)) := by
    apply tendsto_tsum_of_dominated_convergence (tighten X W h)
    · intro i; apply tendsto_const_nhds.congr'; filter_upwards [eventually_ge_atTop (Finset.univ.image i.2)] with A ha
      have ht : i ∈ range (append A) := by
        exact ⟨⟨i.1,fun j => ⟨i.2 j,ha (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩⟩,rfl⟩
      exact (indicator_of_mem ht _).symm
    refine Eventually.of_forall fun D i => ?_
    by_cases hh : i∈range (append D)
    · unfold L; rw [indicator_of_mem hh]
    unfold L; rw [indicator_of_notMem hh,norm_zero]; exact norm_nonneg _
  have hg : Tendsto (fun D => ∑' i,H D i) atTop (𝓝 (∑' i,formed X W i)) := by
    apply tendsto_tsum_of_dominated_convergence hp
    · intro i; apply tendsto_const_nhds.congr'; filter_upwards [eventually_ge_atTop i] with A ha
      have ht : i∈range (push A) := by
        obtain ⟨v,h⟩ := Pad.inclusive (M:=i) (Subtype.val : ↥A → α) (fun i hi => ⟨⟨_,ha hi⟩,rfl⟩); exact ⟨v,h⟩
      exact (indicator_of_mem ht _).symm
    refine Eventually.of_forall fun D i => ?_
    by_cases h : i∈range (push D)
    · unfold H; rw [indicator_of_mem h]
    unfold H; rw [indicator_of_notMem h,norm_zero]; exact norm_nonneg _
  exact tendsto_nhds_unique ((power_cont.continuousAt.tendsto.comp hf).congr he) hg


end YM.Further.ThresholdSourceRestart.Clusters
