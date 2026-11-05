import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Orthogonal
import YM.Next.UV_STRESS.Fringe
import YM.Push.LOCAL_SPLITTING.Transport
import YM.Push.PRICE_COMPILER.Builders
import YM.Push.PRICE_COMPILER.Continuity
import YM.UVNext.PRICED_KERNELS.Assembly


set_option warningAsError false

/-!
# Sector covariance and ordered-window means transform from whole-color row laws

Respell the basis action, with actual `shots`. They use a shifted initial-site
overestimate which we need not assume reflects exactly: remove the projector
algebraically using `skip_bump` on the active inputs ONLY. The scalar part of
a sum of selected row energies is **not** asserted to transform by this trick.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Tensor
open Filter Function Set Lattice RG Wilson Precision Tree Matrix Pressure Stores Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Rows Orthogonal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {G : Gauge}

def ortho (O : ColorOrtho G α) (i : α) : G.Color ≃L[ℝ] G.Color := ((O i).toLinearIsometryEquiv rfl).toContinuousLinearEquiv

def lifting (O : ColorOrtho G α) (e : α ≃ β) : LogArray G β ≃L[ℝ] LogArray G α :=
    ((LinearEquiv.piCongrLeft ℝ (fun _ : β => G.Color) e).symm.trans
      (LinearEquiv.piCongrRight (fun i => (ortho O i).toLinearEquiv))).toContinuousLinearEquiv
lemma lifting_apply (O : ColorOrtho G α) (e : α ≃ β) (a : LogArray G β) (i : α) : lifting O e a i = O i (a (e i)) := rfl

section fd
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
lemma derives (L : H ≃L[ℝ] H) (g : G.Color ≃L[ℝ] G.Color) {F H' : H → G.Color}
    (he : ∀ a,F (L a)=g (H' a)) (a : H) : fderiv ℝ F 0 (L a) = g (fderiv ℝ H' 0 a) := by
  have h := L.comp_right_fderiv (x:=0) (f:=F)
  rw [show F ∘ L = g ∘ H' from funext he, g.comp_fderiv,map_zero] at h
  exact DFunLike.congr_fun h.symm a
end fd

section step
variable {c f : Side} {S : StepData c f}
variable (A A' : Stores S) (F F' : Forest S.ratio) (x : ℝ) (T : Tube G S) (V V' : Config G c) (k k' : S.Choices)

lemma moves_points (s : Signed) (t : Site c) (i : Bond f) :
    Next.SectorChange.points S (sendEdge s (S.ratio.embed t) i) = (affine s t) '' Next.SectorChange.points S i := by
  unfold Next.SectorChange.points; rw [Set.image_insert_eq,Set.image_singleton]
  simp_rw [← Push.Local.parent_affine S.ratio S.patch.odd_side]
  let d := (posDir i.2).rotate s
  let j := affine s (S.ratio.embed t) i.1
  have he : affine s (S.ratio.embed t) (i.1+step i.2)=j+d.vec := by rw [← Step.vec_pos,affine,s.act_add,← Step.vec_rotate]; unfold j affine d; abel
  rw [he,sendEdge]; change {_,_}={S.ratio.parent j,S.ratio.parent _}
  change {S.ratio.parent (d.used j).1,_}=_; unfold Step.used; split
  · next h => simp [Step.vec,h,sub_eq_add_neg,Set.pair_comm]; rfl
  next h => simp [Step.vec,h]; rfl

lemma moves_meeting (s : Signed) (t : Site c) (i j : Bond f) : meeting S x (sendEdge s (S.ratio.embed t) i) (sendEdge s (S.ratio.embed t) j) ↔ meeting S x i j := by
  unfold meeting; simp only [moves_points,Set.forall_mem_image,affine,separation_translate,separation_signed]

abbrev endLinks (i : Active A x F) : Set (Active A x F) := {j | meeting S x i.val.val j.val.val}

open FreeResolvent.Mid (axis) in
abbrev midLinks (i : Active A x F) : Set (Active A x F) := {j | 20 * separation (axis i.val.val) (axis j.val.val) ≤ 2*S.patch.L.val*radiusB x}

lemma mids_together : mids A F x (G:=G)=together _ (midLinks A F x) := by
  ext i j; simp [mids,midsAt,FreeResolvent.Mid.window,cull_address,together]

section relabel
variable {A A' F F' x} (e : Active A' x F' ≃ Active A x F) (O : ColorOrtho G (Active A' x F'))
abbrev BothPlaces : Prop := (∀ i,endLinks A' F' x i = e ⁻¹' endLinks A F x (e i)) ∧
                              ∀ i,midLinks A' F' x i = e ⁻¹' midLinks A F x (e i)
lemma geometry (s : Signed) (t : Site c) (he : ∀ i, (e i).val.val=sendEdge s (S.ratio.embed t) i.val.val) : BothPlaces e := by
  refine ⟨fun i => ?_,fun i => ?_⟩
  · ext j; simp [endLinks,he,moves_meeting]
  ext j; simp [midLinks,he,FreeResolvent.Mid.turned]

structure Equivalent : Prop where
  same : Rows.gram T x V' k' (shots S x) A' F' = warp O e (Rows.gram T x V k (shots S x) A F)
  ends : Schur.per (panels A' F') (Rows.gram T x V' k' (shots S x) A' F') = warp O e (Schur.per (panels A F) (Rows.gram T x V k (shots S x) A F))
  mids : Schur.per (GaussianFieldAlignment.mids A' F' x) (Rows.gram T x V' k' (shots S x) A' F') = warp O e (Schur.per (GaussianFieldAlignment.mids A F x) (Rows.gram T x V k (shots S x) A F))

variable {T V V' k k'}
lemma equivalent (hQ : Rows.gram T x V' k' (shots S x) A' F' = warp O e (Rows.gram T x V k (shots S x) A F)) (he : BothPlaces e) : Equivalent T V V' k k' e O := by
  refine ⟨hQ,?_,?_⟩
  · rw [hQ]; apply warp_per (w:=endLinks A' F' x)
    exact fun i => by ext j; change ((e j.1) ∈ endLinks A F x _) ↔ j.1 ∈ endLinks A' F' x _; rw [he.1 i.1]; rfl
  rw [hQ,mids_together,mids_together]; apply warp_per
  exact fun i => by ext j; change ((e j.1) ∈ midLinks A F x _) ↔ j.1 ∈ midLinks A' F' x _; rw [he.2 i.1]; rfl
variable {O e} (h : Equivalent T V V' k k' e O)
include h
lemma Equivalent.fog : fog A' F' T x V' k'=warp O e (fog A F T x V k) := by unfold Next.SectorChange.fog Schur.clouded; rw [h.ends, ← Relative.symPart,warp_sym]; rfl

end relabel

-- Remove selection using the ZERO ON A *FRESH* COLUMN. Can't drop it on base entries alone.
lemma bias_dot (q : Chi) (d : ℝ) (a : Prices G (Active A x F)) (Y : LinkArray G (Frozen A x F))
    (h : S.patch.Branches S.kernel G) {σ E Λ : ℝ} (hT : T.up.Bounds T.high σ E Λ) :
    let W := shots S x
    a ⬝ᵥ blame T x V k W A F q d Y = slip * slip * ∑ i : Slots S, inner ℝ
      (bump T x V k (fresh x W A F (tape a)) i)
      ((base T x V k+bump T x V k (input x A F (autoShell q d V Y))) i) := by
  intro W
  rw [Rows.blame,dotProduct_transpose_mulVec,dotProduct_comm, moved _ _ _ _ _ _ _ hT,Rows.source]
  have hx (u v : LogArray G (Slots S)) : tape.symm u ⬝ᵥ tape.symm v = ∑ i, inner ℝ (u i) (v i) := by
    simp_rw [dotProduct, Fintype.sum_prod_type,Work.F03.inner_color]; rfl
  rw [hx,Finset.mul_sum]; refine Finset.sum_congr rfl fun ⟨s,i⟩ _ => ?_
  dsimp only [selected,Rows.restrict]; split
  · rw [real_inner_smul_left,real_inner_smul_right,mul_assoc]
  next hh => rw [skip_bump T x V k A F s i _ h hh]; simp

variable {A A' F F' x}

abbrev onBond (O : ColorOrtho G (Bond f)) : ColorOrtho G (Active A x F) := fun i => O i.val.val

variable (b : Equiv.Perm (Bond f)) (O : ColorOrtho G (Bond f))
    (e : Active A' x F' ≃ Active A x F)
    (e' : Frozen A' x F' ≃ Frozen A x F) (u : Equiv.Perm (Slots S)) (P : ColorOrtho G (Slots S))

lemma fresh_move (he : ∀ i, (e i).val.val=b i.val.val) (a : Prices G (Active A x F)) :
    fresh x (shots S x) A' F' (tape (Orthogonal.move (onBond O) e a)) = lifting O b (fresh x (shots S x) A F (tape a)) := by
  funext i
  rw [lifting_apply]
  unfold fresh; split
  · rename_i h
    split
    · rename_i h'
      let j : Active A' x F' := ⟨⟨i,h⟩,h'⟩
      change tape _ j = _
      rw [move_tape,← he j, dif_pos (e j).val.property,dif_pos (e j).property]
    next h' =>
      split
      · next hu =>
          rw [dif_neg (fun ht => h' (absurd_chill _ h hu ht)), map_zero]
      rw [map_zero]
  next h =>
    split
    · next hu => rw [dif_neg (fun ht => h (absurd_trunks _ hu ht)), map_zero]
    rw [map_zero]
where
  bond_inv (i : Active A x F) : (e.symm i).val.val = b.symm i.val.val := b.injective (by rw [← he, e.apply_symm_apply, b.apply_symm_apply])
  absurd_chill i (hi : i ∉ F'.trunks) (hb : b i ∉ F.trunks) (hv : ¬ chill A x F ⟨_,hb⟩) : ¬ chill A' x F' ⟨_,hi⟩ := by
    let t : Active A x F := ⟨⟨_,hb⟩,hv⟩
    have hh : (e.symm t).val=⟨_,hi⟩ := Subtype.ext ((bond_inv t).trans (b.symm_apply_apply _))
    exact hh ▸ (e.symm t).property
  absurd_trunks i (hb : b i ∉ F.trunks) (hv : ¬ chill A x F ⟨_,hb⟩) : i ∉ F'.trunks := by
    let t : Active A x F := ⟨⟨_,hb⟩,hv⟩
    exact ((bond_inv t).trans (b.symm_apply_apply _)) ▸ (e.symm t).val.property

lemma frozen_move (he : ∀ i, (e' i).val.val=b i.val.val) (a : LogArray G (Frozen A x F)) :
    input x A' F' (fun i => O i.val.val (a (e' i))) = lifting O b (input x A F a) := by
  funext i
  rw [lifting_apply]
  unfold input; split
  · rename_i h
    split
    · rename_i h'
      let j : Frozen A' x F' := ⟨⟨i,h⟩,h'⟩
      change O _ (a (e' j)) = O _ _
      rw [← he j, dif_pos (e' j).val.property,dif_pos (e' j).property]
    next h' =>
      split
      · next hu => rw [dif_neg (fun ht => h' (absurd_chill _ h hu ht)),map_zero]
      rw [map_zero]
  next h =>
    split
    · next hu => rw [dif_neg (fun ht => h (absurd_trunks _ hu ht)),map_zero]
    rw [map_zero]
where
  bond_inv (i : Frozen A x F) : (e'.symm i).val.val = b.symm i.val.val := b.injective (by rw [← he, e'.apply_symm_apply, b.apply_symm_apply])
  absurd_chill i (hi : i ∉ F'.trunks) (hb : b i ∉ F.trunks) (hv : chill A x F ⟨_,hb⟩) : chill A' x F' ⟨_,hi⟩ := by
    let t : Frozen A x F := ⟨⟨_,hb⟩,hv⟩
    have hh : (e'.symm t).val=⟨_,hi⟩ := Subtype.ext ((bond_inv t).trans (b.symm_apply_apply _))
    exact hh ▸ (e'.symm t).property
  absurd_trunks i (hb : b i ∉ F.trunks) (hv : chill A x F ⟨_,hb⟩) : i ∉ F'.trunks := by
    let t : Frozen A x F := ⟨⟨_,hb⟩,hv⟩
    exact ((bond_inv t).trans (b.symm_apply_apply _)) ▸ (e'.symm t).val.property

variable {σ E Λ : ℝ} {T V V' k k'} (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ)
    (he : ∀ i, (e i).val.val=b i.val.val)
    (hp : ∀ (a : Directions G f) (i : Slots S), bump T x V' k' (lifting O b a) i = P i (bump T x V k a (u i)))
include h hT he hp

lemma gram_motion (hw : BothPlaces e) : Equivalent T V V' k k' e (onBond O) := by
  apply equivalent _ _ _ hw
  apply warp_of
  intro a a'
  rw [gram_dot _ _ _ _ _ _ _ _ h hT,gram_dot _ _ _ _ _ _ _ _ h hT]
  apply congr_arg
  let U a i := bump T x V k (fresh x (shots S x) A F (tape a)) i
  let U' a i := bump T x V' k' (fresh x (shots S x) A' F' (tape (Orthogonal.move (onBond O) e a))) i
  rw [← Fintype.sum_prod_type (fun i : Slots S => inner ℝ (U a i) (U a' i)), ← Fintype.sum_prod_type (fun i : Slots S => inner ℝ (U' a i) (U' a' i))]
  refine Eq.trans ?_ (Equiv.sum_comp u (fun i : Slots S => inner ℝ (U a i) (U a' i)))
  unfold U U'; exact Finset.sum_congr rfl fun i _ => by rw [fresh_move b O e he,fresh_move b O e he,hp,hp]; exact (P i).inner_map_map ..

lemma blame_motion (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F'))
    (hE : ∀ i, (e' i).val.val=b i.val.val)
    (hF : ∀ i, autoShell q d V' Y' i=O i.val.val (autoShell q d V Y (e' i)))
    (hB : ∀ i, base T x V' k' i=P i (base T x V k (u i))) :
    blame T x V' k' (shots S x) A' F' q d Y' = Orthogonal.move (onBond O) e (blame T x V k (shots S x) A F q d Y) := by
  have H (a : Prices G (Active A' x F')) : a ⬝ᵥ blame T x V' k' (shots S x) A' F' q d Y' = a ⬝ᵥ Orthogonal.move (onBond O) e (blame T x V k (shots S x) A F q d Y) := by
    obtain ⟨a,rfl⟩ := move_surj (onBond O) e a
    rw [bias_dot A' F' x T V' k' q _ _ _ h hT,move_dot,bias_dot A F x T V k q _ _ _ h hT,
      funext hF,frozen_move b O e' hE]
    apply congr_arg
    let U i := bump T x V k (fresh x (shots S x) A F (tape a)) i
    let Q i := base T x V k i + bump T x V k (input x A F (autoShell q d V Y)) i
    refine Eq.trans ?_ (Equiv.sum_comp u (fun i => inner ℝ (U i) (Q i)))
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, fresh_move b O e he,hB,hp,hp,← (P i).map_add]; exact (P i).inner_map_map ..
  funext i; simpa using H (Pi.single i 1)

omit h hT he hp
lemma negative (O : ColorOrtho G α) (e : α ≃ β) (Q : Gaussian.Table (β×G.ColorIndex)) (a : Prices G β) :
    -(warp O e Q).transpose *ᵥ Orthogonal.move O e a = Orthogonal.move O e (-Q.transpose *ᵥ a) := by
  rw [neg_mulVec,warp,transpose_dressed,transpose_submatrix,show dressed (asMatrix O) _ = _ from rfl, ← warp, warp_mv, neg_mulVec]; symm; exact Matrix.mulVec_neg ..

structure Means (q : Chi) (d : ℝ) (O : ColorOrtho G (Active A' x F')) (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F')) : Prop where
  bias : blame T x V' k' (shots S x) A' F' q d Y' = Orthogonal.move O e (blame T x V k (shots S x) A F q d Y)
  ends : meanLog A' F' T x V' k' q d Y'=Orthogonal.move O e (meanLog A F T x V k q d Y)
  mids : middleLog A' F' x T V' k' q d Y'=Orthogonal.move O e (middleLog A F x T V k q d Y)

lemma means (q : Chi) (d : ℝ) (O : ColorOrtho G (Active A' x F')) (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F'))
    (h : Equivalent T V V' k k' e O)
    (he : blame T x V' k' (shots S x) A' F' q d Y' = Orthogonal.move O e (blame T x V k (shots S x) A F q d Y)) : Means (T:=T) (V:=V) (V':=V') (k:=k) (k':=k') e q d O Y Y' :=
  ⟨he,by unfold meanLog; rw [h.ends,he,negative],by unfold middleLog; rw [h.mids,he,negative]⟩
end step
end YM.AnalyticBridge.GaussianFieldAlignment.Tensor
