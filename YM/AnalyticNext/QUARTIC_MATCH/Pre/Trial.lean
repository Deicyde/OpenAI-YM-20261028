import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Progress.STATIONARY_SCENES.Frames



/-!
# Install A0 on all auxiliary meshes, without assuming those meshes in Horizon

Uses the same Tower. No width/size improvement or cost claim at the extended
period. Re-enabling the cheaper centered representative on each period later needs
these *identities*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Pre
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Bloch
open Work.F08 YM.Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

namespace Rows

/-- mean step lands w in block-distance coordinates, reads r (fine residue).
This is the actual finite patch including all path repeats. -/
def reach (P : Patch) (i : TypeFace 1) (v : P.Points × Fin P.L.val) : Cover :=
    v.1.val+v.2.val • step (axisEquiv.symm i)
def tailName (P : Patch) (i : TypeFace 1) (v : P.Points × Fin P.L.val) :=
    ( (arrives (0 : Site P.L) (reach P i v),i), carry (0 : Site P.L) (reach P i v))
def word (P : Patch) : Row (TypeFace 1) (Co P.L (TypeFace 1)) := fun i j z =>
    ∑ v : P.Points × Fin P.L.val, if (j,z)=tailName P i v then P.weight v.1 else 0
lemma word_pay (P : Patch) : Whole (word P) := by
  classical
  let S := Finset.univ.image fun q : TypeFace 1 × (P.Points × Fin P.L.val) => (tailName P q.1 q.2).2
  obtain ⟨C,_,h⟩ := Work.F06.strip_of_fin S (word P) (show ∀ i j z,z∉S → word P i j z=0 from
    fun i j z hn => Finset.sum_eq_zero fun v _ => if_neg fun he => hn (Finset.mem_image.mpr ⟨(i,v),Finset.mem_univ _,
      (congr_arg Prod.snd he).symm⟩)) 1
  exact ⟨1,C,one_pos,h⟩

lemma expression {P : Patch} (i j) (c : Side) (x y : Site c) :
    (word P).acts c (x,i) (y,j) =
      ∑ v : P.Points × Fin P.L.val, if j=(tailName P i v).1 ∧ y=x+wrap c (tailName P i v).2
        then P.weight v.1 else 0 := by
  change sift (fun z => ∑ v : P.Points × Fin P.L.val, if (j,z)=_ then P.weight v.1 else 0) c x y=_
  rw [sift_sum_finite]; swap
  · intro v
    apply summable_of_ne_finset_zero (s:={(tailName P i v).2})
    intro a h
    exact if_neg fun hx => h (Finset.mem_singleton.mpr (congr_arg Prod.snd hx))
  apply Finset.sum_congr rfl; intro v _
  unfold sift
  rw [tsum_eq_single (tailName P i v).2]
  · obtain he : tailName P i v=((tailName P i v).1,(tailName P i v).2) := rfl
    split_ifs <;> grind
  intro z h; split_ifs <;> grind

section period
variable {c f : Side} (S : StepData c f)
lemma catches (z : Body 1 c) (i : S.patch.Points × Fin S.patch.L.val) :
    let b := atPoint S z.1 i.1+i.2.val • step (axisEquiv.symm z.2)
    splitCo S.ratio (TypeFace 1) (b,z.2)=(z.1+wrap c (tailName S.patch z.2 i).2,(tailName S.patch z.2 i).1) := by
  intro b
  let w := reach S.patch z.2 i
  have he : b=S.ratio.embed z.1+wrap f w := by
    unfold b atPoint w reach
    simp only [map_add,map_nsmul,wrap_step]; abel
  have hx : S.ratio.residue (S.ratio.embed z.1)=(0:Site S.patch.L) := Ratio.residue_embed ..
  rw [he,split_co,moves_parent,moves_residue,hx,S.ratio.embed_parent]; rfl
lemma mean_eq : installed S.ratio (transRows (word S.patch))=(mean S).transpose := by
  have he a (x : Body 1 c) :
      (((installed S.ratio (transRows (word S.patch))).transpose)*ᵥ a) x = ∑ v : S.patch.Points × Fin S.patch.L.val,
        S.patch.weight v.1 * a (atPoint S x.1 v.1+v.2.val • step (axisEquiv.symm x.2),x.2) := by
    unfold Matrix.mulVec dotProduct
    simp_rw [installed,Matrix.transpose_apply,Matrix.submatrix_apply,id_eq,acts_trans,Matrix.transpose_apply]
    let Q : Body 1 f ≃ Co c (Co S.patch.L (TypeFace 1)) := splitCo S.ratio _
    have hh (v : Body 1 f) := expression (P:=S.patch) x.2 (Q v).2 c x.1 (Q v).1
    change ∑ v : Body 1 f,(word S.patch).acts c x (Q v)*a v=_
    simp_rw [(show ∀ v, (word S.patch).acts c x (Q v) = _ from hh), Finset.sum_mul]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
    let b : Body 1 f := (atPoint S x.1 i.1 + i.2.val • step (axisEquiv.symm x.2),x.2)
    have hz v : (Q v).2=(tailName S.patch x.2 i).1 ∧
        (Q v).1=x.1+wrap c (tailName S.patch x.2 i).2 ↔ v=b := by
      have hs : Q b=_ := catches S x i
      rw [← (Q).injective.eq_iff, hs]; simp only [Prod.ext_iff]; tauto
    simp_rw [hz,ite_mul, zero_mul]; rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  apply Matrix.transpose_injective; rw [Matrix.transpose_transpose]; apply Matrix.toLin'.injective
  apply LinearMap.ext; intro a; funext x
  change (((installed S.ratio (transRows (word S.patch))).transpose)*ᵥ a) x=(mean S*ᵥ a) x
  rw [he,mean_run_real,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Fin.sum_univ_eq_sum_range (fun j => S.patch.weight i*a (atPoint S x.1 i + j • step (axisEquiv.symm x.2),x.2)) _
end period

/-- Assemble identities with exactly the coverage from the tower. -/
def beast (M : Bed) := composeRows (composeRows (transRows (cobound 1)) M.metric) (cobound 1)
lemma beast_acts {M : Bed} (h : Whole M.metric) (n : Side) : (beast M).acts n=Precision.K (M.metric.acts n) := by
  let W := Whole.boundary 1
  unfold beast Precision.K; rw [(W.flipped.prod h).acts W,W.flipped.acts h,acts_trans]
lemma fine_whole {L : Side} {H : Row (TypeFace 1) (TypeFace 1)} {X : Cross L (TypeFace 1) (TypeFace 1)}
    (h : Whole H) (g : Whole X) : Whole (fineCompose H X) := by
  obtain ⟨σ,C,hp,h⟩ := h; obtain ⟨τ,D,hθ,d⟩ := g; have ht := lt_min hp hθ
  exact ⟨min σ τ,_,ht, strip_fine ht.le (strip_mono h (min_le_left σ τ) le_rfl)
    (strip_mono d (min_le_right σ τ) le_rfl)⟩

lemma horizon {A B : Type*} {P R : Row A B} (h : Whole P) (g : Whole R) {n : ℕ→Side} (hn : Tendsto (fun j => (n j).val) atTop atTop)
    (hg : ∀ j, P.acts (n j)=R.acts (n j)) : P=R := by
  funext i j x; apply tendsto_nhds_unique (entry_limit n hn P h.safe i j x)
  simp_rw [hg]; exact entry_limit n hn R g.safe i j x

/-- Coverage of A0 and K,W. Extending never reselects the Tower. -/
theorem across {c f : ℕ→Side} (S : ∀ i, StepData (c i) (f i)) (P : Patch) (Q : KernelChoices)
    (W : Cross P.L (TypeFace 1) (TypeFace 1)) (M N : Bed)
    (hc : Tendsto (fun i => (c i).val) atTop atTop)
    (h : Whole M.metric) (g : Whole N.metric) (ht : Whole W) (H : ∀ i, (S i).patch=P) (Hq : ∀ i, (S i).kernel=Q)
    (he : ∀ i,
      Inputs (S i) (installed (S i).ratio (show Cross _ (TypeFace 1) (TypeFace 1) from (by rw [show (S i).ratio.count=(S i).patch.L from rfl,H i]; exact W)))
        (M.metric.acts (f i)) (N.metric.acts (c i))) : ∀ c' : Side,
      let R := Sheets.stepAt P Q c'
      Inputs R (installed R.ratio W) (M.metric.acts (c'*P.L)) (N.metric.acts c') := by
  let a := transRows (word P)
  have ha : Whole a := (word_pay P).flipped
  let F := fineCompose (beast M) W
  let G := composeRows a (beast N)
  let T := net a W
  let U := minusRows (unitRow (TypeFace 1)) (scaleRows Q.penalty⁻¹ (beast N))
  have hm : Whole (beast M) := (((Whole.boundary 1).flipped).prod h).prod (Whole.boundary 1)
  have hk : Whole (beast N) := (((Whole.boundary 1).flipped).prod g).prod (Whole.boundary 1)
  have HH (c f : Side) (S : StepData c f) (H : S.patch=P) (hx : S.kernel=Q) :
      let L : Cross S.ratio.count (TypeFace 1) (TypeFace 1) := by rw [show S.ratio.count=S.patch.L from rfl,H]; exact W
      Inputs S (installed S.ratio L) (M.metric.acts f) (N.metric.acts c) ↔
        F.acts c=G.acts c ∧ T.acts c=U.acts c := by
    subst P Q; intro L
    have hW : L=W := rfl
    have h₁ : installed S.ratio F=Precision.K (M.metric.acts f)*installed S.ratio L := by rw [← beast_acts h]; exact Whole.from_fine S.ratio hm ht
    have h₂ : installed S.ratio G=(mean S).transpose*Precision.K (N.metric.acts c) := by rw [← mean_eq S,← beast_acts g]; exact Whole.from_coarse S.ratio ha hk
    have h₃ : T.acts c=mean S*installed S.ratio L := by
      rw [hW, show T.acts c=(installed S.ratio a).transpose*installed S.ratio W from net_action S.ratio ha ht, show installed S.ratio a=_ from mean_eq S, transpose_transpose]
    have h₄ : U.acts c=1-S.kernel.penalty⁻¹ • Precision.K (N.metric.acts c) := by
      unfold U; rw [(Whole.coin _).less (hk.weight _),acts_unit,acts_scale,beast_acts g]
    rw [h₃,h₄]
    constructor
    · intro i; refine ⟨?_,i.dual⟩
      have he : installed S.ratio F=installed S.ratio G := h₁.trans (i.primal.trans h₂.symm)
      ext x y
      have hz := congr_fun (congr_fun he ((splitCo S.ratio (TypeFace 1)).symm x)) y
      simp only [installed, Matrix.submatrix_apply, Equiv.apply_symm_apply,id_eq] at hz; exact hz
    rintro ⟨hr,hv⟩; refine ⟨h₁.symm.trans ((show installed S.ratio F=installed S.ratio G from congr_arg (fun D => D.submatrix (splitCo S.ratio _) id) hr).trans h₂),hv⟩
  have hv (i : ℕ) := (HH _ _ _ (H i) (Hq i)).mp (he i)
  have hi := horizon (fine_whole hm ht) (ha.prod hk) hc (fun i => (hv i).1)
  have hh := horizon (ha.flipped.prod ht) ((Whole.coin _).minus (hk.weight _)) hc (fun i => (hv i).2)
  intro i R; exact (HH _ _ R rfl rfl).mpr ⟨congr_arg (Row.acts · i) hi,congr_arg (Row.acts · i) hh⟩
end Rows
end YM.AnalyticNext.QuarticMatch.Pre
