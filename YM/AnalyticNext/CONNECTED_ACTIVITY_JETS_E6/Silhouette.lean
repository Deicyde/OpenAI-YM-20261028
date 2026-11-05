import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Amass
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unimod

/-!
# The actual per-F scalar IS forest-independent

 Root color uses integer lattice, including reversal signs. Extended Gram
 simultaneously on same carrier in all Signed channels. Needed if F kept
 deterministic, or for returning to treatment with independent tree tags
 in a future output dictionary. No averaging proof on the alphabet here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.TreeColor
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Bid Matter Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F H : Forest S.ratio} {P : Teller G}

lemma rotated_grad (s : Signed) (u: Site f → G.Color) : displacement s (gradient u) 1=gradient (u ∘ s.act) := by
  funext i; cases he : s.flip i.2
  · have hx:= StepData.possite s (0:Site f) i.1 i.2 he; simp only [affine0] at hx
    dsimp only [displacement]; rw [if_neg (by simp [he]), Channel.positive s i he]; simp [gradient,hx]
  have hh:= StepData.negsite s (0:Site f) i.1 i.2 he; simp only [affine0] at hh; have ht : s.act (i.1+step i.2)+step (s.perm i.2)=s.act i.1:= by rw [hh]; abel
  dsimp only [displacement]; rw [if_pos he,Channel.negative s i he]
  simp only [gradient,Pi.one_apply,inv_one,G.adjoint_one,ht, Function.comp_apply]; abel
lemma blankrow (X : Coat T F) (v : Site f→G.Color) (hv : ∀ i,v (S.ratio.embed i)=0) (s : Signed) (p : Rod c f) :
    orientedRow T X.blank.R s p X.blank.V (gradient v)=0 := by
  let A := v ∘ s.act; let a:=gradient A
  unfold orientedRow; rw [show replica S.ratio X.blank.V=(1:Config G f) from funext (fun i=> by unfold replica; split <;> rfl),
    rotated_grad,show pull s 0 X.blank.V=1 from funext (fun i=> by rw [Channel.charge]; split; simp [blank]; rfl),flat_strip, barField]; change Sum.elim _ _ p= _
  rcases p with p|p
  · have he p : faceCurl p (toLog a)=0 := by rw [curl_eq]; simp only [a,gradient]; rw [show p.fst+step p.2.1.1+step p.2.1.2=p.fst+step p.2.1.2+step p.2.1.1 from add_right_comm ..]; abel
    change bareCut _ _ _ (toLog a) p=_; unfold bareCut; split
    next ht => unfold ellCut; simp_rw [he]; simp
    rw [he,smul_zero]
  let g (i:G.ColorIndex) (p : Body 0 f) := (A p.1) i
  have hg i : centered S (g i)=0:= by funext j; dsimp only [centered,g,A,Function.comp_apply]; rw [← S.ratio.signed,hv]; rfl
  have h i : parts G 1 (toLog a) i= Exterior.d 0 f *ᵥ g i:= by
    funext j; obtain ⟨p,rfl⟩:= (poleEquiv f).surjective j
    unfold parts; rw [show poleEquiv f p=pole p from rfl,at_pole]
    exact (d_sites p.fst p.snd (g i)).symm
  have hP j : (probe S *ᵥ parts G 1 (toLog a) j)=0 := by rw [h,root_gradient,hg, Matrix.mulVec_zero]
  change zLin _ (toLog a) 0 _=_; unfold zLin; simp_rw [hP]; simp; exact Or.inr rfl
lemma strata (X : Coat T F) (Y : Coat T H) (p:X.x=Y.x) (t : (↥F.trunks) ≃ ↥H.trunks) (h : P.Funds S T) :
    Y.blank.form * scaleMatrix F H t ℝ G=X.blank.form := by
  obtain ⟨_,_,hk,-⟩:= h.feeds
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro u; let U:= erect G u
  let A:= scaleMatrix F H t ℝ G
  change _ *ᵥ u=X.blank.form*ᵥu
  have hu : A*ᵥ u=stand (surgery F H t U) := by
    rw [consents F H]; funext i; unfold shifts stand
    let L := (EuclideanSpace.proj i.2 (𝕜:=ℝ)).toLinearMap.toAddMonoidHom
    exact congr_fun (add_transport F H t U L) i.1
  have he (F:Forest S.ratio) (X:Coat T F) a : X.blank.lens a=directF F a := by
    ext1 i; unfold Coat.lens directF; rw [no_flat]; split_ifs with ht<;> simp_all
  have hx s i : Y.blank.motion (surgery _ _ t U) (s,i)=X.blank.motion U (s,i) := by
    let v:=directF F U; obtain ⟨a,ha⟩:= SliceRows.linear T X.blank.R hk s i X.blank.V
    unfold Coat.motion; simp only [blank_all,↓reduceIte]
    have hg : Y.blank.lens (surgery F H t U)=v+gradient (aligns H v):= (he H Y _).trans (enwrap ..)
    rw [hg,he F X]; change orientedRow T Y.R s i 1 (v+gradient (aligns H v))=orientedRow T X.R s i 1 v
    rw [show Y.R=X.R from congr_arg till p.symm]; change orientedRow T X.blank.R s i X.blank.V (v+gradient (aligns H v))= orientedRow T X.blank.R s i X.blank.V v; rw [← ha, ← ha,map_add,ha (gradient _),blankrow (F:=F) X _ (aligns_embed H v),add_zero]
  rw [← Matrix.mulVec_mulVec,hu]; funext i; obtain ⟨⟨s,i⟩,j⟩:=i
  rw [← Y.blank.charged_for hk]
  apply Eq.trans _ (X.blank.charged_for hk U ((s,i),j)); unfold stand; rw [hx]
lemma snuggles (X : Coat T F) (Y : Coat T H) (t : (↥F.trunks)≃↥H.trunks) : let A:=scaleMatrix F H t ℝ G
    A.transpose*Y.blank.sleepy*A=X.blank.sleepy := by
  intro A
  have hs (k i : Tubular f G) : (Y.blank.sleepy*A) k i = if k.1∈H.trunks then A k i else 0 := by unfold sleepy; rw [Matrix.diagonal_mul, Y.no_flat]; split_ifs <;> simp_all
  have he (i : Tubular f G) (hi : i.1 ∈ H.trunks) (k) : A i k=(Pi.single k 1 : _→ℝ) ((t.symm ⟨i.1,hi⟩).val, i.2) := by
    rw [← show (A*ᵥ Pi.single k 1) i=A i k from congr_fun (Matrix.mulVec_single_one A k) i,consents F H,shifts,surgery,dif_pos hi]
  ext i j; rw [Matrix.mul_assoc,Matrix.mul_apply]
  by_cases hi : i.1∈F.trunks
  · let p:=t ⟨i.1,hi⟩; let q: Tubular f G :=(p.val, i.2); have ht : q.1∈H.trunks:= p.property
    rw [sum_eq_single q]
    · rw [hs,transpose_apply,if_pos ht, he q ht i,he q ht j]; simp_rw [show ((t.symm ⟨q.1,ht⟩).val,q.2)=i from Prod.ext (congrArg Subtype.val (t.symm_apply_apply _)) rfl]
      by_cases hh:i=j
      · subst j; simp [sleepy,X.no_flat,hi]
      simp [hh,sleepy]
    · intro b hb hz; rw [hs]; split
      next hh=>
        rw [transpose_apply, he b hh i, Pi.single_eq_of_ne ?_,zero_mul]
        rintro he; apply hz; have he': (t.symm ⟨b.1,hh⟩).val=i.1:= congr_arg Prod.fst he
        exact Prod.ext (congr_arg Subtype.val ((t.symm_apply_eq.mp (Subtype.ext he':t.symm ⟨b.1,hh⟩=⟨i.1,hi⟩)).symm.symm)) (show b.2=i.2 from (Prod.ext_iff.mp he).2)
      rw [mul_zero]
    simp
  rw [sum_eq_zero]
  · unfold sleepy; by_cases hp : i=j
    · subst j; simp [no_flat, hi]
    simp [hp]
  intro k hk; rw [hs]; split
  next h => rw [transpose_apply, he k h i,Pi.single_eq_of_ne ?_,zero_mul]; intro ht'; apply hi; rw [← ht']; exact (t.symm _).2
  rw [mul_zero]
lemma unafraid (X : Coat T F) (Y : Coat T H) (p:X.x=Y.x) (h : P.Funds S T) : X.blank.plate.det=Y.blank.plate.det := by
  let t:= tallyF F H; let A:=scaleMatrix F H t ℝ G
  have he : X.blank.plate=A.transpose* Y.blank.plate*A := by
    unfold plate; rw [← strata X Y p t h, transpose_mul,← snuggles X Y t,mul_add,add_mul]; simp only [A,Matrix.mul_assoc]
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]; have hs : A.det*A.det=1:= by
    rw [← sq, ← sq_abs,no_mas F H,one_pow]
  rw [mul_right_comm,hs,one_mul]
lemma expenses (X : Coat T F) (Y : Coat T H) (p:X.x=Y.x) (h : P.Funds S T) (Ñ : ChartRatio G) (b : ℝ) : X.deducted Ñ b=Y.deducted Ñ b := by
  unfold deducted; rw [freed F H, unafraid X Y p h]
lemma overhead_eq (X : Coat T F) (Y : Coat T H) (p:X.x=Y.x) (h : P.Funds S T) (hh:X.V=Y.V) (Ñ : ChartRatio G) (R : Rep G f) : overhead X R Ñ=overhead Y R Ñ := by
  unfold overhead levy; rw [expenses X Y p h,p,hh]
end YM.ConnectedActivityE6.TreeColor
