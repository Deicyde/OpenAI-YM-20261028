import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Payroll
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
import YM.Next.FREE_KERNELS.Signed


/-!
# Price after orientation of inputs (including root shift)
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08  
open Joint Estimate Estimate.Purse  Estimate.Logfee
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n l : Side} {ι : Type} [DecidableEq ι]
namespace Rotate
variable (s : Signed)

def amplify (P : Purse ι (Site n)) (η : ℝ) : Purse ι (Site n) := { P with
  amps := fun i => Real.exp (2*η) * P.amps i
  budget := fun i => mul_nonneg (Real.exp_pos _).le (P.budget i)
  toll := fun i x => P.toll i (s.act x)
  toll_pos := fun i x => P.toll_pos i (s.act x) }

lemma read_norm (i : Axis) (v : Site n) (a : Dir G n) :
    let y := (posDir i).rotate s
    ‖shifts s 0 a (v,coord i)‖=‖a ((y.used (s.act v)).1,coord (y.used (s.act v)).2)‖ := by
  intro y; rw [shifts,ContinuousLinearMap.pi_apply]; dsimp only
  rw [affine,add_zero,show axisEquiv.symm (coord i)=_ from axisEquiv.symm_apply_apply i]; split
  · exact norm_neg _
  rfl
lemma pay_curl (i : PlaqAxes) (v : Site n) (a : Dir G n) :
    ‖faceCurl (v,i) (shifts s 0 a)‖=‖faceCurl (Face.send s 0 (v,i)) a‖ := by
  have hh : faceCurl (v,i) (shifts s 0 a) = turned s i • faceCurl (Face.send s 0 (v,i)) a := by
    ext j
    have he : shifts s 0 a = pulled a s := by
      funext k; unfold shifts pulled; rw [ContinuousLinearMap.pi_apply]; dsimp only; split <;> rfl
    rw [he]
    exact (by
      have h := rotations_d (parts G 1 a j) s v i
      rw [← pigment s n G a j] at h; exact h)
  rw [hh,norm_smul]; rw [Next.Free.turned]; split_ifs <;> norm_num

lemma shorter (p : PlaqAxes) (x : Site n) : separation (s.act x) (Face.send s 0 (x,p)).1 ≤ 2 := by
  unfold Face.send Face.lower; simp only [affine,add_zero,atFace]
  have hx (x : Site n) (a : Step) : separation x (x+if a.neg then a.vec else 0) ≤ 1 := by
    split; exact (Response.by_one ..).1; simp
  apply (separation_triangle _ (s.act x+(if ((posDir p.val.1).rotate s).neg then ((posDir p.val.1).rotate s).vec else 0)) _).trans
  exact Nat.add_le_add (hx _ _) (hx _ _)

lemma shortened (p : PlaqAxes) : Injective (fun i : Site n => (Face.send s 0 (i,p)).1) := by
  intro i j he
  have hh := Face.injective_send s (0:Site n) (a₁:=(i,p)) (a₂:=(j,p)) (Prod.ext he rfl)
  exact congr_arg Prod.fst hh

section fares
variable {P : Purse ι (Site n)} {η : ℝ} (h : tollRate P l η) (he : 0 ≤ η) {d : ι→Dir G n}
include h
omit [DecidableEq ι] in
lemma stays : tollRate (amplify s P η) l η := by
  intro i x y; have hh := h i (s.act x) (s.act y); simp only [Green.wt,separation_signed] at hh; exact hh
include he
omit [DecidableEq ι] in
lemma reindex {C : ℝ} (w : Equiv.Perm (Site n)) {f g : Site n→G.Color} (k : ι)
    (hx : ∀ i, separation (s.act i) (w i) ≤ 2) (hp : ∀ i, ‖f (w i)‖=‖g i‖) (hb : P.Pays {k} f C) : (amplify s P η).Pays {k} g C := by
  let L := Real.exp (2*η)
  have hm i : (amplify s P η).price {k} i* ‖g i‖ ≤ L*(P.price {k} (w i)*‖f (w i)‖) := by
    simp_rw [← hp i,price,Finset.prod_singleton]; rw [← mul_assoc]
    have hh := (enters h he k _ _ _ (hx i)).trans (mul_le_mul_of_nonneg_right (guide_le l 2 η he) (P.toll_pos ..).le)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold amplify L; simpa [mul_comm] using hh
  have ht : (amplify s P η).target {k}=L*P.target {k} := by simp only [target,Finset.prod_singleton]; rfl
  have hl : 0 ≤ L := (Real.exp_pos _).le
  refine ⟨hb.1,fun he i => (hm i).trans ((mul_le_mul_of_nonneg_left (hb.2.1 he _) hl).trans_eq (by rw [ht]; ring)),fun he => ?_⟩
  let x i := P.price {k} i * ‖f i‖
  apply (rless (fun i => mul_nonneg ((amplify s P η).price_pos _ _).le (norm_nonneg _)) hm).trans
  calc
    _ = L*rlen (x ∘ w) := rconstant hl _
    _ = L*rlen x := by rw [rperm]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (hb.2.2 he) hl).trans_eq (by rw [ht]; unfold amplify; dsimp only; ring)
omit h he in
lemma use_bij (y : Step) : Bijective (fun i : Site n => (y.used (s.act i)).1) := by
  rcases y with ⟨a,v|v⟩
  · exact (Signed.actEquiv (R:=Per n) s).bijective
  simp only [Step.used,if_true, sub_eq_add_neg]
  exact ((Signed.actEquiv (R:=Per n) s).toEquiv.trans (Equiv.addRight (-step a))).bijective
omit [DecidableEq ι] in
lemma bonds (hp : Linkbill l P d) : Linkbill l (amplify s P η) (shifts s 0 ∘ d) := by
  intro i j; obtain ⟨k,rfl⟩ := axisEquiv.surjective j
  let y := (posDir k).rotate s
  let F := fun i : Site n => (y.used (s.act i)).1
  have hv : ∀ i : Site n,(y.used i).2=y.dir := by intro i; unfold Step.used; split <;> rfl
  refine reindex s h he (Equiv.ofBijective F (use_bij s y)) i (fun x => ((Response.by_one (s.act x) y).2.trans (by decide))) (fun x => ?_) (hp i (coord y.dir))
  have hh := read_norm s k x (d i); dsimp only at hh; rw [hv] at hh; exact hh.symm
omit [DecidableEq ι] in
lemma bending (hp : Plaque.BendBill l P d) : Plaque.BendBill l (amplify s P η) (shifts s 0 ∘ d) := by
  intro i k; let t (x : Site n) := (Face.send s 0 (x,k)).1
  let w := Equiv.ofBijective t (Finite.injective_iff_bijective.mp (shortened s k))
  have hh j : faceCurl (w j,k.rotate s) (d i)=faceCurl (Face.send s 0 (j,k)) (d i) := rfl
  have hk j : ‖faceCurl (w j,k.rotate s) (d i)‖= ‖faceCurl (j,k) (shifts s (0:Site n) (d i))‖ := by rw [hh,pay_curl]
  exact reindex s h he w (f:=fun x => faceCurl (x,k.rotate s) (d i)) (g:=fun x => faceCurl (x,k) (shifts s (0:Site n) (d i))) i (fun j => shorter s k j) hk (hp i _)
end fares
omit [DecidableEq ι] in
lemma restores {C η : ℝ} {P : Purse ι (Site n)} {x : Site n→ℝ} {k : Finset ι}
    (h : (amplify s P η).Pays k x C) : P.Pays k (x ∘ (fun i => s⁻¹.act i)) (Real.exp (2*η)^k.card*C) := by
  have ht : (amplify s P η).target k=Real.exp (2*η)^k.card*P.target k := by unfold target amplify; simp only
    [Finset.prod_mul_distrib, Finset.prod_const]
  have hp i : P.price k i=(amplify s P η).price k (s⁻¹.act i) := by simp only [price,amplify]; rw [Signed.act_inv]
  have hk : P.cap=(amplify s P η).cap := rfl
  let w (i : Site n) := (amplify s P η).price k i* ‖x i‖
  refine ⟨mul_nonneg (pow_nonneg (Real.exp_pos _).le _) h.1,fun he i => ?_,fun he => ?_⟩
  · calc
      _ = w (s⁻¹.act i) := by unfold w; rw [← hp]; rfl
      _ ≤ _ := (h.2.1 he _).trans_eq (by rw [ht]; ring)
  rw [show (fun i => P.price k i*_)=w ∘ (Signed.actEquiv (R:=Per n) s⁻¹).toEquiv from ?_]
  · rw [rperm]; exact (h.2.2 he).trans_eq (by rw [ht,hk]; ring)
  funext i; unfold w; simp only [Function.comp_apply]; rw [hp i]; rfl
end Rotate
end YM.AnalyticNext.QuarticMatch.Local
