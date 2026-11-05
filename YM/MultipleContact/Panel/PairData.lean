import YM.MultipleContact.Center.Endpoint
import YM.MultipleContact.Panel.TestPrice
import YM.MultipleContact.Tests

/-! Geometry with several separated two-slot operations (orthogonal centroid and normal axes). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.MultipleContact.Panel.PairSet
open Set Function Filter MeasureTheory Table Extraction Ward Spec Bunching Centered Joins Two Script Scene
open scoped ContDiff Classical BigOperators
abbrev Board (b e:ℕ):Type:=(Fin (b+e)→E4) × (Fin b → E4)
def port {b:ℕ}(e:ℕ)(i:Fin b): Lens (Board b e) E4 :=
 let R:= (ContinuousLinearMap.proj (R:=ℝ) i).comp (.snd ℝ _ _)
 let W0: E4→ₗ[ℝ] Board b e := {
     toFun(t:E4):=(0,Pi.single i t)
     map_add' a b := by ext1; exact add_zero _ |>.symm; rw [Prod.snd_add, Pi.single_add]
     map_smul' t a := by ext1; exact smul_zero t |>.symm; simp [Pi.single_smul]
 }
 let W:=LinearMap.toContinuousLinearMap W0
 { read:=R
   put:=W
   take t:=Pi.single_eq_same _ _ }
@[simp] lemma port_read {b:ℕ}(e:ℕ)(i:Fin b)(x): (port e i).read x=x.2 i:=rfl
lemma port_cross {b:ℕ}(e:ℕ)(i j:Fin b)(h:i≠j)(u:E4):(port e i).read ((port e j).put u)=0:=Pi.single_eq_of_ne h _
lemma port_norm {b:ℕ}(e:ℕ)(i:Fin b)(t:E4): ‖(port e i).put t‖≤ ‖t‖:=by
        change max ‖(0:Fin (b+e)→E4)‖ ‖Pi.single (M:=fun _:Fin b=>E4) i t‖≤ ‖t‖
        rw [norm_zero,max_le_iff]; refine ⟨norm_nonneg _,(pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j=>?_)⟩
        by_cases h:j=i; case pos=>rw [h,Pi.single_eq_same]
        rw [Pi.single_eq_of_ne h,norm_zero]; exact norm_nonneg _
@[simp] lemma port_put_left {b:ℕ}(e:ℕ)(i:Fin b)(t:E4):((port e i).put t).1=0:=rfl
@[simp] lemma port_lay_left {b:ℕ}(e:ℕ)(i:Fin b)(x)(y):((port e i).lay x y).1=x.1:=by unfold Lens.lay Lens.off;change 0+(x.1-0)=_; abel
-- Difference normal over 2, in an orthogonal subspace to the centroid axis, giving actual positions z ± y/2. Normal-coordinate prescription uses y (a √2 rescaling of orthonormal length); unit Jacobian with ordinary centroid measure, exactly the two-slot formula.
def jig (y:E4)(i:Fin 2):E4:= if i.val=0 then Two.half y else -Two.half y
@[simp] lemma jig0 (y:E4):jig y 0=Two.half y:=rfl
@[simp] lemma jig1 (y:E4):jig y 1= -Two.half y:=rfl
lemma jig_smooth (i:Fin 2):ContDiff ℝ ∞ (jig · i):=by
      by_cases h:i.val=0
      · simpa [jig,h,half] using contDiff_id.const_smul ((2:ℝ)⁻¹)
      simpa [jig,h,half] using (contDiff_id.const_smul ((2:ℝ)⁻¹)).neg
lemma centroid_formula(z y:E4): z=((2:ℝ)⁻¹) • (z+jig y 0+(z+jig y 1)):=by rw [jig0,jig1,show z+half y+(z+-half y)=z+z by abel,← two_smul ℝ z,smul_smul,inv_mul_cancel₀ (two_ne_zero),one_smul]
lemma difference_formula(z y:E4): (z+jig y 0)-(z+jig y 1)=y:=by simp only [jig0,jig1,half]; module
lemma jig_bound(y:E4)(i:Fin 2):‖jig y i‖≤ ‖y‖:=by dsimp only [jig]; split <;> (try simp only [norm_neg]) <;> exact half_norm y
lemma jig_gap (y:E4) {i j:Fin 2}(h:i≠j):‖jig y i-jig y j‖=‖y‖:=by
        have he := difference_formula 0 y; simp only [zero_add] at he
        by_cases hi:i=0
        · have hh:j=1:=by apply Fin.ext; omega
          rw [hi,hh,he]
        rw [show i=1 by apply Fin.ext;omega,show j=0 by apply Fin.ext;omega,← neg_sub,he,norm_neg]
lemma jig_near {G:Gauge}{B:Register G}{S:Table B}{y:E4}(p:March S)(h:0<‖y‖)(hw:¬∃d D,p=.anchor d D):Nearish 1 p ‖y‖ (jig y):=by
        have he:GapF 1 ‖y‖ (jig y):=⟨fun i j h'=>by rw [jig_gap y h']; linarith,fun i=>(jig_bound y _).trans_lt (by norm_num; linarith)⟩
        refine ⟨?_,he⟩; cases p with
        | anchor d D=> exact (hw ⟨_,D,rfl⟩).elim
        | field d=> trivial
        | raw=> exact ⟨he.1,he.2,fun d D h=>by nomatch h⟩
        | root d D=> exact ⟨he.1,he.2,fun d D h=>by nomatch h⟩
variable {G:Gauge}{B:Register G}{S:Table B}{P:DiffPlan S}
-- Field threshold by the input weights for this labeled word; never recomputed by expanding a detector.
abbrev degree (v:Fin 2→ S.Tag):ℕ:=Bunching.massOf v - 4
def High (v:Fin 2→ S.Tag):Type:= {i:Fin (degree v+1)// 4≤Bunching.massOf v}
abbrev Choice (v:Fin 2 → S.Tag):Type:=Option (High v)
noncomputable instance highFintype(v:Fin 2→S.Tag):Fintype (High v):=show Fintype {i:Fin (degree v+1)// 4≤Bunching.massOf v} by infer_instance
variable (Q:Splitting P)(D:∀ h,Detector S h)
def mode {v:Fin 2→S.Tag}(u:Choice v): March S:=match u with | none=> if 4≤Bunching.massOf v then .root _ (D (degree v)) else .raw | some j=> .field j.val.val
def parcel (v:Fin 2→S.Tag)(z:E4)(y:E4)(w:Choice v):Grammar (Alpha S):=match w with | none=>if 4≤ Bunching.massOf v then Scene.residue S (D (degree v)) v (jig y) z else Scene.packet S v (jig y) z | some j=>Scene.insertion S z (Q.part j.val (degree v) ((D (degree v)).apply v (points (jig y))))
-- NOTE remove optional t/x to avoid compiler ambiguity
variable {b e:ℕ}(v:Fin b→Fin 2→S.Tag)(u:∀i,Choice (v i))(p:Fin e→S.Tag)
abbrev ops:Fin (b+e)→ March S:=Fin.append (fun i=>mode D (u i)) (fun i=>.field ((p i).fst))
abbrev slots:Fin (b+e)→ Fin 2→S.Tag:=Fin.append v (fun i _=>p i)
def soup (y:Fin b→E4):Fin (b+e) → Fin 2→E4:=Fin.append (fun i=>jig (y i)) (fun _ _=>0)
def combine (z:Fin (b+e)→E4)(y:Fin b→E4) :Grammar (Alpha S):= (∏i:Fin b,parcel Q D (v i) (z (i.castAdd e)) (y i) (u i)) * ∏j:Fin e,insertion S (z (j.natAdd b)) (p j).2
-- weighted factors used in this partial proof: any loss δ on unprojected convergent term; η improvement relative to w-1.
def alpha {v:Fin 2→S.Tag}(u:Choice v):ℝ:=match u with | none=> (mode D u).weight v (63/64) | some i=> -(Bunching.massOf v:ℝ)+(i.val:ℕ)-1+1/64
def jetSpec (v:Fin 2→S.Tag)(u:Choice v):ℕ:=match u with | none=>0 | some t=>degree v-t.val.val+1
def effective (v:Fin 2→S.Tag)(u:Choice v):= alpha D u + (jetSpec v u:ℝ)
lemma effective_high (v:Fin 2 →S.Tag)(u:Choice v): (-4:ℝ) < effective D v u :=by
       unfold effective; cases u with
       |none=> unfold alpha jetSpec mode; split_ifs with h
               · dsimp only [March.weight]; rw [Nat.cast_sub h]; push_cast; ring_nf; norm_num
               have hv : (Bunching.massOf v:ℝ) ≤ 3:= by exact_mod_cast Nat.le_of_lt_succ (lt_of_not_ge h)
               dsimp only [March.weight];rw [Nat.cast_zero]; nlinarith
       |some t=> have hw:t.val.val ≤ degree v:=Nat.le_of_lt_succ t.val.isLt
                 unfold alpha jetSpec; push_cast [Nat.cast_sub hw]; rw [Nat.cast_sub t.property]; linarith
end YM.MultipleContact.Panel.PairSet
