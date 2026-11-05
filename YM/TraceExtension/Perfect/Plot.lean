import YM.TraceExtension.Perfect.Alight

/-!
# Relief rack for rectangular J/Y input. Color evaluation exact at harmonic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f:Side}{G:Gauge} (S:StepData c f) (p:PathData G)

abbrev arrange {k:Side} (e: Site k) (i : Lines G k 1):= separation i.1 e
abbrev arranger {k:Side} (e:Site k)(i:pairA G k):= Sum.elim (arrange e) (arrange e) i
-- apply and rebasing
lemma stamp_zero (t:S.Choices)(H:Link G c→ Stationary.Joint G c f)(h:H 0=1): stampA S t H 0=0:= by unfold stampA; simp [h]

def duet (i:Type)[Fintype i] [DecidableEq i] := True
-- stamp derivative transposes
lemma dot_predict {H:Link G c → Stationary.Joint G c f} (t:S.Choices)(h:S.patch.Branches S.kernel G) {pclip:Clip}
    (hx:Thaw H 0)(hv:H 0=1) (hz: Stationary.Teller S t pclip p 1 (1:Stationary.Joint G c f))
    (a: pairA G f) (w:Acr G c):
    fderiv ℝ (stampA S t H) 0 w a=match a with
    | .inl v=> fderiv ℝ (fun x => content (H x).1) 0 (bite G c w).1 v
    | .inr v=>∑ i:Lines G c 1, uniformM (Precision.mean S) (desk v) i * w (.inr i):=by
    let k :=fun i => fderiv ℝ (stampA S t H) 0 w i
    let U : Acr G c→L[ℝ] Link G c := ContinuousLinearMap.fst _ _ _ ∘L (bite ..).toContinuousLinearMap
    let Z (j:Lines G f 1)(i:Lines G c 1)(x:Acr G c):= shuttle S t (H (U x)) (input G c (U x)) (desk j) i*x (.inr i)
    have hh(j:Lines G f 1)(i:Lines G c 1): ContDiffAt ℝ ω (fun x:Acr G c=> shuttle S t (H (U x)) (input G c (U x)) (desk j) i) 0:=by
       apply contDiffAt_pi.mp (steering t h (fun x:Acr G c=> desk j) contDiffAt_const (Thaw.comp (w:=U) (g:=H) (?_) U.contDiff.contDiffAt) _ (Army.powL U.contDiff.contDiffAt))
       rotate_left; · rw [Function.comp_apply,map_zero,hv]
       rw [map_zero]; exact hx
    have hy:= hx.1.logL (show (H 0).1=1 from congr_arg Prod.fst hv)
    have hA : ContDiffAt ℝ ω (stampA S t H) 0:=by
       refine contDiffAt_pi.mpr fun j=>?_ ; cases j with
       | inl j=> apply contDiffAt_pi.mp (ContDiffAt.comp (g:=fun x=> content (H x).1) _ (map_zero U |>.symm ▸ hy) U.contDiff.contDiffAt)
       | inr j=> simp_rw [stamp_entry]; exact ContDiffAt.sum fun i _=> (hh j i).mul (by fun_prop)
    have he(i:pairA G f): fderiv ℝ (stampA S t H) 0 w i=fderiv ℝ (fun x => stampA S t H x i) 0 w:=by
       let L:= ContinuousLinearMap.proj (φ:=fun _: pairA G f=>ℝ) (R:=ℝ) i; change _=fderiv ℝ (L ∘ stampA S t H) 0 w; rw [fderiv_comp _ L.differentiableAt (hA.differentiableAt (by simp)),L.fderiv];rfl
    cases a with
    | inl a=> rw [he]; let V:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _: Lines G f 1=>ℝ) a); let K:= fun x=>content (H x).1
              change fderiv ℝ ((V ∘ K) ∘ U) 0 w = _
              rw [fderiv_comp 0 (by rw [map_zero]; exact V.differentiableAt.comp 0 (hy.differentiableAt (by simp))) U.differentiableAt,U.fderiv,map_zero,fderiv_comp 0 V.differentiableAt (hy.differentiableAt (by simp)),V.fderiv]; rfl
    | inr a=> simp_rw [he (Sum.inr a),stamp_entry]
              rw [fderiv_fun_sum ?_, _root_.sum_apply]; rotate_left
              · intro i _; exact (hh a i).differentiableAt (by simp) |>.mul ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:pairA G c=>ℝ) (Sum.inr i)).differentiableAt)
              apply Finset.sum_congr rfl; intro i _; let K:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:pairA G c=>ℝ) (Sum.inr i)
              let W(x):=shuttle S t (H (U x)) (input G c (U x)) (desk a) i
              change fderiv ℝ (W * (fun z=> K z)) 0 w=_
              rw [fderiv_mul (hh a i|>.differentiableAt (by simp)) K.differentiableAt,_root_.add_apply, K.fderiv]
              simp only [W,Pi.zero_apply,map_zero,zero_smul,zero_add, hv,input_zero]; rw [shuttle_zero t h hz]; simp [K]

end YM.Trace.Perfect
