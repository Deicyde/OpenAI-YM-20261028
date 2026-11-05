import YM.Dash.Inert

/-!
# Actual quotient consumes distribution uptake
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Function Set Filter MeasureTheory Measure Complex Analysis Extraction Boundary TopologicalSpace Metric
open scoped ContDiff Topology FourierTransform InnerProductSpace BigOperators LineDeriv
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Order} {n : ℕ}

lemma Dzero {f : Points n→ℂ} {x} (p : Points n) (h : f =ᶠ[𝓝 x] 0) : D p f x=0 := by
  rw [Analysis.D, h.fderiv_eq]; exact congr_arg (fun u : Points n→L[ℝ] ℂ => u p) (fderiv_const_apply _)

lemma zone (f : Probe (Points n)) (p : Points n) : (∫ x, Analysis.D p f x)=0 := by
  let F := (∂_{p} f : Probe (Points n))
  have he : (∫ x : Points n, Analysis.D p f x) = (𝓕 F) 0 := by change _=𝓕 (⇑F) 0; simp [scanned,wave]; rfl
  rw [he]
  unfold F; rw [SchwartzMap.fourier_lineDerivOp_eq]
  have ht : HasTemperateGrowth (fun v : Points n => inner ℝ v p) := by fun_prop
  simp [SchwartzMap.smulLeftCLM_apply_apply ht]

lemma compactTest {K : Points n→ℂ} (h : ContDiffOn ℝ ∞ K (conf n)) (a : Test n) (p : Fin n) (i : Axis) :
    a.applyTo (D (Points.direction p i) K) = -(down a p i).applyTo K := by
  let P := Points.direction p i
  let g (x) := a x*K x
  have he : HasCompactSupport g := a.hasCompactSupport.mul_right
  have near {x : Points n} (hp : x∉conf n) : (⇑a) =ᶠ[𝓝 x] 0 := by
    have ho : x∈ (tsupport a)ᶜ := fun H => hp (a.tsupport_subset H)
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds ho] with i hi
    exact image_eq_zero_of_notMem_tsupport hi
  have ha {x : Points n} (hp : x∉conf n) : g =ᶠ[𝓝 x] 0 := (near hp).mono fun i hi =>
    show a i*K i=0 from by rw [show a i=0 from hi]; simp
  have hc : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hh : x∈conf n
    · exact a.contDiff.contDiffAt.mul ((h x hh).contDiffAt ((conf_open n).mem_nhds hh))
    exact contDiffAt_const.congr_of_eventuallyEq (ha hh)
  have ht : ContinuousOn (D P K) (conf n) := ((h.fderiv_of_isOpen (m := 0) (conf_open _) (by exact_mod_cast le_top)).continuousOn).clm_apply continuousOn_const
  have hd x : (D P g x) = a x * D P K x+down a p i x * K x := by
    by_cases hh : x∈conf n
    · unfold Analysis.D g; rw [fderiv_fun_mul]; rotate_left
      · exact a.contDiff.differentiable (by simp) _
      · exact ((h x hh).contDiffAt ((conf_open _).mem_nhds hh)).differentiableAt (by simp)
      rw [_root_.add_apply, _root_.smul_apply, _root_.smul_apply, desc]; simp [Analysis.D,P,mul_comm]
    rw [Test.vanishes a hh, Test.vanishes (down a p i) hh,Dzero P (ha hh),zero_mul,zero_mul,zero_add]
  have hh := zone (he.toSchwartzMap hc) P; change (∫ x,Analysis.D P g x)=0 at hh; simp_rw [hd] at hh
  rw [integral_add (Test.smearing a ht) (Test.smearing _ h.continuousOn)] at hh
  exact eq_neg_of_add_eq_zero_left hh

theorem smooth_point {K H : Points n→ℂ} (h : ContDiffOn ℝ ∞ K (conf n)) (p : Fin n) (i : Axis)
    (he : ContinuousOn H (conf n)) : currents K H p i ↔ EqOn H (D (Points.direction p i) K) (conf n) := by
  have ht : ContinuousOn (D (Points.direction p i) K) (conf n) :=
    ((h.fderiv_of_isOpen (m := 0) (conf_open _) (by exact_mod_cast le_top)).continuousOn).clm_apply continuousOn_const
  unfold currents; simp_rw [← compactTest h]; exact Test.unique_kernel he ht

namespace MonitorOps
variable (Y : MonitorOps C)
variable {H : Live S} (h : Y.Wakes S H)

include h in
lemma null_keep (s : S.Smooth) (hp : S.Symmetric) {d e : ℕ} (hv : d≤ e) {a : C.label d} (hx : a∈S.null d) : Y.keep hv a∈S.null e := by
  have hh : a∈ monitor S H d := (notices S H a).2 ((S.equivalent s hp d a).1 hx)
  apply (S.equivalent s hp _ _).mpr
  apply (notices S H _).1; rw [monitor,Submodule.mem_iInf]
  intro i; change i.core _ H _=0; rw [h.keep d e hv]; exact (Submodule.mem_iInf _).1 hh i

include h in
lemma null_tilt (s : S.Smooth) (hp : S.Symmetric) {d} {a : C.label d} (hx : a∈S.null d) (p : Axis) : Y.tilt d p a∈S.null (d+1) := by
  have hh : a∈ monitor S H d := (notices S H a).2 ((S.equivalent s hp d a).1 hx)
  apply (S.equivalent s hp _ _).mpr ((notices S H _).1 ?_)
  rw [monitor,Submodule.mem_iInf]; intro i; change i.core _ H _=0; rw [h.tilt d p, neg_eq_zero]; exact (Submodule.mem_iInf _).1 hh (pushT i p)

def descends (H : Live S) (h : Y.Wakes S H) (s : S.Smooth) (hp : S.Symmetric) : DiffPlan S := ⟨fun {d e} hx => (S.null d).liftQ ((S.project e).comp (Y.keep hx)) (fun _ hI =>
  (Submodule.Quotient.mk_eq_zero _).2 (Y.null_keep h s hp hx hI)), fun d p => (S.null d).liftQ ((S.project _).comp (Y.tilt d p)) fun _ hI =>
    (Submodule.Quotient.mk_eq_zero _).2 (Y.null_tilt h s hp hI p)⟩

-- expose tag reps
lemma head (S : Table C.book) (hp : S.Symmetric) {n d} (a : C.label d) (w : Fin n → S.Tag) {y}
    (hx : y∈conf (n+1)) : S.useAt S y (Fin.cons ⟨d,S.project d a⟩ w) =
      S.read y (Fin.cons ⟨d,a⟩ (fun i => ⟨(w i).1,S.representative _ (w i).2⟩)) := by
  rw [← S.at_project S hp (fun _ => le_rfl) hx]
  congr; ext1 i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  simp only [Fin.cons_succ, Function.comp_apply]; change w j=⟨(w j).1, S.project (w j).1 (S.representative _ (w j).2)⟩
  rw [S.rep]

lemma readies (s : S.Smooth) (hp : S.Symmetric) : (Y.descends H h s hp).Inclusions S := by
  constructor; intro d e hu B n x hx w
  let L (i : Fin n) : C.book.Token := ⟨(w i).1,S.representative _ (w i).2⟩
  obtain ⟨b,rfl⟩ := S.onto _ B
  change S.useAt S _ (Fin.cons (α := fun _ => S.Tag) ⟨e,S.project e (Y.keep hu b)⟩ w)=_
  rw [head S hp _ w hx,head S hp _ w hx]
  have hb (F : Test (n+1)) := h.keep _ _ hu b (Shot.mk _ 0 (Fin.cons (α:=fun _ => C.book.Token) ⟨d,b⟩ L) F)
  let f (a : C.book.Token) (x : Points (n+1)) := S.read x (Fin.cons a L)
  refine (Test.unique_kernel (K:= f ⟨e,Y.keep hu b⟩) (P:=f ⟨_,b⟩)
    ((S.smooth_read s _).continuousOn) ((S.smooth_read s _).continuousOn)).1 ?_ hx
  intro u
  have he x : update (Fin.cons (α:= fun _ => C.book.Token) ⟨d,b⟩ L) 0 x=Fin.cons x L := by simp
  have ht := hb u; change u.applyTo (fun x => S.read x (update _ 0 (⟨e,_⟩:C.book.Token)))=u.applyTo (fun x => S.read x (update _ 0 _)) at ht
  rw [he,he] at ht; exact ht

lemma tilts (s : S.Smooth) (hp : S.Symmetric) : (Y.descends H h s hp).Derivatives S := by
  constructor; intro d i B n x hx w
  let L (i : Fin n) : C.book.Token := ⟨(w i).1,S.representative _ (w i).2⟩
  obtain ⟨b,rfl⟩ := S.onto _ B
  change S.useAt S _ (Fin.cons (α := fun _ => S.Tag) ⟨d+1,S.project _ (Y.tilt d i b)⟩ w)=_
  rw [head S hp _ w hx]
  let f (a : C.book.Token) (x : Points (n+1)) := S.read x (Fin.cons a L)
  have he := H
  apply Eq.trans ((smooth_point (K:= f ⟨_,b⟩) (H:=f ⟨d+1,Y.tilt d i b⟩)
    (S.smooth_read s _) 0 i (S.smooth_read s _).continuousOn).1 ?_ hx) ?_
  · intro u
    have hb := h.tilt d i b (Shot.mk (L:=C.book) _ 0 (Fin.cons (α:=fun _ => C.book.Token) ⟨d,b⟩ L) u)
    have he x : update (Fin.cons (α:= fun _ => C.book.Token) ⟨d,b⟩ L) 0 x=Fin.cons x L := by simp
    change u.applyTo (fun x => S.read x (update _ 0 _))=-(down u 0 i).applyTo (fun x => S.read x (update (Fin.cons (α:=fun _ => C.book.Token) ⟨d,b⟩ L) 0 _)) at hb
    rw [he,he] at hb; exact hb
  apply GermD
  filter_upwards [(conf_open _).mem_nhds hx] with y hy using (head S hp b w hy).symm
end MonitorOps
end YM.Dash
