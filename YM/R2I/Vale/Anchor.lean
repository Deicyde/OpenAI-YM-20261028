import YM.AnalyticBridge.VERIFIED_RESET_STEP.Isotropy
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Calculus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet
/-!
 # Repair Projection currency across widened alias

 Real anchor independence (only for ALL nonwrapping): express projection a a as linear functional Plane on the FULL Θ torus reading, by exact finite Ward (no derivative costs). Hessian at flat never reads seam issues. This applies to movement of the ENTIRE bouquet & choir merged with Θ-houses. Not licensed for arbitrarily resized winding marks.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Averaging.Anchor
open Function Filter Set Lattice Wilson RG StressFlux Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}
-- Metric dot independent of anchor
lemma op (o x y : Site n) (h: 10*separation x o < n.val) (hp: 10*separation y o < n.val) (a : Axis) : coord y x a= coord o x a - coord o y a:= by
  have he : lift (x-y)=lift (x-o)-lift (y-o) := lift_eq_iff.mpr ⟨by rw [map_sub,wrap_lift,wrap_lift]; abel, fun i=>by
    have h' : (lift (x-o) i).natAbs ≤ separation x o:=component_le (x-o) i; have h₁ : (lift (y-o) i).natAbs ≤ separation y o:=component_le (y-o) i; rw [Pi.sub_apply]; omega⟩
  simp [coord,he]

abbrev lamp (a : PlaqAxes) (x : Site n) : Dir G n:= Pi.single (x,a.val.2) (spike G)
abbrev wallplate (a : PlaqAxes) (n : Side) : Dir G n:= ∑ x,lamp a x
lemma offsite (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) (a:PlaqAxes) (x:Site n) (hx:x∉X) (v:Dir G n) : logHessian f (lamp a x) v=0:= by
  refine Eq.trans (hessian_agrees hG h (b:=0) (fun i hi _=> ?_) (d:=v) (fun _ _ _=>rfl)) ?_; swap; · simp [hessian_eq]
  exact Pi.single_eq_of_ne (show i≠(x,a.val.2) from fun he=> hx ((show i.1=x from congr_arg Prod.fst he) ▸ hi)) _

-- Both roots and α shelves differ. plane collects over EVERY link-to-link kernel but uses displacement L_native.
def plane (a : PlaqAxes) (f : Pot G n) := -(1/2:ℝ)* ∑ i : Site n,∑ j, (coord i j a.val.1)^2*logHessian f (lamp a i) (lamp a j)
variable {g:G.Simple}
private lemma wall_aff (o : Site n)(a : PlaqAxes): (⟨fun i=>if i=a.val.2 then spike G else 0,0⟩:LinearJet G).field o= wallplate a n:= by
  ext1 i; simp only [wallplate,LinearJet.field,Pi.zero_apply,smul_zero,sum_const_zero,add_zero,Finset.sum_apply]
  rcases i with ⟨x,y⟩; by_cases h:y=a.val.2; · subst y; simp [lamp,Pi.single_apply]
  simp [lamp,h]
lemma planar (hG:G.Simple)(hn : 4≤n.val) (A : RegularAddress n) (a:PlaqAxes) (ha : Nonwrapping (expand A) A.site) {f:Pot G n} (h:p.Regular A.support f) : projection A f a a=plane a f:= by
  let X := A.support; let o:=A.site
  have hp: Nonwrapping X o:= fun i hi=> ha i (mem_union_left _ hi)
  let V:= Dir G n; let u: LinearJet G:= ⟨fun i=>if i=a.val.2 then spike G else 0,0⟩
  have h0: u.positive=0:= by ext1 i; simp [u,LinearJet.positive,LinearJet.curl]; -- uses dot
  let g (i j : Site n):= logHessian f (lamp a i) (lamp a j)
  have h1 i : ∑ j, g j i=0 := by
    obtain ⟨s,hs⟩:= u.gradient_agrees hp hn h0; rw [wall_aff] at hs -- maybe delta
    unfold g; simp_rw [hessian_eq]; rw [← _root_.sum_apply,← map_sum, ← hessian_eq]
    exact (hessian_agrees hG h (a:=gradient s) (b:=wallplate a n) hs (c:=lamp a i) (d:=lamp a i) (fun _ _ _=>rfl)).symm.trans (hessian_gradient hG h s _)
  have h2 i : ∑ j, g i j=0:= by rw [show ∑ j,g i j=∑ j,g j i from (Finset.sum_congr rfl fun j _=> hessian_symm h ..), h1]
  let x (i : Site n) := coord o i a.val.1
  have hx (i j): (coord i j a.val.1)^2*g i j=(x j-x i)^2*g i j:= by
    by_cases he:i∈X; swap; · rw [show g i j=0 from offsite hG h a i he _,mul_zero,mul_zero]
    by_cases ht:j∈X; swap; · rw [show g i j=0 from (hessian_symm h _ _).trans (offsite hG h a j ht _),mul_zero,mul_zero]
    rw [op o _ _ (hp j ht) (hp i he)]
  let W:=wedge a (spike G)
  have he : W.field o=∑ i,x i • lamp a i:= by
    funext e; obtain ⟨i,j⟩:=e; unfold W; rw [wedge_field]; by_cases hh:j=a.val.2; · subst j; simp [lamp,Pi.single_apply,x,Finset.sum_apply,smul_ite]
    simp [lamp,x,Finset.sum_apply,hh,Ne.symm hh]
  rw [projection,if_pos ha]; change logHessian f (W.field o) (W.field o)= (-_:ℝ) * (∑ i, ∑ j, _*g i j); rw [he]
  have hl : logHessian f (∑ i,x i • lamp a i) (∑ i,x i • lamp a i)= ∑ i, ∑ j, x i*(x j*g i j):= by
    simp only [hessian_eq,map_sum,map_smul,_root_.sum_apply,smul_apply,smul_eq_mul, Finset.mul_sum]
    simp_rw [← hessian_eq]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> congr_arg (fun z => x i*(x j*z)) (hessian_symm h ..)
  simp only [hx,hl]; -- use double sum distribute
  have hf i : ∑ j, x i ^ 2 * g i j=0 := by rw [← Finset.mul_sum,h2,mul_zero]
  have hr j : ∑ i, x j ^2 * g i j =0:= by rw [← Finset.mul_sum,h1,mul_zero]
  simp only [show ∀ i j,(x j-x i)^2*g i j=x j^2*g i j+x i^2*g i j-2*(x i*(x j*g i j)) from fun i j=> by ring, Finset.sum_sub_distrib,Finset.sum_add_distrib,hf,add_zero,← Finset.mul_sum]
  rw [Finset.sum_comm (f:=fun (i j : Site n)=> x j^2*g i j)]; simp_rw [hr,Finset.sum_const_zero]; ring

lemma projectedNull (f : Pot G n)(c:ℝ) (hf:f=Function.const _ c)(x:RegularAddress n)(b:PlaqAxes) : projection x f b b=0:= by
  unfold projection; split; next h=> rw [hf]; exact hessian_zero c _ _
  rfl
lemma germ_coach (f g:Pot G n) (h : VerifiedReset.germ f=ᶠ[𝓝 0] VerifiedReset.germ g)(a:PlaqAxes) : plane a f=plane a g:=by
  unfold plane; apply congr_arg; refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=> ?_)); apply congr_arg; unfold logHessian; rw [show iteratedFDeriv ℝ 2 (fun x=> f (increment 1 x)) 0=_ from (h.iteratedFDeriv ℝ 2).eq_of_nhds]; rfl
lemma plane_add {f g:Pot G n}(h:p.Regular X f)(ht:p.Regular X g)(a:PlaqAxes): plane a (f+g)= plane a f+plane a g := by
  have he (x y : Dir G n): logHessian (f+g) x y=logHessian f x y+logHessian g x y := by
    change iteratedFDeriv ℝ 2 (VerifiedReset.germ f+VerifiedReset.germ g) 0 _ = _
    rw [iteratedFDeriv_add_apply (germ_diff h) (germ_diff ht)]; rfl
  simp_rw [plane,he,mul_add,sum_add_distrib,mul_add]
lemma plane_zero (c:ℝ)(a:PlaqAxes): plane (G:=G) (n:=n) a (Function.const _ c) = 0 := by
  unfold plane; simp_rw [show ∀ (u v: Dir G n),logHessian (Function.const _ c) u v=0 from hessian_zero c,mul_zero,sum_const_zero,mul_zero]
lemma plane_sum (a:PlaqAxes){ι:Type} (s:Finset ι) (f : ι → Pot G n)(h:∀ i∈s,p.Regular X (f i)) : plane a (∑ i∈s,f i)=∑ i∈s, plane a (f i):= by
  induction s using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; exact plane_zero 0 a
  | @insert i s hi ih =>
    have hs i (hi:i∈s) := h i (mem_insert_of_mem hi)
    rw [sum_insert hi,sum_insert hi,plane_add (h i (mem_insert_self ..)) (PhysicalNext.Repeat.Meadow.regularA s hs), ih hs] -- dependent HE
end YM.AnalyticBridge.VerifiedReset.Averaging.Anchor
#print axioms YM.AnalyticBridge.VerifiedReset.Averaging.Anchor.planar
