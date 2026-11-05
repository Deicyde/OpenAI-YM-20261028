import YM.OPE.Schemes.Read
/-!
# Local differentiation of continuum evaluations
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set MeasureTheory Filter Table Matrix
open scoped Topology BigOperators Classical ContDiff
variable {I J L : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
variable {G:Gauge}{R:Register G}{S:Table R}(A:Table R)(d:I→ℕ)(p: I→ R.Token)(w:J→R.Token)
variable {x:I→ E4} (i:I)(a:Axis)(P: DiffPlan S)

def kindle (i:I) (a:Axis): I→E4:= Pi.single i (basis a)
def deriveLabel : R.Token:= ⟨(p i).1+1, S.representative _ (P.deriv (p i).1 a (S.project _ (p i).2))⟩
def touched := update p i (deriveLabel p i a P)
lemma bumped : sigma (touched p i a P)=sigma p+1:=by
    unfold sigma; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),← Finset.add_sum_erase (f:=fun i=>(p i).1) _ (Finset.mem_univ i),touched,update_self]
    have hx: ∑ x∈ Finset.univ.erase i, ((touched p i a P) x).1= ∑ x∈ Finset.univ.erase i,(p x).1:= Finset.sum_congr rfl fun j hj=> by rw [touched,Function.update_of_ne (Finset.mem_erase.mp hj).1]
    unfold touched at hx; rw [hx]; change (p i).1+1+_=_; omega
lemma open_inj : IsOpen {x:I→E4| Injective x}:=by
    refine isOpen_iff_mem_nhds.mpr fun x hx=>?_ ;
    have hc : (points (x ∘ runNames I))∈ conf _:= runs_conf.mpr hx
    apply (show Continuous fun x:I→E4=> points (x ∘ runNames I) from (by unfold points; fun_prop)).continuousAt.tendsto.eventually ((conf_open _).mem_nhds hc) |>.mono ?_
    exact fun i hi=> runs_conf.mp hi

private def namedAt (I:Type)[Fintype I]: (I→E4)→L[ℝ] Points (Fintype.card I):=
   { toFun:= fun x=> points (x ∘ runNames I), map_add':= fun _ _=> by ext; rfl, map_smul':=fun _ _=> by ext; rfl, cont:= by unfold points; fun_prop }
lemma observeDiff (hx:A.Smooth)(he:Injective x): DifferentiableAt ℝ (fun x:I→E4=> observe A x p) x:=by
    unfold observe worded; simp only [A.readAt]; have hk: namedAt I x∈ conf _:= runs_conf.mpr he
    exact ((((A.smooth_read hx (p ∘ runNames I)) _ hk).contDiffAt ((conf_open _).mem_nhds hk)).differentiableAt (by simp)).comp (f:=namedAt I) x (namedAt I).differentiableAt
private lemma of_chart {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y](x:X)(A:X→L[ℝ] Y) : fderiv ℝ (⇑A) x = A:= A.fderiv
set_option maxHeartbeats 800000 in
lemma observeBump (h:A.Hierarchy)(hx:P.Derivatives A)(hr:A.respects S)(hs:Injective x):
    fderiv ℝ (fun x:I→E4=> observe A x p) x (kindle i a)= observe A x (touched p i a P):=by
    let K:= namedAt I; let j:= (runNames I).symm i; let v:= fun k=> S.classTokens (p (runNames I k)); let p':=P.deriv (p i).1 a (S.project _ (p i).2)
    have hi:runNames I j=i:= Equiv.apply_symm_apply ..; have he: K x∈conf _:= runs_conf.mpr hs
    let F y:= S.useAt A y v; let V (p:I→R.Token) (x:I→E4):= observe A x p; have hF : (V p)=ᶠ[𝓝 x] F ∘ K:= (show ∀ᶠ i in 𝓝 x, Injective i from open_inj.mem_nhds hs).mono fun i H=> observe_exact A p h.laws.toSymmetric hr H
    have hG(p): DifferentiableAt ℝ (fun x=> S.useAt A x p) (K x):=((S.class_smooth A h.smooth p _ he).contDiffAt ((conf_open _).mem_nhds he)).differentiableAt (by simp)
    have h₀: Function.update v j (S.classTokens (p i))=v:=by rw [show S.classTokens (p i) = v j from (by unfold v; rw [hi])]; exact Function.update_eq_self ..
    have h₁: Function.update v j ⟨_,p'⟩ = fun k=> S.classTokens ((touched p i a P) (runNames I k)):=by
       funext k; by_cases hk:k=j; subst k
       · rw [update_self,hi,touched,update_self]; unfold classTokens deriveLabel; rw [rep]
       rw [update_of_ne hk,touched,update_of_ne (show runNames I k≠i from (by rw [← hi]; exact (runNames I).injective.ne hk))]
    change ((fderiv ℝ (V p) x) _) = _; rw [hF.fderiv_eq, fderiv_comp x (hG _) (K.differentiableAt), (show fderiv ℝ K x=K from of_chart x K), ContinuousLinearMap.comp_apply]
    have hh:= P.derivative_slot hx h.laws.toSymmetric h.smooth he j v (S.project _ (p i).2) a; rw [h₀,h₁] at hh
    rw [observe_exact A _ h.laws.toSymmetric hr hs, show K (kindle i a)=Points.direction j a from ?_]; exact hh.symm
    ext1 b; by_cases h:b=j
    · subst b; change Pi.single i (M:=fun _=>E4) (basis a) ((runNames I) j)=_; rw [hi]; simp [Points.direction]
    let f:= runNames I; have hi:f b≠i:=hi ▸ f.injective.ne h;
    change Pi.single i (M:=fun _=>E4) (basis a) (f b) = _; simp [hi,h,Points.direction, PiLp.single_apply]
variable {y:J→ E4}
def besideLinear (I J:Type)[Fintype I][Fintype J] : (I→E4) →L[ℝ] (I⊕J→ E4):=
   { toFun:= fun x=>beside x 0
     map_add' := fun x y => funext fun i=> by cases i <;> simp
     map_smul' := fun c v => funext fun i=> by cases i <;> simp
     cont := continuous_pi fun i=> by cases i; exact continuous_apply _; exact continuous_const }
lemma beside_derive : HasFDerivAt (fun x:I→E4=> beside x y) ((besideLinear I J)) x:= by
    rw [show (fun x:I→E4=>beside x y)=(fun x:I→E4=>besideLinear I J x+beside 0 y) from funext fun x=> funext fun i=> by cases i <;> simp [besideLinear]]
    exact ((besideLinear I J).hasFDerivAt).add_const _
lemma beside_touches (i:I)(a:Axis) : touched (beside p w) (.inl i) a P= beside (touched p i a P) w:= by
    funext j; rcases j with j|j
    · by_cases h:j=i; subst j; · simp only [touched,update_self,beside_left]; rfl
      simp [touched,h]
    simp [touched]
lemma under_read (h:A.Hierarchy)(hx:P.Derivatives A)(hr:A.respects S)(hs:Injective (beside x y)) :
    let F:=fun (p:I→R.Token) (x:I→E4)=> observe A (beside x y) (beside p w); DifferentiableAt ℝ (F p) x ∧ ∀ i a, fderiv ℝ (F p) x (kindle i a)= F (touched p i a P) x:=by
    let g(x):= observe A x (beside p w); have he:DifferentiableAt ℝ g (beside x y):= observeDiff _ _ h.smooth hs
    intro F; refine ⟨he.comp (f:=fun x:I→E4=> beside x y) x beside_derive.differentiableAt,fun i a=> ?_⟩; have hf: (besideLinear I J) (kindle i a)=kindle (Sum.inl i) a := by ext1 j; rcases j with j|j; by_cases h:i=j <;> simp [besideLinear,kindle,h,Pi.single_apply,eq_comm]; simp [besideLinear,kindle,Pi.single_apply] -- edit Ne
    rw [(show fderiv ℝ (F p) x=(fderiv ℝ g (beside x y)).comp (besideLinear I J) from (he.hasFDerivAt.comp (f:=fun x:I→E4=>beside x y) x beside_derive|>.fderiv)),ContinuousLinearMap.comp_apply,hf]; unfold g; rw [observeBump A (beside p w) _ _ _ h hx hr hs, beside_touches]
end YM.OPE
