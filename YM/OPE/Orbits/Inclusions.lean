import YM.OPE.Orbits.System

/-! Label invariance, unit and exact inter-stage readout laws for the
intrinsic coefficient system. Any inclusion used here is in the actual
ordered field table, not a hypothetical associated grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits.Reader
open Function Set Filter MeasureTheory Table Extraction
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{ρ:S.RealSpin}{X:S.Rotation}{I:Type}[Fintype I]{d:I→ℕ}
    (R:Reader Q X ρ)

variable (f:(I→L.Token)→ℂ)
private lemma soul {x:I→L.Token}{y:I→L.Token} (h0 : (fun i=> (x i).fst) ≤ fun i=> (y i).fst) (he : ∀ i:I, Q.rise (h0 i) (S.project _ (x i).snd) = S.project _ (y i).snd) (hf: ∀ i y', f (Function.update y' i (x i))=f (Function.update y' i (y i))) : f x=f y:=by
     let g(s:Finset I)(i:I):= if i∈s then x i else y i
     have hid (s:Finset I): f (g s)= f y:=by
         induction s using Finset.induction_on with
         | empty=> simp_rw [g,Finset.notMem_empty,ite_false]
         | @insert i b hi ih=>
              have h':∀j,j≠i→ g (insert i b) j=g b j:=fun j he=>by simp [g,he]
              rw [show g (insert i b) = update (g b) i (x i) from ?_,hf,← ih]; apply congr_arg
              · apply funext; intro j; by_cases hh : j=i; swap; exact update_of_ne hh ..
                subst j; simp [g,hi]
              funext j; by_cases hh : j=i; subst j; · simp [g,update_self]
              rw [update_of_ne hh,h' j hh]
     rw [← hid Finset.univ]; simp [g]
include R
variable {h:I→ℕ}(h0: d≤ h) (x:I→E4)(o:E4) (n:ℕ)(v:Labels S d)
private lemma shadow_inclusion : shadowOld R.port n x o v= shadowOld R.port n x o (fun i=>Q.rise (h0 i) (v i)) := by
    let p(i):=names (d:=d) v i; let q(i):=names (d:=h) (fun i=>Q.rise (h0 i) (v i)) i
    have ht:∀ i:I, Q.rise (h0 i) (S.project _ (p i).snd) = S.project _ (q i).snd:=by intro i; unfold p q names; erw [S.rep,S.rep]
    refine Finset.sum_congr rfl (fun j hj=> congr_arg (· • R.port.loaded j n) (soul (Q:=Q) (fun z=> R.port.ope j x z o) (x:=p) (y:=q) h0 ht (fun i y=> ?_)))
    exact Prescription.respectsLabel R.port y R.spans R.continuum.laws.toSymmetric R.lifts i _ (ht i) j |>.symm
private lemma average_inclusion :averageV R.port X n x o v=averageV R.port X n x o (fun i=> Q.rise (h0 i) (v i)) :=by
    unfold averageV; split; swap; rfl
    apply integral_congr_ae; refine Eventually.of_forall fun i=>?_ ; apply congr_arg (X.act _ i)
    have he:(roll X i⁻¹ (fun j=> Q.rise (h0 j) (v j)))=(fun j=>Q.rise (h0 j) ((roll X i⁻¹ v) j)):=funext (fun _=>R.law.filtered ..)
    rw [he]; apply shadow_inclusion R h0
lemma fresh_inclusions : R.fresh n x o (fun i=>Q.rise (h0 i) (v i))=R.fresh n x o v:=by
    show R.knife n _ = R.knife n _
    rw [checkValue,checkValue] -- after show lacks fresh? adjust
    have hb:bar ρ (fun i=>Q.rise (h0 i) (v i))=fun i=>Q.rise (h0 i) (bar ρ v i):=funext fun i=> R.stands.realInc ..
    rw [hb, average_inclusion R h0 x o n v,average_inclusion R h0 x o n (bar ρ v)]
lemma inclusions (i:R.channels n): R.coef n i x v o=R.coef n i x (fun i=>Q.rise (h0 i) (v i)) o:=by
    apply congrArg (fun z:R.stratum n=> (R.basis n).repr z i); exact Subtype.ext ((R.fresh_inclusions ..)|>.symm)

variable (m:ℕ)(z:E4)
private lemma token_unit {x':I→L.Token}{p:L.Token} (hp:(S.project p.fst p.snd)=S.unit p.fst)(i:Mode Q)
    (hi:∀ e∈ (R.port.sheet i).support,Injective (beside (away (beside (sole z) x) o) (bearing e))) : R.port.ope i (beside (sole z) x) (beside (sole p) x') o= R.port.ope i x x' o:=by
      let a:=beside (sole p) x'
      have hr := Prescription.respectsLabel (p:=p) (x:=beside (sole z) x) (z:=o) R.port a R.spans R.continuum.laws.toSymmetric R.lifts (.inl ()) (v':=L.one p.fst) (le_refl _) (show Q.rise (d:=p.fst) (p.fst.le_refl) (S.project _ _)=S.project _ _ from ?_) i
      swap; exact (Q.arrival R.continuum.laws.toSymmetric R.lifts _).trans hp
      symm; calc
         _ = R.port.ope i _ _ _:= (OPE.unit_words R.port R.continuum x' i p.fst hi).symm
         _ = R.port.ope i (beside (sole z) x) (@update _ _ (Classical.decEq _) a (.inl ()) (L.one p.fst)) o:=congr_arg (fun v:Unit⊕I→ L.Token => R.port.ope i (beside (sole z) x) v o) (funext (fun j=>?_))
         _ = _ := hr
         _ = _ :=congr_arg (fun v:Unit⊕I→ L.Token=>R.port.ope i (beside (sole z) x) v o) (funext (fun j=>?_))
      · rcases j with j|j; · cases j; symm; apply @update_self (Unit⊕I) (fun _=>L.Token) (Classical.decEq _)
        symm; apply @update_of_ne _ (fun _ => L.Token) (Classical.decEq _) _ _ Sum.inr_ne_inl
      rcases j with j|j; · cases j; apply @update_self (Unit⊕I) (fun _=>L.Token) (Classical.decEq _)
      exact @update_of_ne (Unit⊕I) (fun _=>L.Token) (Classical.decEq _) _ _ Sum.inr_ne_inl _ _

lemma average_unit (hm:orbitMargin R.port m (beside (sole z) x) o): averageV R.port X m (beside (sole z) x) o (stages (sole (S.unit n):Labels S (fun _:Unit=> n)) v)=averageV R.port X m x o v:=by
      have hv:orbitMargin R.port m x o:=by
        intro i hi k e he; let f:I⊕Fin e.n → (Unit⊕I)⊕Fin e.n:=Sum.map Sum.inr id
        let Z:= beside (away (Ortho.move k ∘ beside (sole z) x) (Ortho.move k o)) (bearing e)
        have hf:Injective f:=?_ -- cases
        rw [show beside (away (Ortho.move k ∘ x) _) _=Z ∘ f from funext fun j=> by cases j<;>rfl]
        exact (hm i hi k e he).comp hf
        rintro (j|j) (q|q) e <;> simp only [f,Sum.map_inl,Sum.map_inr,id_eq,Sum.inl.injEq,Sum.inr.injEq] at * <;> simp_all
      unfold averageV; rw [if_pos hm,if_pos hv]; apply integral_congr_ae; refine Eventually.of_forall fun k=> ?_
      apply congr_arg (X.act m k); refine (Finset.sum_congr rfl fun i hi=> ?_); apply congr_arg (· • _);
      have hz: Ortho.move k⁻¹ ∘ beside (sole z) x=beside (sole (Ortho.move k⁻¹ z)) (Ortho.move k⁻¹ ∘ x):=funext fun j=>by cases j <;> rfl
      let p' := names (d:=fun _:Unit=>n) (roll X k⁻¹ (sole (S.unit n))) ()
      have hp:names (roll X k⁻¹ (stages (sole (S.unit n):Labels S (fun _:Unit=>n)) v))=beside (sole p') (names (roll X k⁻¹ v)):=funext fun j=>by cases j <;> rfl
      change R.port.ope _ (Ortho.move k⁻¹ ∘ beside (sole z) x) _ _ = _
      rw [hz,hp]; exact R.token_unit (Ortho.move k⁻¹ ∘ x) _ _ (by unfold p' names; erw [S.rep]; exact R.law.identity ..) i (hz ▸ hm i hi k⁻¹)
lemma fresh_unit (hm:orbitMargin R.port m (beside (sole z) x) o): R.fresh m (beside (sole z) x) o (stages (sole (S.unit n):Labels S (fun _:Unit=> n)) v)=R.fresh m x o v:=by
      apply congrArg (R.knife m); rw [checkValue,checkValue,show bar ρ (stages _ v) = stages (sole (S.unit n):Labels S (fun _:Unit=>n)) (bar ρ v) from ?_,R.average_unit ..,R.average_unit ..]
      any_goals exact hm
      all_goals funext j; cases j <;> simp [bar,stages,sole]
      all_goals first | exact @Table.conj_unit _ _ S ρ n | rfl
end YM.OPE.Orbits.Reader
