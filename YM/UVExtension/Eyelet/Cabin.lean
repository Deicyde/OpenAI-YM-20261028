import YM.UVExtension.Eyelet.Arch
/-! address-lane re-index and merge. All proofs for aggregate K retain alias list.Not post hoc repr. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert BoundedContinuousFunction
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ} {F:Frame G d} {H: Hol G} {p: BudgetPoint}{R:Rep G n} {ι:Type}
section choice
variable {E:Type} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℂ E] {U:Type}{X:U→Type}
    [∀ i,NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)] {f:(i:U)→ X i→L[ℂ] E} {c:ℝ}
lemma tribe (h:∀ i v, ‖f i v‖≤ c*‖v‖) : ∃ L:(lp X 1)→L[ℂ] E, ∀ v, NormSum (fun i=>f i (v i)) (L v)∧‖L v‖ ≤ c*‖v‖:=by
   let F (v:lp X 1):E:= ∑' i,f i (v i); have hm(v:lp X 1) := insured _ (fun i x=> f i x) v (fun i=>h i _)
   let k:lp X 1 →ₗ[ℂ] E := {
       toFun:=F
       map_add':=fun x y=> by
          have he i: f i ((x+y) i)=f i (x i)+f i (y i):=map_add (f i) _ _
          unfold F; simp_rw [he]; exact (hm x).1.2.summable.tsum_add ((hm y).1.2.summable)
       map_smul':=fun a x=>by
          have he i: f i ((a • x) i)=a • f i (x i):=map_smul (f i) _ _
          unfold F; simp_rw [he]; exact ((hm x).1.2.summable.tsum_const_smul a) }
   exact ⟨k.mkContinuous c (fun v=> (hm v).2),hm⟩
end choice
variable (H p d)
-- reindex by injection on natural positions
private def lime (e : ℕ ↪ ℕ) (i: Eyelet.Slot n) (x:Gondola d H i.1 p) : Roc d H n p:= lp.single 1 (i.1,e i.2) x

def moverL (e :ℕ↪ℕ) (i:Eyelet.Slot n) : Gondola d H i.1 p →L[ℂ] Roc d H n p:= lp.singleContinuousLinearMap ℂ (fun i:Eyelet.Slot n =>Gondola d H i.1 p) 1 (i.1,e i.2)
lemma madeL (e:ℕ↪ℕ) (i:Eyelet.Slot n) (x:Gondola d H i.1 p): ‖moverL (d:=d) H p e i x‖= ‖x‖ := lp.norm_single (E:=fun i:Eyelet.Slot n=> Gondola d H i.1 p) (p:=1) (by simp) (i.1,e i.2) x

lemma ducts (e:ℕ↪ℕ) : ∃ L:Roc d H n p→L[ℂ] Roc d H n p, ∀ v, NormSum (fun i=> moverL d H p e i (v i)) (L v)∧ ‖L v‖≤1*‖v‖ := tribe (fun i x=> (madeL d H p e i x).le.trans ((one_mul ..).symm.le))

def duct (n:Side) (e:ℕ↪ℕ): Roc d H n p→L[ℂ] Roc d H n p:=(ducts d H p e).choose
lemma duck (e:ℕ↪ℕ)(k:Roc d H n p):‖duct d H p n e k‖ ≤ ‖k‖ :=((ducts d H p e).choose_spec k).2.trans (one_mul _|>.le)
lemma mote (e:ℕ↪ℕ) (i:Eyelet.Slot n) (x:Gondola d H i.1 p) : moverL d H p e i x=lp.single 1 (i.1,e i.2) x:=rfl
set_option quotPrecheck false
lemma ages (e:ℕ↪ℕ) (v:Roc d H n p) (X:Region n) (i:ℕ) : duct d H p n e v (X,e i)=v (X,i):=by
   let t:= moverL (n:=n) d H p e; let T:= duct d H p n e
   have h:= ((lp.evalCLM ℂ _ 1 (X,e i))).hasSum (((ducts d H p e).choose_spec v).1.2)
   change HasSum _ (T v (X,e i)) at h
   refine h.tsum_eq.symm.trans ((tsum_eq_single (X,i) ?_).trans (show t (X,i) (v (X,i)) (X,e i)=v (X,i) from lp.single_apply_self (E:=fun i:Eyelet.Slot n=> Gondola d H i.1 p) 1 (X,e i) _))
   intro j hj; have he:(X,e i) ≠ (j.1,e j.2):= fun h=> hj (Prod.ext (Prod.mk.inj h |>.1.symm) (e.injective (Prod.mk.inj h|>.2.symm)))
   change lp.single (E:=fun i:Eyelet.Slot n=> Gondola d H i.1 p) 1 (j.1,e j.2) (v j) (X,e i)=_; simp [Pi.single_eq_of_ne he]
lemma off (e:ℕ↪ℕ) (v:Roc d H n p)(i:Eyelet.Slot n)(h:i.2∉Set.range e): duct d H p n e v i=0 :=by
   let t:= moverL (n:=n) d H p e; let T:= duct d H p n e; have hb:= ((lp.evalCLM ℂ _ 1 i)).hasSum (((ducts d H p e).choose_spec v).1.2)
   refine hb.tsum_eq.symm.trans ((tsum_congr ?_).trans tsum_zero); intro j
   change lp.single (E:=fun i:Eyelet.Slot n=> Gondola d H i.1 p) 1 (j.1,e j.2) (v j) i=0; simp [Pi.single_eq_of_ne (show i≠(j.1,e j.2) from fun he=> h ⟨_,congr_arg Prod.snd he|>.symm⟩)]

def aisleN (e:ℕ≃ι×ℕ) (i:ι): ℕ↪ℕ:= (⟨fun j=>(i,j),fun _ _ hx=>Prod.mk.inj hx|>.2⟩ : ℕ ↪ι×ℕ).trans e.symm.toEmbedding
variable {H d p}
section water
variable (e:ℕ≃ι×ℕ) (P:ι→ Coefficient F n){v:ℝ}(h:∀ i, Eligible (P i) H R v) (hZ:Eligible (Extra.Histories.merge e P) H R v) {t:ι→ℝ}(hw:∀ i,(P i).remBound 0 R v (t i))(he:Summable t)
include he hw
lemma blazeK : NormSum (fun i=> (h i).tollK) hZ.tollK:=by
   let f i:=(h i).tollK; have hs:Summable (fun i=> ‖f i‖):=he.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>le_trans (le_add_of_nonneg_left (norm_nonneg _)) ((h i).costs (hw i))) -- ambiguity
   refine ⟨hs,?_⟩; rw [← show (∑' i,f i)=hZ.tollK from ?_]; exact hs.of_norm.hasSum
   apply Coil.ext; intro i j; let z:Lab G n:= ⟨j⟩
   apply ((tire R.p i z).hasSum hs.of_norm.hasSum).tsum_eq.symm.trans
   have hp i': tire R.p i z (f i')=_ := Eligible.make (h i') i z
   change ∑' k, tire R.p i z (f k)= tire R.p i z hZ.tollK; simp_rw [hZ.make i z, hp]
   exact ((profile_merge e P hZ.vigor hw he i.val z.tag).mul_left _).tsum_eq

lemma blazeE : NormSum (fun i=> duct d H R.p n (aisleN e i) (h i).tollE) hZ.tollE:=by
  let f i:= duct d H R.p n (aisleN e i) (h i).tollE; have hs : Summable (fun i=>‖f i‖):= he.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>(duck ..).trans (le_trans (le_add_of_nonneg_right (norm_nonneg _)) ((h i).costs (hw i))))
  refine ⟨hs,?_⟩; rw [← show (∑' i,f i)= hZ.tollE from ?_]; exact hs.of_norm.hasSum
  apply Roc.ext; rintro ⟨i,j⟩ z; let K:= e j; let T:= gaze d H R.p (i,j) z; have hx:(aisleN e K.1) K.2=j:=e.symm_apply_apply _
  have hT(p):T (f p)=flash H d R.p (i,j) z (f p (i,j)):=rfl
  apply (T.hasSum hs.of_norm.hasSum).tsum_eq.symm.trans
  rw [tsum_eq_single K.1]; swap;
  · intro b hb
    have hr:j ∉ Set.range (aisleN e b):=by rintro ⟨s,h⟩; apply hb; exact congr_arg Prod.fst (show (b,s)=K from (e.apply_symm_apply _).symm.trans (congr_arg e h))
    rw [hT, show f b (i,j)= 0 from off _ _ _ _ _ _ hr,map_zero]
  have hl:f K.1 (i,j)=(h K.1).tollE (i,K.2):=by
     -- equality j in dependent? cast! extract general auxiliary
     let hE : ∀ (e:ℕ↪ℕ)(v:Roc d H n R.p)(j i':ℕ), e i'=j → duct d H R.p n e v (i,j)=v (i,i'):= by intro e v j i' hx; subst j; exact ages _ _ _ _ v i i'
     exact hE _ _ _ _ hx
  rw [hT,hl,show flash H d R.p (i,j) z ((h K.1).tollE (i,K.2))=_ from (h K.1).take (i,K.2) z]; exact (hZ.take (i,j) z).symm
end water
end YM.UVExtension.Eyelet
