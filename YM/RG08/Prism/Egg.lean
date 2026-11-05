import YM.RG08.Prism.Cluster

/-!
# Identify formal finite stock at TRUE coarse variables valuation incl extensive component.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Filter Function Matrix Lattice Exterior Stationary RG Laurent Fold Glyph Room Camera Steam MvPolynomial Finset Bloch Mount Drum Forms
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries
variable {I J U R O:Type}[Fintype I][Fintype J][Fintype U][Fintype R][Fintype O]
-- ω input pts, q external test alphabet

def script (A:Drum I J U)(E:J⊕U≃R):Matrix R U ℝ:=(fun r u=> (E.symm r).elim (fun j=> A.mean j u) (fun a=> if a=u then 1 else 0))

omit [Fintype R] in
lemma mvread (A:Drum I J U)(E:J⊕U≃R)(t:U→O)(h:A.Flourishes)(x:Camera.Cellar (Camera.Raw I O)):
 Haze.mView (morn A.dark (A.direction h) O) (speak A E t) *ᵥ x = script A E *ᵥ ((x ∘ Sum.inr) ∘ t):=by
 funext j; unfold Haze.mView Matrix.mulVec;rw [dotProduct,Fintype.sum_sum_type];simp [morn]; cases he:E.symm j with
 | inl k=>
   change ∑ b:O,_ = _
   have he0 (b:O):speak A E t j (.inr b)=exposure A t k b:=by unfold speak; rw [he];rfl
   simp_rw [he0]; change (exposure A t *ᵥ (x∘ Sum.inr)) k= dotProduct (script A E j) _; rw [exposure,←mulVec_mulVec,whistle];unfold script;rw [he];rfl
 | inr k=>
    have he0(b:O):speak A E t j (.inr b)=whisk t k b:=by unfold speak;rw [he];rfl
    simp_rw [he0];change (whisk t *ᵥ (x∘Sum.inr)) k=_;rw [whistle];simp only [script,he,Sum.elim_inr,dotProduct,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,mem_univ,↓reduceIte]

def col (A:Drum I J U)(E:J⊕U≃R)(X:Grain R):Port U:= liftInn (shelter A.N MvPolynomial.X)+pushed (Γ:=press A E) (script A E) X -- XVAR μ id var

lemma atHome (A:Drum I J U)(E:J⊕U≃R)(X:Grain R)(t:U→O)(h:A.Flourishes):
    ash A h E t X=belt (fun i:U=>rod (I:=Camera.Raw I O) (Sum.inr (t i))) (col A E X):=by
 let K := Haze.mView (morn A.dark (A.direction h) O) (speak A E t); let B:=script A E
 unfold ash col;rw [map_add];apply congrArg₂ (·+·)
 · ext n :1; change tap n (Fold.platen (spend A t) I)=tap n (belt (fun i:U=>rod (Sum.inr (t i))) _);rw [Cairn.censor,platen,tap,PowerSeries.coeff_C];unfold tap;rw [PowerSeries.coeff_C];split_ifs
   · apply MvPolynomial.funext;intro x;rw [eval_rename,sink,shelter_read,shelter_read]
     simp only [eval_X]; unfold spend winery winB;rw [Matrix.mul_assoc _ A.N,← Drum.pairing,←mulVec_mulVec,whistle];rfl
   rw [map_zero]
 ext n:1
 let π(i:U):Camera.Raw I O:= .inr (t i)
 change tap n (Glyph.stock (allG _ X K))=tap n (belt (fun i=>rod (π i)) (Glyph.stock (allG _ X B)));rw [Cairn.censor,Glyph.allG_on,Glyph.allG_on,amended_stock,amended_stock,tap,PowerSeries.coeff_map]
 unfold tap;rw [PowerSeries.coeff_map]
 apply MvPolynomial.funext; intro x
 rw [eval_rename]
 erw [aim_eval K x,aim_eval B (x∘π), mvread A E t h x];rfl
lemma autumn (A:Drum I J U)(E:J⊕U≃R)(X:Grain R)(t:U→O)(h:A.Flourishes){F:Type}[Fintype F](a:Camera.Raw I O→Port F):
 belt a (ash A h E t X)=belt (fun i=>a (.inr (t i))) (col A E X):=by
 rw [atHome]; change ((belt a).comp (belt (fun i:U=>rod (I:=Camera.Raw I O) (.inr (t i))))) _=_;rw [switched];simp_rw [belt_x]

/- The calendar specialization of the belt identity is stated and proved by
   `Bore.zap` in `YM.RG08.Prism.Glow`. -/

end YM.RG08.Prism
