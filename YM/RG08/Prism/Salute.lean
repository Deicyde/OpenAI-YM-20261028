import YM.RG08.Prism.Fan
/-!
# Supply quadratic china from base physical constitutive check
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Wilson RG Precision Stationary RG08.Line Fold Drum Bloch Laurent Finset Filter Glyph Room Camera Tack Mount MvPolynomial
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{F:Tree.Forest S.ratio}{b v:Bed}{C:Castle G}
namespace Proceed
abbrev wx (S:StepData c f)(z:Cellar (Epic S.patch G c)):=z ∘ lowSlot S
abbrev wy (S:StepData c f)(z:Cellar (Epic S.patch G c)):=z ∘ highSlot S
lemma jungle (x: Cellar (Epic S.patch G c)) :
  ∑ i:Edge (Site c),inner ℝ (missing S i x) (missing S i x)=dotProduct (wy S x - patron G (probe S) *ᵥ wx S x) (wy S x-patron G (probe S)*ᵥ wx S x):=by
 unfold dotProduct;simp_rw [Fintype.sum_prod_type]
 apply Finset.sum_congr rfl;intro j _
 rw [← Equiv.sum_comp axisEquiv (fun i:TypeFace 1=>_)]
 apply Finset.sum_congr rfl;intro i _; simp only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial];apply Finset.sum_congr rfl;intro k _; change ((high S x) (j,coord i) k- (probe S *ᵥ parts G 1 (low S x) k) (j,coord i))*_= _
 congr 1 <;> erw [Pi.sub_apply, Line.painted G (probe S) (wx S x) k ((j,coord i):Body 1 c)]
 -- possibly one goal
 all_goals rfl
lemma zerobelt (h:S.patch.Branches S.kernel G)(hc:Stable C) (he:Proceed C b f)(x:Cellar (Epic S.patch G c)) :
 eval x (tap 0 (china h C)) = -(1/2:ℝ) * (winB (patron G (Precision.K (b.metric.acts f))) (wx S x) (wx S x)+S.kernel.penalty * dotProduct (wy S x - patron G (probe S)*ᵥ wx S x) (wy S x - patron G (probe S)*ᵥ wx S x)):=by
 let u:S.Choices:=(fun _=>(S.patch.center,1),fun _=> S.patch.center)
 rw [china_tap h u C hc];simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Cairn.leaf,pow_zero,one_mul,map_neg,map_add,taxed h u]
 rw [Cairn.censor,eval_rename,Camera.audited,show 0+Mount.rank 0=2 from rfl, he,jungle];ring
end Proceed

variable {O:Type}[Fintype O](t:Lines G c 1→O)
lemma china_peak (h:S.patch.Branches S.kernel G)(hc:Stable C) (he:Proceed C b f)(hr:(grace G S F b v).Flourishes) :
 let Z:=grace G S F b v; let L:=speak Z (fir S) t
 ; twistMean L (tap 0 (china h C))= heater Z.inside O + sink (spend Z t) (Key F G):=by
 intro Z L
 apply MvPolynomial.funext; intro x
 let w:=L *ᵥ x
 obtain ⟨hy,hA⟩:= speak_zone Z (fir S) t x
 have ht: Proceed.wx S w=Z.v*ᵥ (x ∘ Sum.inl)+Z.mean*ᵥ ((x ∘ Sum.inr) ∘ t):=hy
 have hu: Proceed.wy S w= (x ∘ Sum.inr) ∘ t:=hA
 rw [aim_eval,Proceed.zerobelt h hc he,heater,sink,map_add,shelter_read,shelter_read]
 simp only [eval_X]
 rw [show Proceed.wx S _= _ from ht,show Proceed.wy S _=_ from hu]
 erw [Z.completes hr]
 have he : winB (spend Z t) (x∘Sum.inr) (x∘Sum.inr) = winB Z.N ((x ∘ Sum.inr)∘t) ((x ∘ Sum.inr)∘t):=by
    unfold spend winB; rw [Matrix.mul_assoc,← Drum.pairing,←Matrix.mulVec_mulVec,whistle]
 change _=(-1/2:ℝ)*winB _ (x ∘ Sum.inl) (x ∘ Sum.inl)+(-1/2)*winB _ (x ∘ Sum.inr) (x∘Sum.inr)
 rw [he];ring

end YM.RG08.Prism
