import YM.RemainderComparison.Ethereal.Crest
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Ethereal
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{p : BudgetPoint}
-- Scalar costs before changing.Some analytic model.E extra packets also inhabit these, with Hessian null.Normed.
open Lacuna Vowel PhysicalNext.Repeat
variable {I κ:Type} (V : Vowel G n I)(X : Vowel G n ℕ)(p:BudgetPoint)
variable {b u σ:ℝ}
structure Normal : Prop where
    airy i : p.Regular (V.sign i).support (V.stanza i)
    at_zero i : V.stanza i 1=0
    hc i : Nonwrapping (V.sign i).support (V.sign i).site → ∀ x y, IsAffineDirection (V.sign i).site x→IsAffineDirection (V.sign i).site y→ logHessian (V.stanza i) x y=0
    moves : V.Moves
variable (A : Activities G n) (hA:A.E=X.stanza)(h'A:A.reg=X.sign)
lemma normal {A:Activities G n}(h:A.RegularFamily p)(he:(fun i=> A.E i)=X.stanza)(hf:A.reg=X.sign)(hx: X.Moves):Normal X p:=by
    have h' : A.E=X.stanza:=he
    refine ⟨?_,?_ ,?_ ,hx⟩
    · rw [← hf,← h']; exact h.smooth
    · rw [← h']; exact h.at_flat
    rw [← hf,← h']; exact h.vanish

-- coding derivative laws
lemma lineTest {x z:RegularAddress n}{s:Signed}{b:Site n}(h:z.site = affine s b x.site) (hh:z.support=x.support.image (affine s b)) : Song.line x (s,b)=z:=by
   have he: ∀ (P Q:RegularAddress n),P.site=Q.site→P.support=Q.support→P=Q:=by rintro ⟨_,_,_⟩ ⟨_,_,_⟩ a b; congr
   exact he _ _ h.symm hh.symm
lemma brain {A:Activities G n}(he:A.E=X.stanza) (hf:A.reg=X.sign) (hg:∀ s b,Nonempty (A.Moves s b)): X.Moves:=by
   constructor; intro s b; obtain ⟨e⟩:=hg s b; refine ⟨e.ep,fun i=>by rw [←hf,←he]; exact ⟨(Ethereal.lineTest (e.reg_site i) (e.reg_support i)).symm,funext (e.valuesE i)⟩⟩
include hA h'A
lemma retinue (hx:Normal X p): A.RegularFamily p:=by
   obtain ⟨h,hb,hh,-⟩:=hx; refine ⟨?_,?_,?_⟩
   · rw [hA,h'A]; exact h
   · rw [hA]; exact hb
   rw [hA,h'A]; exact hh
lemma burns (hp:p.supportExponent ≤ σ)(h:X.Pricings p σ u): A.EBound p u:=by
   obtain ⟨f,h,hf⟩:= h.marks; refine ⟨f,?_ ,?_⟩
   · rw [hA,h'A]; exact fun i=> (h i).2
   rw [h'A]; intro i; apply budget_mono (hf i)
   · intro j; split; · exact mul_nonneg (Real.exp_pos _).le (h j|>.2.1)
     exact le_rfl
   intro j; split; next hP=>
      rw [BudgetPoint.mass, mul_comm]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (h j|>.2.1)
   next=>exact le_rfl
omit hA h'A
lemma accounted (h:V.Pricings p σ u)(hp:0 ≤ σ)(U:Config G n): SumBudget (fun i=> ‖V.ray p i U‖) (Fintype.card (Site n)*u):=by
   obtain ⟨f,h,hV⟩:=h.marks; have hs i : 0 ≤ f i:= (h i).2.1
   have hf: SumBudget f (Fintype.card (Site n)*u):=by
       apply budget_of_sum hs
       intro z
       have hh x : ∑ i∈z, (if (V.sign i).site=x then f i else 0)≤ u:=le_trans (Finset.sum_le_sum fun i _=> ?_) (budget_sum (hV x) z)
       swap; · split_ifs; exact le_mul_of_one_le_right (hs i) (Real.one_le_exp (mul_nonneg hp (by positivity))); exact le_rfl
       have hx : ∑ x:Site n,(∑ i∈z, if (V.sign i).site=x then f i else 0)= ∑ i∈z,f i:=by rw [Finset.sum_comm]; simp
       rw [← hx]; exact le_trans (Finset.sum_le_sum fun i _=> hh i) (by simp)
   exact budget_mono hf (fun i=> norm_nonneg _) (fun i=> CouplingShape.mask_cost (h i).2 U)
-- append resets on rebill.K.G.
variable (W : Vowel G n κ)

def ethic : Vowel G n (I⊕κ):= ⟨Sum.elim V.sign W.sign,Sum.elim V.stanza W.stanza⟩
local notation "A₁"=> Ethereal.ethic V W
lemma stair (h:V.Pricings p σ b)(hp: W.Pricings p σ u): Vowel.Pricings A₁ p σ (b+u):= by
   obtain ⟨f,hf,h⟩:=h.marks; obtain ⟨g,hg,hp⟩:=hp.marks
   let F:= Sum.elim f g; have hv i : p.Regular ((A₁).sign i).support ((A₁).stanza i) ∧ p.supBounds ((A₁).sign i).site ((A₁).sign i).support ((A₁).stanza i) (F i):=by rcases i with i|i;exact hf i;exact hg i
   exact ⟨⟨F,fun i=> (hv i).2.1⟩,⟨F,hv,fun i=> Cost.sum (h i) (hp i)⟩⟩
lemma tilted (hx:V.Moves) (hp:W.Moves): Vowel.Moves (A₁):=by
   constructor; intro s b; obtain ⟨e,he⟩:=hx.continual s b; obtain ⟨g,hg⟩:=hp.continual s b; refine ⟨Equiv.sumCongr e g,fun i=>?_⟩; rcases i with i|i; exact he i; exact hg i
lemma brought (hx:V.Pricings p σ b)(hp:W.Pricings p σ u) (hσ:0 ≤ σ)(U:Config G n): (A₁).overlay p U= V.overlay p U+W.overlay p U:= Summable.tsum_sum (f:=fun i=>(A₁).ray p i U) (accounted V p hx hσ U).2.1.of_norm (accounted W p hp hσ U).2.1.of_norm
lemma developed (hx:Ethereal.Normal V p)(hp:Ethereal.Normal W p) : Normal A₁ p:=by
   refine ⟨?_,?_ ,?_, Ethereal.tilted V W hx.moves hp.moves⟩ <;> rintro (i|i) <;> first| exact hx.airy i| exact hp.airy i| exact hx.at_zero i| exact hp.at_zero i| exact hx.hc i| exact hp.hc i
-- negative sign.V

def negP : Vowel G n I:=⟨V.sign,fun i=> - V.stanza i⟩
local notation "M" => Ethereal.negP V
lemma earns (hx:V.Pricings p σ b): Vowel.Pricings (M) p σ b:=by
   obtain ⟨f,h,hv⟩:=hx.marks; refine ⟨⟨f,fun i=> (h i).2.1⟩,⟨f,fun i=>?_ ,hv⟩⟩
   have he:= CouplingShape.reg_scale (-1) (h i).1; have hf := CouplingShape.sup_scale (-1) (h i).2; rw [neg_one_smul] at he hf; simp only [abs_neg,abs_one,one_mul] at hf; exact ⟨he,hf⟩
lemma rung (h:V.Moves): Vowel.Moves (negP V):=by
    constructor; intro s b; obtain ⟨e,he⟩:=h.continual s b; exact ⟨e,fun i=> ⟨(he i).1, congr_arg Neg.neg (he i).2⟩⟩
lemma fades (U:Config G n): (negP V).overlay p U= - V.overlay p U :=by
    unfold overlay; rw [← tsum_neg]; refine tsum_congr fun i=>?_ ; by_cases h: Healthy p.threshold (V.sign i).support U
    · unfold Vowel.ray negP; dsimp only; rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
    unfold Vowel.ray negP; dsimp only; rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,neg_zero]
end YM.RemainderComparison.Ethereal
