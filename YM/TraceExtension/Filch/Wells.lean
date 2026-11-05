import YM.TraceExtension.Filch.Tail
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k m:ℕ}{o:Site n}{r:ℕ}{F:Acr G n→ℝ}{a A C:ℝ}
lemma greens(A F:Acr G n→ℝ)(k:ℕ) (v:Acr G n): neap k F 0 v=(k.factorial:ℝ)⁻¹*∑ i: Fin k→pairA G n,(∏ j,v (i j)) * leaf F 0 k i:=by
    unfold neap; exact congr_arg ((k.factorial:ℝ)⁻¹ • ·) (many (.atomic k) (iteratedFDeriv ℝ k F 0) (fun _=> v))
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private lemma allows_mul₀ {f g:X→ℝ}{x:X} (h: Allows k f x A)(hp: Allows k g x C):Allows k (fun y=> f y*g y) x (2^k*A*C):=by
    let L:=ContinuousLinearMap.mul ℝ ℝ; have he:= h.bilinear L hp (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
    rw[mul_one] at he; exact he
private lemma allows_group {x:X}{ι:Type}[DecidableEq ι](s:Finset ι)(V:ι→X→ℝ)(h:∀ i∈s,Allows k (V i) x A) : Allows k (fun y=>∏ i∈s,V i y) x ((2^k*A)^s.card):=by
    induction s using Finset.induction with
    | empty=>simpa using allows_const (v:=(1:ℝ)) (C:=1) x (by norm_num) (n:=k)
    | insert i s hi ih => simp_rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi, pow_succ']; exact allows_mul₀ (h i (mem_insert_self ..)) (ih (fun j hj=> h j (mem_insert_of_mem hj)))
def green (k m:ℕ)(C:ℝ):= |(m.factorial:ℝ)⁻¹| *((2^k*C)^m)
lemma grove(V:X→ Acr G n)(x:X)(hv:∀ i,Allows k (fun y=> V y i) x C)(hC:0≤ C)(hA:cost (landW o) a 4 0 (leaf F 0 m)≤ A)(ha:0≤ a): Allows k (fun y=> neap m F 0 (V y)) x (green k m C *A):=by
    let W(i:Fin m→pairA G n)(y:X):=(∏ j,V y (i j)) * leaf F 0 m i;let K:=(2^k*C)^m; have hk:0 ≤ K:=by positivity
    have he(i): Allows k (W i) x (‖leaf F 0 m i‖*K):=by
        have hp:Allows k (fun y=> ∏ j,V y (i j)) x K:=by simpa using! allows_group univ (fun j y=>V y (i j)) (A:=C) (k:=k) (fun j _=> hv _)
        exact (hp.smul (leaf F 0 m i)).germ (Eventually.of_forall fun _=> mul_comm ..)
    simp_rw [greens F F]; apply ((allows_sum (f:=W) (s:=univ) (C:=fun i=> ‖leaf F 0 m i‖*K) (fun i _=>he i)).smul ((m.factorial:ℝ)⁻¹)).mono
    unfold green; refine le_trans ?_ (le_of_eq (show |(m.factorial:ℝ)⁻¹| *(A*K)= _ by ring))
    rw[← Finset.sum_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply mul_le_mul_of_nonneg_right _ hk
    refine le_trans ?_ hA; apply sum_le_sum; intro i _; exact le_mul_of_one_le_left (norm_nonneg _) (spot_one ha ..)

def Define (G:Gauge)(C:ℝ)(k:ℕ)(f:ℕ→ℝ):Prop := ∀ (X:Type) [NormedAddCommGroup X] [NormedSpace ℝ X]{n:Side}{o:Site n}{r:ℕ}{A a:ℝ}{J:Acr G n→ℝ},0≤a→(∀ i,i≤4→cost (landW o) a 4 0 (leaf J 0 i)≤ A) → ∀ (U:X→ Config G n) (w:X→ Link G n)(x:X), (∀ i, Allows k (fun y=>G.mat (U y i)) x C)→ (∀ i,Allows k (fun y=>edgeColor (w y) i) x C)→
   Allows k (fun y=>cloud J o r (U y) (w y)) x (f r*A)
lemma stencilG (G:Gauge)(C:ℝ)(k:ℕ)(h:0≤ C):∃ f:ℕ→ℝ,MarksP f ∧ Define G C k f:=by
    obtain ⟨F,hF,H⟩:=crop_ext G C k h; let f i n:= green k i (F n)
    have hg i:MarksP (f i):=(token _ (abs_nonneg (α:=ℝ) (i.factorial:ℝ)⁻¹)).pair (((token ((2:ℝ)^k) (by positivity)).pair hF).tier i)
    refine ⟨_,mark_sum (range (4+1)) f (fun i _=> hg i),?_⟩; intro X _ _ n o r A a J he hp U w x hU hw; dsimp only; rw [Finset.sum_mul]
    let S(y:X):= stone (landW o) r (patio o 4 (U y) (w y))
    have hx j: Allows k (fun y=> S y j) x (F r):=by
       simp_rw [S,stone_at]; split
       · exact H X U w x hU hw o r j (by assumption)
       exact allows_const _ ((norm_zero (E:=ℝ)).trans_le (hF.1 _))
    unfold cloud; simp_rw [reverberate]; exact allows_sum (s:=range (4+1)) (f:=fun i y=> neap i J 0 (S y)) (fun i hi=>grove _ x hx (hF.1 _) (hp i (by have h:= mem_range.mp hi; omega)) he)
lemma dew (G:Gauge):∃ D:ℝ,∃ P:ℕ,0 ≤ D ∧ ∀ (n:Side)(o:Site n)(r:ℕ)(a A:ℝ), 0<a→a≤1 → 0 ≤ A→
   (∀ Z:Peat G n,Z∈loom G n→Estate o (ballX Z) a (fun _=>A)→Estate o (ballX (Z-lakesC o r Z)) (a/100) (fun _=>D*momentPrice P (a/4)*Real.exp (-(a/4)*r)*A))∧
   ∀ Y:Gal G n,Y∈rains G n→Estate o (bottom Y) a (fun _=>A)→Estate o (bottom (Y-lakesY o r Y)) (a/100) (fun _=>D*momentPrice P (a/4)*Real.exp (-(a/4)*r)*A):=by
   obtain ⟨D,P,hD,H⟩:= longshoals G; refine ⟨D,P,hD,fun n o r a A ha hb h=>?_⟩
   have hp(J:Acr G n→ℝ)(hJ:Estate o J a (fun _=>A))(hx:J 0=0)(hy:fderiv ℝ J 0=0) (j:ℕ)(hj:j≤4): cost (landW o) a 4 0 (leaf J 0 j) ≤ A:=by
       match j with
       | 0=>simpa [Perfect.cost,Perfect.leaf,Perfect.bank,iteratedFDeriv_zero_apply,hx] using h
       | 1=>simpa[Perfect.cost,Perfect.leaf,Perfect.bank, iteratedFDeriv_one_apply,hy] using h
       | j+2=>exact hJ.values _ hj (by omega)
   constructor
   · intro Z hZ he
     obtain ⟨ht,hv,hx⟩:= loom_read hZ
     rw [show ballX (Z-lakesC o r Z)=ballX Z - ballX (lakesC o r Z) from rfl,pinch o r hZ]; exact ⟨fun i hi _=> H n o r a A _ ha hb h hx (glowP (show Cleric _∧_ from hZ).1 o) (hp _ he ht hv) _ hi⟩
   intro Z hZ he
   obtain ⟨ht,hv,hx,-⟩:=rain_read hZ
   rw[show bottom (Z-lakesY o r Z)=bottom Z -bottom (lakesY o r Z) from funext (fun x=>sub_dotProduct ..),pinchY o r hZ]; exact ⟨fun i hi _=>H n o r a A _ ha hb h hx (bloomP (show Cloaked _∧_ from hZ).1 o) (hp _ he ht hv) i hi⟩
end YM.Trace.Filch
