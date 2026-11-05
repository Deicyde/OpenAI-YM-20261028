import YM.FullVolume.Vision.Jet
/-! Shape interpolation.Canen. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Change.Reading
open Function Filter Precision Work OrderedFinpartition
open scoped Topology ContDiff BigOperators Classical
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]{n:ℕ}{w:ℝ}
-- n index = last frozen (inclusive). Aff top n+1
variable (f g h:X→Y) (x:X) in
structure Knot (n:ℕ)(w:ℝ) :Prop where
   equal : Matches n f g x
   credit : Matches n f h x
   shift : sign h x (n+1) = sign f x (n+1)+w • (sign g x (n+1)-sign f x (n+1))
variable {f g u:X→Y}{F G W:Y→Z}{f' g' h':X→Y}{x:X}
lemma uniqueLever (h: Matches n f g x) (he:1≤n): fderiv ℝ f x=fderiv ℝ g x:= (h.lower (show 1≤n from he)).ahead.value
lemma charge (h:Knot F G W (f x) n w) (hu:Matches n f g x) (he: Matches n f u x) :
     carta W u (n+1) x (u x)= carta F f (n+1) x (f x)+w • (carta G g (n+1) x (g x)- carta F f (n+1) x (f x)) :=by
    rw [← hu.value, ← he.value]; unfold carta; rw [← Finset.sum_sub_distrib, Finset.smul_sum,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hv
    have hb j: i.partSize j ≤ n:=Nat.le_of_lt_succ (part_small i (Finset.mem_filter.mp hv).2 j)
    rw [show (fun j=>sign u x (i.partSize j))=_ from (funext fun j=> (he.jets _ (hb j)).symm), show (fun j=> sign g x (i.partSize j))=_ from funext fun j=> (hu.jets _ (hb j)).symm]
    let B:= i.compAlongOrderedFinpartitionL ℝ X Y Z
    have hh(k)(p:k=i.length): sign W (f x) k=sign F (f x) k+w • (sign G (f x) k-sign F (f x) k):=by
         rcases eq_or_lt_of_le (show k ≤ n+1 from p ▸ i.length_le) with hx|hx
         · rw [hx]; exact h.shift
         simp only [sign, ← h.equal.jets k (by omega),← h.credit.jets k (by omega),sub_self,smul_zero,add_zero]
    rw [hh i.length rfl, map_add,map_smul, map_sub,_root_.add_apply,_root_.smul_apply,_root_.sub_apply]
lemma easel (h: Knot F G W (f x) n w)(u₀:Matches n f g x)(v:Matches n f u x) (hN:1≤n):
     let L:= fderiv ℝ F (f x); let Δ:=fun (t:Tensor.T X Y (n+1)) => L.compContinuousMultilinearMap t
     sign (W∘u) x (n+1)-(sign (F∘f) x (n+1)+w • (sign (G∘g) x (n+1)-sign (F∘f) x (n+1))) =
       Δ (sign u x (n+1) - (sign f x (n+1)+w • (sign g x (n+1)-sign f x (n+1)))):=by
    intro L Δ; rw [docking (g:=W) (v.value ▸ h.credit.right) v.right (by omega), docking (g:=F) h.equal.left u₀.left (by omega), docking (g:=G) (u₀.value ▸ h.equal.right) u₀.right (by omega)]
    rw [charge h u₀ v,←u₀.value,← v.value,← uniqueLever h.equal hN, ← uniqueLever h.credit hN]
    ext1 w; unfold Δ; simp only [_root_.sub_apply,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.compContinuousMultilinearMap_coe] -- map L
    simp [Function.comp_def,L, smul_sub,smul_add]; abel
lemma Knot.comp (h:Knot F G W (f x) n w)(v:Knot f g u x n w)(hn:1≤n): Knot (F∘f) (G∘g) (W∘u) x n w:=by
    refine ⟨h.equal.comp v.equal,h.credit.comp v.credit,?_⟩; apply sub_eq_zero.mp; have he:= easel h v.equal v.credit hn; dsimp only at he; rw [he,v.shift,sub_self]; ext1 v; exact (fderiv ℝ F (f x)).map_zero -- map 0
lemma Knot.constant (hf:ContDiffAt ℝ ω f x) : Knot f f f x n w:=⟨matches_self n hf,matches_self n hf,by simp⟩
lemma Knot.dawn (h:Knot f g u x n w)(H: f=ᶠ[𝓝 x] f')(I:g=ᶠ[𝓝 x] g')(J:u=ᶠ[𝓝 x] h'): Knot f' g' h' x n w:=by
    refine ⟨h.equal.unchanged H I,h.credit.unchanged H J,?_⟩
    unfold sign; rw [← (H.iteratedFDeriv ℝ (n+1)).self_of_nhds,← (I.iteratedFDeriv ℝ (n+1)).self_of_nhds,← (J.iteratedFDeriv ℝ (n+1)).self_of_nhds]; exact h.shift
lemma Knot.add (h:Knot f g u x n w)(H:Knot f' g' h' x n w): Knot (f+f') (g+g') (u+h') x n w:=by
    refine ⟨h.equal.add H.equal,h.credit.add H.credit,?_⟩
    unfold sign; rw [iteratedFDeriv_add_apply (h.credit.right.of_le le_top) (H.credit.right.of_le le_top),show iteratedFDeriv ℝ (n+1) u x=_ from h.shift,show iteratedFDeriv ℝ (n+1) h' x=_ from H.shift,
        iteratedFDeriv_add_apply (h.equal.left.of_le le_top) (H.equal.left.of_le le_top),iteratedFDeriv_add_apply (h.equal.right.of_le le_top) (H.equal.right.of_le le_top),smul_sub,smul_sub,smul_sub,smul_add,smul_add]; unfold sign; abel
-- derivatives
lemma Knot.advances (h:Knot f g u x (n+1) w): Knot (fderiv ℝ f) (fderiv ℝ g) (fderiv ℝ u) x n w:=by
   refine ⟨h.equal.ahead,h.credit.ahead,?_⟩
   let L:= continuousMultilinearCurryRightEquiv' ℝ (n+1) X Y; apply L.symm.injective
   change L.symm _ = L.symm _; rw [L.symm.map_add,L.symm.map_smul,L.symm.map_sub]
   have hk(g:X→ Y): L.symm (sign (fderiv ℝ g) x (n+1))=sign g x (n+1+1):= by unfold sign; (conv_rhs => rw [iteratedFDeriv_succ_eq_comp_right]); rfl
   rw [hk,hk,hk]; exact h.shift
lemma Knot.promotes (h: Matches (n+1) f g x)(hv:Matches (n+1) f u x)(he:Knot (fderiv ℝ f) (fderiv ℝ g) (fderiv ℝ u) x n w): Knot f g u x (n+1) w:=by
   refine ⟨h,hv,?_⟩
   unfold sign at *; rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
   let L:= continuousMultilinearCurryRightEquiv' ℝ (n+1) X Y; change L.symm (sign (fderiv ℝ u) x _) = L.symm _ + w • (L.symm _ - L.symm _); rw [he.shift,L.symm.map_add,L.symm.map_smul,L.symm.map_sub]
lemma Knot.pairs {f' g' h':X→Z} (h: Knot f g u x n w)(hz:Knot f' g' h' x n w) : Knot (fun x=>(f x,f' x)) (fun x=>(g x,g' x)) (fun x=>(u x,h' x)) x n w:=by
     refine ⟨h.equal.prod hz.equal,h.credit.prod hz.credit,?_⟩; unfold sign; rw [iteratedFDeriv_prodMk h.equal.left hz.equal.left le_top, iteratedFDeriv_prodMk h.equal.right hz.equal.right le_top, iteratedFDeriv_prodMk h.credit.right hz.credit.right le_top, show iteratedFDeriv ℝ (n+1) u x=_ from h.shift, show iteratedFDeriv ℝ (n+1) h' x=_ from hz.shift]; rfl
end YM.WilsonStartup.Change.Reading
