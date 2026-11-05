import YM.OPE.Splitting.Detector
/-!
# Projection, coherently applied
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Word Table
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{L:Register G}{S:Table L}(T : Table L)
    {P:DiffPlan S} (U: Prescription P)
    {I J K:Type}[Fintype I][Fintype J][Fintype K]{x:I→ E4}(v:I→ L.Token) {n m: ℕ} {z:E4} {y:J→ E4} (w:J→L.Token)

lemma observe_exact (hx:T.Symmetric) (hr:T.respects S) (h:Injective x): observe T x v=S.useAt T (points (x ∘ runNames I)) (fun i=> S.classTokens (v (runNames I i))) := by unfold observe worded; rw [T.readAt]; exact (S.at_project T hx hr (runs_conf.mpr h) _).symm
lemma observe_replace [DecidableEq I]{p v': L.Token} (hx:T.Symmetric)(hr:T.respects S)(hp:P.Inclusions T)(hi:Injective x) (a:I)
    (he:p.fst ≤ v'.fst)(hc: P.rise he (S.project _ p.snd) = S.project _ v'.snd) : observe T x (update v a v') = observe T x (update v a p):=by
    rw [observe_exact T (update v a v') hx hr hi,observe_exact T (update v a p) hx hr hi]
    let f:= S.classTokens ∘ v; let E:= runNames I; obtain ⟨b,rfl⟩:= E.surjective a
    have hh p : (fun i=> S.classTokens ((update v (E b) p) (runNames I i)))= update (f ∘ runNames I) b (S.classTokens p):=by
       funext i; by_cases h:i=b; · subst i; rw [Function.update_self, Function.update_self]
       rw [Function.update_of_ne h,Function.update_of_ne (by exact E.injective.ne h)]; rfl
    rw [hh,hh]; change S.useAt _ _ (update _ _ ⟨v'.fst,S.project _ _⟩)=_ ; rw [← hc]; exact P.inclusion_slot hp hx he (runs_conf.mpr hi) b (f ∘ runNames I) _
namespace Prescription
lemma evaluateProjection (hp:P.Inclusions T)(hx:T.Symmetric)(hr:T.respects S)(ht:Injective (beside (sole z) y)) (k: Mode P) (hk:k∈ bands P n) :
    observeOne S T z y w n (U.loaded k n) = observe T (beside (sole z) y) (beside (sole (U.letter k)) w):=by
    rw [cost _ _ hk,lowerOne T w _ _ hp hx ht _ hr]; unfold letter; rw [← projectedOne T w k.fst (S.representative _ _) hx hr ht,S.rep] -- wildcard
lemma sumAll (hp:P.Inclusions T)(hx:T.Symmetric)(hr:T.respects S)(ht:Injective (beside (sole z) y))(hU:U.Coherent)(a:L.Ref n):
    ∑ k∈ bands P n, U.test k n (S.project n a) * observe T (beside (sole z) y) (beside (sole (U.letter k)) w)= observe T (beside (sole z) y) (beside (sole ⟨n,a⟩) w):=by
    conv_rhs=> rw [← projectedOne T w n a hx hr ht, ← (hU n).rebuilds (S.project n a)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi=>?_ ; rw [map_smul,evaluateProjection T U w hp hx hr ht i hi]; rfl
lemma term_carry (a:E4) {U:Prescription P}{i:Mode P} : U.ope i (fun i=> x i+a) v (z+a) = U.ope i x v z := by unfold ope reading; simp
lemma reading_permute (h:S.Symmetric){p: Exterior L}(e:J≃I) : reading S (x ∘ e) (v ∘ e) z p = reading S x v z p:=by
    unfold reading; try dsimp only; let q:= Equiv.sumCongr e (Equiv.refl (Fin p.n)); let y:= fun i=>x i-z; rw [show beside (fun i=> (x ∘ e) i-z) (bearing p)= beside y (bearing p) ∘ q from funext fun j=> by cases j<;> rfl,show beside (v ∘ e) p.letter= beside v p.letter ∘ q from funext fun j=>by cases j<;> rfl]; split
    next hv=>
      have he : Injective (beside y (bearing p)):=by
         intro i j hij; obtain ⟨i,rfl⟩:=q.surjective i; obtain ⟨j,rfl⟩:=q.surjective j; exact congr_arg q (hv (show (beside y (bearing p) ∘ q) i = (beside y (bearing p) ∘ q) j from hij))
      rw [if_pos he]; exact perm_observe S h q _ he
    next hv=> split; next hx=> exact (hv (hx.comp q.injective)).elim
              rfl
lemma coefficient_perm (h:S.Symmetric) (e:J≃I) (i:Mode P): U.ope i (x ∘ e) (v ∘ e) z = U.ope i x v z:=by unfold ope; simp_rw [reading_permute v h e]
lemma respectsLabel {p v':L.Token} (hU:U.Coherent)(h:S.Symmetric) (hp:P.Inclusions S) (a:I)
    (he:p.fst ≤ v'.fst)(hc:P.rise he (S.project _ p.snd)= S.project _ v'.snd)(k:Mode P): U.ope k x (update v a v') z= U.ope k x (update v a p) z:=by
    have hx(i: Exterior L): reading S x (update v a v') z i = reading S x (update v a p) z i:=by
       unfold reading; try dsimp only; split; swap; exact rfl
       next h' =>
       have he(a':L.Token):beside (update v a a') i.letter=update (beside v i.letter) (.inl a) a':=by
          funext j; rcases j with j|j
          · by_cases h:j=a; subst j; · simp
            rw [beside_left,update_of_ne h,update_of_ne (Sum.inl_injective.ne h)]; rfl
          rw [update_of_ne (Sum.inr_ne_inl)]; rfl
       rw [he,he]; apply observe_replace S _ h (fun _=>le_rfl) hp h' (.inl a) _ hc
    unfold ope; simp_rw [hx]
end Prescription
end YM.OPE
