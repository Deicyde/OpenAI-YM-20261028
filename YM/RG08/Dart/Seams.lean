import YM.RG08.Dart.Verge
/-! # Every planted finite demand. Exact tally before assembly, $e-j$ in own meshes. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295 Work.F03 Shade Tall
open Wax Town Creek Scores Loom
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {I:Type}[Fintype I][DecidableEq I]{T:Finset I}{G:Gauge}{E e j k D τ:ℕ}{σ C R w:ℝ}{U:Layouts I G D R}{a:I→ℕ}
-- CURRENT occupied marker set T. Absolute stencil converted to root relative a at p. sectors all i with p relation bounded. Preserve orientation capability by explicit placement true anchor. Maxwell not projected.
def moneyP (F:Layouts I G D R)(k:I→ℕ)(p:↥T)(q:ℕ) : Swan T (Loc G 1) D R := fun i x=> if vanes k T≤ q+i then Town.season (-(x p)) (F x T) (q+i-vanes k T) i else 0
lemma portals_r (he:Sense a U)(p:↥T)(q n:ℕ): Portals n (moneyP U a p q):= by
   intro x y m; let P:= vanes a T; let X:= Town.season (-(x p)) (access y (U x) T); have ht:Stone P X:= (he.stone ..).transport _
   obtain ⟨V,H⟩:= shelved (ht.shore m 0) (p:=q) (n:=n+P) (by omega) ht.tidy
   let W:=V∘ input G m
   have Wv : ContDiffAt ℝ ω W 0:= H.hol
   have hi : Tendsto (input G m) (𝓝 0) (𝓝 1) := by simpa only [input_zero] using! input_cont.continuousAt.tendsto (x:= (0: Link G m))
   refine ⟨W,Wv.analyticAt,?_,fun s=>?_,fun j hj=>?_⟩
   · have hx:Tendsto (moveField (G:=G) (m:=m)) (𝓝 0) (𝓝 0):= by simpa only [moveField_zero] using! (moveField_analytic (G:=G) (m:=m)).continuousAt.tendsto
     refine H.coast (input G m∘ (Prod.snd (α:=BaseSites G m))) (input G m ∘ moveField) (switchSite ∘ Prod.fst) (𝓝 0) (hi.comp (continuous_snd.tendsto (0:Swatch G m))) (hi.comp hx) moveField_germ
   · have ht: Tendsto (stain (m:=m) s) (𝓝 0) (𝓝 0):= by simpa using! (stain s (m:=m)).continuous.tendsto (0:Link G m)
     exact H.coast (input G m) (input G m ∘ stain s) (fun _ _=>s) (𝓝 0) hi (hi.comp ht) (Eventually.of_forall fun v=> (stain_cons ..).symm)
   rw [show Tensor.coeff W j 0= _ from H.scores_at j (by omega)]; unfold moneyP Loom.strand
   by_cases ht:P ≤ q+j; · simp only [ht,↓reduceIte,P]; rfl
   rw [if_neg ht,if_neg ht]; congr
lemma camp_zero {W E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](p:Finset I)(h:0≤C) (v:ℝ)(r:ℕ): Camp p v (fun _=> (0:Rooted E W r)) C:=by
   have hv: Owns v p (fun _=> (0:Rooted E W r)) C:= owns_none p v h _ _ _
   refine ⟨hv.1,h,fun a=>?_⟩ -- name
   obtain ⟨A,hA,H⟩:=hv.2.2 a; exact ⟨A,fun i=> Ink.raise (Ink.none _ _) (hA i).nonneg,H⟩
lemma coin_pre (T:Finset I)(p:↥T)(k E q:ℕ)(hp:q≤k+E)(v:ℝ)(he:0<v)(G:Gauge)(R:ℝ)(D:ℕ) : ∃ w C:ℝ, 0<w ∧ w≤v ∧ 0≤C ∧ ∀ (U:Layouts I G D R)(a:I→ℕ) (B:ℝ),Sense a U → k=vanes a T → (∀ i≤E,∀ j, Owns v T (fun x=> U x T i j) B) → ∃ S:Ample T G D R,Armor (moneyP U a p q) (k-q) (k+E-q+1-(k-q)) S w (B*C) := by
    let z:=k+E-q+1; let σ:= v / ((z+1:ℕ):ℝ); have hz:0 < σ:=div_pos he (by positivity)
    have ht:T.Nonempty:= ⟨p.val,p.property⟩; have he: k-q+(z-(k-q))=z:= by unfold z; omega
    obtain ⟨w,C,hw,hz',hC,H⟩:= arose T D R G (k-q) (z-(k-q)) hz ht
    refine ⟨w,C,hw,hz'.trans (div_le_self ‹0<v›.le (by exact_mod_cast show 1≤z+1 from by omega)),hC,fun U a B hv HK hh=> ?_⟩; have hB:= (hh 0 (Nat.zero_le _) 0).pos
    refine H (moneyP U a p q) B hB (fun i hi=>?_ ) (portals_r hv p q _) ?_
    · unfold moneyP; rw [←HK]; split; next h=>
        rw [he] at hi; have he': q+i-k≤ E:= by unfold z at hi; omega
        refine ⟨camps (hh _ he' _) (?_ ) hz p, fun x=>tidy_roam (hv.style x T|>.tidy ..) _⟩; unfold σ
        exact le_trans (mul_le_mul_of_nonneg_left (show (↑(i+1:ℕ):ℝ) ≤ ↑(z+1:ℕ) from Nat.cast_le.mpr (by omega)) hz.le) (le_of_eq (div_mul_cancel₀ _ (by positivity)))
      exact ⟨camp_zero T hB σ i,fun _=> Tidy.zero ..⟩
    intro i hi; funext x; unfold moneyP; rw [← HK, if_neg (by omega)]; rfl
-- cost of root+paths ALL list+addresses in own mesh. include connector pins to test cell endpoints (native length cap R) & arc polygons. Use arbitrary finite extra position moments of this total via width division. Canonical picture by translation no asserting term shape.
abbrev lengthsHere (a:T) (b:Fleet T) (p:Beads (Loc G 2) j) := Mounts a b + (actionP p).length
lemma lengths_pay {P:Cornea T (Loc G 2) D R j} (hk: Stint T P w C)(hv:0 ≤ w) (a:T) (x:Cover): SumBudget (fun i: Held a x × Beads (Loc G 2) j=> ‖P (loose T i.1.val) i.2‖*Real.exp (w*lengthsHere a i.1.val i.2)) (Real.exp (w*↑(4*j))*C) := by
   obtain ⟨A,hA,H⟩:= hk.for_all a
   let B:=Real.exp (w*(4*j:ℕ)); refine budget_rows _ (fun i:Held a x=> B*Tribe a i.val w (A i.val)) (fun i=>?_) (budget_scale (Real.exp_pos _|>.le) (H x))
   rw [show B*Tribe a i.val w (A i.val)= B*Real.exp (w*↑(Mounts a i.val))*A i.val from (mul_assoc ..).symm]
   convert budget_scale (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)) (hA i.val) using 1; ext1 k; unfold lengthsHere; rw [budget_atom,Nat.cast_add,Nat.cast_add,mul_add,Real.exp_add,mul_add,Real.exp_add,ling]; dsimp only; ring
end YM.RG08.Dart
