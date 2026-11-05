import YM.RG08.Wax.Folds
/-! # Canon POST local charge on aligned full T. NO inverse multiplies all
 unknown deficiencies. Reusable explicit prices. Tower widths all in v+w.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset Push.AbsoluteSums UVExt.Paths Town Work.F08
open scoped Topology BigOperators Real Classical
variable {I X:Type} [Fintype I] [DecidableEq I][Fintype X][DecidableEq X] {i j e E k n τ s r t l D:ℕ}{v w B C R Z:ℝ}
variable {M:Row X X}{S:Canticle X}{A: Places I→Turf I D R X}
-- explicit bills
abbrev Head (I:Type) := Finset I → ℝ
structure Crease (p:Head I): Prop where
   pos (t:Finset I):0≤p t
   rise (t:Finset I) (U : Finset I × Finset I) : U∈partners t → p U.1*p U.2≤p t -- F fix

variable {U V T:Finset I}{p:Head I}
def sleeps (A:Places I→ Turf I D R X):Prop:=∀ x, A x ∅=0
def carnival (p:Head I) (v B:ℝ)(A:Places I→ Turf I D R X) (n E:ℕ):Prop:= ∀ j≤n,∀ i≤E,∀ W r,Owns v W (fun x=> A x W j i r) (B*p W)
abbrev parPort (c: Type) [Fintype c](k:ℕ) := ((Fintype.card c:ℕ)+3*k+6 : ℕ)
lemma needed (hi:r+s≤k) : strip_need (Fintype.card I) r s 1 ≤ (parPort I k:ℝ) := by
  unfold strip_need parPort; push_cast; have h : (r:ℝ)+s≤k:=by exact_mod_cast hi
  linarith
lemma par_need (hi:r+s≤k)(hv:0≤v)(hc:(parPort I k:ℝ)*v≤w): strip_need (Fintype.card I) r s v≤w := by
   apply le_trans (le_of_eq (show strip_need (Fintype.card I) r s v= strip_need (Fintype.card I) r s 1*v by unfold strip_need; ring)) ((mul_le_mul_of_nonneg_right (needed hi) hv).trans hc)
lemma port_w (I:Type) [Fintype I] (k:ℕ)(hv:0≤v) : v ≤ (parPort I k:ℝ)*v := le_mul_of_one_le_left hv (show _ by exact_mod_cast show 1≤parPort I k from by unfold parPort; omega)

private lemma wound_sounds {F:Rooted (Poise U D R) X (r+1)} {G:Rooted (Poise V D R) X (s+1)} (h:∀ i:Beads X (r+1)× Beads X (s+1), tape_pair none T M F G i=0): wounds none T M F G=0:=by
  unfold wounds; rw [show tape_pair none _ _ _ _=0 from funext h]; rw [show tub (0:Coves X r s→Poise T D R) stemPair=0 from funext fun i=>tsum_zero,smul_zero]; exact (by simpa only [sub_self] using sew_sub (x:=(0:Rooted (Poise T D R) X (r+s))) (y:=0))
lemma wound_miss (x:Rooted (Poise V D R) X (r+1)) (hp:0 ≤ R) : wounds none T M (0:Rooted (Poise U D R) X (s+1)) x=0 := by
    refine wound_sounds fun i=> ?_
    have he : sale (0:Poise U D R) (x i.2) T=0 := norm_le_zero_iff.mp ((sale_cost (0:Poise U D R) (x i.2) T).trans_eq (by simp))
    change _ • sale (0:Poise U D R) _ _ = 0; rw [he,smul_zero]
lemma wound_wait (x:Rooted (Poise U D R) X (r+1)) (hp:0 ≤ R) : wounds none T M x (0:Rooted (Poise V D R) X (s+1))=0 := by
    refine wound_sounds fun i=> ?_
    have he : sale (x i.1) (0:Poise V D R) T=0 := norm_le_zero_iff.mp ((sale_cost (x i.1) (0:Poise V D R) T).trans_eq (by simp))
    change _ • sale _ (0:Poise V D R) _ = 0; rw [he,smul_zero]

def bob_fee (M w B C:ℝ) := M*C*(B^2*shells w)
lemma bob_pos (hv:0<v)(he:0≤C)(h:0≤Z):0≤bob_fee Z v B C:=by unfold bob_fee; have hb:=shells_pos hv; positivity
lemma pair_fare (he:Crease p)(hu:sleeps A)(hh:0≤R)(hv:0<v)(hC:0≤C)(hB:0≤B)(ht:(U,V)∈partners T)(hk:r+s≤t)(hx: (parPort I t:ℝ)*v≤w)(hw:M.strip w C) (F:Owns w U (fun x=> A x U i j (r+1)) (B*p U))(G:Owns w V (fun x=> A x V e k (s+1)) (B*p V)) :
   Owns v T (fun x=> wounds none T M (A x U i j (r+1)) (A x V e k (s+1))) (bob_fee ‖syl r s‖ v B C*p T) := by
    have hP := mul_nonneg (bob_pos (B:=B) hv hC (norm_nonneg (syl r s))) (he.pos T)
    by_cases h:U=∅; · subst U; rw [show (fun x=> wounds none T M (A x ∅ i j (r+1)) (A x V e k (s+1)))=(fun x:Places I=>0) from funext fun a=>by rw [hu a]; exact wound_miss _ hh]; exact owns_none T _ hP _ _ _
    by_cases hV:V=∅; · subst V; rw [show (fun x=> wounds none T M (A x U i j (r+1)) (A x ∅ e k (s+1)))=(fun x:Places I=>0) from funext fun a=>by rw [hu a]; exact wound_wait _ hh]; exact owns_none T _ hP _ _ _
    obtain ⟨hp,hL⟩:= (norms_par ..).mp ht
    apply owns_mono (pair_mark hp hL (nonempty_iff_ne_empty.mpr hV) (nonempty_iff_ne_empty.mpr h) hv (par_need hk hv.le hx) (card_le_univ U) (card_le_univ V) hC hw F G) le_rfl
    rw [show _*(B*p (U:Finset I)*(B*p V*shells v))=bob_fee ‖syl r s‖ v B C*(p U*p V) by unfold bob_fee; ring]; apply mul_le_mul_of_nonneg_left (he.rise T (U,V) ht) (bob_pos hv hC (norm_nonneg _))
-- cash per degree e,r step explicitly

def posSticks (v B C:ℝ)(r e n:ℕ)(T:Finset I) :=
      let b:=∑ _i∈wheel n,∑ _j∈ wheel e, ∑ a ∈ wheel r, ‖syl a.1 a.2‖ * (C*C*B)
      let w:=∑ _i∈ partners T, ∑ _∈wheel n,∑ _∈wheel e, ∑ a∈wheel r, bob_fee ‖syl a.1 a.2‖ v B C
      ‖batting r‖*C*B+b+‖(1/2:ℝ)‖*w
lemma sticks_live (v B C:ℝ)(r e n:ℕ)(T:Finset I)(hv:0<v)(hB:0≤B)(hC:0≤C):0 ≤ posSticks v B C r e n T := by dsimp only [posSticks]; apply add_nonneg (add_nonneg (by positivity) (by positivity)); exact mul_nonneg (norm_nonneg _) (sum_nonneg (fun i _=> sum_nonneg (fun j _=> sum_nonneg fun k _=> sum_nonneg fun a _=>bob_pos hv hC (norm_nonneg _))))

-- note pear-shaped width parameters P.LINK; e cap. grant doesn't require hk' bigger for pre new ranks. 
lemma sticks_pass (he:Crease p) (hv:0<v) (hP:0≤R) (h:sleeps A)(hA: carnival p w B A n E) (hB:0≤B)(hC:0≤ C)(ht:(parPort I t:ℝ)*v≤w)(hf:r≤t)(hk:j≤n)(hc:e≤E)
      (hW:M.strip w C) (hQ:∀ i≤n,∀ j≤E,∀ k,Glow (Refrain M S none i j k) w C)(T:Finset I):
    Owns v T (fun x=> blue none M S (A x) T j e r) (posSticks v B C r e j T*p T):= by
    have hh := (port_w I t hv.le).trans ht
    have hZ : Owns v T (fun x=> jib none M (A x T j e (r+2))) (‖batting r‖*C*B*p T):= by
       have H:= owns_mono (hA j hk e hc T (r+2)) hh le_rfl
       rw [mul_assoc (‖batting r‖*C)]
       exact owns_tilt H le_rfl (mul_nonneg (norm_nonneg _) hC) (jib none M) (fun f z C K=> Ink.raise (jib_pail z K hv.le hW (hv.le.trans hh) hC) (by rw [mul_assoc]))
    unfold blue posSticks; dsimp only; rw [add_mul,add_mul]
    refine owns_plus (owns_plus hZ ?_) ?_
    · simp_rw [sum_mul]; refine owns_sum (wheel j) (U:=fun i x=>_) (fun i hi=>?_); refine owns_sum (wheel e) (U:=fun q x=>_) (fun q hq=>?_)
      unfold Quire.hymn; refine owns_sum (wheel r) (U:=fun a x=>_) (fun a ha=>?_)
      have hy:=mem_antidiagonal.mp hi; have hq:=mem_antidiagonal.mp hq; have hD:=mem_antidiagonal.mp ha
      have H₁:= hA i.1 (by omega) q.1 (by omega) T (a.1+1)
      have H₂:=hQ i.2 (by omega) q.2 (by omega) (a.2+1)
      let g:=Refrain M S none i.2 q.2 (a.2+1)
      have hl:(↑(a.2+1):ℝ)*v≤w:=le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show a.2+1≤parPort I t from by unfold parPort; omega)) hv.le) ht
      have hL:=strip_mono hW ((mul_le_mul_of_nonneg_right (show (a.2:ℝ)≤↑(a.2+1:ℕ) by push_cast; linarith) hv.le).trans hl) le_rfl
      cases hD.symm; simp_rw [grant_self]
      apply owns_mono (owns_tilt (owns_mono H₁ hl le_rfl) (le_mul_of_one_le_left hv.le (show _ by exact_mod_cast (show 1 ≤ a.2+1 by omega))) (op:=fun x=> clasp M x g) (mul_nonneg (norm_nonneg (syl a.1 a.2)) (mul_nonneg hC hC)) (fun U z u H=>Ink.raise (clasp_pail z H (glow_less H₂ hh le_rfl) hv.le hL hC) (le_of_eq (by ring)))) le_rfl (le_of_eq (by ring))
    rw [mul_assoc];
    let P:=fun x=> ∑ b∈partners T,spunL none M T b (A x) j e r
    apply owns_s (F:=P) _ (1/2)
    unfold P spunL taps; simp_rw [sum_mul]; refine owns_sum (partners T) (U:=fun b x=>_) (fun b hb=>?_) ; refine owns_sum (wheel j) (U:=fun c x=>_) (fun c hc'=>?_) ; refine owns_sum (wheel e) (U:=fun d x=>_) (fun d hd=>?_); refine owns_sum (wheel r) (U:=fun g x=>_) (fun g hg=>?_)
    have hL:=mem_antidiagonal.mp hc'; have hz:=mem_antidiagonal.mp hd; have hJ:=mem_antidiagonal.mp hg
    cases hJ.symm; simp_rw [grant_self]
    exact pair_fare he h hP hv hC hB (U:=b.1) (V:=b.2) hb (by omega) ht hW (hA c.1 (by omega) d.1 (by omega) _ _) (hA c.2 (by omega) d.2 (by omega) _ _)
end YM.RG08.Wax
