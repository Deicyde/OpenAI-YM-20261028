import YM.FullVolume.Tess.Bowl
import YM.FullVolume.Ray.Mono
/- equally spaced tables, elementary. pays C^M times sample max on all M including remainder estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset RG Push.AbsoluteSums Ray Asymptotics
open PhysicalNext.Repeat.Muse
open scoped Topology BigOperators Classical ContDiff
variable {n m k:ℕ}{r:ℝ}
open Polynomial
lemma Crop.book (X Y: Beam ℂ)(p:Fin (n+1)→ sun)(h:Injective p)(hp:Crop X n)(hq:Crop Y n)(he:∀ i, read ℂ (p i) X=read ℂ (p i) Y):X=Y:=by
    let P := fun X:Beam ℂ=> ∑ i∈Finset.range (n+1), Polynomial.monomial (R:=ℂ) i (X i)
    have hv (X:Beam ℂ) : (P X).degree < (Finset.univ (α:=Fin (n+1))).card:=by
        apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _); rw [Finset.sup_lt_iff] <;> try exact WithBot.bot_lt_coe _
        intro i hi; apply lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) (WithBot.coe_lt_coe.mpr ?_); simpa using Finset.mem_range.mp hi
    have hX (X:Beam ℂ)(hp:Crop X n)(s:sun): read ℂ s X=(P X).eval (s.val:ℂ):=by
         unfold P; rw [Crop.still X hp,eval_finsetSum]; apply sum_congr rfl; intro i _; rw [eval_monomial,mul_comm,← Complex.ofReal_pow]; exact (IsScalarTower.algebraMap_smul ℂ (s.val^i) (X i)).symm
    let p' (i:Fin (n+1)):ℂ:= (p i).val
    have ht:Injective p':= Complex.ofReal_injective.comp (Subtype.val_injective.comp h)
    have hh:= eq_of_degrees_lt_of_eval_index_eq _ ht.injOn (hv X) (hv Y) (fun i _=> (hX X hp (p i)).symm.trans ((he i).trans (hX Y hq (p i)))) -- open poly
    exact soul X Y (fun s=> by change read ℂ s X= read ℂ s Y; rw [hX _ hp,hX _ hq,hh])
section
variable {Y : Type*}[NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (V:ℕ→sun)(f:sun→Y)(X: Beam Y)
-- degree-n divided difference table step
lemma joined (i k:ℕ)(A B:Beam Y)(v:ℝ)(hv:0<v)(hV:(V (i+(k+1))).val-(V i).val=v)(ha:Crop A k)(hb:Crop B k)
    (hp:∀ j:ℕ,i ≤  j→ j  ≤ i+k→ read Y (V j) A=f (V j)) (he:∀ j:ℕ,i+1  ≤  j→j ≤ i+(k+1)→ read Y (V j) B=f (V j)):
      ∃ X: Beam Y,Crop X (k+1) ∧ ‖X‖  ≤  2*(‖A‖+‖B‖)/v ∧ ∀ j:ℕ,i  ≤  j→ j  ≤  i+(k+1)→ read Y (V j) X=f (V j):= by
    let a:= V i; let b:= V (i+(k+1)); let Z:= arms b A-arms a B
    refine ⟨v⁻¹ • Z, Crop.timesP _ (Crop.play _ (Crop.marsh _ _ ha) _ (Crop.marsh _ _ hb)) _,?_,?_⟩
    · rw [norm_smul,norm_inv,Real.norm_of_nonneg hv.le,← div_eq_inv_mul]; exact div_le_div_of_nonneg_right ((norm_sub_le ..).trans ((add_le_add (armsN ..) (armsN ..)).trans_eq (by ring))) hv.le
    intro j hj hh; rw [map_smul] -- edit
    unfold Z; rw [map_sub, armsL,armsL]
    apply Eq.trans (congr_arg (v⁻¹ • ·) (_ : _ = v • f (V j))) (inv_smul_smul₀ hv.ne' _)
    by_cases h:i=j
    · subst j; rw [hp,show a=V i from rfl,sub_self,zero_smul,sub_zero]; rw [show _= v from hV]; rfl; omega
    have hvB := he j (by omega) hh; by_cases h' : j=i+(k+1)
    · subst j; rw [hvB]; unfold b; rw [sub_self,zero_smul,zero_sub,← neg_smul,neg_sub,show _= v from hV]
    rw [hp j hj (by omega),hvB,← sub_smul, sub_sub_sub_cancel_right,show _=v from hV]
lemma twins (M:ℝ)(hv:∀ k, ‖f (V k)‖ ≤  M)(C:ℝ)(hc:0<C){s:ℕ}(he:∀ k:ℕ, k ≤ s→ (V k).val=k/C)(i k:ℕ)(h:i+k  ≤  s):∃ X:Beam Y, Crop X k ∧ ‖X‖ ≤ (4*C)^k/(Nat.factorial k:ℝ)*M ∧ ∀ j:ℕ,i  ≤  j→ j  ≤  i+k→ read Y (V j) X=f (V j):=by
    induction k generalizing i with
    | zero=>
       refine ⟨arm (f (V i)),Crop.shoots _,by simpa [armN] using hv i,fun j hh h'=>?_⟩
       rw [show i=j from (by omega)]; exact armL ..
    | succ k ih=>
       obtain ⟨A,hA,hX,hP⟩:= ih i (by omega); obtain ⟨B,hB,hY,hQ⟩:= ih (i+1) (by omega)
       let v:=((k+1:ℕ):ℝ)/C; have hp:0<v:=by unfold v; positivity
       have hx:(V (i+(k+1))).val-(V i).val=v:=by rw [he _ h,he _ (by omega)]; unfold v; push_cast;ring
       obtain ⟨X,hX0,hz,hK⟩:= joined V f i k A B v hp hx hA hB hP (fun j hj ht=> hQ j hj (by omega))
       refine ⟨X,hX0,hz.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hX hY) zero_le_two) hp.le).trans_eq ?_),hK⟩
       unfold v; rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]; have ha:0< ((k+1:ℕ):ℝ):=by positivity
       field_simp; ring
end
lemma rocketP (k:ℕ) (hk:0<k): ∃ V:ℕ→sun,(∀ i:ℕ,i  ≤  k→ (V i).val=(i:ℝ)/k):=by
    choose V hV using fun i:ℕ=> show ∃ v:sun,i  ≤  k→ v.val=(i:ℝ)/k from (by
        by_cases h:i ≤  k
        · have hp : 0 ≤ (i:ℝ)/k:=by positivity
          refine ⟨⟨(i:ℝ)/k,⟨by linarith,?_⟩⟩,fun _=> rfl⟩; exact (div_le_one (by positivity)).2 (by exact_mod_cast h)
        let a:sun:=⟨0,⟨by norm_num,by norm_num⟩⟩; exact ⟨a,fun ht=> (h ht).elim⟩)
    exact ⟨V,hV⟩
abbrev aurora :ℝ:=4*Real.exp 1
lemma aurora_above : 1<aurora:=by unfold aurora; have hh:= Real.add_one_le_exp (1:ℝ); linarith
lemma welded (X: Beam ℂ)(h:Crop X k)(c:ℝ) (hc:∀ v:sun, ‖read ℂ v X‖ ≤  c):‖X‖ ≤ aurora^k*c:=by
   rcases Nat.eq_zero_or_pos k with hk | hk
   · subst k
     let a:sun:=⟨0,⟨by norm_num,by norm_num⟩⟩; have he:=hc a
     rw [Crop.still X h] at he; have ht:X=arm (X 0):=by
          apply lp.ext; funext i; change X i=arm (X 0) i; rcases Nat.eq_zero_or_pos i with hh | hh; subst i; simp [arm,lp.single_apply]; rw [Crop.shoots _ i hh]; exact h i hh
     rw [pow_zero,one_mul,ht,armN]; simpa using he -- avg
   obtain ⟨p,hp⟩:= rocketP k hk; let f(v:sun):= read ℂ v X
   obtain ⟨U,hU,hq,hP⟩:= twins p f c (fun _=> hc _) (k:ℝ) (by positivity) hp 0 k (by omega)
   have hx:0 ≤  c:=(norm_nonneg _).trans (hc (p 0))
   let y(i:Fin (k+1)):= p i.val
   have hy: Injective y:= by
       have h' : (k:ℝ) ≠ 0:=by positivity
       intro i j hx
       have he := congr_arg Subtype.val hx; unfold y at he; rw [hp i (by have h:=i.isLt; omega),hp j (by have h:=j.isLt; omega)] at he; exact Fin.ext (Nat.cast_injective (div_left_inj' h' |>.mp he))
   have hh : U=X:= Crop.book U X y hy hU h (fun i=> hP _ (by omega) (by have h:=i.isLt; omega))
   refine le_trans (hh ▸ hq) (mul_le_mul_of_nonneg_right ?_ hx); unfold aurora
   rw [mul_pow,mul_pow,mul_div_assoc]
   apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← Real.exp_nat_mul, mul_one]; exact Real.pow_div_factorial_le_exp _ (by positivity) k
end YM.FullVolume.Amp.Beam
#print axioms YM.FullVolume.Amp.Beam.welded
