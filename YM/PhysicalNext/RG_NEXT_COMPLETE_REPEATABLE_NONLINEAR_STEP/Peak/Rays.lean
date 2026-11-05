import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
/-!
 # general Heir.Spec at integer cutoff (not promised E family at every calibration mark).
    Real projection. Keep Bundle costs.K weighed Z. Ports motif at general taper degree.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
     MultiNext.SignedSource MultiNext.SignedSource.Mom ProofPorts Next.Foundations Planned.AtomRegular MapPrices
open MultiNext.SignedSource.Banjo WardBin.Lies JointLoad.Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side} {k m n b D : ℕ}
open Source Labels
variable {o:Site c} {P : BudgetPoint}{X : Support c}{f' : Config G c→ℝ}


-- easier require exact directional through screen and prove

def lit (o:Site c)(X:Support c)(f:Config G c→ℝ)(d:ℕ) := ∀ (m:ℕ)(a:Fin m→ℕ)(v:Fin m→ Directions G c), (∑ i,a i) ≤ d→ (∀ i,1≤a i ∧ Mom.screen X (v i) ∈ Mom.Maps o X (a i))→ iteratedFDeriv ℝ m (f ∘ increment 1) 0 v=0
lemma spoke (g:Config G c→ℂ) (A:ℂ→L[ℝ] ℝ) (u:Source.Hol G) (X:Support c)
    (hg:P.Regular X g) (hx: Nonwrapping X o) (hc: 2≤ c.val)(hp:b≤P.order)(hk:b≤D)
    (hh:∀ (i:Jet G) (j:ℕ),j ≤ b → iteratedDeriv j (fun t:ℝ=>g (u.testLinks D o i t)) 0=0) : lit o X (A ∘ g) b:=by
  intro m a v ha he; have hm:m ≤ P.order:= (le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _=>1) (fun j _=> (he j).1)) ha).trans hp
  have hF:= hg.smooth 1 (one_healthy X P.threshold P.threshold_pos.le)
  have hf : ContDiffAt ℝ b (g ∘ increment 1) 0 := hF.of_le (Nat.cast_le.mpr hp)
  have hq : iteratedFDeriv ℝ m (g ∘ increment 1) 0 v=0:= Mom.wiped o X u hg.sites hg.symmetry hx hc hk hf hh a v ha he
  change iteratedFDeriv ℝ m (A ∘ (g ∘ increment 1)) 0 v=0; rw [A.iteratedFDeriv_comp_left (show ContDiffAt ℝ (↑(P.order:ℕ):ℕ∞ω) (g ∘ increment 1) 0 from hF) (Nat.cast_le.mpr hm)]; change A (iteratedFDeriv ℝ m (g ∘ increment 1) 0 v)=0; rw [hq,map_zero]
section discrete
-- use Rights outputs; caller small supports
variable {C ξ z:ℝ} (h:P.Regular X f')(he:Peak.lit o X f' b) (hb:P.supBounds o X f' z)
    (hξ:0≤ξ)(ht:ξ≤1)(hC:1≤ C)(Q: JointLoad.Heir.Rights G n) (hn:n ≤ P.order)
local notation "A"=> ((b:ℝ)+1)
include h he hb hξ ht hC Q hn
lemma spectrum (hm:m≤n)(v:Fin m→ Directions G c)(hv:∀ i, Promise b C ξ P o X (v i)) : ‖iteratedFDeriv ℝ m (f' ∘ increment 1) 0 v‖ ≤ (((b+1:ℝ)*C)^n* ξ^(b+1))*Q.fee*z:=by
  choose w hw hW hS using hv; let T := iteratedFDeriv ℝ m (f' ∘ increment (1:Config G c)) 0; change ‖T v‖ ≤ _
  have h0:= Q.large; have hφ:= hb.1; rw [funext hw,T.map_sum (α:=fun _=> Fin (b+1))]; apply (norm_sum_le ..).trans
  refine (Finset.sum_le_sum (g:=fun _=> (C^m*ξ^(b+1))*Q.fee*z) (fun j _=>?_)).trans ?_
  · let a (i:Fin m):ℕ:= (j i).val+1
    by_cases hh : ∑ i,a i≤ b
    · rw [show T _=0 from he _ _ _ hh (fun i=> ⟨Nat.zero_lt_succ _,hS i _ (by have hk:a i ≤ b:= (Finset.single_le_sum (f:=a) (fun _ _=> Nat.zero_le _) (Finset.mem_univ _)).trans hh; unfold a at hk; omega)⟩),norm_zero]; positivity
    apply (Q.born 1 _ (fun i=>C*ξ^(a i)) hm (hm.trans hn) h hb (one_healthy _ _ P.threshold_pos.le) (fun i=>hW i _)).trans
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hξ ht (by omega)) (by positivity)) (by positivity)) hφ
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  have hz:1≤ (A)*C:= one_le_mul_of_one_le_of_one_le (by simp) hC
  calc
    _= ((A*C)^m*ξ^(b+1))*Q.fee*z:=by push_cast; rw [mul_pow]; ring
    _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hz hm) (by positivity)) (by positivity)) hφ

-- doesn't ask Perr. Just cutoff graded b followed by sized tail.
omit h he hb hξ ht hC Q hn in
private lemma further {x y a b:ℝ}(h:‖x-y‖≤a)(h1:‖y‖ ≤ b) : ‖x‖ ≤ a+b:=by simpa using (norm_add_le (x-y) y).trans (add_le_add h h1)
lemma facet (u : Directions G c)(hu:Promise b C ξ P o X u) (ho:∀ i, needed X i → ‖u i‖ ≤ 1 ∧ Lyre.width P o i ≤ 1)
    (hs:∀ t ∈ Set.Icc (0:ℝ) 1, Healthy P.threshold X (increment 1 (t • u))) (hK: b+1≤n)(hm:m≤n) (v:Fin m → Directions G c) (hv:∀ j,Promise b C ξ P o X (v j)): ‖iteratedFDeriv ℝ m (f' ∘ increment 1) u v‖ ≤ (n+1:ℝ)*((A*C)^n * ξ^(b+1))*Q.fee*z:=by
  let F:= f' ∘ increment (1:Config G c); let s:= ((A*C)^n*ξ^(b+1))*Q.fee*z
  have hf:= Q.large; have hτ:= hb.1
  have hz: 0≤ s:=by unfold s; positivity
  have H (j)(hj:j≤n)(v:Fin j→ Directions G c)(hw:∀ i, Promise b C ξ P o X (v i))(x : ℝ)(hx:x∈ Set.Icc (0:ℝ) 1): ‖iteratedFDeriv ℝ j F (x • u) v‖ ≤ ((n+1-j:ℕ):ℝ)*s:=by
    have Hs t i (hp:t∈Set.Icc (0:ℝ) 1)(hi:i≤n):ContDiffAt ℝ (i:ℕ∞ω) F (t • u):= (JointLoad.Heir.along h (hs t hp)).of_le (Nat.cast_le.mpr (hi.trans hn))
    induction hj using Nat.decreasingInduction generalizing x with
    | self=>
       rw [show n+1-n=1 by omega,Nat.cast_one,one_mul]
       refine (Q.moves 1 (x • u) v (fun _=>A*C*ξ) le_rfl hn h hb (hs x hx) ?_ (fun i=> (hw i).shot hξ ht (zero_le_one.trans hC))).trans ?_
       · intro i hi; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hx.1]; exact ⟨mul_le_one₀ hx.2 (norm_nonneg _) (ho i hi).1,(ho i hi).2⟩
       rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin,mul_pow]; unfold s; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hξ ht hK) (by positivity)) (by positivity)) hτ
    | of_succ j hj ih =>
       have ha : ∀ i:Fin (j+1),Promise b C ξ P o X ((Fin.cons u v:Fin (j+1)→ Directions G c) i):=Fin.cases (by simpa using hu) (fun i=>by simpa using hw i)
       have H:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=> iteratedFDeriv ℝ j F (t • u) v) (fun x hx=> (along_deriv u v x (Hs x (j+1) hx hj)).hasDerivWithinAt)
         (fun x hx=> ih (Fin.cons u v) ha x hx) (convex_Icc ..) (show 0∈Set.Icc (0:ℝ) 1 by simp) hx
       rw [zero_smul,sub_zero,Real.norm_of_nonneg hx.1] at H
       have hp:= H.trans (mul_le_of_le_one_right (by positivity) hx.2)
       apply (further hp (spectrum h he hb hξ ht hC Q hn (Nat.le_of_lt hj) v hw)).trans_eq
       change _+s=_; rw [show n+1-j=n+1-(j+1)+1 by omega,Nat.cast_add_one,add_mul,one_mul]
  have hx := H m hm v hv 1 (by simp); rw [one_smul] at hx
  refine hx.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) hz).trans_eq ?_); unfold s; push_cast; ring
end discrete
end YM.PhysicalNext.Repeat.Peak
