import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Teller


/-!
# Use post-L currency on directional changes

Route counting without summing away intermediate keys. Transfers also
at intermediate visits which may coincide with endpoints. Fares reusable
from any tested site, *if* buying the according Knew/geometry overhead
only (not any derivative of log/HAAR etc.).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Differential
open Function Filter Set Matrix MeasureTheory FreeResolvent Ink TestD
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : E→Square ι} {x : E} {τ : Type*}
variable {D : Cost X} {v : τ→E} {G : Mark τ X} {p : ι→X} {W : ι→Set ι} {k n : ℕ} {C q B α β δ U ε : ℝ}

section weights
omit [DecidableEq ι] in
lemma fare_spend {A : Square ι} {l : List τ} {s : ℝ} (h : Mark.Bill G D p p l s α A) (i j : ι) :
    G.pay l (p i)*|A i j| ≤ α*D.weight (-s) (p i) (p j) := by
  have he := h.row.entry i j
  apply le_of_mul_le_mul_left (a:=D.weight s (p i) (p j)) _ (D.weight_pos ..)
  apply le_trans _ (le_trans he (le_of_eq ?_))
  · rw [mul_left_comm]
  rw [mul_left_comm,← Cost.weight_add,add_neg_cancel,Cost.weight_zero,mul_one]

omit [DecidableEq ι] in
lemma bundle_neg (h : Bundle v G D p p A x k δ α) : Bundle v G D p p (fun x => -A x) x k δ α := by
  have he := h.scale (-1); simp_rw [neg_one_smul] at he; simpa only [abs_neg,abs_one,one_mul] using he

def multiplier (U : ℝ) (k : ℕ) : ℝ := 2^k*U^k
lemma multiplier_large (k) (h : 1≤U) : 1 ≤ multiplier U k := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ h)
lemma multiplier_pos (k) (h : 1≤U) : 0 < multiplier U k := zero_lt_one.trans_le (multiplier_large k h)

omit [DecidableEq ι] in
/-- Price BEFORE unwinding/summing, valid also without closing the route. -/
lemma road_test {P S : E→Square ι} (hα : 0≤α) (hβ : 0≤β) (hd : 0≤δ) (hm : Mark.Move G D δ U) (hu : 1≤U)
    (hp : Bundle v G D p p P x k ((k+1:ℕ)*δ) α) (hs : Bundle v G D p p S x k ((k+1:ℕ)*δ) β) (l : List τ)
    (hl : l.length ≤ k) (i j : ι) (w : Fin n→ι) :
    let R := fares D p δ
    G.pay l (p i) * |jet v (fun y=>road (P y) (S y) i j w) l x| ≤ α*(multiplier U k *β)^n * road R R i j w := by
  intro R
  have hg : 0 ≤ U := zero_le_one.trans hu
  have hv : 0<multiplier U k := multiplier_pos k hu
  have hr (i j : ι) : 0 ≤ R i j := D.weight_nn ..
  let s : ℝ := (k+1:ℕ)*δ
  induction n generalizing P α i l with
  | zero =>
    simp only [road,pow_zero,mul_one]
    rw [entry v l (smooth_of_le hp.smooth hl)]
    exact fare_spend ((hp.bound l hl).mono (show δ ≤ s from le_mul_of_one_le_left hd (by push_cast; simp)) le_rfl) i j
  | succ n ih =>
    simp_rw [road]
    let r : ι := w 0; let t := Fin.tail w
    let A y:=P y i r
    let T y:=road (S y) (S y) r j t
    let W := β*(multiplier U k*β)^n *road R R r j t
    have hw : 0 ≤ W := mul_nonneg (by positivity) (road_pos _ _ hr hr r j t)
    have he m : G.pay l (p i)*|jet v A (lo l m) x * jet v T (hi l m) x| ≤ U^k * α * R i r * W := by
      set L := G.pay (lo l m) (p i)
      have hlo := (len_low l m).trans hl; have hhi := (len_high l m).trans hl
      have hL : 0≤L := (G.pay_pos (lo l m) (p i)).le
      have hb : L*|jet v A (lo l m) x| ≤ α*D.weight (-s) (p i) (p r) := by
        unfold A; rw [entry v _ (smooth_of_le hp.smooth hlo)]; exact fare_spend (hp.bound (lo l m) hlo) i r
      let C := D.weight (k*δ) (p i) (p r)
      have ht : 0 ≤ C := D.weight_nn ..
      have hM : G.pay (hi l m) (p i) ≤ U^k*C*G.pay (hi l m) (p r) := (hm.transfer hg _ _ _).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ hu hhi) (D.weight_mono
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hhi) hd) ..) (D.weight_nn ..) (pow_nonneg hg _)) (G.pay_pos ..).le)
      have hh : G.pay (hi l m) (p r)*|jet v T (hi l m) x| ≤ W := ih hβ hs _ hhi _ _
      have hq := (mul_le_mul_of_nonneg_left hh (mul_nonneg (pow_nonneg hg k) ht))
      rw [← mul_assoc] at hq
      rw [G.pay_masks l m (p i),abs_mul,mul_mul_mul_comm]
      apply (mul_le_mul hb ((mul_le_mul_of_nonneg_right hM (abs_nonneg _)).trans hq)
        (mul_nonneg (G.pay_pos ..).le (abs_nonneg _)) (mul_nonneg hα (D.weight_nn ..))).trans_eq
      calc _ = U^k * α * (D.weight (-s) (p i) (p r) * C) * W := by ring
           _ = _ := by unfold C; rw [← Cost.weight_add,show -s+k*δ= -δ by unfold s; push_cast; ring]; rfl
    have hh : jet v (fun y=> A y*T y) l x = ∑ m : Masks l, jet v A (lo l m) x*jet v T (hi l m) x :=
      leibniz v (ContinuousLinearMap.mul ℝ ℝ) l (typed (smooth_of_le hp.smooth hl) i r) (road_smooth (smooth_of_le hs.smooth hl) (smooth_of_le hs.smooth hl) r j t)
    change G.pay l (p i) *|jet v (fun y=>A y*T y) l x| ≤ _
    rw [hh]; apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (G.pay_pos ..).le).trans
    rw [Finset.mul_sum]; apply (Finset.sum_le_sum fun m _ => he m).trans
    simp only [Finset.sum_const,Finset.card_univ,TestD.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤ 2) hl) (mul_nonneg (mul_nonneg (by positivity) (hr _ _)) hw)).trans_eq
    rw [pow_succ _ n]; unfold W multiplier r t; ring
end weights
namespace Speech
variable (J : Speech D p W G v A x k δ U C q ε)

lemma jet_neg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E→F} (v : τ→E) (l : List τ)
    (h : ContDiffAt ℝ l.length g x) : jet v (fun y=> -g y) l x= -jet v g l x :=
    TestD.jet_linear v l (-ContinuousLinearMap.id ℝ F) h

include J


lemma stamp (z : Letter ι 0) (l : List τ) (hl : l.length ≤ k) :
    let i:=z.2.1; let w:=z.2.2; let P:=fares D p δ
    let g y:=errata W (A y) z
    ContDiffAt ℝ k g x ∧ G.pay l (p i)*|jet v g l x| ≤ (multiplier U k*q)^(z.1+1)*road P P i i w := by
  intro i w P g
  have hg := bundle_neg J.arrange
  let r y := road (-excess W (A y)) (-excess W (A y)) i i w
  let u := ((z.1:ℝ)+1)⁻¹
  have hi : g=fun y=>u • -r y := by ext1; unfold g errata; dsimp only; change -r _ / _ = u*_; rw [div_eq_mul_inv,mul_comm]
  have hu : 0 ≤ u := by unfold u; positivity
  have h := road_smooth hg.smooth hg.smooth i i w
  refine ⟨hi.symm ▸ h.neg.const_smul u,?_⟩
  have hk : u ≤ 1 := inv_le_one_of_one_le₀ (by simp)
  have hT : 0 ≤ road P P i i w := road_pos _ _ (fun _ _=>D.weight_nn ..) (fun _ _=> D.weight_nn ..) i i w
  rw [hi,jet_const_smul v l _ (smooth_of_le h.neg hl),jet_neg v l (smooth_of_le h hl),smul_eq_mul,
      abs_mul,abs_of_nonneg hu,abs_neg,mul_left_comm, pow_succ' (multiplier U k*q)]
  have he := road_test J.profit J.profit J.er.le J.motion J.paper hg hg l hl i i w
  apply le_trans (mul_le_of_le_one_left (mul_nonneg (G.pay_pos ..).le (abs_nonneg _)) hk)
  have hm : q ≤ multiplier U k * q := le_mul_of_one_le_left J.profit (multiplier_large k J.paper)
  exact he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (pow_nonneg (mul_nonneg (multiplier_pos k J.paper).le J.profit) _)) hT)

variable [FiniteDimensional ℝ E]

omit J in
lemma judge {g : ℝ→ℝ} (hU : 0≤U) (hf : IntegrableOn g (Ioi 0)) (h : ∀ u∈Ioi 0, U*|g u| ≤ C*attenuation u^2) :
    U*(∫ u in Ioi 0,|g u|) ≤ C ∧ U*|∫ u in Ioi 0,g u| ≤ C := by
  have he := hf.norm.const_mul U
  have hp : U*(∫ u in Ioi 0, |g u|) ≤ C := by
    rw [← integral_const_mul]
    exact (integral_mono_ae he (attenuation_square.1.const_mul C) ((ae_restrict_mem measurableSet_Ioi).mono h)).trans_eq (by
      rw [integral_const_mul,attenuation_square.2, mul_one])
  exact ⟨hp,le_trans (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hU) hp⟩



lemma standard (l : List τ) (i : ι) (hl : l.length ≤ k) :
    let f u:=jet v (fun y => attenuation u-pie W (A y) u i i) l x
    let g y:= letterBase W (A y) i
    ContDiffAt ℝ k g x ∧ IntegrableOn f (Ioi 0) ∧ jet v g l x=∫ u in Ioi 0, f u ∧
      G.pay l (p i)* |jet v g l x| ≤ if l=[] then (C+1)*C else C*ε := by
  intro f g
  have ht := annotated_base v J.work.smooth J.pd J.dawn i
  obtain ⟨he,hP⟩ := ht.2 l hl
  refine ⟨ht.1,he,hP,?_⟩
  by_cases hh : l=[]
  · subst l; rw [zeroth,Mark.pay,one_mul,if_pos rfl]; exact (J.priced.regular_price i).2
  rw [if_neg hh, (show jet v g l x=∫ u in Ioi 0,f u from hP)]
  suffices hv : ∀ u∈Ioi 0, G.pay l (p i)*|f u| ≤ (C*ε)*attenuation u^2 from (judge (G.pay_pos l (p i)).le (g:=f) he hv).2
  intro u hu
  have hj := smooth_of_le (J.started u hu.out.le).smooth hl
  unfold f
  rw [jet_sub v l contDiffAt_const (typed hj i i),jet_const v l hh,zero_sub,abs_neg,entry v l hj]
  have hh' := ((J.glimpse u hu.out.le l hl).row.entry i i)
  rw [D.weight_self, one_mul,charges,if_neg (ne_of_gt (List.length_pos_iff.mpr hh))] at hh'
  exact hh'.trans_eq (by unfold drain attenuation; ring)
end Speech
end YM.AnalyticBridge.RelativeLogdet.Differential
