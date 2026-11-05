import YM.Planned.PRIMARY_INTEGRAL_295.Glints
/-!
# C[k,k] cost in finite no-hole affine marginal with anchor cuts

Compares to exact hub-inverse only at central contact, *not* equality
across arbitrary hulls. Proves for represented real matrices. No
assuming larger weak H sectors. All polynomial u, epsilon L.B thresholds
payable by delay when actual ancestors secured. No earning global-E
thermal inverse/density chains. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Glints
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Tropics Cedar Precision Exterior Tree Streets Porous Carrier Bloch
open Progress.StationaryScenes.Green Push.Uniform Matrix Floor Glints.Windows Kelps
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace
variable {E F ι κ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n k : ℕ} {C M σ α u s : ℝ} {f : Side} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
private lemma estimate_sq (T:Matrix ι ι ℝ) (u:ℝ) (hu : 1≤u) (hc:(Fintype.card ι:ℝ)≤u) (ht:∀ i j, |T i j|≤u)
    (x:ι→ℝ) : (∑ i, (T.mulVec x i)^2) ≤ u^4 * ∑ i, x i^2 := by
   let r:=∑ i,x i^2; have hr:0 ≤ r:=by unfold r; positivity
   have he (i:ι) : (T.mulVec x i)^2 ≤ u^3*r:= by
      apply (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (T i) x).trans (mul_le_mul_of_nonneg_right ?_ hr)
      have hq j :=pow_le_pow_left₀ (abs_nonneg _) (ht i j) 2
      simp only [sq_abs] at hq; apply (Finset.sum_le_sum (fun j _=> hq j)).trans
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [pow_succ' u 2]; exact mul_le_mul_of_nonneg_right hc (by positivity)
   apply (Finset.sum_le_sum (fun i _=> he i)).trans
   simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; rw [pow_succ' u 3,mul_assoc]; exact mul_le_mul_of_nonneg_right hc (show 0≤u^3*r by positivity)

omit [DecidableEq ι] in
private lemma dot_card (x:ι→ℝ) : dotProduct x x=∑ i,x i^2:=by simp only [pow_two,dotProduct]

namespace Windows.Glaze
variable {e : κ↪ι} (K:Windows e) {h:Aim} {A:E→Matrix ι ι ℝ} {r:ℕ} {l:ι→Site f} (H: K.Glaze h A l k u r)
include H

-- δ bottom≥1/u⁵. No gap condition W(K) second beyond Camp.
omit [Fintype κ] [DecidableEq κ] in
lemma bottom_of_hub : Bottom (A 0)⁻¹ (u^5)⁻¹ := by
   have hb:=H.price; have he:= h.cap_t H.heat (lt_of_lt_of_le zero_lt_one hb)
   obtain ⟨hy,hq,hA⟩:= Aim.Camp.cost h H.camp
   have ht (i j) : |A 0 i j|≤u:= ((H.core i j).2.value).trans (mul_le_of_le_one_right (zero_le_one.trans hb) (h.dust_le ..))
   intro x; let p:= ((A 0)⁻¹).mulVec x -- syntax below
   have hv : (A 0).mulVec p=x:=by unfold p; rw [mulVec_mulVec,hy,one_mulVec]
   have hX : dotProduct x x ≤ u^4*dotProduct p p := by
      have hh:= estimate_sq (A 0) u hb H.tops ht p; rwa [hv,←dot_card,←dot_card] at hh
   have hP : 0 ≤ dotProduct p p:=by rw [dot_card]; positivity
   have hT:= H.camp.bottom p; rw [hv,dotProduct_comm p x] at hT
   refine (mul_le_mul_of_nonneg_left hX (show 0≤(u^5)⁻¹ by positivity)).trans ?_
   change _ ≤ dotProduct x p; apply le_trans _ hT; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hP
   have hv : u≠0:=by positivity
   rw [show (u^5)⁻¹*u^4=u⁻¹ from by field_simp]; exact he

def clearFuel (u:ℝ) := 2*u^5
omit H in
lemma clearFuel_pos (u:ℝ) (hu:1≤u) : 1≤clearFuel u:=by
   unfold clearFuel; refine one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hu)
/-- Bill at post thresholds. `r` any d_LLower paper B/25. -/
lemma balance (he:2*u^11*mist h r≤1) : Tropics.Clear (K.coin (A 0)) (clearFuel u) := by
   let B:= K.coin (A 0)
   let X:=(A 0)⁻¹; let D:=X.submatrix e e
   have hh: (Fintype.card κ:ℝ)≤u:= (Nat.cast_le.mpr (Fintype.card_le_of_embedding e)).trans H.tops
   let m:=u^5*mist h r
   have hX : X.IsHermitian:= by unfold X; rw [Matrix.IsHermitian, conjTranspose_nonsing_inv, H.camp.hm.eq]
   have hp i j : |(D-B) i j|≤m:=by
     let p:= K.reed (A 0) i (e j)-X (e j) (e i); let q:= K.reed (A 0) j (e i)-X (e i) (e j)
     have hq : (D-B) i j=-(1/2:ℝ)*(p+q) :=by
       simp only [D,B,Windows.coin,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.of_apply]; unfold p q
       rw [show X (e j) (e i)=X (e i) (e j) from hX.apply ..]; ring
     have hs : |p|≤m:=closer K H i (e j); have hu : |q|≤m:=closer K H j (e i)
     rw [hq,abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
     refine (mul_le_mul_of_nonneg_left (abs_add_le ..) (by norm_num : (0:ℝ)≤1/2)).trans ?_; linarith
   have hu:=H.price; have hm : 0≤m:= mul_nonneg (pow_nonneg (zero_le_one.trans hu) 5) (mist_pos _ _).le
   have ha : Bottom B (clearFuel u)⁻¹:= by
      have ht:Bottom D (u^5)⁻¹:= Bottom.restrict (H.bottom_of_hub K) e
      intro x; have hy: |dotProduct x ((D-B).mulVec x)| ≤ u*m*dotProduct x x:= by
         refine Progress.StationaryScenes.Green.schur _ _ _ (fun i=> ?_) fun i=>?_
         · apply (Finset.sum_le_sum (fun j _=>hp i j)).trans; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hh hm
         apply (Finset.sum_le_sum (fun j _=>hp j i)).trans; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hh hm
      rw [Matrix.sub_mulVec,dotProduct_sub] at hy
      have hm':0 < clearFuel u:=lt_of_lt_of_le zero_lt_one (clearFuel_pos u hu)
      have hd : u*m ≤ (clearFuel u)⁻¹:= by
         rw [← one_div,le_div_iff₀ hm']; apply le_trans _ he; unfold clearFuel m; apply le_of_eq; ring
      have hh : 2*(clearFuel u)⁻¹=(u^5)⁻¹:=by unfold clearFuel; field_simp
      have he' : 0≤dotProduct x x:=by rw [dot_card]; positivity
      have hv := ht x
      rw [← hh] at hv
      nlinarith only [(le_abs_self _).trans hy,hh,hv,mul_le_mul_of_nonneg_right hd he']
   refine ⟨clearFuel_pos u hu,K.coin_symmetric _,fun i=>?_⟩
   rw [EuclideanSpace.real_norm_sq_eq, Matrix.inner_toEuclideanCLM]; rw [← dot_card]
   have hw:=ha i; have hm':0 < clearFuel u:=lt_of_lt_of_le zero_lt_one (clearFuel_pos u hu)
   exact (by rwa [mul_comm,← div_eq_mul_inv, div_le_iff₀ hm', mul_comm _ (clearFuel u)] at hw)
end Windows.Glaze

section Embers
open Tropics
private lemma pure_one (i j:κ): ‖MapB κ (Matrix.single i j 1)‖ ≤ 1 :=by
   apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro x hx
   have he:= Finset.single_le_sum (s:=Finset.univ) (fun i _=>sq_nonneg (x i)) (Finset.mem_univ j)
   rw [←EuclideanSpace.real_norm_sq_eq,hx,one_pow] at he
   let H:=MapB κ (Matrix.single i j 1) x
   have hy : ‖H‖^2 ≤ 1:=by
     rw [EuclideanSpace.real_norm_sq_eq]
     have hM p:H p=(if p=i then x j else 0):=by
       change ((Matrix.single i j (1:ℝ)).mulVec (fun i=>x i)) p=_
       by_cases h : p=i
       · subst p; simp [Matrix.single,mulVec,dotProduct]
       simp [Matrix.single,mulVec,dotProduct, h,Ne.symm h]
     simp_rw [hM]; simpa using he
   nlinarith [norm_nonneg H]

lemma stream_em {B:E→Matrix κ κ ℝ} (h:∀ i j, Ember k (fun x=> B x i j) C) : Ember k (MapB κ ∘ B) ((Fintype.card κ:ℝ)^2*C):=by
    let f (i j:κ) :=fun x:E=> B x i j • MapB κ (Matrix.single i j 1)
    have he : MapB κ ∘ B = fun x=> ∑ i,∑ j,f i j x := by
       funext p; simp_rw [f,← map_smul,← map_sum]; change MapB κ (B p)=_
       apply congr_arg (MapB κ ·); ext i j; simp [Matrix.sum_apply,Matrix.single,ite_and]
    rw [he]; have hf i j : Ember k (f i j) C:=by
       let L:=ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (MapB κ (Matrix.single i j 1))
       have ht:= h i j
       have hh : ‖L‖≤1:= by
          apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro r hr
          change ‖r • MapB κ (Matrix.single i j 1)‖ ≤ _; rw [norm_smul,hr,one_mul]; exact pure_one ..
       have hb:= Seas.paidLinear L ht.1 ht.2 hh; rw [one_mul] at hb; exact ⟨(show ContDiffAt ℝ k (L ∘ fun x=>B x i j) 0 from L.contDiff.contDiffAt.comp _ ht.1), hb⟩
    have hy := Ember.cumul (fun i x=>∑ j,f i j x) (fun i=> Ember.cumul _ (hf i)); rw [← mul_assoc,←pow_two] at hy; exact hy
end Embers
end YM.Planned.PrimaryIntegral295.Glints
