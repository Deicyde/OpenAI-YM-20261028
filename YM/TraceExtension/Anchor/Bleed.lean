import YM.TraceExtension.Anchor.Range

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Function Filter Set Finset MeasureTheory Analysis Extraction Table Cells Lattice Wilson Next.UVStress
open Asymptotics
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

lemma dTap_sub (f g:ℤ→ℂ)(i : ℤ) : dTap (f-g) i=dTap f i-dTap g i:=by
   unfold dTap; rw [← sum_sub_distrib]; refine Finset.sum_congr rfl (fun j _=> ?_)
   simp only [Pi.sub_apply,smul_sub]; abel

def fare:ℝ := ∑ i, ‖cash i‖* (4*(steps i):ℝ)

lemma collective (f : ℤ→ℂ) (n:ℕ) (hn:10 ≤ n)(r:ℝ) (hf:∀ i:ℤ, -4 ≤ i→ i ≤ n+4→‖f i‖≤r) :
    ‖∑ l∈Finset.range n,dTap f l‖ ≤ fare*r := by
   let Q(i:Fin 4) := (steps i:ℤ)
   have hz(i:Fin 4): ‖∑ l∈Finset.range n, (f (l+Q i)-f (l-Q i))‖ ≤ ((2:ℝ)*(steps i)*r) * 2 := by
      -- overlapping ranges shifted each by steps, giving two strips of width 2 steps. fix coefficient.
      let a:= steps i; have ha:a ≤ 4:=by unfold a steps; have := i.isLt; omega
      let w:= n- (2*a); let P(j:ℕ):=f (j-(a:ℤ))
      have hg : w+2*a=n:=by omega
      have hy(l:ℕ) : f (l+Q i)=P (l+2*a):=by unfold P; congr 1; change (l:ℤ)+↑a= _-_; push_cast; ring
      have ht(l:ℕ) : f (l-Q i)=P l := rfl
      have hu:((∑ l∈Finset.range n, P (l+2*a)) + ∑ l∈Finset.range (2*a), P l) =
          (∑ l∈Finset.range (2*a+n), P l):= by rw [Finset.sum_range_add]; simp_rw [add_comm (2*a)]; abel
      have hB : ‖∑ l∈Finset.range n,(f ((l:ℤ)+Q i)- f ((l:ℤ)-Q i))‖=‖(∑ l∈Finset.range (2*a),P (n+l)) - ∑ l∈Finset.range (2*a),P l‖:=by
         rw [Finset.sum_sub_distrib]; simp_rw [hy,ht]; rw [← eq_sub_of_add_eq hu|>.symm]; rw [add_comm (2*a) n,Finset.sum_range_add]; congr 1; abel
      have hP(m:ℕ)(hm:m ≤ n): ‖∑ l∈Finset.range (2*a),P (m+l)‖ ≤ 2*(a:ℝ)*r:=by
         refine (norm_sum_le ..).trans (le_trans (sum_le_sum (fun l hl=> hf _ ?_ ?_)) (le_of_eq ?_))
         · simp only [Finset.mem_range] at hl; omega
         · simp only [Finset.mem_range] at hl; omega
         simp
      rw [hB]; have h:=hP 0 (Nat.zero_le _); simp only [zero_add] at h; have hh:=(norm_sub_le ..).trans (add_le_add (hP n le_rfl) h); exact hh.trans_eq (by ring)
   unfold dTap; rw [sum_comm]; simp_rw [← Finset.smul_sum]; refine (norm_sum_le ..).trans ?_
   unfold fare; rw [Finset.sum_mul]; refine sum_le_sum fun i _=>?_ ; rw [norm_smul]; exact (mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)).trans_eq (by ring)
section
variable {G : Gauge}{C : Family G}{S: Table C.book} {D:ℕ}
lemma sampling (S: Schedule) {p:ℝ} (hp:p<0) : ∃ n:ℕ→ℕ,(∀ᶠ k:ℕ in atTop,10 ≤ n k) ∧ Tendsto (fun k=> S.a k*n k) atTop (𝓝 0) ∧ Fast S fun k=> factor S p k/(S.a k*n k) := by
   let q:ℝ:=max (p/2) (-1/2); have hq:q<0:=max_lt (by linarith) (by norm_num); have hx:q>p:=lt_of_lt_of_le (by linarith only [hp]:p<p/2) (le_max_left ..)
   let n:ℕ→ℕ:=fun k=> Nat.ceil (factor S q k /S.a k); let a:=S.a
   have hz(k:ℕ): factor S q k ≤ S.a k*n k:= by rw [mul_comm]; exact (div_le_iff₀ (S.a_pos k)).mp (Nat.le_ceil _)
   have ht(k:ℕ): S.a k*n k ≤ factor S q k+S.a k:=by
      have hu:= mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (show 0≤factor S q k/S.a k from div_nonneg (Real.exp_pos _).le (S.a_pos _).le)) (S.a_pos k)
      exact hu.le.trans_eq (by rw [mul_add,mul_one,mul_div_cancel₀ _ (S.a_pos _).ne'])
   refine ⟨n,?_, squeeze_zero' ?_ (Eventually.of_forall ht) ?_,p-q,by linarith, isBigO_of_le _ ?_⟩
   · have hh := (factor_weight S (-1) q (lt_of_lt_of_le (by norm_num : (-1:ℝ)< -1/2) (le_max_right ..))).bound (show 0<(1/10:ℝ) by norm_num)
     filter_upwards [hh] with k hk
     rw [shrunk, Real.norm_of_nonneg (S.a_pos _).le,Real.norm_of_nonneg (Real.exp_pos _).le] at hk
     apply Nat.cast_le (α:=ℝ)|>.mp
     apply le_of_mul_le_mul_left _ (S.a_pos k); norm_cast at *
     linarith only [hk,hz k]
   · exact Eventually.of_forall fun k=> (Real.exp_pos (S.scale k*q)).le.trans (hz k)
   · have h : Tendsto (factor S q) atTop (𝓝 0):=Real.tendsto_exp_atBot.comp (by simpa [mul_comm _ q] using! S.divergent.const_mul_atTop_of_neg hq)
     simpa only [add_zero] using h.add S.shrinks
   intro k
   rw [factor_sub,Pi.div_apply]; simp only [norm_div, Real.norm_of_nonneg (Real.exp_pos _).le]
   rw [Real.norm_of_nonneg ((Real.exp_pos _).le.trans (hz k))]; gcongr
   exact hz k

variable (HE:S.Hierarchy)
include HE
private lemma moving_test (I:Watch C) (a:Axis){n:ℕ→ℕ}(ht:∀ᶠ i in atTop, (n i)>0)(hh:Tendsto (fun k=>C.S.a k*↑(n k)) atTop (𝓝 0)) (v:S.Field D):
    Tendsto (fun k=>(n k:ℝ)⁻¹ • ∑ i∈Finset.range (n k), plant I S D ((C.S.a k*(i:ℝ)) • basis a) v) atTop (𝓝 (I.tester S D v)):= by
   let p(z:ℝ):= plant I S D (z • basis a) v
   have hp : ContinuousAt p 0:=(spin_smooth HE I a (by rw [zero_smul,at_home]; exact I.distinct) v).continuousAt
   have hs:p 0=I.tester S D v:=by unfold p; rw [zero_smul,tester_home]
   rw [← hs]; apply Metric.tendsto_nhds.mpr; intro ε hε
   obtain ⟨u,hu,hU⟩:= Metric.continuousAt_iff.mp hp (ε/2) (half_pos hε)
   filter_upwards [hh.eventually (gt_mem_nhds hu),ht] with k hh he
   let N:=n k;let t:=C.S.a k; let y(i:ℕ):= p (t*i)
   have hf:0<t:=C.S.a_pos _
   change dist ((N:ℝ)⁻¹ • ∑ i∈Finset.range N,y i) (p 0)<ε
   rw [dist_eq_norm, ← show (N:ℝ)⁻¹ • (∑ _ ∈ Finset.range N,p 0)=p 0 by simp only [Finset.sum_const,Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; rw [inv_mul_cancel₀ (by exact_mod_cast he.ne'),one_smul], ← smul_sub, ← Finset.sum_sub_distrib]
   have h (i:ℕ) (hp:i∈ Finset.range N) : ‖y i-p 0‖≤ε/2:=by
       rw [Finset.mem_range] at hp
       have ht:t*i<t*N:=mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hp) hf
       rw [← dist_eq_norm]; refine (hU (show dist (t*(i:ℝ)) 0 < u from ?_)).le; rw [dist_zero_right,Real.norm_of_nonneg (by positivity)]; exact ht.trans hh
   rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]; refine lt_of_le_of_lt ((mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum h)) (inv_nonneg.mpr (Nat.cast_nonneg N))).trans (le_of_eq (b:=ε/2) ?_)) (by linarith only [hε]); simp [← mul_assoc,(show (N:ℝ)≠0 by exact_mod_cast he.ne')]
lemma differentiation (W:DiffPlan S) (hw:W.Derivatives S) {b:Filter (ℕ×ℕ)} [b.NeBot] {X Y:CutNet C} {v:ℕ→S.Field D}{w:ℕ→S.Field (D+1)} (a:Axis)
    (hd : D ≤ 7)(hp : Book b X v)(hx: Calms C.S D v)(hT: Book b Y w)
    (hr : ∀ I: Watch C, ∀ᶠ k:ℕ in atTop,∀ᶠ i : ℕ×ℕ in b,∀ l:ℤ,smoke I (l • step a) Y k i.1 i.2=(C.S.a k)⁻¹ • dTap (fun j=>smoke I (j • step a) X k i.1 i.2) l): Fast C.S (fun k=> W.deriv D a (v k) - w k):=by
   apply response_fast HE _
   intro I
   obtain ⟨c1,hc1,E,hE,he⟩:=hp I
   obtain ⟨c2,hc2,F,hF,hf⟩:=hT I
   obtain ⟨c₃,q,B,hc₃,hq,hB⟩:=axis_advance (d:=D) HE I a W hw
   obtain ⟨p,hp,hE'⟩:= Fast.money hE; obtain ⟨n,hN,hn,HN⟩:= sampling C.S hp
   let A:= C.S.a; let c:= min (min c1 c2) c₃; have cH:0<c:=lt_min (lt_min hc1 hc2) hc₃
   let T (k):= ((n k:ℝ)⁻¹) • ∑ i∈Finset.range (n k), plant I S (D+1) ((A k*(i:ℝ)) • basis a)
   have heq k x : T k x= (n k:ℝ)⁻¹ • ∑ i∈Finset.range (n k), plant I S (D+1) ((A k*(i:ℝ)) • basis a) x:=by unfold T; rw [LinearMap.smul_apply,LinearMap.sum_apply]
   refine ⟨T,fun x=>by simp_rw [heq]; exact moving_test HE I a (hN.mono (fun _ h=> Nat.lt_of_lt_of_le (by decide) h)) hn x,?_⟩
   let C' k : ℝ:= B * ‖v k‖*A k^8
   let M k:= factor C.S p k/(A k * n k)*fare
   have h : Calms C.S ((D:ℝ)-8) C':=by
      have hV: Calms C.S D (fun k=> ‖v k‖):=fun p hp=> isBigO_norm_left.mpr (hx p hp)
      have ht: (fun k=> A k^8)=factor C.S (-8):=funext (fun k=> by unfold A; rw [← shrunk C.S k,factor,factor,← Real.exp_nat_mul]; congr 1; norm_num; ring)
      exact (show (fun _=>B)*(fun k=> ‖v k‖)*factor C.S (-8)=C' by rw [← ht];rfl) ▸
         (show Calms C.S (D-8:ℝ) _ by rw [sub_eq_add_neg]; exact ((zero_add (D:ℝ)) ▸ Calms.mul (show Calms C.S 0 fun _=> B from fun x he=> factor_const _ _ _ he) hV).mul (factor_calms _ _))
   have hD : (D:ℝ)-8 < -(1/2:ℝ):=by have ht : (D:ℝ) ≤ 7:= Nat.cast_le.mpr hd; linarith only [ht]
   have h0:= Fast.add (Fast.add (show Fast C.S C' from ⟨- (1/2),by norm_num,h _ hD⟩) (show Fast C.S M from HN.mul (fun _ h=> factor_const _ fare _ h))) (hF.smaller (show (fun k=> ‖F k‖) =O[atTop] F from isBigO_norm_left.mpr (isBigO_refl ..)))
   apply h0.smaller
   have hk : ∀ᶠ k in atTop,A k*((n k:ℝ)+4) ≤ c:=by
      have ht : Tendsto (fun k=> A k*((n k:ℝ)+4)) atTop (𝓝 0):=by simpa only [mul_add,zero_mul,add_zero] using! hn.add (C.S.shrinks.mul_const (4:ℝ))
      exact ht.eventually (ge_mem_nhds cH)
   refine isBigO_iff.mpr ⟨1,?_⟩
   filter_upwards [hN,hk,he,hf,hE',hr I,(C.S.shrinks.eventually (ge_mem_nhds hq))] with k hN hK hZ hY hE hR hq
   let x:=A k; have hx':0<x:= C.S.a_pos k; let N:=n k; let Z(l:ℤ)(d:ℕ):= plant I S d ((l*x:ℝ) • basis a)
   have hm(l:ℤ) (hi:-4 ≤ l)(hp:l ≤ N+4): |(l:ℝ)*x| ≤ c:=by
      rw [abs_mul, abs_of_pos hx',mul_comm]; apply le_trans _ hK
      apply mul_le_mul_of_nonneg_left _ hx'.le; change |(l:ℝ)| ≤ (N:ℝ)+4
      rw [abs_le]; constructor
      · have hf:-(4:ℝ) ≤ l:=by exact_mod_cast hi
        linarith [Nat.cast_nonneg (α:=ℝ) N]
      exact_mod_cast hp
   let J:=Finset.Icc (-4:ℤ) (N+ (4:ℤ)); let u l:=Z l D (v k)
   let u' l:= Z l (D+1) (W.deriv D a (v k)); let g l := Z l (D+1) (w k)
   let X (l:ℤ)(i:ℕ×ℕ):=smoke I (l • step a) X k i.1 i.2; let Y (l:ℤ)(i:ℕ×ℕ):= smoke I (l • step a) Y k i.1 i.2
   have hs:∀ᶠ i:ℕ×ℕ in b, ∀ l∈ J, ‖X l i-u l‖ ≤ ‖E k‖ ∧ ‖Y l i-g l‖ ≤ ‖F k‖:=by
       refine (J.eventually_all.mpr (fun l hl=> ?_)); obtain ⟨ht,h⟩:= Finset.mem_Icc.mp hl
       have hd:= (hm _ ht h).trans (min_le_left ..); exact (hZ l a (hd.trans (min_le_left ..))).and (hY l a (hd.trans (min_le_right ..)))
   obtain ⟨i,hx,hy⟩:= (hs.and hR).exists
   let V(l:ℤ):=X l i
   have he i' : T k i'=(N:ℝ)⁻¹ • ∑ l ∈ Finset.range N, Z (l:ℤ) (D+1) i':=by rw [heq]; simp [Z,N,x,A, mul_comm]
   rw [he]; simp_rw [map_sub]; change ‖(N:ℝ)⁻¹ • ∑ j∈ Finset.range N,(u' (j:ℤ)-g (j:ℤ))‖ ≤ 1*_ ; rw [one_mul]
   let J':=Finset.range N; let t l:= x⁻¹ • dTap u l; let z l:= x⁻¹ • dTap V l
   have ha k' (h:k'∈J'): (k':ℤ)∈J:= Finset.mem_Icc.mpr ⟨by omega, by have h:= Finset.mem_range.mp h; omega⟩
   have hU(l:ℕ)(ht:l ∈ J'):‖u' l-t l‖≤C' k:=by rw [norm_sub_rev]; have h1:= Finset.mem_Icc.mp (ha _ ht); exact hB _ x hx' hq ((hm _ h1.1 h1.2).trans (min_le_right ..)) _
   have ht:‖(N:ℝ)⁻¹ • ∑ l∈J',(u' l-t l)‖ ≤ C' k:=by
      rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ)⁻¹)]; exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum hU)) (by positivity)).trans_eq (by simp only [Finset.sum_const,J',Finset.card_range,nsmul_eq_mul]; field_simp [show (N:ℝ)≠0 by exact_mod_cast (show n k≠ 0 by omega)])
   have hf(l:ℕ)(ht:l∈J'): ‖z l-g l‖ ≤ ‖F k‖:=by
      have he:Y l i=z l:=hy _; rw [← he]; exact (hx _ (ha _ ht)).2
   have hG:‖(N:ℝ)⁻¹ • ∑ l∈J',(z l - g l)‖ ≤ ‖F k‖:=by
      rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ)⁻¹)]; exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum hf)) (by positivity)).trans_eq (by simp only [Finset.sum_const,J',Finset.card_range,nsmul_eq_mul]; field_simp [show (N:ℝ)≠0 by exact_mod_cast (show n k≠ 0 by omega)])
   have hH: ‖(N:ℝ)⁻¹ • ∑ l∈J',(t l - z l)‖ ≤ M k:=by
      have hu : (∑ l ∈ J', (t l-z l)) = x⁻¹ • ∑ l∈ J', dTap (u-V) l:=by simp_rw [dTap_sub,Finset.smul_sum,smul_sub]; rfl
      rw [hu,norm_smul,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ)⁻¹), Real.norm_of_nonneg (by positivity : 0 ≤ x⁻¹)]
      have hD(l:ℤ)(h1:-4 ≤ l)(h2:l ≤ N+4): ‖(u-V) l‖ ≤ factor C.S p k:= by
          rw [Pi.sub_apply,norm_sub_rev]; exact (hx l (Finset.mem_Icc.mpr ⟨h1,h2⟩)).1.trans hE.le
      exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (collective _ _ hN _ hD) (by positivity)) (by positivity)) (le_of_eq (by unfold M x A N; ring))
   have hs : ∑ j∈ J',(u' (j:ℤ)-g j)=(∑ j∈ J',(u' j-t j))+(∑ j∈ J',(t j-z j)) + ∑ j∈J', (z j-g j) :=by simp_rw [Finset.sum_sub_distrib]; abel
   rw [hs,smul_add,smul_add]; apply le_trans (le_trans (norm_add_le ..) (add_le_add (le_trans (norm_add_le ..) (add_le_add ht hH)) hG))
   exact Real.le_norm_self _
end
end YM.Trace.Pull
