import YM.TraceExtension.Shelves.Wilt
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Set Finset MeasureTheory Analysis Extraction Table Cells Lattice Wilson Next.UVStress
open Asymptotics Pull
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C : Family G}{S: Table C.book} {D:ℕ}
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
lemma front_low (h:G.Simple)(I:Watch C)(x:E4)(hd:D<4)(hv:rows I x∈conf _)(v:S.Field D): plant I S D x v=plant I S D 0 v:=by
    let F:= C.labels.level D; let P:= S.representative D v; have hp : P=P 0 • F.e0:=by
        ext1 i; by_cases ht:i=0; subst i; simp[Labels.Frame.e0]
        exfalso;have hx:= nbase F (by omega) i ht h; have h:=F.bound i; omega
    let z:ℂ:= (C.S.a (C.ref D))^(D:ℕ); have he : z ≠ 0:=by change ( (C.S.a (C.ref D):ℂ)^ (D:ℕ))≠0; apply pow_ne_zero; exact_mod_cast (C.S.a_pos _).ne'
    have hu:v=(P 0*z⁻¹) • S.unit D:= calc
         v=S.project D P := (S.rep D v).symm
         _=(P 0*z⁻¹) • S.unit D:=by nth_rw 1 [hp]; rw[map_smul,mul_smul, show z⁻¹ • S.unit D=S.project D F.e0 from ?_]; change z⁻¹ • S.project D (z • F.e0)=_; rw[map_smul,inv_smul_smul₀ he]
    conv=> arg 1;rhs;rw [hu]
    conv=> arg 2;rhs;rw[hu]
    rw[map_smul,map_smul]; apply congr_arg; unfold plant; rw[Work.A01.front_eval,Work.A01.front_eval,S.at_unit HE.laws hv, S.at_unit HE.laws (show rows I 0∈_ from ?_)];· rfl
    rw[at_home]; exact I.distinct
-- forward difference on Horizon3, projects onto exact unit
lemma lent {b:Filter (ℕ×ℕ)} [b.NeBot]{X Y: CutNet C}{v:ℕ→ S.Field 3}{w:ℕ→ S.Field 4}(a:Axis)(h:G.Simple)(hp:Book b X v)(hY:Book b Y w)
   (hx:∀ I:Watch C,∀ᶠ k in atTop,∀ᶠ i in b,∀ l:ℤ,let f(q:ℤ):=Pull.smoke I (q • step a) X k i.1 i.2; Pull.smoke I (l • step a) Y k i.1 i.2=(C.S.a k)⁻¹ • (f (l+1)-f l)):
     Fast C.S w:=by
    apply response_fast HE w; intro I; obtain ⟨cX,hX,E,hE,he⟩:=hp I; obtain ⟨cY,h',V,hV,hV'⟩:=hY I; obtain ⟨B,hB,H⟩:= screen I; let c:=min (min cX cY) B; have hc:0<c:=lt_min (lt_min hX h') hB
    obtain ⟨p,hp,hE'⟩:=Fast.money hE; obtain ⟨n,hN,hn,H'⟩:= sampling C.S hp
    let t:=C.S.a; let f k(j:ℕ):=plant I S 4 ((t k*j:ℝ) • basis a); let u k:= (n k:ℝ)⁻¹ • ∑ j∈ Finset.range (n k), f k j
    have hx'(k:ℕ)(v:S.Field 4): u k v=(n k:ℝ)⁻¹ • ∑ j∈ Finset.range (n k), f k j v:=by unfold u; rw[LinearMap.smul_apply,LinearMap.sum_apply]
    refine ⟨u,fun v=>by simp_rw [hx']; exact moving_test HE I a (hN.mono (fun i hi=> lt_of_lt_of_le (by omega) hi)) hn v,?_⟩
    let q(k):= factor C.S p k/(C.S.a k*n k) * (2:ℝ)
    have hQ: Fast C.S (fun k=> ‖V k‖ + q k):= ((hV.smaller (isBigO_norm_left.mpr (isBigO_refl ..))).add (H'.mul (fun _ he=> factor_const _ (2:ℝ) _ he)))
    refine hQ.smaller (isBigO_iff.mpr ⟨1,?_⟩);
    filter_upwards [hN, he, hV', hx I,hE', hn.eventually (ge_mem_nhds hc)] with k hN he hr h hh hC
    let N:= n k; let A:= C.S.a k; have hs:0<A:= C.S.a_pos _; have htA:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
    have hf(l:ℕ)(hl:l≤N): |(l:ℝ)*A| ≤ c:= (abs_of_nonneg (by positivity : 0≤ (l:ℝ)*A)).trans_le (by rw [mul_comm]; exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) hs.le).trans hC)
    let U:= Finset.range N; have hp(l:ℕ)(hl:l≤N):((l:ℤ):ℝ)=l:=by exact_mod_cast (by rfl : (l:ℤ)=l)
    let H₁(k':ℕ)(i:ℕ×ℕ):=Pull.smoke I ((k':ℤ) • step a) Y k i.1 i.2; let T₁ (l:ℤ)(i:ℕ×ℕ):= Pull.smoke I (l • step a) X k i.1 i.2; let P:=plant I S 3 0 (v k); have hT(j:ℕ)(hl:j≤N):∀ᶠ i in b,‖T₁ (j:ℤ) i-P‖≤ ‖E k‖:=by
        have hh:= (hf j hl); have hk : |((j:ℤ):ℝ)*A| ≤ c:=(by rwa [hp j hl]); have hx':rows I ((((j:ℤ):ℝ)*A) • basis a)∈conf _:= generic_conf _ (H _ ((by simpa [norm_smul] using hk.trans (min_le_right ..))))
        have ht:= he (j:ℤ) a (hk.trans ((min_le_left ..).trans (min_le_left ..)))
        unfold A at hx'; simp_rw [front_low HE ‹_› I _ (by omega) hx' (v k)] at ht;exact ht
    let y(l:ℕ):= f k l (w k); have hW(j:ℕ)(hl:j∈U): ∀ᶠ i in b, ‖H₁ j i-y j‖ ≤ ‖V k‖:=by
       have hx : j ≤ N:= le_of_lt (Finset.mem_range.mp hl); have hw:= hf j hx; rw [← hp j hx] at hw; have hq:= hr (j:ℤ) a (hw.trans ((min_le_left ..).trans (min_le_right ..))); simp_rw [show ((j:ℤ):ℝ)*C.S.a k=t k*j from (by rw[hp j hx,mul_comm])] at hq; exact hq
    obtain ⟨i,ht,hM,hP,hN'⟩:= (h.and ((U.eventually_all.mpr hW).and ((hT 0 (Nat.zero_le _)).and (hT _ le_rfl)))).exists
    rw [hx']; let V'(j:ℕ):= H₁ j i
    have hz: ‖(N:ℝ)⁻¹ • ∑ j∈U,(y j-V' j)‖ ≤ ‖V k‖:=by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (htA.le))]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (g:=fun _=>‖V k‖) (fun j hj=> ?_))) (by positivity)).trans_eq ?_
        · rw[norm_sub_rev]; exact hM j hj
        simp only [U,sum_const,card_range,nsmul_eq_mul, ← mul_assoc]; rw [inv_mul_cancel₀ htA.ne',one_mul]
    let f(x:ℕ):= T₁ (x:ℤ) i; have hF(k:ℕ):V' k=A⁻¹ • (f (k+1)-f k):= (ht (k:ℤ)).trans (by dsimp only [f,T₁];rw[Nat.cast_add,Nat.cast_one]);
    have hu': ‖(N:ℝ)⁻¹ • ∑ j∈U,V' j‖ ≤ q k:=by
        simp_rw [hF]; rw[← Finset.smul_sum,show ∑ j∈U,(f (j+1)-f j)=f N-f 0 from Finset.sum_range_sub f _,norm_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr htA.le), Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
        have hm:= norm_sub_le_norm_sub_add_norm_sub (f N) P (f 0); rw[norm_sub_rev P (f 0)] at hm; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hm.trans (add_le_add (hN'.trans hh.le) (hP.trans hh.le))) (inv_nonneg.mpr hs.le)) (inv_nonneg.mpr htA.le));apply le_of_eq; change _=factor C.S p k/(A*N) * 2;field_simp;ring
    apply le_trans _ ((Real.le_norm_self _).trans_eq (one_mul _).symm)
    change ‖(N:ℝ)⁻¹ • ∑ j∈U,y j‖ ≤ ‖V k‖+q k; rw [show ∑ j∈U,y j=(∑ j∈U,(y j-V' j))+∑ j∈U,V' j from (by rw [Finset.sum_sub_distrib,sub_add_cancel]), smul_add];
    exact (norm_add_le ..).trans (add_le_add hz hu')
end YM.Trace.Shelves
