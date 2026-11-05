import YM.TraceExtension.Terrace.Lyre
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG RG.Supply Wilson Push.PriceCompiler Push.GridApprox Vac Stock
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}(A:Levels G) {i j k:ℕ} (h:G.Simple) (θ:PostT A)

abbrev basin (K:Tabs A)(j:ℕ):= Tabs.chosen A 1 K j
variable (K:Tabs A)
lemma unwinds (i:ℕ): i ≤ basin A K i:= (Tabs.opened A 1 K i).1
lemma tracks (i:ℕ): Tabs.opens A 1 i (basin A K i):= Tabs.opened ..
lemma bondB : Tendsto (basin A K) atTop atTop:= tendsto_atTop_mono (unwinds A K) tendsto_id
lemma Bcharged(k:ℕ): ((A.clock.coverSize k):ℝ) ≤ Lyra A k^2 +1:=(Nat.ceil_lt_add_one (sq_nonneg (Lyra A k))).le
lemma gate_flex (d:ℕ) {c:ℝ}(hd:d<48)(hc:0<c):∀ᶠ x:ℝ in atTop,(Real.log x)^d ≤ c*Gate x:=by
    have he :0 <48-d:=by omega
    filter_upwards [((tendsto_pow_atTop (n:=48-d) (by omega)).comp Real.tendsto_log_atTop|>.const_mul_atTop hc).eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with x hx hi
    have hu:= Real.log_pos hi
    refine (le_mul_of_one_le_left (pow_nonneg hu.le d) hx).trans_eq ?_; simp only [comp_apply] at *;rw [mul_assoc,← pow_add,show 48-d+d=48 by omega];rfl
lemma summer (H:i≤ j): A.S.a i ≥ A.S.a j:= A.S.strictAnti.antitone H
lemma scale_p(j:ℕ) (hp:1≤Lyra A j): Lyra A j ≤ Gate (A.clock.hatBeta j):=by simpa only [Lyra,Gate,pow_one] using! pow_le_pow_right₀ hp (show 1 ≤ 48 by decide)
lemma lip (i:ℕ) (hu:8 ≤ Lyra A i):
    ((A.clock.coverSize i):ℝ) ≤ Lyra A i^3:=by
   apply (Bcharged ..).trans
   set y:=Lyra A i; have hz:0≤y:=by positivity
   nlinarith only [hu, mul_le_mul_of_nonneg_left hu hz,mul_le_mul_of_nonneg_left hu (sq_nonneg y)]
lemma expA (x:ℝ) : x ≤ Real.exp x:= le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)
include h θ
lemma open_budget : ∀ᶠ i:ℕ in atTop,basin A K i < summit A i :=by
    filter_upwards [bond A h θ,(lrate A h).eventually_ge_atTop 8] with i hB hi
    let x:= A.clock.hatBeta i; let y:= Lyra A i; let w:= Gate x; let K':= summit A i; let j:= K'-1; let m:= basin A K i
    have hk : i ≤ j ∧ j+1=K':=by have hp:i<K':=stellar ..; unfold j; omega
    have hx : 8 ≤ y:= hi; have hx':0 ≤ y:=by linarith only [hx]
    have ht : Lyra A j ≤ 2*y:= (lypos A h (show j≤K' from hk.2 ▸ Nat.le_succ j)).trans hB.2.1
    have hv: ((A.clock.coverSize j):ℝ) ≤5*y^2:= (Nat.cast_le.mpr (ladder A h (show j ≤ K' by omega))).trans hB.2.2
    have hz: w -2*y ≤ gap A i j:=by
       have hp:w ≤ gap A i j+gap A j (j+1):= (gstar A i).trans_eq (by rw[← triangle,hk.2])
       have he:gap A j (j+1) ≤2*y:= by rw[qNext]; exact (Real.log_le_self (Nat.cast_nonneg _)).trans ((θ.bloom j).trans ht)
       linarith only[hp,he]
    have hl : m ≤ j:=by
       refine Nat.find_min' _ (show Tabs.opens A 1 i j from ⟨hk.1,?_⟩)
       rw [one_mul,z_scale]
       refine (pow_le_pow_left₀ (Nat.cast_nonneg _) hv _).trans ?_
       -- below
       have hP : (5*y^2)^2 ≤ w-2*y:=by
           let z:= y^5; have ht:w ≥ y^6:= pow_le_pow_right₀ (by linarith) (by decide)
           have hY:y^2≤ y^3:= pow_le_pow_right₀ (by linarith) (by decide)
           have hh:y^2 ≥ 64:= by nlinarith only [hx]
           have hl:y≤ y^4:=by simpa only[pow_one] using pow_le_pow_right₀ (show 1 ≤ y by linarith) (show 1 ≤ 4 by decide)
           nlinarith only [ht, mul_le_mul_of_nonneg_left hh (pow_nonneg hx' 4), hl, hx']
       exact (hP.trans hz).trans (expA _)
    exact hl.trans_lt (show j < K' from hk.2 ▸ Nat.lt_succ_self j)
lemma Bgap :∀ᶠ i:ℕ in atTop, A.S.a i/A.S.a (basin A K i) ≤ (Lyra A i)^6∧ gap A i (basin A K i) ≤ Lyra A i^6:=by
    filter_upwards [open_budget A h θ K,bond A h θ,(lrate A h).eventually_ge_atTop 100,eventually_gt_atTop (0:ℕ)] with i ht hB hl hz
    let m:= basin A K i; let j:= summit A i; let x:= Lyra A i; have hx:x≥100:=hl; have hx':0≤x:=by linarith only [hx]
    have hM:i≤ m:=unwinds ..; have ht : m < j:=ht
    have he : A.S.a i/A.S.a m ≤ x^6:=by
      obtain ⟨k,hk⟩:= Nat.exists_eq_succ_of_ne_zero (show m≠0 by omega)
      have hu:k ≤ j:=by omega
      have hv: ((A.S.block k).val:ℝ) ≤ 2*x:= (θ.bloom k).trans ((lypos A h hu).trans hB.2.1)
      have hY: ((A.clock.coverSize k):ℝ)≤5*x^2:= (Nat.cast_le.mpr (ladder A h hu)).trans hB.2.2
      rw [hk]; apply (Tabs.expensive A 1 K le_rfl i k hk).trans; rw[one_mul]
      apply (mul_le_mul hv (pow_le_pow_left₀ (Nat.cast_nonneg _) hY _) (sq_nonneg _) (by linarith only [hx])).trans; nlinarith only [mul_le_mul_of_nonneg_right hx (pow_nonneg hx' 5),pow_nonneg hx' 5]
    refine ⟨he,?_⟩; rw [z_scale] at he; exact (expA _).trans he
lemma liability :∀ᶠ i:ℕ in atTop, (A.S.a i/A.S.a (basin A K i))^4 * Vac.treasury A (basin A K i) ≤ Lyra A i^27:=by
    filter_upwards [open_budget A h θ K,bond A h θ,Bgap A h θ K,(lrate A h).eventually_ge_atTop 100, (bondB A K).eventually (Vac.treasury_stage A h)] with i hi hb hv hx hs
    let x:= Lyra A i; let k:= basin A K i; have he:0≤x:=(lira ..).le
    have hm:Lyra A k ≤ 2*x:= (lypos A h hi.le).trans hb.2.1; have hP : Vac.treasury A k ≤ (2*x)^2:= hs.trans ((θ.purse _).trans (pow_le_pow_left₀ (lira ..|>.le) hm _))
    let u:= A.S.a i/A.S.a k
    apply le_trans (mul_le_mul_of_nonneg_left hP (pow_nonneg (div_nonneg (A.S.a_pos _).le (A.S.a_pos _).le) (4:ℕ))); apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg (A.S.a_pos _).le (A.S.a_pos _).le) hv.1 4) (sq_nonneg _)); have hp : 4 ≤ x:=by unfold x; linarith only [hx]
    linarith only [mul_le_mul_of_nonneg_left hp (pow_nonneg he 26)]
lemma glacier : ∀ᶠ i:ℕ in atTop, Gate (A.clock.hatBeta i)/2 ≤ gap A (basin A K i) (summit A i):=by
    filter_upwards [Bgap A h θ K, (hrate A h).eventually (gate_flex 6 (c:=1/2) (by decide) (by norm_num))] with i hx ht
    have he:=gstar A i; rw [triangle A i (basin A K i)] at he
    have hv:= ht; change Lyra A i^6≤ _ at hv; linarith only [hv,hx.2,he]
lemma wallK : ∀ᶠ i:ℕ in atTop, (↑(A.clock.J (summit A i)):ℝ) ≤ Lyra A (summit A i):=by
    refine (Sstar A).eventually (p:= fun i=>(↑(A.clock.J i):ℝ) ≤ Lyra A i) ?_; filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi
    cases i with
    | zero=> omega
    | succ i=> have ht := θ.cropK i; unfold ctl at ht; exact (Nat.cast_le.mpr (show A.clock.J _ ≤ (A.S.block i).val from le_trans (by omega) ht)).trans ((θ.bloom _).trans (lypos A h (Nat.le_succ _)))
-- any poly-x radius is okay. coarse bill for k
lemma Kagura(d:ℕ): ∀ᶠ i in atTop,∀ l:ℕ,(l:ℝ)≤ (A.clock.hatBeta (summit A i))^d → Push.GridApprox.room A i (summit A i) l:=by
   let C:ℝ:= 10000*2^d; have hx:0<C:=by unfold C; positivity
   have ht := ((Real.tendsto_exp_atTop.comp ((grate A h).const_mul_atTop (show 0 < (1/2:ℝ) by norm_num))).eventually_ge_atTop C)
   filter_upwards [bond A h θ,wallK A h θ,(lrate A h).eventually_ge_atTop 8,ht, (hrate A h).eventually (exponent_gate (1/2) d 1 (by norm_num))] with i hi hj hL ht hx l hl
   let t:= summit A i; let x:= A.clock.hatBeta i; let y:= Lyra A i; let B:= Gate x
   have hS:0< A.S.a t:= A.S.a_pos _; have hy:8 ≤ y:=hL; have hM:0 < y:= lira ..; have hx' :1 ≤ x:= (A.fits.delayed _).le
   unfold room tail; change 2*(A.S.a t *_+30*A.S.a t*(_+_))< _
   set r :ℝ:=A.S.a t
   have he: (l:ℝ) ≤ 2^d*x^d:= (hl.trans (pow_le_pow_left₀ (bell ..|>.le) hi.1 _)).trans_eq (by ring)
   have hp : (l:ℝ)+30*((A.clock.J t:ℝ)+5) <r⁻¹*A.S.a i/2:=by
      rw [mul_comm r⁻¹, ←div_eq_mul_inv,show A.S.a i/r=_ from z_scale A i t]
      have hs := gstar A i; have hq:y ≤ x^d*y:=le_mul_of_one_le_left hM.le (one_le_pow₀ hx'); have hv:x^d*y ≤ Real.exp ((1/2)*B):= by rw[pow_one] at hx; exact hx
      have hb: C* (x^d*y) ≤ Real.exp B:=(mul_le_mul ht hv (le_trans hM.le hq) (Real.exp_pos _).le).trans_eq (by dsimp only [comp_apply]; rw[← Real.exp_add]; congr 1; unfold B; ring)
      have hE : (A.clock.J t:ℝ) ≤ 2*y:=hj.trans hi.2.1
      set Z:= x^d
      have h1:1 ≤ (2:ℝ)^d:=one_le_pow₀ (by norm_num); have hw := one_le_pow₀ (n:=d) hx'; change 10000*(2:ℝ)^d * (Z*y) ≤ _ at hb; linarith only [hE,hb,he,Real.exp_monotone hs,hy,hq, mul_le_mul_of_nonneg_right (le_trans (by norm_num: (1:ℝ) ≤ 8) hy) (mul_nonneg (zero_le_one.trans h1) (zero_le_one.trans hw)),mul_le_mul_of_nonneg_left h1 (show 0≤Z*y from hM.le.trans hq)]
   have hS : 0< r:=hS
   field_simp at hp; change 2 * (r * _ + 30 * r * (_ + 5)) < _; linarith only [hp]
end YM.Trace.Terrace
