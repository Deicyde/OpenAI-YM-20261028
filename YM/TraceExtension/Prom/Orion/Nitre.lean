import YM.MergeProof.East.Nitre
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.East.Nitre for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Lattice RG Next.Rank Next.Rank.Station Perch Glimmer Atlas
open scoped Topology BigOperators Classical
variable {G:Gauge}
-- maximum over both neighbor factors
abbrev topL (A:Levels G)(k:ℕ):ℝ:= max (wheel A k) (((A.clock.factor (A.clock.J k-1)).val):ℝ)
private lemma ellTop {A:Levels G}{b:ℝ} {k i:ℕ}(h:AllowedSky A b k)(hi : widthSky A b k ≤ i)(hx:i ≤ k) : wheel A i ≤ topL A k:= by
    let J:= A.clock.J k; have hh:J-1 ≤ A.clock.J i:=h.bracket i hi hx; have hz:A.clock.J i ≤ J:= A.fits.mono hx; unfold wheel; rcases eq_or_lt_of_le hz with he|he
    · rw [he]; exact le_max_left ..
    rw [show A.clock.J i=J-1 by omega]; exact le_max_right ..
private lemma gain_limit (T:Levels G)(i:ℕ)(r L:ℝ)(h:1≤L)(hR:1≤r)(hf: gainSky T.S i r < i → ((T.S.block (gainSky T.S i r)).val:ℝ) ≤ L): T.S.a (gainSky T.S i r)/T.S.a i ≤ L*r:=by
   let k:= gainSky T.S i r; have he:k ≤ i:=gain_under ..;change T.S.a k / T.S.a i≤_
   rcases lt_or_eq_of_le he with he|he
   · have hp: T.S.a (k+1)/T.S.a i ≤ r:= (lt_of_not_ge (fun hz' => Nat.not_succ_le_self k (gain_fee he hz'))).le
     let l:ℝ:= (T.S.block k).val; have hL : 0<l:= Nat.cast_pos.mpr (T.S.block k).property; have h': T.S.a k/T.S.a i=l*(T.S.a (k+1)/T.S.a i):=by rw [T.S.a_step]; change _= l*(T.S.a k/l/T.S.a i); field_simp
     rw [h']; exact mul_le_mul (hf he) hp (div_nonneg (T.S.a_pos _).le (T.S.a_pos _).le) (zero_le_one.trans h)
   rw [he,div_self (T.S.a_pos _).ne']; exact one_le_mul_of_one_le_of_one_le h hR

lemma echo_scaleSky (A:Levels G)(hG:G.Simple) : ∀ᶠ k:ℕ in atTop, ∀ b:ℝ, 0<b →
    AllowedSky A b k → topL A k ≤ A.clock.monitor k →
      A.S.a (widthSky A b k)/A.S.a k ≤ bill (b+5) (clim A k):=by
    have hz:= YM.UVNext.Annulus.opens_radius hG A (s:=1) le_rfl (show 0<(1/5:ℝ) by norm_num)
    filter_upwards [hz] with k hz b hb h ht
    let X:=clim A k; let V:=A.clock.coverSize k; let M:=A.clock.monitor k;let r:=wheel A k
    have hV : (1:ℝ) ≤ V:= by exact_mod_cast (A.budget k).B_pos
    have hm : 1 ≤ M:= by rw [show M=bill 1 X from Atlas.fire_bill A k]; exact Glimmer.costed _ _ zero_le_one
    have hs : (V:ℝ)^10≤M:=by
       change 16*(1:ℝ)*(V:ℝ)^2 ≤ Station.mag A (1/5:ℝ) k at hz
       have hc:(V:ℝ)^2 ≤ Perch.bill (1/5) X:=by rw [← show Station.mag A (1/5) k=bill (1/5) X from Atlas.mag_bill ..]; have hv:0≤(V:ℝ)^2:=sq_nonneg _;linarith only [hz,hv]
       rw [show (10:ℕ)=2*5 from rfl,pow_mul]
       apply le_trans (pow_le_pow_left₀ (sq_nonneg _) hc _) _; rw [Glimmer.bills,show M=_ from Atlas.fire_bill A k]; norm_num; exact le_rfl
    let i:=widthSky A b k
    let w:= widthSky A b k; let j:= middleSky A b k
    have hg: 1 ≤ mag A b k:=Real.one_le_rpow hm hb.le
    have he i (hp:widthSky A b k ≤ i)(hi:i < k): ((A.S.block i).val:ℝ) ≤ M:=by rw [← A.fits.sameFactor]; exact (ellTop h (hp.trans (Nat.le_succ _)) hi).trans ht
    have hX:= widerSky A b k; have hx:= beforeSky A b k
    have hj : A.S.a j/A.S.a k ≤ M*(mag A b k*M^2):= gain_limit A k _ _ hm (one_le_mul_of_one_le_of_one_le hg (one_le_pow₀ hm (n:=2))) (fun H=> he _ hX H)
    have hw : A.S.a w/A.S.a j ≤ M*((V:ℝ)^10):= gain_limit A j _ _ hm (one_le_pow₀ hV (n:=10)) (fun H=> he w le_rfl (H.trans_le hx))
    rw [show A.S.a (widthSky A b k)/A.S.a k = A.S.a w/A.S.a j*(A.S.a j/A.S.a k) by field_simp [(A.S.a_pos j).ne']; rfl]
    apply (mul_le_mul (hw.trans (mul_le_mul_of_nonneg_left hs (zero_le_one.trans hm))) hj (div_nonneg (A.S.a_pos _).le (A.S.a_pos _).le) (mul_nonneg (zero_le_one.trans hm) (zero_le_one.trans hm))).trans
    rw [Atlas.mag_bill,show M=_ from Atlas.fire_bill A k,bills,overlap,overlap,overlap,overlap]; norm_num; ring_nf; exact le_rfl
lemma echo_priorSky (A : Levels G)(n:ℝ)(hG:G.Simple): ∀ᶠ k:ℕ in atTop,∀ b:ℝ, 0<b → AllowedSky A b k→topL A k ≤ A.clock.monitor k→
    let m:=widthSky A b k
    n* A.S.a m < A.S.a (m-1) ∧ A.S.a (m-1)/A.S.a k ≤ bill (b+6) (clim A k) := by
    obtain ⟨z,hz⟩:= eventually_atTop.mp ((YM.Planned.CalibratedMixedHistory.Bridge.reach A).eventually_gt_atTop n)
    filter_upwards [A.fits.deep.eventually_gt_atTop (A.clock.J z+1),echo_scaleSky A hG] with k hk he b hb h hl m
    have hp:m≥z+1:=by
       by_contra! hs; have hv : A.clock.J k-1 ≤ A.clock.J m:=h.bracket m le_rfl ((widerSky ..).trans (beforeSky ..)); have he:= A.fits.mono (show m ≤ z by omega); omega
    have hQ:m-1≥z:=by omega
    have hf:m-1+1=m:=by omega
    have hs:((A.S.block (m-1)).val :ℝ)=wheel A m:=by
       unfold wheel; rw [← A.fits.sameFactor (m-1),hf]
    let u:=wheel A m
    have hl': wheel A m ≤ A.clock.monitor k := (ellTop h le_rfl ((widerSky ..).trans (beforeSky ..))).trans hl
    have hj : A.S.a m*u = A.S.a (m-1):=by
       rw [show u=((A.S.block (m-1)).val:ℝ) from hs.symm]
       have hx:= A.S.a_step (m-1); rw [hf] at hx; rw [hx]; exact div_mul_cancel₀ _ (by exact_mod_cast (A.S.block (m-1)).property.ne')
    have hv:= A.S.a_pos
    rw [← hj];constructor
    · rw [mul_comm]; apply mul_lt_mul_of_pos_left _ (hv m); exact lt_of_lt_of_eq (hz _ hQ) hs
    rw [mul_comm, mul_div_assoc]; apply (mul_le_mul hl' (he b hb h hl) (div_nonneg (hv _).le (hv _).le) (Real.exp_pos _).le).trans_eq; rw [Atlas.fire_bill,overlap]; congr 1; ring
end YM.MergeProof.East
