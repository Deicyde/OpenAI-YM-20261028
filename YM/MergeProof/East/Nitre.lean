import YM.Next.FREE_KERNELS.Lifts
import YM.Next.RANK.ParticleGate
import YM.Planned.CALIBRATED_MIXED_HISTORY.Bridge
import YM.UVNext.ANNULUS_COMPARISON.Shadow




/-! # room after booking at two shorter bands -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Lattice RG Next.Rank Next.Rank.Station Perch Glimmer Atlas
open scoped Topology BigOperators Classical
variable {G:Gauge}
private lemma pays_wants {u t:ℝ} (hu:1<u)(ht:1≤t): u^want u t ≤ t*u:=by
    cases h:want u t with
    | zero=>rw [pow_zero];exact one_le_mul_of_one_le_of_one_le ht hu.le
    | succ i=>
       have he:u^i < t:= lt_of_not_ge (fun hp=> by have hh:= ((wanted hu (zero_lt_one.trans_le ht) i).1 hp);omega)
       rw [pow_succ]; gcongr
lemma echo_scale (A:Levels G)(hG:G.Simple)(b:ℝ)(hb:0<b) : ∀ᶠ k:ℕ in atTop,
    Allowed A b k → wheel A k ≤ A.clock.monitor k →
      A.S.a (width A b k)/A.S.a k ≤ bill (b+5) (clim A k):=by
    have hz:= YM.UVNext.Annulus.opens_radius hG A (s:=1) le_rfl (show 0<(1/5:ℝ) by norm_num)
    filter_upwards [hz] with k hz h ht
    let X:=clim A k; let V:=A.clock.coverSize k; let M:=A.clock.monitor k;let r:=wheel A k
    have hV : (1:ℝ) ≤ V:= by exact_mod_cast (A.budget k).B_pos
    have hm : 1 ≤ M:= by rw [show M=bill 1 X from Atlas.fire_bill A k]; exact Glimmer.costed _ _ zero_le_one
    have hs : (V:ℝ)^10≤M:=by
       change 16*(1:ℝ)*(V:ℝ)^2 ≤ Station.mag A (1/5:ℝ) k at hz
       have hc:(V:ℝ)^2 ≤ Perch.bill (1/5) X:=by rw [← show Station.mag A (1/5) k=bill (1/5) X from Atlas.mag_bill ..]; have hv:0≤(V:ℝ)^2:=sq_nonneg _;linarith only [hz,hv]
       rw [show (10:ℕ)=2*5 from rfl,pow_mul]
       apply le_trans (pow_le_pow_left₀ (sq_nonneg _) hc _) _; rw [Glimmer.bills,show M=_ from Atlas.fire_bill A k]; norm_num; exact le_rfl
    let i:=width A b k;let j:=middle A b k
    have hp := h.large
    rw [h.scales (width ..) k le_rfl ((wider ..).trans (before ..)) le_rfl]
    change r^(k-i) ≤ bill _ X
    have hG : 1 ≤ Station.mag A b k:=Real.one_le_rpow hm hb.le
    rw [show k-i=(k-j)+(j-i) by have hs:i≤j:=wider ..; have hT:j ≤ k:=before ..; omega,pow_add,show k-j=height A b k from h.full,show j-i=surplus A k from h.shift]
    apply le_trans (b:=(Station.mag A b k*M^2*M)*(M*M))
    · apply mul_le_mul _ _ (by have h:0<r:= zero_lt_one.trans hp; positivity) (by positivity)
      · exact (pays_wants hp (one_le_mul_of_one_le_of_one_le hG (one_le_pow₀ hm (n:=2)))).trans (mul_le_mul_of_nonneg_left ht (by positivity))
      exact (pays_wants hp (one_le_pow₀ hV (n:=10))).trans (mul_le_mul hs ht (zero_le_one.trans hp.le) (zero_le_one.trans hm)) -- adjust
    rw [Atlas.mag_bill,show M=_ from Atlas.fire_bill A k, bills,overlap,overlap,overlap,overlap]; norm_num; ring_nf; exact le_rfl
lemma echo_prior (A : Levels G)(b n:ℝ)(hb:0<b)(hG:G.Simple): ∀ᶠ k:ℕ in atTop,Allowed A b k→wheel A k ≤ A.clock.monitor k→
    let m:=width A b k
    n* A.S.a m < A.S.a (m-1) ∧ A.S.a (m-1)/A.S.a k ≤ bill (b+6) (clim A k) := by
    obtain ⟨z,hz⟩:= eventually_atTop.mp ((YM.Planned.CalibratedMixedHistory.Bridge.reach A).eventually_gt_atTop n)
    filter_upwards [A.fits.deep.eventually_gt_atTop (A.clock.J z),echo_scale A hG b hb] with k hk he h hl m
    have hp:m≥z+1:=by
       by_contra! hs; exact not_lt_of_ge (show A.clock.J k ≤ A.clock.J z by rw [← h.plateau m le_rfl ((wider ..).trans (before ..))]; exact A.fits.mono (by omega)) hk
    have hQ:m-1≥z:=by omega
    have hf:m-1+1=m:=by omega
    have hs:((A.S.block (m-1)).val :ℝ)=wheel A k:=by
       unfold wheel; rw [← A.fits.sameFactor (m-1),hf,h.plateau m le_rfl ((wider ..).trans (before ..))]
    let u:=wheel A k
    have hj : A.S.a m*u = A.S.a (m-1):=by
       rw [show u=((A.S.block (m-1)).val:ℝ) from hs.symm]
       have hx:= A.S.a_step (m-1); rw [hf] at hx; rw [hx]; exact div_mul_cancel₀ _ (by exact_mod_cast (A.S.block (m-1)).property.ne')
    have hv:= A.S.a_pos
    rw [← hj];constructor
    · rw [mul_comm]; apply mul_lt_mul_of_pos_left _ (hv m); exact lt_of_lt_of_eq (hz _ hQ) hs
    rw [mul_comm, mul_div_assoc]; apply (mul_le_mul hl (he h hl) (div_nonneg (hv _).le (hv _).le) (Real.exp_pos _).le).trans_eq; rw [Atlas.fire_bill,overlap]; congr 1; ring
end YM.MergeProof.East
