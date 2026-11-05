import YM.TraceExtension.Loft.Ket
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {G:Gauge}{f:Side}{p:Clip}{m n:ℕ}{σ μ:ℝ}
lemma sip_n (p:Site f) : FrontBox (sip p):=by
    intro i; change |pitchf f * ↑(lift p i)| ≤ Real.pi
    obtain ⟨hx,hp⟩:=lift_centers p i
    have hv: 2 * (↑(lift p i):ℝ) ≤ (f.val:ℝ):=by exact_mod_cast hp
    have ht: - (f.val:ℝ) < 2 * (↑(lift p i):ℝ):=by exact_mod_cast hx
    unfold pitchf; rw [abs_le]; constructor
    · have he:= mul_lt_mul_of_pos_left ht Real.pi_pos; rw[div_mul_eq_mul_div,le_div_iff₀ (by exact_mod_cast f.property)]; linarith
    have he:= mul_le_mul_of_nonneg_left hv Real.pi_pos.le; rw[div_mul_eq_mul_div,div_le_iff₀ (by exact_mod_cast f.property)];linarith
lemma sipe (p:Site f) : pitchf f*↑(pdist p)≤ flay (sip p):=by
    obtain ⟨i,hi,hx⟩:= Finset.exists_mem_eq_sup (s:= (univ:Finset Axis)) (f:=fun i=> (lift p i).natAbs) Finset.univ_nonempty
    have hh:= norm_le_pi_norm (sip p) i; refine le_trans ?_ (hh.trans (orbit_at _))
    rw[show pdist p= (lift p i).natAbs from hx, Real.norm_eq_abs]; change _ ≤ |(pitchf f)*↑(lift p i)|; rw[abs_mul,abs_of_pos pitch_pos,show (↑(lift p i).natAbs:ℝ)=|(↑(lift p i):ℝ)| by simp]
lemma aria (R:ℝ)(h:pitchf f ≤ R){s:Finset (Site f)}(hp: ∀ x∈s, flay (sip x)≤R): (↑s.card:ℝ)≤ (3*R/pitchf f)^4:=by
    have hr:0 < R:= pitch_pos.trans_le h
    let k:= ⌊R/(pitchf f)⌋₊
    have hv: s⊆ halo k ({(0:Site f)}: Support f):= fun x hx=> halo_spec.mpr ⟨0,mem_singleton_self _,by
       rw [separation_comm,separation,sub_zero]; exact Nat.le_floor ((le_div_iff₀ pitch_pos).2 ((mul_comm _ _).trans_le ((sipe x).trans (hp x hx))))⟩
    have hb:s.card ≤ (k+k+1)^4:=by exact le_trans (card_le_card hv) (by simpa using Corona.halo_size ({(0:Site f)}: Support f) k)
    have hz: (s.card:ℝ)≤ ((k:ℝ)+k+1)^4:=by exact_mod_cast hb
    apply hz.trans; apply pow_le_pow_left₀ (by positivity) _ 4; rw [mul_div_assoc]; have he:= Nat.floor_le (show 0 ≤ R/pitchf f from div_nonneg hr.le pitch_pos.le); have hy:1 ≤ R/pitchf f:= (one_le_div pitch_pos).mpr h; unfold k; linarith
lemma loy (h:0<μ)(x:ℝ)(hp:μ ≤ x): ∃ i:ℕ, μ*2^i ≤ x ∧ x≤ μ*2^(i+1):=by
    have hv: ∃ n:ℕ,x<μ*2^(n+1):=by obtain ⟨n,H⟩:= pow_unbounded_of_one_lt (x/μ) (by norm_num:(1:ℝ)<2); refine ⟨n,?_⟩; apply lt_of_lt_of_le ((div_lt_iff₀ h).1 H); rw[mul_comm μ]; gcongr <;> first|omega|norm_num
    let k:=Nat.find hv; refine ⟨k,?_,(Nat.find_spec hv).le⟩; cases ht:k with
    | zero=> simpa
    | succ n=> exact le_of_not_gt (Nat.find_min hv (by change n< k; omega))
lemma fractions (b:ℕ): ∑ n∈range b,(2:ℝ)⁻¹ ^ n ≤ 2:=by
    have hv:= geom_sum_mul (x:= (2:ℝ)⁻¹) b; have hp:0 ≤ (2:ℝ)⁻¹ ^ b:=by positivity
    norm_num at hv ⊢; have hx:0 ≤ (1/2:ℝ)^b:=pow_nonneg (by positivity) _; linarith
lemma sip_charge (h:pitchf f ≤ μ): Wsc f * ∑ x:Site f, (flay (sip x)+μ)⁻¹ ^ (5:ℕ) ≤ 2*6^4/((2*Real.pi)^4*μ):=by
    have hp:0 < μ:= pitch_pos.trans_le h; let Z(x: Site f):=flay (sip x)+μ; let V(k:ℕ):= μ*2^k
    have hv(k):0 < V k:=by unfold V; positivity
    choose k hK ht using (fun x:Site f=> loy hp (Z x) (le_add_of_nonneg_left (orbit_nonneg _)))
    let K:=Finset.univ.sup k+1; have hx:∀ i∈(univ:Finset (Site f)), k i ∈range K:=fun i hi=>mem_range.mpr (lt_of_le_of_lt (Finset.le_sup (f:=k) hi) (Nat.lt_succ_self _))
    have hq(i:ℕ): ∑ x∈univ.filter (fun x=>k x=i), (Z x)⁻¹ ^(5:ℕ) ≤ 6^4/(pitchf f)^4/μ*(2:ℝ)⁻¹ ^ i:=by
        let s:=univ.filter fun x=> k x=i; have he(x)(h:x∈s): V i ≤ Z x ∧ Z x ≤ V i*2:=by rw [← (mem_filter.mp h).2]; exact ⟨hK x,(ht x).trans_eq (by unfold V; ring)⟩
        have hh: μ ≤ V i:=le_mul_of_one_le_right hp.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
        have hr:V i ≤ V i*2:=le_mul_of_one_le_right (hv i).le (by norm_num)
        have hw:= aria _ (h.trans (hh.trans hr)) (fun x h => (le_add_of_nonneg_right hp.le).trans ((he x h).2))
        calc
         _ ≤ ∑ x∈s, (V i)⁻¹ ^ (5:ℕ) := sum_le_sum fun x hp=>pow_le_pow_left₀ (inv_nonneg.mpr ((hv i).trans_le ((he x hp).1)|>.le)) (inv_anti₀ (hv i) (he x hp|>.1)) _
         _ ≤ (3*(V i*2)/pitchf f)^4 * ((V i)⁻¹ ^ (5:ℕ)):=by rw[sum_const,nsmul_eq_mul];exact mul_le_mul_of_nonneg_right hw (pow_nonneg (inv_nonneg.mpr (hv i).le) _)
         _ = _ :=by
            rw [show (2:ℝ)⁻¹ ^ i= _ from inv_pow ..]; unfold V; have hb:0 < pitchf f:=pitch_pos; field_simp; ring
    have hm:0 ≤ Wsc f:=inv_nonneg.mpr cents_pos.le
    rw [← sum_fiberwise_of_maps_to hx]; calc
      _ ≤ Wsc f*∑ i∈range K, (6^4/(pitchf f)^4/μ*(2:ℝ)⁻¹^ i):= mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> hq i) hm
      _ ≤ Wsc f*(6^4/(pitchf f)^4/μ*2):=by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (fractions _) (by have ht:0 < pitchf f:=pitch_pos; positivity)) hm
      _ = _:=by unfold Wsc cents pitchf; have hx: (0:ℝ)< f.val:=Nat.cast_pos.mpr f.property; rw[site_card]; push_cast; field_simp
end YM.Trace.Loft
