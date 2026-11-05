import YM.TraceExtension.Perfect.Eureka

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {η C:ℝ}{v:RowGrade}
lemma station_at (c:Side)(z:Cover) (h:2*size z<c.val) : lift (wrap c z)=z:=by
 apply lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩; have he : (z i).natAbs≤size z:= Finset.single_le_sum (f:=fun i=>(z i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i); omega
private lemma stream_budget (x:Cover){q:Cover→ℝ} (hσ:0<η) (hv:Width η C q)(g: Cover→ℝ) (h:∀ z, ‖g z‖≤4*Carrier.liftCost 2 z):
   SumBudget (fun z=>‖q z*g (x+z)‖) (4*Carrier.liftCost 2 x*Carrier.widthCost η 2*C):= Carrier.stream_income hσ hv _ _ (by norm_num : (0:ℝ)≤4) h
variable {W: Type*}{D:Filter W}(L:Side){n m:W→Side}(g: ∀ w, Ratio (n w) (m w))(hw:∀ w,(g w).count=L)
   (F:∀ w,CrossA (g w).count)
include hw
lemma orbit_gain (hη:0<η)(he:0 ≤ C)(hc:∀ w,(F w).strip η C)(h:Tendsto (fun w=>(n w).val) D atTop)
    (u: RowGrade)(x:Cover)(v:∀ w, Site (n w))(ℓ b:TypeFace 1):
    Tendsto (fun w=> (installed (g w) (F w) *ᵥ probeF u (v w) ℓ) ((g w).embed (v w)+ wrap _ x,b) -
         ∑' z,(F w) (wrap (g w).count x,b) ℓ z * u.price (Carrier.cellar L x+z)) D (𝓝 0):=by
    let p := Carrier.cellar L x; let f w := fun z=>F w (wrap (g w).count x,b) ℓ z
    have ht w : Width η C (f w):= hc w _ _
    let t:=η/2; have hh:0<t:=half_pos hη
    let V:=4*Carrier.liftCost 2 p*Carrier.widthCost t 2; have hV : 0≤V:=by have := Carrier.widthCost_ge hh 2; have :=Carrier.liftCost_pos 2 p; positivity
    apply Metric.tendsto_nhds.mpr; intro ε he'
    have hv : Tendsto (fun k:ℕ=> V*(Real.exp (-t*k)*C) + V*(Real.exp (-t*k)*C)) atTop (𝓝 0):=by
       have hx:Tendsto (fun k:ℕ=> Real.exp (-t*k)) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hh))
       have hx': Tendsto (fun k:ℕ=>V*(Real.exp (-t*k)*C)) atTop (𝓝 0):=by simpa only [zero_mul,mul_zero] using (hx.mul_const C|>.const_mul V)
       exact (zero_add (0:ℝ)) ▸ hx'.add hx'
    obtain ⟨k,hk⟩:= (hv.eventually (gt_mem_nhds he')).exists
    filter_upwards [h.eventually (eventually_gt_atTop (2*(size p+k)))] with w hN
    rw [dist_zero_right]; simp_rw [bank_eval _ (x:=x) ⟨η,C,hη,hc w⟩,show Carrier.cellar (g w).count x = p from congr_arg (fun a:Side=>Carrier.cellar a x) (hw w)]
    let V' (y:Cover):=u.price (lift (wrap (n w) y)); let P(z):=if k < size z then f w z else 0
    suffices ha:‖(∑' z,P z*V' (p+z))-∑' z,P z*u.price (p+z)‖ < ε by
       have hx : ∑' z, f w z *(V' (p+z)-u.price (p+z))=∑' z,P z*(V' (p+z)-u.price (p+z)):= by
           refine tsum_congr fun z=>?_ ; unfold V' P; split;next => rfl
           next h => rw [station_at]; ring; exact (by have hf:=size_add p z; omega)
       have hY(z): ‖P z‖≤ ‖f w z‖:=by unfold P;split; rfl; rw [norm_zero]; exact norm_nonneg _
       have hP: Width η C P:=Work.F08.budget_minor (ht w) (fun _=>by positivity) (fun z=>mul_le_mul_of_nonneg_left (hY z) (Real.exp_pos _).le)
       let Q := stream_budget p hη (ht w) V' (fun z=> RowGrade.dolls ..)
       simp_rw [mul_sub] at hx
       rw [(Q.2.1.of_norm).tsum_sub ((stream_budget p hη (ht w) u.price (fun z=>u.bounded z)).2.1.of_norm), (stream_budget p hη hP V' (fun z=>RowGrade.dolls ..)).2.1.of_norm.tsum_sub ((stream_budget p hη hP u.price (fun z=>u.bounded z)).2.1.of_norm)] at hx
       change ‖(∑' z,f w z*V' (p+z))-∑' z,f w z*u.price (p+z)‖< _; rw [hx]; exact ha
    have hC' : Width t (Real.exp (-t*k)*C) P:=by
        let D:=Real.exp (-t*k); let u z:=Real.exp (η*size z)*‖f w z‖
        have hd : SumBudget (fun z=>D*u z) (D*C):= ⟨fun z=> mul_nonneg (Real.exp_pos _).le ((ht w).1 z),(ht w).2.1.mul_left D,Eq.trans_le tsum_mul_left (mul_le_mul_of_nonneg_left (ht w).2.2 (Real.exp_pos _).le)⟩
        apply Work.F08.budget_minor hd (fun _=>by positivity) (fun z=>?_); unfold P; split; rotate_left; · rw [norm_zero,mul_zero];exact hd.1 _
        rename_i ht; unfold u; rw [← mul_assoc, show D= _ from rfl]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        unfold D; rw [← Real.exp_add]; apply Real.exp_monotone; have hp:= ht.le; have he:=Nat.cast_le (α:=ℝ)|>.mpr hp; unfold t; nlinarith only[hη,he]
    let Q := stream_budget p hh hC' V' (fun z=> RowGrade.dolls ..)
    have hZ:= stream_budget p hh hC' u.price (fun z=>u.bounded z)
    exact lt_of_le_of_lt ((norm_sub_le ..).trans (add_le_add ((norm_tsum_le_tsum_norm Q.2.1).trans Q.2.2) ((norm_tsum_le_tsum_norm hZ.2.1).trans hZ.2.2))) hk
end YM.Trace.Perfect
