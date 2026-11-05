import YM.FullVolume.Train.Yards
/-! Principal & all aliases. No real limit inferred at harmonic before extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.OnTrack
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Finset
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} (A:Levels G) (x:Axis) (i:ℕ)
local notation "f₀" => fun d=> flying A d i
private lemma seed_still (a:Axis)(p:Momentum): Tendsto (fun d=>seedQ (flying A d i).mass p a) atTop (𝓝 (Complex.I*p a)):=by
   let L(d:ℕ):=(flying A d i).mass
   have hp : Tendsto (fun d=>(↑((L d).val:ℝ):ℂ)⁻¹) atTop (𝓝 0):=by
       simpa using ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_natCast_atTop_atTop.comp (far_mass A i))).ofReal
   let w (d:ℕ):= narrow (L d) p a; have hw : Tendsto w atTop (𝓝 0):=by simpa only [w,narrow_apply,div_eq_mul_inv, Complex.ofReal_natCast,mul_zero] using (hp.const_mul (p a))
   have he : HasDerivAt chip Complex.I 0 := by
        have hh := ((hasDerivAt_id' (0 : ℂ)).const_mul Complex.I).cexp.sub_const 1
        unfold chip; simpa only [mul_one,one_mul,mul_zero,zero_mul,Complex.exp_zero] using hh
   have ht : Tendsto (dslope chip 0 ∘ w) atTop (𝓝 Complex.I):= by
      rw [←he.deriv, ← dslope_same]; exact (continuousAt_dslope_same.2 he.differentiableAt).tendsto.comp hw
   refine (ht.mul_const _).congr fun d=>?_
   have hu : w d * dslope chip 0 (w d)= chip (w d):= by simpa using sub_smul_dslope chip 0 (w d)
   unfold seedQ
   rw [show chip _= _ from hu.symm]; change _ = ((L d).val:ℂ)*(narrow _ _ _ * _)
   rw [←mul_assoc,narrow_apply,mul_div_cancel₀ _ (side_ne _),mul_comm]; rfl
lemma plane (p:Momentum)(hp:physical p): Tendsto (fun d=> divisor (flying A d i).mass p) atTop (𝓝 (lengthSq p:ℂ)):=by
   have H : Tendsto (fun d=> ∑ a, ‖seedQ (flying A d i).mass p a‖^2) atTop (𝓝 (lengthSq p)):=by
      apply tendsto_finsetSum _ fun a _=>?_; simpa using ((seed_still A i a p).norm.pow 2)
   simp_rw [divisor_normSq _ hp]; exact H.ofReal
private def vaultX (z : Cover):ℝ:= ((∏ a, (1+((z a).natAbs:ℝ)))^2)⁻¹
lemma settled (M:ℕ→Side)(h:Tendsto (fun i=> (M i).val) atTop atTop)(z:Cover): ∀ᶠ i in atTop,lift (wrap (M i) z)=z:=by
   have he x : ∀ᶠ i in atTop, -((M i).val:ℤ)< 2*z x∧2*z x≤ (M i).val:=by
       filter_upwards [h.eventually_gt_atTop (2*(z x).natAbs)] with i hy; omega
   filter_upwards [eventually_all.mpr he] with i hi; exact lift_eq_iff.mpr ⟨rfl,hi⟩
private lemma VA (M:ℕ→Side)(h:Tendsto (fun i=> (M i).val) atTop atTop): Summable vaultX:=by
  obtain ⟨C,-,H⟩:= decay_cost
  apply summable_of_sum_le (f:=vaultX) (fun i=> by unfold vaultX; positivity) (c:=C)
  intro s
  obtain ⟨j,h⟩:= ((s.eventually_all).mpr (fun z _=> settled M h z)).exists
  refine le_trans ?_ (H (M j))
  calc
   _ = ∑ i∈ s.image (wrap (M j)), decay 2 i :=by
         rw [Finset.sum_image];swap; · intro i hi j' hj he; exact h i hi |>.symm.trans ((congr_arg lift he).trans (h _ hj))
         refine Finset.sum_congr rfl fun i hi=>?_; simp only [decay,mix,up,h i hi]; rfl
   _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _=>(decay_pos ..).le
lemma above_the_wing (p: Momentum)(hp:p∈baseCube): ∃ y,Tendsto (fun d=> high (flying A d i) x p) atTop (𝓝 y):=by
   let M d := (flying A d i).mass
   let U d := Finset.univ.erase (0: Site (M d)); let S d := (U d).image lift
   let W (d:ℕ) (l:Site (M d)):= yen ((flying A d i).drive x) (aliasAt p l) * (blow 1 p l)⁻¹
   let F(d:ℕ)(z:Cover):= if z∈ S d then W d (wrap _ z) else 0
   have he d : ∑' i,F d i= high (flying A d i) x p := by
         change _=∑ l∈ U d,W d l
         rw [tsum_eq_sum (s:=S d) (fun i hi=>if_neg hi)]
         unfold S; rw [Finset.sum_image (lift_inj (L:=M d)).injOn]; exact Finset.sum_congr rfl fun i hi=> by rw [if_pos (Finset.mem_image_of_mem lift hi), wrap_lift]
   let Z:= Σ d, { l// l∈ U d}; let L := fun z:Z=> M z.1; let v (z:Z): Site (L z):= z.2.val
   have ho (j:Z) : Odd (L j).val := Train.mass_odd _
   have hx(z:Z): v z≠0:= (Finset.mem_erase.mp z.2.2).1
   have h:= (blow_control L (fun _ => 1) ho v).inv (blow_firm L (fun _=>1) ho v hx) fun i=> pow_pos (grade_pos _) _
   have H : Moderate (fun z=> decay (A.clock.J i) (v z)* (grade (v z)^2)⁻¹) fun (t:Z) q =>yen ((flying A t.1 i).drive x) (aliasAt q (v t))*(blow 1 q (v t))⁻¹ :=
           (Train.drive_yen (fun z:Z=> flying A z.1 i) v (fun _=> x)).mul h
   obtain ⟨α,C,hα,hC,HH⟩:=H
   have hj : Tendsto (fun i=>(M i).val) atTop atTop:=far_mass A i
   have hk d z : ‖F d z‖ ≤ C*vaultX z:=by
        unfold F; split; rename_i hy
        · obtain ⟨t,ht,rfl⟩:= mem_image.mp hy; rw [wrap_lift]
          let Z' : Z := ⟨d,t,ht⟩; have he:grade (v Z') ≠ 0 := (grade_pos _).ne'
          apply ((HH Z').bound p (mem_cube_real (base_subset_realCube hα hp) hα)).trans
          have hu := mul_le_of_le_one_right (decay_pos t (A.clock.J i)).le (inv_le_one_of_one_le₀ (one_le_pow₀ (n:=2) (grade_ge t)))
          exact mul_le_mul_of_nonneg_left (hu.trans (decay_anti t (le_trans (by decide:2≤4) (A.clock.adm i)))) hC.le
        unfold vaultX; rw [norm_zero]; positivity
   have hv z: ∃ y,Tendsto (fun d=> F d z) atTop (𝓝 y):=by
       by_cases h : z=0
       · subst z; refine ⟨(0:ℂ),tendsto_const_nhds.congr fun d=>?_⟩
         refine Eq.symm (if_neg fun h=>?_); obtain ⟨i,hi,he⟩:=mem_image.mp h
         exact (Finset.mem_erase.mp hi).1 (lift_inj (he.trans (lift_origin _).symm))
       let q:= p+reciprocal z; have he : physical q := physical_iff q|>.mpr fun i=>by simp [q,physical_iff p |>.mp hp.1, reciprocal]
       have hs : q≠0:= by
         intro hk; have hP := base_subset_realCube zone_pos hp
         have hu : q∈realCube zone := hk ▸ show (0:Momentum)∈realCube zone from ⟨by unfold physical; simp, by intro i; simp [add_pos Real.pi_pos zone_pos]⟩
         exact (overlap_regular h hP hu).2 hk
       obtain ⟨w,hw⟩:=soldY A x i q he
       have hy : (↑(lengthSq q):ℂ)≠0:= Complex.ofReal_ne_zero.mpr (lengthSq_pos hs).ne'
       refine ⟨_,(hw.mul (plane A i q he|>.inv₀ hy)).congr' ?_⟩
       filter_upwards [settled _ hj z] with d hd
       have hb : aliasAt p (wrap (M d) z)=narrow (M d) q:=by ext1 j; rw [alias_value,narrow_apply,hd]; rfl
       have hm : wrap (M d) z∈ U d:= mem_erase.mpr ⟨fun he=> h (hd.symm.trans (he ▸ lift_origin _)),mem_univ _⟩
       have hu : blow 1 p (wrap (M d) z)=divisor (M d) q:=by
          have ht:= blow_zero q 1 (M d)
          simpa only [blow,hb,alias_zero_eq,mul_one] using (show blow 1 q 0=divisor (M d*1) q from ht)
       change _=F d z; rw [show F d z=_ from if_pos (show z∈ S d from mem_image.mpr ⟨_,hm,hd⟩)]
       unfold W; rw [hu,hb]
   choose y hy using hv
   refine ⟨_,(tendsto_tsum_of_dominated_convergence ((VA M hj).mul_left _) hy (Eventually.of_forall hk)).congr he⟩
end YM.Next.Free.OnTrack
namespace YM.Next.Free.OnTrack
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Finset
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} (A:Levels G) (x:Axis) (i:ℕ)
lemma arrival {p:Momentum}(hp:p∈baseCube)(he:p≠0){k:ℝ}(hk:0<k):
    ∃ y:ℂ, 0 < y.re ∧ Tendsto (fun N=> Train.levelD k (location A N i) x p) atTop (𝓝 y):=by
   obtain ⟨b,hb⟩:=above_the_wing A x i p hp; obtain ⟨c,hc,H⟩:=dusty A x i p hp; obtain ⟨f,hF⟩:=soldY A x i p hp.1
   have HE := ((plane A i p hp.1).inv₀ (Complex.ofReal_ne_zero.mpr (lengthSq_pos he).ne')); let K:=f* (↑(lengthSq p):ℂ)⁻¹+b
   have hpw : Tendsto (fun d=> feed (flying A d i) x (fun p=> (divisor 1 p)⁻¹) p) atTop (𝓝 K):=by
       refine ((hF.mul HE).add hb).congr fun d=>?_; let y:= flying A d i
       have h:=pole_split k y x p; unfold levelD drain at h; rw [←add_assoc] at h; exact (add_right_cancel h).symm
   have Hy : 0≤ K.re:=ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hpw) fun d=> (feed_cost (flying A d i) x (fun v hv => (Silver.chipSq 1 hv).inv) p hp.1).re_nonneg
   have HN : Tendsto (fun N:ℕ=> N-i) atTop atTop:= tendsto_atTop_atTop.mpr fun d=> ⟨d+i,fun j h => by omega⟩
   refine ⟨K+(k:ℂ)⁻¹*c,?_,(hpw.add (H.const_mul _)).comp HN⟩
   rw [←Complex.ofReal_inv,Complex.add_re,Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
   exact add_pos_of_nonneg_of_pos Hy (mul_pos (inv_pos.mpr hk) (zero_lt_one.trans_le hc))
end YM.Next.Free.OnTrack
