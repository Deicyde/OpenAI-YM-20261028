import YM.UVExtension.Free.History
/-! Pointwise full UV limits on the real momentum cube, including the
cutoff-dependent metric recipes. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Filter Function Lattice Exterior Laurent Bloch RG Next.Free
open scoped Topology BigOperators Classical
variable {G : Gauge} (A : Levels G)

lemma mass_growth (i : ℕ) : Tendsto (fun k => (flying A k i).mass.val) atTop atTop := by
  simp_rw [flying_mass]; exact steps_infinite ..

section continuum
variable {u : ℕ→Side} (h : Tendsto (fun k => (u k).val) atTop atTop) (p : Momentum)
include h
lemma seed_limit (i : Axis) : Tendsto (fun k => seedQ (u k) p i) atTop (𝓝 (p i * Complex.I)) := by
  let f (j) := narrow (u j) p i
  have he : Tendsto (fun k => (((u k).val:ℂ))⁻¹) atTop (𝓝 (0:ℂ)) := by
    have hx := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h))
    simpa only [comp_def,Complex.ofReal_zero,Complex.ofReal_inv, Complex.ofReal_natCast] using hx
  have hv : Tendsto f atTop (𝓝 0) := by
    simp only [f,narrow_apply,div_eq_mul_inv]
    simpa only [mul_zero] using he.const_mul (p i)
  have hD : HasDerivAt chip Complex.I 0 := by
    have hh := ((hasDerivAt_id' (0 : ℂ)).const_mul Complex.I).cexp.sub_const 1
    unfold chip; simpa only [mul_one,one_mul,mul_zero,zero_mul,Complex.exp_zero] using hh
  have hd : ContinuousAt (dslope chip 0) 0 := continuousAt_dslope_same.mpr (hD.differentiableAt)
  have hT:= (hd.tendsto.comp hv).const_mul (p i)
  rw [dslope_same,hD.deriv] at hT
  refine hT.congr fun i'=>?_
  have hx : f i' * dslope chip 0 (f i')=chip (f i') := by simpa using sub_smul_dslope chip 0 (f i')
  have hr : (((u i').val:ℂ)) * f i' = p i := by unfold f; rw [narrow_apply,mul_div_cancel₀ _ (side_ne _)]
  exact calc
    _ = ((((u i').val:ℂ)) * f i') * dslope chip 0 (f i') := by rw [hr]; rfl
    _ = _ := by rw [mul_assoc,hx]; rfl

lemma divisor_limit : Arrives (fun i => divisor (u i) p) :=
    Arrives.sum _ fun i _=> (Arrives.times (show Arrives fun k=> seedQ (u k) p i from ⟨_,seed_limit h p i⟩)
      (show Arrives fun k=> seedQ (u k) (-p) i from ⟨_,seed_limit h (-p) i⟩))
end continuum

private def padded (i : Cover) : ℝ := ((∏ j : Axis, (1+((i j).natAbs:ℝ)))^2)⁻¹
private lemma padded_lift {L : Side} (l : Site L) : padded (lift l)=decay 2 l := rfl
private lemma padded_nonneg (i : Cover) : 0≤ padded i := by unfold padded; positivity

private lemma relevant {u : ℕ→Side} (h : Tendsto (fun k => (u k).val) atTop atTop) (j : Cover) :
    ∀ᶠ i : ℕ in atTop, lift (wrap (u i) j)=j := by
  have hp s : Tendsto (fun i=> ((u i).val:ℤ) - 2*j s) atTop atTop := by
    simp only [sub_eq_add_neg]; exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp h)
  have hs k : ∀ᶠ i in atTop, (-((u i).val:ℤ)<2*j k ∧ 2*j k≤ (u i).val) := by
    filter_upwards [(hp k).eventually_ge_atTop 0,(tendsto_natCast_atTop_atTop.comp h).eventually_gt_atTop (-2*j k)] with i he hx
    change _≤ ((u i).val:ℤ) - 2*j k at he; change _ < ((u i).val:ℤ) at hx; omega
  filter_upwards [eventually_all.mpr hs] with i hi; exact lift_eq_iff.mpr ⟨rfl,hi⟩

private lemma padded_sum : Summable padded := by
  obtain ⟨C,hC,h⟩ := decay_cost
  refine summable_of_sum_le (c:=C) (padded_nonneg) ?_
  intro t
  let u (n : ℕ) : Side := ⟨n+1,Nat.succ_pos _⟩
  have hh : ∀ᶠ i in atTop, ∀ j∈t, lift (wrap (u i) j)=j :=
    (Finset.eventually_all t).mpr fun j _=> relevant (u:=u) (tendsto_add_atTop_nat _) j
  obtain ⟨i,hi⟩ := hh.exists
  let T := t.image (wrap (u i))
  have ht : ∑ j ∈ t,padded j = ∑ j ∈ T, decay 2 j := by
    unfold T; rw [Finset.sum_image]
    · apply Finset.sum_congr rfl; intro x hx; exact (congr_arg padded (hi x hx).symm).trans (padded_lift _)
    intro x hx y hy he; rw [← hi x hx, ← hi y hy, he]
  exact ht.trans_le ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun i _ _=> (decay_pos ..).le)).trans (h _))


/-- uniform cost on the HIGH aliases in a fixed level as cutoff moves. -/
private lemma high_budget {i : ℕ} (V : ℕ→ Train i) (hv: 2 ≤ i) (p : Momentum) (hp : p ∈ baseCube) (a : Axis) :
    ∃ r : ℝ, 0<r ∧ ∀ k (l : Site (V k).mass), l≠0 → ‖yen ((V k).drive a) (aliasAt p l) * (blow 1 p l)⁻¹‖ ≤ r*decay 2 l := by
  let L k := (V k).mass
  let I := Σ k, {l : Site (L k) // l ≠ 0}
  let v (x:I) := V x.1; let g (x:I) := x.2.val
  have hg (i : I) : g i ≠ 0 := i.2.property
  have hk i : Odd (L i).val:= (V i).mass_odd
  obtain ⟨θ,c,hθ,hc,hh⟩:=blow_firm (fun x:I=> L x.1) (fun _=>1) (fun x=>hk x.1) g hg
  obtain ⟨η,C,hη,hC,h⟩ := Train.drive_yen v g (fun _=>a)
  refine ⟨C*c⁻¹,mul_pos hC (inv_pos.mpr hc),fun k l he=> ?_⟩
  let x:I:=⟨k,l,he⟩
  have ht : ‖yen ((V k).drive a) (aliasAt p l)‖ ≤ C*decay i l :=
    (h x).bound p (mem_cube_real (base_subset_realCube hη hp) hη)
  have hq : c ≤ ‖blow 1 p l‖ :=
    (le_mul_of_one_le_right hc.le (one_le_pow₀ (grade_ge l))).trans (hh x p (base_subset_realCube hθ hp))
  rw [norm_mul,norm_inv]
  exact (mul_le_mul (ht.trans (mul_le_mul_of_nonneg_left (decay_anti l hv) hC.le))
    ((inv_le_inv₀ (hc.trans_le hq) hc).2 hq) (inv_nonneg.mpr (norm_nonneg _)) (by have hx:= decay_pos l 2; positivity)).trans_eq (by ring)

lemma arrive_lid (a : Axis) (i : ℕ) (p : Momentum) (hp : physical p) :
    Arrives fun d => (flying A d i).lid a p := by
  simp only [Train.lid, yen, ← narrow_neg]
  exact (drive_history A a i p hp).times (drive_history A a i (-p) ((star_neg p).trans (congr_arg Neg.neg hp)))

private lemma blow_flat (L : Side) (p : Momentum) (l : Site L) (a : Cover) (h : lift l = a) :
    blow 1 p l = divisor L (p+reciprocal a) := by
  rw [← (show blow 1 (p+reciprocal a) (0 : Site L)=_ from ((blow_zero ..).trans (congr_arg (fun l=>divisor l _) (mul_one L))))]
  simp only [blow]; congr 1; apply congr_arg
  rw [alias_zero_eq, show aliasAt p l=narrow L (p+reciprocal a) by ext j; rw [alias_value,narrow_apply,h]; rfl]

private lemma eventual_high (i : ℕ) (p : Momentum) (hp : p∈baseCube) (b : Cover) (hb : b≠0) :
    let M d:=(flying A d i).mass
    Arrives fun d=> (blow 1 p (wrap (M d) b))⁻¹ := by
  intro M
  have ht:= mass_growth A i
  have H := relevant ht b
  apply Arrives.reci
  · refine (divisor_limit (u:=M) ht (p+reciprocal b)).copy ?_
    filter_upwards [H] with i hi; exact (blow_flat _ p _ _ hi).symm
  have hF d (l : Site (M d)): Odd (M d).val:= (flying A d i).mass_odd
  let I:= Σ d,{l : Site (M d)// l≠0}
  obtain ⟨η,c,hη,hc,h⟩:= blow_firm (fun x:I=>M x.1) (fun _=>1) (fun x=> hF x.1 x.2.val) (fun x=>x.2.val) (fun x=>x.2.property)
  refine ⟨c,hc,?_⟩
  filter_upwards [H] with k hk; let l:= wrap (M k) b
  have hv : l≠0 := fun he=> hb (hk.symm.trans ((congr_arg lift he).trans (lift_origin _)))
  exact (le_mul_of_one_le_right hc.le (one_le_pow₀ (grade_ge l))).trans (h ⟨k,l,hv⟩ p (base_subset_realCube hη hp))

lemma arrive_high (a : Axis) (i : ℕ) (p : Momentum) (hp : p ∈ baseCube) :
    Arrives fun k=> (flying A k i).high a p := by
  let V k := flying A k i
  let M k:= (V k).mass
  let S k:= (Finset.univ.erase (0 : Site (M k))).image lift
  let f k (u: Site (M k)):= yen ((V k).drive a) (aliasAt p u) * (blow 1 p u)⁻¹
  let F k (x:Cover):= if x ∈ S k then f k (wrap (M k) x) else 0
  obtain ⟨c,hc,h⟩ := high_budget V ((by decide : 2≤4).trans (A.clock.adm i)) p hp a
  have ht (k): (V k).high a p=∑' x,F k x:= by
    rw [tsum_eq_sum (s:=S k)]
    · have hg (l) (hi:l∈ Finset.univ.erase (0 : Site (M k))) : f k l=F k (lift l):= by
        unfold F; rw [if_pos (Finset.mem_image_of_mem _ hi),wrap_lift]
      unfold S; rw [Finset.sum_image]; exact Finset.sum_congr rfl hg
      exact lift_inj.injOn
    intro i hi; exact if_neg hi
  suffices he : Arrives (fun k=> ∑' x,F k x) from he.copy (Eventually.of_forall fun k=> (ht k).symm)
  have hx k x: ‖F k x‖ ≤ c*padded x:= by
    unfold F; split
    next he => obtain ⟨l,hl,rfl⟩:= Finset.mem_image.mp he; rw [wrap_lift,padded_lift]; exact h k l ((Finset.mem_erase.mp hl).1)
    next => rw [norm_zero]; exact mul_nonneg hc.le (padded_nonneg x)
  have he (x): Arrives fun k=> F k x := by
    by_cases e:x=0
    · subst x; refine (Arrives.steady (0:ℂ)).copy (Eventually.of_forall fun i=>?_)
      refine (if_neg (show (0:Cover) ∉ S i from fun he=>?_)).symm
      obtain ⟨l,hl,hx⟩:= Finset.mem_image.mp he
      exact (Finset.mem_erase.mp hl).1 (lift_inj (hx.trans (lift_origin _).symm))
    let q := p+reciprocal x
    have hp' : physical q := by
      unfold q physical; rw [star_add,hp.1]; apply congr_arg; funext i; simp [reciprocal]
    refine ((arrive_lid A a i q hp').times (eventual_high A i p hp x e)).copy ?_
    filter_upwards [relevant (mass_growth A i) x] with k hk
    let l:=wrap (M k) x
    have hi : l≠0 := by intro ht; exact e (hk.symm.trans ((congr_arg lift ht).trans (lift_origin _)))
    have hu : x∈S k:= Finset.mem_image.mpr ⟨l,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩,hk⟩
    rw [show F k x = f k l from if_pos hu]; unfold f
    rw [show aliasAt p l = narrow (M k) q by ext j; rw [alias_value,narrow_apply,show lift l=x from hk]; rfl]; rfl
  choose D hD using he
  exact ⟨_, tendsto_tsum_of_dominated_convergence ((padded_sum).mul_left c) hD (Eventually.of_forall hx)⟩

private lemma noise_increment (i d : ℕ) (p : Momentum) (a : Axis) :
    (flying A (d+1) i).levelNoise a p=(flying A d i).levelNoise a p+ feed (flying A d i) a (fun _=>1) p := by
  induction d generalizing p i with
  | zero => simp only [flying,Flight.land]; rw [Train.nozzle_flow]; simp [Train.levelNoise, Train.stream, Train.nozzle, slide, shuttle,stageHop,feed_top]
  | succ d h =>
    let P := (A.clock.op i 0).patch
    let V:= flying A d (i+1); let U:= flying A (d+1) (i+1)
    rw [flying, flying]
    change (Train.hop P _ _ U).levelNoise a p=(Train.hop P _ _ V).levelNoise a p+feed (Train.hop P _ _ V) a (fun _=>1) p
    rw [Train.nozzle_flow,Train.nozzle_flow,bind_feeds]
    have hX : U.levelNoise a = fun y=> V.levelNoise a y+ 1*feed V a (fun _=>1) y := funext fun y=> by unfold U V; rw [h,one_mul]
    erw [hX,Train.bound_shuttle]; rw [one_mul,add_assoc]; rfl

lemma arrive_noise (a : Axis) (i : ℕ) (p : Momentum) (hp : p ∈ baseCube) :
    Arrives fun d=> (flying A d i).levelNoise a p := by
  let V k:= flying A k i; let g k:=feed (V k) a (fun _=>1) p
  obtain ⟨η,C,hη,hC,h⟩:= Train.feed_budget (A.clock.adm i) V (fun _=>a)
  have hf : Summable g:= by
    apply (summable_geometric_two.mul_left C).of_norm_bounded
    intro k
    refine ((h k).bound p (mem_cube_real (base_subset_realCube hη hp) hη)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC.le
    dsimp only [V]; rw [flying_mass]
    have hh : (2:ℝ)^k ≤ (A.S.steps i k).val := by exact_mod_cast steps_big A.S k i
    rw [div_pow,one_pow,one_div]; exact inv_anti₀ (by positivity) (hh.trans (le_self_pow₀ (by exact_mod_cast (A.S.steps i k).property) (by omega)))
  have he (k): ∑ i'∈Finset.range k, g i'=(V k).levelNoise a p:= by
    induction k with
    | zero=> simp [V,flying,Train.levelNoise,Train.stream,Train.nozzle]
    | succ k h => rw [Finset.sum_range_succ,h]; exact (noise_increment ..).symm
  refine (show Arrives _ from ⟨_,hf.hasSum.tendsto_sum_nat⟩).copy (Eventually.of_forall he)

lemma levelD_history (k : ℝ) (a : Axis) (i : ℕ) (p : Momentum) (hp : p ∈ baseCube) (he : p ≠ 0) :
    Arrives fun d=> (location A d i).levelD k a p := by
  have hD := divisor_limit (mass_growth A i) p
  let V n:= flying A n i
  have ht : Arrives (fun n => (V n).levelD k a p) := by
    simp_rw [Train.pole_split,Train.drain]
    refine ((arrive_lid A a i p hp.1).times (hD.reci ?_)).plus
      ((arrive_high A a i p hp).plus ((Arrives.steady (k:ℂ)⁻¹).times (arrive_noise A a i p hp)))
    exact ⟨_,mul_pos (pow_pos meter.low_pos _) (lengthSq_pos he),Eventually.of_forall fun i=> ((divisor_real_bounds _ (base_subset_realCube zone_pos hp)).1).trans (Complex.re_le_norm _)⟩
  exact ht.upon (fun n=>n-i) (tendsto_sub_atTop_nat i)
end YM.UVExtension.Free
