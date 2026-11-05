import YM.Extension.UV.FreeBounds
/-! Contractive propagation at nonzero real momentum. No stationarity assumption about the
quadratic kernels: they are re-run from Wilson Laplacian and the SAME scales via Next.Free.location.
The extra floor does not depend on the cutoff and can be requested before choosing rolls.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Filter Function Lattice RG Laurent Bloch Metric Next.Free
open scoped Topology BigOperators
variable {j : ℕ} {G:Gauge}

lemma slide_sub (P : RG.Patch) (a : Axis) (f g : Momentum→ℂ) (p : Momentum) : slide P a (fun q=>f q-g q) p=slide P a f p - slide P a g p := by
  simpa only [sub_eq_add_neg,neg_mul,one_mul] using Train.bound_shuttle P a f g (-1) p
lemma D_diff_tied (k : ℝ) (A : Levels G) (a : Axis) (n n' : ℕ) (i m : ℕ) (hi:i ≤ n) (hi':i≤ n') (h:m≤ i) (p : Momentum) :
    Train.levelD k (location A n m) a p- Train.levelD k (location A n' m) a p=feed (location A i m) a (fun q=>Train.levelD k (location A n i) a q - Train.levelD k (location A n' i) a q) p := by
  set d := i - m
  have hh := show m +d = i by omega
  clear_value d
  subst i
  induction d generalizing m p with
  | zero => simp only [Nat.add_zero,loc_top,feed_top]
  | succ d ih =>
    simp_rw [show m+(d+1)=m+1+d by omega] at *
    have hN : m < n := by omega
    have hN' : m < n' := by omega
    have hh' (z : Momentum) := ih (m+1) z (by omega) (by omega) (by omega) 
    rw [loc_land _ n _ hN,loc_land _ n' _ hN', Flight.land,Flight.land, Train.D_feedback, Train.D_feedback, add_sub_add_right_eq_sub, loc_land A (m+1+d) m (by omega)]
    have hslide : slide (destination A n m).patch a (Train.levelD k (destination A n m).wing a) p - slide (destination A n' m).patch a (Train.levelD k (destination A n' m).wing a) p = _ := (slide_sub (destination A n m).patch a (Train.levelD k (destination A n m).wing a) (Train.levelD k (destination A n' m).wing a) p).symm
    apply Eq.trans hslide
    apply Eq.trans ?_ (bind_feeds (P:=(destination A (m+1+d) m).patch) .. |>.symm)
    change slide _ _ (fun q=> Train.levelD k (location A n (m+1)) a q - Train.levelD k (location A n' (m+1)) a q) _ = _
    conv_lhs => arg 3; intro q; rw [hh' q]
    rw [show m+(d+1)=m+1+d by omega]
    exact rfl

lemma alias_lower (p : Momentum) (hp:p∈baseCube) (h0 : p≠0) : ∃ c>0,∀ (j : ℕ) (v:Train j) (l : Site v.mass), c / (v.mass.val:ℝ) ≤ ‖aliasAt p l‖ := by
  have he := norm_pos_iff.mpr h0
  refine ⟨min (Real.pi/4) ‖p‖,lt_min (div_pos Real.pi_pos (by positivity)) he,fun j v l=>?_⟩
  let M := v.mass
  have hm := side_pos M
  by_cases hz : l=0
  · subst l; rw [alias_zero_eq,narrow,norm_smul,norm_inv,Complex.norm_natCast]; rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left (min_le_right ..) (by positivity)
  obtain ⟨a,ha⟩ := hit_grade l
  have hg := grade_gt hz
  have hC := base_subset_realCube zone_pos hp
  have h' := scaled_alias_lower l (mem_cube_real hC zone_pos) a (by intro h; simp_all [up])
  rw [div_le_iff₀ hm]
  calc
    min (Real.pi/4) ‖p‖ ≤ Real.pi/4 := min_le_left ..
    _ ≤ (Real.pi/4)*up l a := (le_mul_of_one_le_right (div_nonneg Real.pi_pos.le (by positivity)) (up_ge ..))
    _ ≤ M.val*‖aliasAt p l a‖ := h'
    _ ≤ ‖aliasAt p l‖*M.val := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (norm_le_pi_norm _ _) (by positivity)

lemma Dtail_bound (k : ℝ) (A:Levels G) (m : ℕ) (a : Axis) (p : Momentum) (hp:p∈baseCube) (h0:p≠0) : ∃ B:ℝ,0<B ∧
    ∀ i, m≤ i → ∀ n ≥ i,∀ n' ≥ i, ‖Train.levelD k (location A n m) a p - Train.levelD k (location A n' m) a p‖ ≤ B * (Dcost k (A.clock.J i) / ((location A i m).mass.val:ℝ)):= by
  obtain ⟨η,C,hη,hC,h⟩ := Train.feed_budget (A.clock.adm m) (fun i: Train (A.clock.J m)=> i) (fun _=>a)
  obtain ⟨c,hc,ha⟩ := alias_lower p hp h0
  refine ⟨C*2*(1+c⁻¹),by positivity,fun i hi n hn n' hn' => ?_⟩
  let K := Dcost k (A.clock.J i)
  let v := location A n m
  let w := location A i m
  set M : ℝ := (w.mass.val:ℝ)
  have hM : 1 ≤ M := by change (1:ℝ) ≤ (w.mass.val:ℝ); exact_mod_cast w.mass.property
  have hM' : 0 < M := by positivity
  have hx (l:Site w.mass) : 0 < ‖aliasAt p l‖ := by apply lt_of_lt_of_le _ (ha _ w l); positivity
  have hy l := diff_bound k (A.clock.adm i) (location A n i) (location A n' i) a (aliasAt p l) (alias_base hp l w.mass_odd) (norm_pos_iff.mp (hx l))
  set f := fun p=> Train.levelD k (location A n i) a p - Train.levelD k (location A n' i) a p
  have hk := Dcost_pos k (A.clock.J i)
  have h' (l:Site w.mass) : ‖f (aliasAt p l)‖ ≤ 2*K*(M*(1+c⁻¹)) := by
    have he := ha _ w l
    calc
      _ ≤ 2*K*(1+‖aliasAt p l‖⁻¹) := hy l
      _ ≤ 2*K*(1+(c/M)⁻¹) := by gcongr
      _ = 2*K*(1+M*c⁻¹) := by rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm M]
      _ ≤ _ := by
         have hKK : 0 ≤ 2*K := by dsimp [K]; positivity
         nlinarith
  have hu := (h w).bound p (mem_cube_real (base_subset_realCube hη hp) hη)
  rw [D_diff_tied k A a n n' i m hn hn' hi]
  apply (feed_control w a p hp.1 f h').trans
  calc
    _ ≤ (C*(M^2)⁻¹)*(2*K*(M*(1+c⁻¹))) := mul_le_mul_of_nonneg_right hu (by unfold K; positivity)
    _ = _ := by change _ = C*2*(1+c⁻¹)*(K/M); field_simp

lemma mass_growth (A:Levels G) (m i:ℕ) (h:m< i) : ((A.S.block (i-1)).val:ℝ)*2^(i-1-m) ≤ (location A i m).mass.val:= by
   set d:= i-1-m
   have hh : m+1+d=i := by omega
   clear_value d
   subst i
   induction d generalizing m with
   | zero => simp only [Nat.add_zero,pow_zero,mul_one,Nat.add_sub_cancel] at *
             rw [loc_land A (m+1) m h]; change _ ≤ ((((A.S.block m)*(location A (m+1) (m+1)).mass).val):ℝ)
             rw [loc_top]; simp [Train.mass]
   | succ d ih =>
     have h' : m+1<m+1+ (1+d) := by omega
     have ht := ih (m+1) (show m+1<m+1+1+d by omega)
     rw [show m+1+(d+1)=(m+1)+1+d by omega,loc_land _ _ _ (by omega)]
     change _ ≤ ((((A.S.block m)*(location A ((m+1)+1+d) (m+1)).mass).val):ℝ)
     rw [mul_side_real,pow_succ,← mul_assoc,mul_comm ((A.S.block m).val:ℝ)]
     exact mul_le_mul ht (by exact_mod_cast (by have := A.S.block_large m; omega : 2 ≤ (A.S.block m).val)) (by positivity) (by positivity)

end YM.Extension.UV.Linear
