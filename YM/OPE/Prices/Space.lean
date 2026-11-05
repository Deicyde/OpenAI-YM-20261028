import YM.OPE.Prices.Circuit

/-! # The trace from the truncated projector fits by the actual trace size
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Lattice RG Push MergeProof Accent Ribbons
open scoped Topology BigOperators
variable {G:Gauge}{C:Family G}{ι:Type*}{I:Type}[Fintype I][DecidableEq I](i₀:I){l:Filter ι}{T:ι→ℝ}{a b c:ℝ}
variable {m k j:ι→ℕ}
variable (hG:G.Simple){W r D} (L: Package C W r D)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "P'"=> C.path.levels.budget
local notation "Λ" => C.S.scale
local notation "J" => C.path.levels.clock.J
lemma note_reg (p:Levels G) : Note p.S (fun i=> (p.clock.J i:ℝ)+5) 0:=by
    let u(i):ℝ:= p.clock.J i +5; let x(i):= p.S.scale i; let B:=Real.log 3; let f (i:ℕ) := 1/B*x i
    have hB:0<B:= Real.log_pos (by norm_num)
    have hC(i):1 ≤ u i:=by unfold u; have ht : (0:ℝ)≤p.clock.J i:=Nat.cast_nonneg _; linarith
    have he(i):0 ≤ x i:= Shoot.scale_nn p i
    have hv(i) : u i ≤ u 0 + f i:= by
       induction i with
       | zero=> rw [show f 0=0 from (by unfold f x;simp)]; linarith only
       | succ i ih=>
          have hp : (p.clock.J (i+1):ℝ) ≤ (p.clock.J i:ℝ)+1:= by exact_mod_cast p.fits.stepSlow i
          have hu : B ≤ Real.log (p.S.block i).val:= Real.log_le_log (by norm_num) (by exact_mod_cast p.S.block_large i)
          have hy : f (i+1)= f i+Real.log (p.S.block i).val/B:=by unfold f x; rw [Schedule.scale_succ]; ring
          rw [hy]; have ht': 1 ≤ f (i+1)-f i:=by rw [hy]; linarith only [(one_le_div hB).mpr hu]
          rw [hy] at ht'; unfold u at *; linarith only [hp,ht',ih]
    refine ⟨fun i=> zero_lt_one.trans_le (hC i),tendsto_of_tendsto_of_tendsto_of_le_of_le' (h:=fun i=> Real.log (u 0+1/B)/x i+Real.log (x i)/x i) tendsto_const_nhds ?_ ?_ ?_⟩
    · let y:ℝ:= u 0+1/B; have hy:0<y:= add_pos_of_pos_of_nonneg (zero_lt_one.trans_le (hC _)) (by positivity)
      apply (show Tendsto (fun i=> Real.log (u 0+1/B)/x i+Real.log (x i)/x i) atTop (𝓝 0) from by simpa only [zero_add] using ( (show Tendsto (fun i=> Real.log y/x i) atTop (𝓝 0) from tendsto_const_nhds.div_atTop p.S.divergent).add (show Tendsto (fun i=>Real.log (x i)/x i) atTop (𝓝 0) from (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp p.S.divergent)))
    · exact Eventually.of_forall fun i=> div_nonneg (Real.log_nonneg (hC i)) (he i)
    filter_upwards [p.S.divergent.eventually_ge_atTop 1] with i hi; have hU(i):0 < u i:= zero_lt_one.trans_le (hC _); have ht : 0 < x i:= zero_lt_one.trans_le hi; change Real.log (u i)/x i≤ _; rw [← add_div,← Real.log_mul (by exact ne_of_gt (add_pos (hU 0) (by positivity))) (ne_of_gt ht)];
    refine div_le_div_of_nonneg_right (Real.log_le_log (hU _) ((hv _).trans ?_)) ht.le
    rw [add_mul]; exact add_le_add (le_mul_of_one_le_right (hU 0|>.le) hi) le_rfl
lemma height_room (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hT:Tendsto T l atTop)(h:b<a)(r:ℕ) : ∀ᶠ i in l, GridApprox.room C.path.levels (k i) (m i) r:=by
    have hx:= ((RateIs.const (c:=30) hT (by norm_num)).mul hm.mesh).mul (height0 (note_reg (Y)) hm)
    have he:= (RateLE.const (2:ℝ) hT).mul ((RateLE.mul (hm.mesh.pays hT) (RateLE.const (r:ℝ) hT)).add (hx.pays hT|>.mono (by linarith only)) hT)
    exact hk.mesh.overtakes he hT (by linarith only [h])
end YM.OPE
