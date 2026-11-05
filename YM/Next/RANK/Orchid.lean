import YM.Next.RANK.Ratios

/-!
# Post U costs over actual A sites
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} (Q : Purse)
private lemma tether : ∀ᶠ s in atTop, walls s ≤ 64*walls (s/2):= by
  filter_upwards [(Real.tendsto_log_atTop.comp half).eventually_ge_atTop (max 1 (Real.log 2)),eventually_gt_atTop 0] with s hs hp
  have hx : 1 ≤ Real.log (s/2):= le_trans (le_max_left ..) hs; have h₂:Real.log 2 ≤ Real.log (s/2):= le_trans (le_max_right ..) hs
  have he : Real.log s= Real.log (s/2)+Real.log 2:= by rw [Real.log_div (by positivity) (by norm_num),sub_add_cancel]
  have ht : M s ≤8 * M (s/2):= by
    have hz: (M s:ℝ)<Real.log s^2+1:= Nat.ceil_lt_add_one (sq_nonneg _); have hh: Real.log (s/2)^2 ≤ (M (s/2):ℝ):= Nat.le_ceil _
    have hb:0≤Real.log 2:= Real.log_nonneg (by norm_num); exact_mod_cast (show (M s:ℝ) ≤ 8* M (s/2) by nlinarith)
  unfold walls; calc
    _ ≤ _:= Nat.pow_le_pow_left ht 2
    _ = _:= by ring

-- account proportional placements only when also meeting min room
private lemma space_v (q : ℕ) : ∀ᶠ s in atTop,3*q*walls s+3 ≤ M s^10:= by
  filter_upwards [many.eventually_ge_atTop (max (3*q+3) 2)] with s hs
  have hp:1 ≤ M s:= by omega
  have he:= one_le_pow₀ (n:=2) hp
  calc
    _ ≤ (3*q+3) * M s^2:= by unfold walls; linarith only [he]
    _ ≤ M s*M s^2:= by gcongr; omega
    _ = M s^3:= by ring
    _ ≤ _ := pow_le_pow_right₀ hp (by omega)
lemma sizes_C (u : ℝ) (q d : ℕ) {L : ℕ} (hm:10≤ d) (h:d+10 ≤ q) (hL : 128*q ≤ L):
    ∀ᶠ s in atTop, ∀ (A : Levels G) (p k : ℕ), wheel A k=(L:ℝ) → clim A k =s →
      Allowed A u k→(∀ i,Station.width A u k ≤ i → i≤ k → clim A i∈Set.Icc (s/2) s) →
        roomTest A u k p d q := by
  filter_upwards [space_v q,tether,Perch.half.eventually_ge_atTop 1,(Perch.big.comp Perch.half).eventually_ge_atTop 8] with s hw ht he hy
  intro A p k hl hx H HR
  let l:=middle A u k
  let f m := walls (clim A m)
  have hh (i) (hg : Station.width A u k ≤ i) (hk : i ≤ k):walls (s/2)≤f i∧ f i≤walls s:= by
    have hp:=HR i hg hk; exact ⟨wall_mono (show 1 ≤ s/2 from he) (le_trans he hp.1) hp.1, wall_mono (le_trans he hp.1) ((le_trans he hp.1).trans hp.2) hp.2⟩
  have he(i) (g:l ≤ i) (h:i≤k):3*q*f i+3 ≤ (A.clock.coverSize k)^10:= by
    rw [← hx] at hw; apply le_trans _ hw; rw [hx]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hh i ((Station.wider ..).trans g) h).2) _
  refine ⟨hm,h,fun i hv hB=>?_,fun i hv hV=>?_,fun i H h=> le_trans hy (hh i ((Station.wider ..).trans H) h).1,he⟩
  · let w:= A.S.toDepth (Station.wider A u k) p; let lh:=Station.width A u k
    have hz:w.count.val≤(A.S.side i p).val:= by
      apply le_trans (b:=(A.S.side l p).val)
      · rw [w.exact_size];exact Nat.le_mul_of_pos_left _ (A.S.side lh p).property
      exact Nat.mul_le_mul_left (A.S.period p).val (A.S.den_strict.monotone hv)
    have H': (A.clock.coverSize k)^10 ≤ w.count.val:= H.surplusage p
    change 2*(q*f i+1)< _; linarith only [H',hz,he i hv hB,Nat.zero_le (q*f i)]
  intro r
  have hs': (A.S.block i).val=L := by exact_mod_cast ((H.blocks i ((Station.wider ..).trans hv) hV).trans hl)
  have ha' : r.count.val=L:= hs'
  change q*f (i+1)+r.count.val≤ f i*r.count.val; rw [ha']
  have hx := hh i ((Station.wider ..).trans hv) hV.le; have ht': f (i+1) ≤ 64 * f i := (hh (i+1) (((Station.wider ..).trans hv).trans (Nat.le_succ _)) hV).2.trans (ht.trans (Nat.mul_le_mul_left _ hx.1))
  have hq : 8 ≤ f i:= Nat.le_trans (show 8≤walls (s/2) from hy) hx.1; linarith only [Nat.mul_le_mul_right (f i) hL,Nat.mul_le_mul_right L hq,Nat.mul_le_mul_left q ht',Nat.zero_le L]
end YM.Next.Rank.Tapes
