import YM.Next.RANK.ArraySpace
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {V : Type}
variable {N k p v : ℕ} {b : ℝ}
variable (C : Family G) (X : Points v)

private lemma in_cell (h : Fit C.path.levels b k X) (i j : Fin v) (p : ℕ) (a : Axis) :
    let A:= C.path.levels; let z:= Station.choose A b k X; let v:=wrap (C.side k p)
    ((z i a)-(z j a)).natAbs ≤ separation (v (z i)) (v (z j)):= by
  intro A z w; let s:= C.S.toDepth (before A b k) p
  unfold separation; rw [← map_sub]
  have hx : s.count.val ≤ (C.side k p).val := by
    rw [s.exact_size]; exact Nat.le_mul_of_pos_left _ (C.side _ p).property
  have hi : lift (w (z i-z j))=z i-z j:= lift_eq_iff.mpr ⟨rfl,fun b=> by
    have hp:8*(z i b).natAbs≤ s.count.val:= lengthTag C X h p ..
    have he:8*(z j b).natAbs≤ s.count.val:= lengthTag C X h p ..
    have H:0<s.count.val:=s.count.property;simp only [Pi.sub_apply];omega⟩
  simpa only [hi] using! (component_le (w (z i-z j)) a)

lemma riseX (h : G.Simple) (hp : X ∈ conf _) (hb : 0<b)(κ:ℕ→ℕ)(px:ℕ→ Points v) (hκ:Tendsto κ atTop atTop)(HP:Tendsto (fun i=> tested C.path.levels b (κ i) (px i)) atTop (𝓝 X)) : ∀ᶠ k in atTop,
    ∀ (_ : Fit C.path.levels b (κ k) (px k)) (_ : Allowed C.path.levels b (κ k)),∀ p N (hN : κ k≤N), Spaced (M (clim C.path.levels (κ k))) (seats C b (px k) hN p):= by
  let A:= C.path.levels
  have ht i j : ∀ᶠ k in atTop, i≠j → ∃ u : Axis, M (clim A (κ k)) ^2 ≤ ((Station.choose A b (κ k) (px k) i) u- (Station.choose A b (κ k) (px k) j) u).natAbs:= by
    by_cases he:i=j
    · exact Eventually.of_forall fun _ H=> (H he).elim
    have hx' := (show Function.Injective X.ofLp from hp).ne he
    obtain ⟨η,hη⟩:= show ∃ a:Axis,X i a ≠ X j a from by
       by_contra! H; exact hx' (PiLp.ext H)
    let a:= X i η; let c:= X j η; have hχ : a≠c:= hη
    let u:= |a-c|; have hu : 0<u := abs_pos.mpr (sub_ne_zero.mpr hχ)
    have hx : Tendsto (fun k=> |tested A b (κ k) (px k) i η-tested A b (κ k) (px k) j η|) atTop (𝓝 u) := (show Continuous fun p : Points v=> |p i η - p j η| from by fun_prop).continuousAt.tendsto.comp HP
    have hv := hx.eventually (le_mem_nhds (show u/2<u by linarith))
    filter_upwards [hv, ((hat_rate A h).comp hκ).eventually (Paint.absorb (b/2) b (by linarith) (2/u)),((hat_rate A h).comp hκ).eventually (Paint.q_power 1 (b/2) (by positivity))] with k hi hk hz H
    let z:=Station.choose A b (κ k) (px k);let M':=clim A (κ k); let m:= Station.mag A b (κ k)
    have hp:=mag_pos A b (κ k); have hg:= mag_bill A b (κ k)
    have hv : |tested A b (κ k) (px k) i η-tested A b (κ k) (px k) j η|=m⁻¹* |(((z i η-z j η):ℤ):ℝ)|:= by
      rw [reading]; change |m⁻¹*↑(z i η)-m⁻¹*↑(z j η)|=_; rw [← mul_sub,Int.cast_sub,abs_mul,abs_of_nonneg (inv_pos.mpr hp).le]
    rw [hv,← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast, ← div_eq_inv_mul,le_div_iff₀ hp] at hi
    rw [pow_one] at hz
    have hX : ((walls M'):ℝ)≤ u/2*m := by
      change (2/u)*_≤_ at hk; rw [div_mul_eq_mul_div, div_le_iff₀ hu] at hk; unfold m; rw [hg]; dsimp only [Function.comp_apply] at hk hz; unfold clim; exact le_trans hz (by linarith only [hk])
    refine ⟨η,?_⟩; exact_mod_cast (hX.trans hi)
  filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr (ht i), ((hat_rate A h).comp hκ).eventually (many.eventually_ge_atTop 8)] with k H hk H₀ H' p N hN
  rintro ⟨a,i⟩ ⟨c,j⟩ hi
  rw [at_depth, at_depth]; let s:= A.clock.coverSize (κ k)
  let Z:= A.S.toDepth ((wider A b (κ k)).trans (before A b (κ k))) p
  let T:= center A.S p ((wider A b (κ k)).trans (before A b (κ k))) 0
  let Y:= Station.choose A b (κ k) (px k)
  let XZ (a : T.Cell) (i : Fin v):= affine (T.omega a) (T.translateBy a) (wrap (C.side (κ k) p) (Y i))
  change s^2 ≤ separation (XZ a i) (XZ c j)
  by_cases ha : a=c
  · subst c; have hz : i ≠ j:= fun H=> hi (H ▸ rfl); unfold XZ; rw [s_sep]
    obtain ⟨η,hη⟩:= H i j hz; exact hη.trans (in_cell C _ H₀ _ _ p η)
  have hm i j: separation (Z.embed i) (XZ i j) ≤ Z.count.val/8:= by
    unfold XZ; rw [show Z.embed i=affine (T.omega i) (T.translateBy i) 0 by simpa only [zero_add] using! (show 0+Z.embed i= T.copyMap i 0 from (copy_home ..).symm),s_sep,separation_comm,separation,sub_zero]
    apply Finset.sup_le; intro a _
    apply (lap ..).trans; change (Y j a).natAbs≤ _
    have hp:= lengthTag C (px k) H₀ p j a; let L:= A.S.toDepth (before A b (κ k)) p;let Q:=A.S.toDepth (wider A b (κ k)) p
    change 8*(Y j a).natAbs≤ L.count.val at hp
    have he: L.count.val≤Z.count.val := (Nat.le_mul_of_pos_right _ Q.count.property).trans (size_comp Q L Z).symm.le
    omega
  have hB : Z.count.val≤ separation (Z.embed a) (Z.embed c):= by rw [both]; exact Nat.le_mul_of_pos_right _ (separation_pos a c ha)
  have he : 2*s^2≤ Z.count.val:= by
    change 8 ≤ s at hk
    have hd := H'.surplusage p; let L:= A.S.toDepth (before A b (κ k)) p;let Q:=A.S.toDepth (wider A b (κ k)) p
    have hh : 2 ≤ s^8:= by apply Nat.le_trans hk _ |> fun h=>le_trans (show 2 ≤ 8 by decide) h; simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ s by omega) (by decide : 1≤8)
    calc
      _ ≤ s^8*s^2:= by gcongr
      _ = s^10:= by ring
      _ ≤ Q.count.val:=hd
      _ ≤ _ := (Nat.le_mul_of_pos_left _ L.count.property).trans (size_comp Q L Z).symm.le
  have ht:= separation_triangle (Z.embed a) (XZ a i) (Z.embed c)
  have hp:=separation_triangle (XZ a i) (XZ c j) (Z.embed c); rw [separation_comm (XZ c j)] at hp
  have hX:=hm a i; have hY:=hm c j; omega
end YM.Next.Rank.Edition
