import YM.Next.RANK.Gust
import YM.Next.RANK.NoSpill

/-!
# Every mixed k history can pay for its source slots from old M

All probes apart in rank's A layout. Between slots use a positive generic
separation (wrap calculated literally), and between copies use the actual
number of cells L(b_*). Works even before N→∞.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {V : Type}
variable {N k p v : ℕ} {b : ℝ}
variable (C : Family G) (X : Points v)

-- normalized separations uniform at arbitrary charged comparison stamps

def Spaced (M : ℕ) (ζ : V→Site n) := ∀ i j, i≠j → M^2 ≤ separation (ζ i) (ζ j)
lemma injected (M : ℕ) (ζ : V→Site n) (hM : 0<M) (h : Spaced M ζ) : Function.Injective ζ:= by
  intro i j hh; apply Classical.byContradiction; intro hj; have hp:= h i j hj; rw [hh,separation_self] at hp; exact not_le_of_gt (pow_pos hM _) hp

lemma lengthTag (h : Fit C.path.levels b k X) (p : ℕ) (i j):
    let A:=C.path.levels
    let s:= A.S.toDepth (before A b k) p
    8*(Station.choose A b k X i j).natAbs ≤ s.count.val := by
  -- physical tag deep
  intro A v
  let z:= Station.choose A b k X i j
  have hi := h.deep i j
  change |A.S.a k * (z:ℝ)|≤ _ at hi
  rw [abs_mul,abs_of_pos (A.S.a_pos k),← A.S.embeds_scale v] at hi
  have hh : A.S.a k*(8*|(z:ℝ)|) ≤ A.S.a k*v.count.val := by linarith only [hi]
  have ht := le_of_mul_le_mul_left hh (A.S.a_pos k)
  rw [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] at ht; exact_mod_cast ht

lemma at_depth (X : Points v) (b : ℝ) (hN : k≤N) (p : ℕ) (i : Listens C b (v:=v) hN p) :
    let A:= C.path.levels; let T:= Cells.center C.S p ((wider A b k).trans (before A b k)) 0; let x:= wrap (C.side k p) (Station.choose A b k X i.2)
    seats C b X hN p i = affine (T.omega i.1) (T.translateBy i.1) x:= by
  intro A T x; unfold seats Peak.readers; rw [exact_camp]; exact (C.S.toDepth hN p).embed_parent _

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

lemma raise (h : G.Simple) (hp : X ∈ generic _) (hb : 0<b) : ∀ᶠ k in atTop,
    ∀ (_ : Fit C.path.levels b k X) (_ : Allowed C.path.levels b k),∀ p N (hN : k≤N), Spaced (M (clim C.path.levels k)) (seats C b X hN p):= by
  let A:= C.path.levels
  have ht i j : ∀ᶠ k in atTop, ∀ (_:i≠j), M (clim A k) ^2 ≤ ((Station.choose A b k X i) 0- (Station.choose A b k X j) 0).natAbs:= by
    by_cases he:i=j
    · exact Eventually.of_forall fun _ H=> (H he).elim
    let a:= X i 0; let c:= X j 0; have hχ : a≠c:= fun h=> he (hp 0 h)
    let u:= |a-c|; have hu : 0<u := abs_pos.mpr (sub_ne_zero.mpr hχ)
    have hx : Tendsto (fun k=> |tested A b k X i 0-tested A b k X j 0|) atTop (𝓝 u) := (show Continuous fun p : Points v=> |p i 0 - p j 0| from by fun_prop).continuousAt.tendsto.comp (tuning A X h hb)
    have hv := hx.eventually (le_mem_nhds (show u/2<u by linarith))
    filter_upwards [hv, (hat_rate A h).eventually (Paint.absorb (b/2) b (by linarith) (2/u)),(hat_rate A h).eventually (Paint.q_power 1 (b/2) (by positivity))] with k hi hk hz H
    let z:=Station.choose A b k X;let M':=clim A k; let m:= Station.mag A b k
    have hp:=mag_pos A b k; have hg:= mag_bill A b k
    have hv : |tested A b k X i 0-tested A b k X j 0|=m⁻¹* |(((z i 0-z j 0):ℤ):ℝ)|:= by
      rw [reading]; change |m⁻¹*↑(z i 0)-m⁻¹*↑(z j 0)|=_; rw [← mul_sub,Int.cast_sub,abs_mul,abs_of_nonneg (inv_pos.mpr hp).le]
    rw [hv,← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast, ← div_eq_inv_mul,le_div_iff₀ hp] at hi
    rw [pow_one] at hz
    have hX : ((walls M'):ℝ)≤ u/2*m := by
      change (2/u)*_≤_ at hk; rw [div_mul_eq_mul_div, div_le_iff₀ hu] at hk; unfold m; rw [hg]; exact le_trans hz (by linarith only [hk])
    exact_mod_cast (hX.trans hi)
  filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr (ht i), (hat_rate A h).eventually (many.eventually_ge_atTop 8)] with k H hk H₀ H' p N hN
  rintro ⟨a,i⟩ ⟨c,j⟩ hi
  rw [at_depth, at_depth]; let s:= A.clock.coverSize k
  let Z:= A.S.toDepth ((wider A b k).trans (before A b k)) p
  let T:= center A.S p ((wider A b k).trans (before A b k)) 0
  let Y:= Station.choose A b k X
  let XZ (a : T.Cell) (i : Fin v):= affine (T.omega a) (T.translateBy a) (wrap (C.side k p) (Y i))
  change s^2 ≤ separation (XZ a i) (XZ c j)
  by_cases ha : a=c
  · subst c; have hz : i ≠ j:= fun H=> hi (H ▸ rfl); unfold XZ; rw [s_sep]
    exact (H i j hz).trans (in_cell C X H₀ _ _ p 0)
  have hm i j: separation (Z.embed i) (XZ i j) ≤ Z.count.val/8:= by
    unfold XZ; rw [show Z.embed i=affine (T.omega i) (T.translateBy i) 0 by simpa only [zero_add] using! (show 0+Z.embed i= T.copyMap i 0 from (copy_home ..).symm),s_sep,separation_comm,separation,sub_zero]
    apply Finset.sup_le; intro a _
    apply (lap ..).trans; change (Y j a).natAbs≤ _
    have hp:= lengthTag C X H₀ p j a; let L:= A.S.toDepth (before A b k) p;let Q:=A.S.toDepth (wider A b k) p
    change 8*(Y j a).natAbs≤ L.count.val at hp
    have he: L.count.val≤Z.count.val := (Nat.le_mul_of_pos_right _ Q.count.property).trans (size_comp Q L Z).symm.le
    omega
  have hB : Z.count.val≤ separation (Z.embed a) (Z.embed c):= by rw [both]; exact Nat.le_mul_of_pos_right _ (separation_pos a c ha)
  have he : 2*s^2≤ Z.count.val:= by
    change 8 ≤ s at hk
    have hd := H'.surplusage p; let L:= A.S.toDepth (before A b k) p;let Q:=A.S.toDepth (wider A b k) p
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
