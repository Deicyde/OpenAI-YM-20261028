import YM.Bid.Phase
import YM.Next.PHASE.Trains

/-!
# Uniform constants and Seats (red node RSeats)

This proves `Bid.Seats`. No assumption of `CenteredBook` (its separate each-period
part is not a premise here). Uses the CellHyp on the same extraction; proof does
not need the corrected detectors until assembly of the phase. No dependence of
the operator-bound constants on the length, separation, slab width, exterior
probe or number of copies. Train cost `B` in `QRead` may of course depend on the
exterior probe and the main field data, but not the number of replicas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Phase
open Function Filter Set Cells Extraction Extraction.Spin OS
open scoped Topology NNReal BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {f : Order} {S : Table C.book}

/-- Bound the whole signed/reflected raw family, not assuming orthonormal
 action for the raw coefficient norm. -/
private lemma mirror_ball (L : Register G) (D : ℕ) (R : ℝ) : ∃ Q : ℝ, 0 < Q ∧
    ∀ v : L.Token, v.1 ≤ D → ‖v.2‖ ≤ R → ∀ b : Frame, ‖(token L v b).2‖ ≤ Q := by
  let B (d : ℕ) (s : Signed) := LinearMap.toContinuousLinearMap (L.mirrorGroup d s)
  have h (i : Fin (D+1) × Signed) : ∀ᶠ q : ℝ in atTop, ‖B i.1 i.2‖*R ≤ q := eventually_ge_atTop _
  obtain ⟨Q,hQ,H⟩ := ((eventually_gt_atTop (0:ℝ)).and (eventually_all.mpr h)).exists
  refine ⟨Q,hQ, fun ⟨d,v⟩ hd hv b => ?_⟩
  have hb : ‖L.mirrorGroup d b.1 v‖ ≤ Q := ((B d b.1).le_opNorm v).trans
    ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (H (⟨d,Nat.lt_succ_of_le hd⟩,b.1)))
  rcases b with ⟨s,_|_⟩
  · exact hb
  change ‖star (L.mirrorGroup d s v)‖ ≤ _
  rw [norm_star]; exact hb

private lemma one_side (Q : Schedule) (k : ℕ) : 1 ≤ (Q.a k)⁻¹ :=
  (one_le_inv₀ (Q.a_pos k)).mpr (Q.a_zero ▸ Q.strictAnti.antitone (Nat.zero_le k))

private lemma one_grade (h : CellHyp C f) (d : ℕ) (R : ℝ) (hr : 0 < R) :
    ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ k ≥ M, ∀ t : C.book.Ref d, ‖t‖ ≤ R →
    f.late (centeredBudget C ⟨d,t⟩ (B*(C.S.a k)⁻¹^(d+1)) k) := by
  obtain ⟨M,hM,A,hA,hk⟩ := h.centered d 1 R zero_lt_one hr
  refine ⟨M,A+1,by positivity,fun k he t ht => ?_⟩
  refine (hk k he 1 zero_lt_one).mono fun j hj => hj.mono ?_
  rintro i ⟨hi, hh⟩
  refine ⟨hi,hM.trans (he.trans hi),fun o => ?_⟩
  obtain ⟨ha,hb⟩ := hh t ht o
  refine ⟨ha,hb.trans ?_⟩
  rw [show -(d:ℝ)-1=-((↑(d+1:ℕ)):ℝ) by push_cast; ring,
    Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast,add_mul,one_mul]
  gcongr; exact one_le_pow₀ (one_side C.S k)

/-- Constants pay *all* frames and remain fixed for arbitrary main word lengths. -/
lemma rates (H : CellHyp C f) (D : ℕ) (R : ℝ) :
    ∃ (F P : ℕ) (B : ℝ), 0 < B ∧ ∀ k ≥ F, ∀ v : C.book.Token, v.1 ≤ D → ‖v.2‖ ≤ R →
      f.late (Single C v (B*(C.S.a k)⁻¹^P) k) := by
  classical
  obtain ⟨Q,hQ,hv⟩ := mirror_ball C.book D R
  choose m b hb h using fun i : Fin (D+1) => one_grade H i Q hQ
  obtain ⟨F,hF⟩ := (eventually_all.mpr fun i : Fin (D+1) => eventually_ge_atTop (m i)).exists
  obtain ⟨B,hB,O⟩ := ((eventually_gt_atTop (0:ℝ)).and (eventually_all.mpr fun i => eventually_ge_atTop (b i))).exists
  let P := D+1
  have he (k : ℕ) (hh : F ≤ k) (w : C.book.Token) (hd : w.1 ≤ D) (hw : ‖w.2‖ ≤ Q) :
      f.late (centeredBudget C w (B*(C.S.a k)⁻¹^P) k) := by
    let i : Fin (D+1) := ⟨w.1,Nat.lt_succ_of_le hd⟩
    exact (h i k ((hF i).trans hh) w.2 hw).mono fun p hp => hp.mono fun j hj => fixup C hj
      (mul_le_mul (O i) (pow_le_pow_right₀ (one_side C.S k) (Nat.succ_le_succ hd))
        (pow_nonneg (inv_nonneg.mpr (C.S.a_pos k).le) _) hB.le)
  refine ⟨F,P,B,hB,fun k hk v hd hw => ?_⟩
  have ht x := he k hk (token C.book v x) (by simpa) (hv v hd hw x)
  unfold Order.late at ht ⊢
  filter_upwards [eventually_all.mpr ht] with p hp
  filter_upwards [eventually_all.mpr hp,
    eventually_all.mpr (fun x => Around.fit (f:=f) (token C.book v x) k),
    f.mesh.cofinal.eventually (eventually_ge_atTop k)] with j hj ht he
  exact ⟨he, fun _ x => ⟨hj x,ht x _⟩⟩

/-- Quantitative scale choice for the main field. One power bound for arbitrarily
 small `r` and *all* positive `n`, still after meeting any fixed family threshold `F`. -/
private lemma room_for (Q : Schedule) (F : ℕ) (H : Q.Gentle) : ∃ c : ℝ, 0 < c ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ m : ℕ, At Q F m (r/32) → ∀ n : ℕ, 0 < n →
    ∃ k : ℕ, m ≤ k ∧ (↑(2*n:ℕ):ℝ)*(2*(5*Q.a k)) < Q.a m ∧ c*(r/n)^4 ≤ Q.a k := by
  obtain ⟨t,ht,h⟩ := thickness Q F H
  let b := t/32^2
  let s := min (b/21) 1
  have hb : 0<b := by unfold b; positivity
  have hs : 0<s := lt_min (by positivity) zero_lt_one
  refine ⟨t*s^2,by positivity,fun r hr hr' m hm n hn => ?_⟩
  have hp : b*r^2 ≤ Q.a m := calc
    _ = t*(r/32)^2 := by unfold b; ring
    _ ≤ _ := h _ (by positivity) (by linarith) _ hm
  let δ : ℝ := s*(r/n)^2
  have hδ : 0<δ := by unfold δ; positivity
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hy : (0:ℝ) < n := by linarith
  have h₀ : δ ≤ 1 := mul_le_one₀ (min_le_right ..) (sq_nonneg _) (pow_le_one₀ (by positivity)
    ((div_le_one hy).mpr (hr'.trans hx)))
  obtain ⟨k,hk⟩ := OS.turn Q F δ hδ
  have ht₀ : (20*n:ℝ)*Q.a k < Q.a m := calc
    _ < (20*n:ℝ)*δ := mul_lt_mul_of_pos_left hk.2.1 (by positivity)
    _ ≤ b*r^2 := by
      have hh : (20*n:ℝ)*δ=20*s*r^2/n := by unfold δ; field_simp
      rw [hh]; apply le_trans (div_le_self (by positivity) hx)
      gcongr; linarith [show s ≤ b/21 from min_le_left ..]
    _ ≤ _ := hp
  have hm' : Q.a k < Q.a m := lt_of_le_of_lt (le_mul_of_one_le_left (Q.a_pos k).le (by linarith)) ht₀
  refine ⟨k,(Q.strictAnti.lt_iff_gt.mp hm').le,by push_cast; linarith,?_⟩
  calc
    _ = t * δ^2 := by unfold δ; ring
    _ ≤ _ := h _ hδ h₀ k hk

private lemma ext_room (Q : Schedule) (k n : ℕ) : ∀ᶠ b in atTop, (n:ℝ)*(2*(3*Q.a b))<Q.a k := by
  apply (show Tendsto (fun b => (n:ℝ)*(2*(3*Q.a b))) atTop (𝓝 0) from by
    simpa only [mul_zero] using (((Q.shrinks.const_mul (3:ℝ)).const_mul (2:ℝ)).const_mul (n:ℝ))).eventually
    (gt_mem_nhds (Q.a_pos k))

/-- Uniform train estimate at all covered slab widths on these scales. -/
theorem replicas (H : C.Makes) (hs : S.Hierarchy) (h : f.PointLimits C S) (hp : CellHyp C f) : Tiled C.S S timeAxis := by
  intro D R
  obtain ⟨F,P,J,hJ,hf⟩ := rates hp D R
  obtain ⟨c,hc,hc'⟩ := room_for C.S F C.path.levels.fits.mesh
  let B := J*(c⁻¹)^P
  have hB : 0 < B := by unfold B; positivity
  refine ⟨F,B,4*P,hB,fun r hr hr' m hm d hd w hw he hh hg => ?_⟩
  have ho := Nat.pos_of_ne_zero (show w.length≠0 from fun H => he (List.length_eq_zero_iff.mp H))
  obtain ⟨k,hk,hK,hA⟩ := hc' r hr hr' m hm _ ho
  let A := J*(C.S.a k)⁻¹^P
  have ha : A^w.length ≤ Spread.radius B (4*P) w r := by
    have hv : (C.S.a k)⁻¹ ≤ c⁻¹*(w.length/r)^4 := calc
      _ ≤ (c*(r/w.length)^4)⁻¹ := inv_le_inv₀ (C.S.a_pos k) (by positivity) |>.mpr hA
      _ = _ := by rw [mul_inv,← inv_pow, inv_div]
    calc _ ≤ (J*(c⁻¹*(w.length/r)^4)^P)^w.length := by
                  apply pow_le_pow_left₀ (by unfold A; have hh := C.S.a_pos k; positivity)
                  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have hh := C.S.a_pos k; positivity) hv _) hJ.le
         _ = _ := by unfold Spread.radius B; simp only [pow_mul,mul_pow]; ring
  intro v
  obtain ⟨e,ht⟩ := Ground.future_reach v
  obtain ⟨E,W,hW,t,ht',ht₁,ht₂⟩ := affordable ht
  obtain ⟨l,hl,hsep⟩ := ((eventually_ge_atTop k).and (C.S.shrinks.eventually (gt_mem_nhds ht'))).exists
  obtain ⟨g,K,Q,hQ,hq⟩ := rates hp E W
  obtain ⟨b,hb,hb',hb₀⟩ := ((eventually_ge_atTop l).and ((eventually_ge_atTop g).and
    (ext_room C.S l (2*v.val.length)))).exists
  let X := Q*(C.S.a b)⁻¹^K
  have hX : 0≤X := by unfold X; have hh := C.S.a_pos b; positivity
  refine ⟨X^(2*v.val.length),fun q => ?_⟩
  apply (travel_price H f S hs h hk hl hb hh hg hd v ht₂ q (hm.2.1.trans (by linarith))
    hsep hK hb₀ A X hX (fun i hi => hf k (hm.1.trans hk) i.2 (hw i hi).1 (hw i hi).2)
    (fun i hi => hq b hb' i.2 (hW i hi).1 (hW i hi).2)).trans
  rw [pow_mul A w.length]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (pow_nonneg (by unfold A; have hh := C.S.a_pos k; positivity) _) ha _) (pow_nonneg hX _)

/-- RSeats: `QRead` on a covered positive sub-width *chosen before* the exterior. -/
theorem seats : Bid.Seats := by
  intro G C S f s D R
  obtain ⟨F,B,K,hB,H⟩ := replicas s.cutoff s.kernel s.generic s.copies D R
  refine ⟨B,K,hB,fun d w hw hh hd r hr hr' h => ?_⟩
  obtain ⟨m,hm⟩ := OS.turn C.S F (r/32) (by positivity)
  obtain ⟨t,ht,hD,hH,hv⟩ := narrow C.S w hr hd h hw hm.2.1
  exact ⟨m,t,hD,ht,hH,H r hr hr' m hm t ht w hh hw hH hv⟩
end YM.Next.Phase
