import YM.RG08.Fields.Argyle

/-! # Pointwise movement of full `D` on the real cube: same history's
**unmodified** symbol, all components (not just horizontal). Puncture gain
integrable. This estimate also allows price on the step T/A. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators
variable {j : ℕ} {k : ℝ}

lemma frost_read {α β : Type} {A : Row α β} {p : Momentum} (hp : physical p) {σ C : ℝ}
    (hs : 0<σ) (h : A.strip σ C) (i : α) (j : β) : ‖A.read p i j‖ ≤ C := by
  have hx := Laurent.Width.series (Row.constant_strip A h i j) p (fun i=> (Work.F07.realStrip _ hs hp i).le)
  exact (norm_tsum_le_tsum_norm hx.2.1).trans hx.2.2
lemma lengthSnap (p : Momentum) : ‖p‖^2≤ lengthSq p := by
  have h : 0≤lengthSq p := Finset.sum_nonneg fun i _=> pow_two_nonneg (‖p i‖)
  rw [← Real.sq_sqrt h]; refine pow_le_pow_left₀ (norm_nonneg _) ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_) _
  intro i; exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.sqrt_nonneg _) (by decide : 2≠0)).1 (by
    rw [Real.sq_sqrt h]; exact Finset.single_le_sum (f:=fun i => ‖p i‖^2) (fun _ _=> by positivity) (Finset.mem_univ _))
lemma lengthHSnap (p : Momentum) : lengthSq p ≤ 4*‖p‖^2 := by
  unfold lengthSq
  refine (Finset.sum_le_sum (g:=fun _ => ‖p‖^2) fun i _=> pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm p i) _).trans_eq ?_
  simp [Axis]
lemma jewel_charge {p} (hp : p∈baseCube) (a : Axis) : ‖jewel 1 p a‖ ≤ meter.high^2 * ‖p‖^2 := by
  have hs (p) (hv : p∈realCube zone) := meter.above (p a) (zone_in_disk p (mem_cube_real hv zone_pos) _)
  have hv := base_subset_realCube zone_pos hp; rw [jewel_one,norm_mul]
  refine (mul_le_mul (hs p hv) (hs _ (realCube_neg hv)) (norm_nonneg _) ((norm_nonneg _).trans (hs p hv))).trans ?_
  change meter.high *_ * (meter.high* ‖- p a‖) ≤ _
  rw [norm_neg,mul_mul_mul_comm, ← pow_two, ← pow_two]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ _) _) (by positivity)

lemma full_coin (hk : 0<k) (hj : 4 ≤ j) : ∃ C>0, ∀ (v : Train j) (a : Axis) p, p∈baseCube → p≠0 →
    ‖v.levelD k a p‖ ≤ C/ ‖p‖^2 ∧ ‖(v.levelD k a p)⁻¹‖ ≤ C*‖p‖^2 := by
  let v (x : Train j × Axis):=x.1; let a (x : Train j × Axis):=x.2
  obtain ⟨s,c,hs,hc,H⟩ := Train.bulb_budget k hj v a
  obtain ⟨t,d,ht,hd,U⟩ := Train.bulb_firm k hk v a
  let X:=c/meter.low^2; let Y:=meter.high^2*4/d; have ha := meter.low_pos
  have hM : 0<X := by unfold X; positivity
  refine ⟨max X Y,lt_max_of_lt_left hM,fun W b p hp he=> ?_⟩
  have hx := base_subset_realCube zone_pos hp
  have hq := divisor_real_bounds W.mass hx
  have hg := Silver.chipSq W.mass hp.1
  have hm : ‖Train.bulb k W p b‖ ≤ c := ((H (W,b)).bound p (mem_cube_real (base_subset_realCube hs hp) hs)).trans_eq (mul_one _)
  have hr : d ≤ ‖Train.bulb k W p b‖ := (mul_one d) ▸ U (W,b) p (base_subset_realCube ht hp)
  have hu := norm_pos_iff.mpr he
  rw [Train.D_bulb _ W hx he b,norm_inv,norm_div,inv_div, hg.norm]
  constructor
  · calc
     _ ≤ c/(meter.low^2*‖p‖^2) := div_le_div₀ hc.le hm (by positivity) ((mul_le_mul_of_nonneg_left (lengthSnap p) (by positivity)).trans hq.1)
     _ = X/‖p‖^2 := by rw [div_div]
     _ ≤ _ := div_le_div_of_nonneg_right (le_max_left ..) (by positivity)
  calc
    _ ≤ (meter.high^2*(4*‖p‖^2))/d := div_le_div₀ (by positivity) (hq.2.trans (mul_le_mul_of_nonneg_left (lengthHSnap _) (by positivity))) hd hr
    _ = Y*‖p‖^2 := by unfold Y; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)

-- blade formula for analytic **inverse** D including cost near origin
private def rhPair (i j : Axis) (h : i≠j) : TypeFace 2 :=
    ⟨{i,j},by simp [h]⟩
private def rhsH (i j : Axis) : Axis := Classical.choose (show ∃ x : Axis, x≠i∧x≠j from by revert i j; decide)
private lemma rhsH_law (i j) : rhsH i j≠i ∧ rhsH i j≠j := Classical.choose_spec (p:=fun x : Axis=> x≠i∧x≠j) _
lemma dual_books (hk : 0<k) (v : Train j) {p} (hp : p∈baseCube) (he : p≠0) (i z : Axis) (h : i≠z) :
    vault k v p (rhPair i z h) (rhPair i z h)=v.rho k p * v.levelD k i p * v.levelD k z p ∧
    pulse k v p (rhPair i z h) (rhPair i z h)=(vault k v p (rhPair i z h) (rhPair i z h))⁻¹ := by
  have hv := base_subset_realCube zone_pos hp
  rw [vault_sources k hk _ hv he,pulse_sources k hk _ hv he]
  simp [mask,inventory,rhPair,h,mul_left_comm,mul_comm,mul_assoc]
private def north (v : Train j) (k : ℝ) (p : Momentum) (i z : Axis) :=
    let a:=rhsH i z; let y:=rhPair i a (rhsH_law i z|>.1.symm); let q:=rhPair z a (rhsH_law i z|>.2.symm)
    vault k v p y y * pulse k v p q q
private lemma rho_lives (hk : 0<k) (v : Train j) {p} (hp : p∈baseCube) (he : p≠0) : Train.rho k v p≠0 := by
    have h := scaleR_live 1 k hk v (base_subset_realCube zone_pos hp) he; simpa [scaleR] using h
private lemma north_lives (hk : 0<k) (v : Train j) {p} (hp : p∈baseCube) (he : p≠0) (i z : Axis) :
    north v k p i z = v.levelD k i p / v.levelD k z p := by
  have hr := rhsH_law i z; have hj := base_subset_realCube zone_pos hp; unfold north; dsimp only
  rw [(dual_books hk v hp he _ _ hr.2.symm).2,(dual_books hk v hp he _ _ hr.1.symm).1,(dual_books hk v hp he _ _ hr.2.symm).1]
  have hu (j) := Train.D_live k hk v hj he j; have hv:= rho_lives hk v hp he
  field_simp [hu]
lemma tip_lives (hk : 0<k) (v : Train j) {p} (hp : p∈baseCube) (he : p≠0) (i z : Axis) (h : i≠z) :
    (v.levelD k i p)⁻¹=∑ j : Axis, jewel 1 p j * north v k p z j * pulse k v p (rhPair i z h) (rhPair i z h) := by
  have hv := base_subset_realCube zone_pos hp
  have hj (j) := Train.D_live _ hk v hv he j
  simp_rw [← Finset.sum_mul, north_lives hk v hp he, (dual_books hk v hp he _ _ h).2,(dual_books hk v hp he _ _ h).1]
  rw [show ∑ j : Axis,jewel 1 p j * (v.levelD k z p / v.levelD k j p)= v.rho k p * v.levelD k z p from (by
    unfold Train.rho; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _=> by ring)]
  field_simp [hj,rho_lives hk v hp he]

structure Ripple (a b : ℂ) (c δ : ℝ) : Prop where
  up : ‖a‖ ≤ c
  down : ‖b‖ ≤ c
  both : ‖a-b‖ ≤ c*δ
namespace Ripple
variable {a b d e : ℂ} {σ τ δ δ' : ℝ}
lemma bright (h : Ripple a b σ δ) : 0 ≤ σ := (norm_nonneg _).trans h.up
lemma mul (h : Ripple a b σ δ) (g : Ripple d e τ δ) : Ripple (a*d) (b*e) (2*(σ*τ)) δ := by
  have hx := mul_nonneg h.bright g.bright
  have hm : σ*τ ≤ 2*(σ*τ) := by linarith
  refine ⟨norm_mul .. |>.trans_le ((mul_le_mul h.up g.up (norm_nonneg _) h.bright).trans hm),
      norm_mul .. |>.trans_le ((mul_le_mul h.down g.down (norm_nonneg _) h.bright).trans hm),?_⟩
  rw [show a*d - b*e = (a-b)*d + b*(d-e) by ring]
  apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact (add_le_add (mul_le_mul h.both g.up (norm_nonneg _) ((norm_nonneg _).trans h.both))
    (mul_le_mul h.down g.both (norm_nonneg _) h.bright)).trans_eq (by ring)
lemma add (h : Ripple a b σ δ) (g : Ripple d e τ δ) : Ripple (a+d) (b+e) (σ+τ) δ := by
  refine ⟨(norm_add_le ..).trans (add_le_add h.up g.up),(norm_add_le ..).trans (add_le_add h.down g.down),?_⟩
  rw [show a+d-(b+e)=a-b+(d-e) by ring]; exact (norm_add_le ..).trans ((add_le_add h.both g.both).trans_eq (add_mul ..).symm)
lemma self (h : 0≤δ) (ha : ‖a‖ ≤ σ) : Ripple a a σ δ := ⟨ha,ha,by rw [sub_self,norm_zero]; exact mul_nonneg ((norm_nonneg _).trans ha) h⟩
lemma swap_pair (h : Ripple a b σ δ) : Ripple b a σ δ := ⟨h.down,h.up,by rw [norm_sub_rev];exact h.both⟩
lemma tack (h : Ripple a b σ δ) (g : σ ≤ τ) (hp : 0 ≤ δ) : Ripple a b τ δ :=
    ⟨h.up.trans g, h.down.trans g,h.both.trans (mul_le_mul_of_nonneg_right g hp)⟩
lemma sum {ι : Type*} {a b : ι→ℂ} {w : ι→ℝ} (I : Finset ι) (h : ∀ i∈I, Ripple (a i) (b i) (w i) δ) :
    Ripple (∑ i∈I, a i) (∑ i∈I,b i) (∑ i∈I,w i) δ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨by simp,by simp,by simp⟩
  | insert i I ht IH=> simp_rw [Finset.sum_insert ht]; exact (h i (Finset.mem_insert_self ..)).add (IH fun j hj => h j (Finset.mem_insert_of_mem hj))
end Ripple

lemma fountain_move {σ X η C : ℝ} (hk : 0<k) (hj : 4≤j) (hη : 0<η) (hF : Frost k j σ η C)
    (hX : 0≤X) (v w : Train j) (hx : (minusRows (hessian (pink k v)) (hessian (pink k w))).strip σ X)
    {p} (hp : p∈baseCube) (i t : TypeFace 2) :
    Ripple (pulse k v p i t) (pulse k w p i t) C X ∧ Ripple (vault k v p i t) (vault k w p i t) C X := by
  rw [← (heart_see hk hj v hp).1, ← (heart_see hk hj w hp).1, ← (heart_see hk hj v hp).2, ← (heart_see hk hj w hp).2]
  have hh:= hF.lift X v w hX hx
  have hu {A B : Row (TypeFace 2) (TypeFace 2)} (ha : A.strip η C) (hb : B.strip η C) (hv : (minusRows A B).strip η (X*C)) : Ripple (A.read p i t) (B.read p i t) C X := by
    refine ⟨frost_read hp.1 hη ha i t,frost_read hp.1 hη hb i t,?_⟩
    rw [← Matrix.sub_apply,← read_less (Whole.safe ⟨_,_,hη,ha⟩) (Whole.safe ⟨_,_,hη,hb⟩) hp.1,mul_comm]; exact frost_read hp.1 hη hv i t
  exact ⟨hu (hF.hue v).1 (hF.hue w).1 hh.1,hu (hF.hue v).2 (hF.hue w).2 hh.2⟩

lemma inv_stream {σ η C : ℝ} (hk : 0<k) (hj : 4≤j) (hη : 0<η) (hC : 0 ≤ C) (hF : Frost k j σ η C) :
    ∃ B>0, ∀ X:ℝ, ∀ v w : Train j, 0 ≤ X → (minusRows (hessian (pink k v)) (hessian (pink k w))).strip σ X →
      ∀ p∈baseCube, p≠0 → ∀ i : Axis, Ripple ((v.levelD k i p)⁻¹) ((w.levelD k i p)⁻¹) (B*‖p‖^2) X := by
  let A:= 2*C^2
  let B:=4*(2*(2*(meter.high^2*A)*C)); have hb : 0≤B:= by unfold B A; positivity
  refine ⟨B+1,by linarith,fun X v w hX hx p hp he i=>?_⟩
  let z:=rhsH i i; have ht : i≠z:= (rhsH_law i i|>.1).symm
  rw [tip_lives hk v hp he i z ht, tip_lives hk w hp he i z ht]
  have hv (i j : TypeFace 2) := fountain_move hk hj hη hF hX v w hx hp i j
  let f:=rhPair i z ht
  have hh (a : Axis) : Ripple (north v k p z a) (north w k p z a) A X := by
    unfold A north; dsimp only; rw [pow_two]; exact ((hv _ _).2).mul ((hv _ _).1)
  refine (Ripple.sum Finset.univ (fun i _=> ((Ripple.self hX (jewel_charge hp i)).mul (hh i)).mul ((hv f f).1))).tack ?_ hX
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (by linarith : B ≤ B+1) (by positivity)); apply le_of_eq; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,Axis]; unfold B; push_cast; ring

structure Creek (k : ℝ) (j : ℕ) (σ C : ℝ) : Prop where
  req (X : ℝ) (v w : Train j) : 0 ≤ X → (minusRows (hessian (pink k v)) (hessian (pink k w))).strip σ X → ∀ p∈baseCube, p≠0 →
      ∀ i, Ripple (Train.levelD k v i p) (Train.levelD k w i p) (C/ ‖p‖^2) X ∧
        Ripple ((v.levelD k i p)⁻¹) ((w.levelD k i p)⁻¹) (C*‖p‖^2) X

lemma furnish {σ : ℝ} (hk : 0<k) (hj : 4 ≤ j) (hs : 0<σ) : ∃ C>0, Creek k j σ C := by
  obtain ⟨η,C,hη,hC,F⟩ := possible_frost hk hj hs
  obtain ⟨A,hA,N⟩ := inv_stream hk hj hη hC F
  obtain ⟨B,hB,P⟩ := full_coin hk hj
  let R:=max (max A B) (A*(B*B))
  have ht : A ≤ R := (le_max_left ..).trans (le_max_left ..); have hh:B ≤ R := (le_max_right ..).trans (le_max_left ..)
  refine ⟨R,hA.trans_le ht,⟨fun X v w hX hx p hp he i=> ?_⟩⟩
  let y:=v.levelD k i p; let z:=w.levelD k i p; let l:= ‖p‖^2
  have hy : y≠0 := Train.D_live k hk v (base_subset_realCube zone_pos hp) he _; have hz : z≠0 := Train.D_live k hk w (base_subset_realCube zone_pos hp) he _
  have iu := (P v i _ hp he).1; have iv := (P w i _ hp he).1
  have hL : 0 < l:= pow_pos (norm_pos_iff.mpr he) _; have hM := div_le_div_of_nonneg_right hh hL.le
  have hk:= N X v w hX hx p hp he i
  refine ⟨⟨iu.trans hM,iv.trans hM,?_⟩,hk.tack (mul_le_mul_of_nonneg_right ht hL.le) hX⟩
  change ‖y-z‖ ≤ _
  calc
    _ = ‖z⁻¹-y⁻¹‖* ‖y‖*‖z‖ := by rw [← norm_mul,← norm_mul]; congr 1; field_simp
    _ ≤ A*l*X*(B/l)*(B/l):= mul_le_mul (mul_le_mul hk.swap_pair.both iu (norm_nonneg _) ((norm_nonneg _).trans hk.both)) iv (norm_nonneg _) (by positivity)
    _ = A*(B*B)/l*X := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right ..) hL.le) hX
end YM.RG08.Drift
