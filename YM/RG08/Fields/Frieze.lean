import YM.RG08.Fields.Parch

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators
variable {j : ℕ} {k σ : ℝ}

lemma scaleD_L (hk : 0<k) (hj : 4 ≤ j) (S : Side) : ∃ C>0, ∀ (v : Train j) p, p ∈ baseCube → p ≠ 0 →
    ‖(scaleR S k v p)⁻¹‖ ≤ C*rim p^4 := by
  obtain ⟨s,c,hs,hc,H⟩ := Train.bend_firm k hk hj (id : Train j → _)
  let b : ℝ := (S.val:ℝ)^4 * meter.low^4 * c
  have ht := meter.low_pos; have hb : 0 < b := by unfold b; positivity
  refine ⟨b⁻¹, inv_pos.mpr hb,fun v p hp h=> ?_⟩
  have he : 0<‖p‖ := norm_pos_iff.mpr h
  have hx := base_subset_realCube zone_pos hp
  have hf : meter.low^2*‖p‖^2 ≤ ‖divisor v.mass p‖ := ((mul_le_mul_of_nonneg_left (lengthSnap p) (by positivity)).trans
      (divisor_real_bounds v.mass hx).1).trans (Complex.re_le_norm ..)
  have hg := (H v p (base_subset_realCube hs hp)).trans_eq (by rfl); rw [mul_one] at hg
  have hm : b*‖p‖^4 ≤ ‖scaleR S k v p‖ := by
    unfold scaleR; rw [Train.recover_rho _ hk v hx h]; simp only [norm_mul,norm_pow,Complex.norm_natCast]
    exact le_trans (le_of_eq (by unfold b; ring : _= (S.val:ℝ)^4*((meter.low^2*‖p‖^2)^2*c))) (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (by positivity) hf _) hg hc.le (by positivity)) (by positivity))
  rw [norm_inv]
  refine ((inv_le_inv₀ ((mul_pos hb (pow_pos he 4)).trans_le hm) (mul_pos hb (pow_pos he 4))).2 hm).trans ?_
  rw [_root_.mul_inv,← inv_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_max_right ..) 4) (by positivity)

/-- Select flights varying train at fixed patch. -/
def flutter {i t} (S : Flight i t) (v : Train i) : Flight i t := {S with wing:=v}
lemma stake_near (hk : 0<k) {i t} (P : Flight i t) : ∃ c:ℝ, 0<c ∧ ∀ (V : Train i) p,p∈baseCube → p≠0 →
    c ≤ ‖Flight.tabE k (flutter P V) p‖ := by
  let S:=P.L; let I (_:Unit):= P
  obtain ⟨Z,hZ,F⟩:= full_coin hk P.legal
  obtain ⟨t,c,ht,hc,H⟩:= Flight.bills_firm I
  let B:=(S.val:ℝ)^2*(Z*domainRadius^2)
  have hp := domainRadius_pos; have hB : 0<B := by unfold B; positivity
  refine ⟨c^2*B⁻¹,by positivity,fun V p hv he=> ?_⟩
  let X:= flutter P V
  let q (l : Site P.L):=aliasAt p l
  have hq (l) := alias_base hv l P.odd
  have hy (l : Site P.L) := alias_regular (P:=P) (base_subset_realCube zone_pos hv) l (Or.inr he)
  let Y (l : Site P.L):= yen (massFilter P.patch) (q l)
  have hz (l) : Y l= massFilter P.patch (q l)* star (massFilter P.patch (q l)) := by
    unfold Y yen massFilter; rw [star_pow,Train.area_conj,show star (q l)=q l from (hq l).1]
  have hu l : Silver (Y l) := by rw [hz]; exact Silver.gram _
  have hw (l) : Silver (X.total k (q l)) := Silver.sum _ _ (fun i _ => ((Silver.side S|>.pow 2).inv).mul (Train.D_cost k hk V i (hq l).1))
  have hk' (l : Site P.L) : Silver (Y l*X.total k (q l)) := (hu l).mul (hw l)
  let D:= scaleD S k V (q 0)
  have hx (l): Silver (D l) := ((Silver.side S|>.pow 2).inv).mul (Train.D_cost k hk V _ (hq 0).1)
  have hm : 0< (D 0).re := (hx 0).re_ne (scaleD_live _ k hk V (hy 0).1 (hy 0).2 _)
  have h1 : c^2 ≤ (Y 0).re := by
    have hx:= (mul_one c).symm.trans_le (H () _ (base_subset_realCube ht hv))
    rw [← (hu _).norm,hz,norm_mul,norm_star,← pow_two]; exact pow_le_pow_left₀ hc.le hx _
  have h2 : ‖(D 0)⁻¹‖ ≤ B := by
    have h:= F V 0 _ (hq 0) (hy 0).2
    unfold B D scaleD; rw [_root_.mul_inv_rev,inv_inv,norm_mul,norm_pow,Complex.norm_natCast,mul_comm]
    exact mul_le_mul_of_nonneg_left (h.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (pineNorm (hq 0)) _) hZ.le)) (by positivity)
  rw [norm_inv,(hx 0).norm] at h2
  have h3 : B⁻¹ ≤ (X.total k (q 0)).re := by
    apply le_trans _ (show (D 0).re ≤ _ from by unfold Flight.total; rw [Complex.re_sum]; exact Finset.single_le_sum (f:=fun i:Axis=> (D i).re) (fun i _ => (hx i).re_nonneg) (Finset.mem_univ 0))
    rw [← inv_inv ((D 0).re)]
    exact (inv_le_inv₀ hB (inv_pos.mpr hm)).mpr h2
  change _ ≤ ‖∑ l : Site P.L,Y l*X.total k (q l)‖
  rw [(Silver.sum _ _ (fun i _=> hk' i)).norm, Complex.re_sum]
  apply le_trans _ (Finset.single_le_sum (f:=fun l=> (Y l * Flight.total k X (q l)).re) (fun l _ => (hk' l).re_nonneg) (Finset.mem_univ 0))
  rw [(hu 0).real_mul]; exact mul_le_mul h1 h3 (by positivity) (hu _).re_nonneg

section Tickets
variable {I : Type*} {p w : I→Momentum} {u v : I → Train j} {Z : I→ℝ}
variable (hk : 0<k) (hj : 4 ≤ j) (hs : 0<σ) (hZ : ∀ i,0≤Z i) (hp : ∀ i, p i∈baseCube) (he : ∀ i,p i≠0)
    (hh : ∀ i, (minusRows (hessian (pink k (u i))) (hessian (pink k (v i)))).strip σ (Z i))
    (ht : ∃ L:ℝ, 0≤L ∧ ∀ i,rim (p i) ≤ L*rim (w i))
include hk hj hs hZ hp he hh ht
lemma couloir (S : Side) (a : Axis) : Wave Z w 2 (fun i=> scaleD S k (u i) (p i) a) (fun i=> scaleD S k (v i) (p i) a) := by
  obtain ⟨C,hC,H⟩ := furnish hk hj hs
  apply (Wave.constant hZ _).times (u:=0) (v:=2)
  refine Wave.punctured hZ hC.le (fun i=> ?_) ht
  have hx := (H.req _ _ _ (hZ i) (hh i) _ (hp i) (he i) a).1
  refine hx.tack ?_ (hZ i)
  rw [div_eq_mul_inv,← inv_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_max_right ..) _) hC.le
omit ht
lemma debit (a : Axis) : Wave Z w 0 (fun i=> ((u i).levelD k a (p i))⁻¹) (fun i=> ((v i).levelD k a (p i))⁻¹) := by
  obtain ⟨C,hC,H⟩ := furnish hk hj hs
  exact ⟨C*domainRadius^2,by positivity,fun i=> (H.req _ _ _ (hZ i) (hh i) _ (hp i) (he i) a).2.tack
    (by rw [pow_zero,mul_one]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (pineNorm (hp i)) _) hC.le) (hZ i)⟩
lemma dome (S : Side) : Beam Z w 0 (fun i => fieldI S k (u i) (p i)) (fun i=> fieldI S k (v i) (p i)) := by
  apply Beam.mask_one_w hZ; intro a; simp only [scaleD,_root_.mul_inv_rev,inv_inv]
  exact ((debit (w:=w) hk hj hs hZ hp he hh a).times (Wave.constant hZ _))
lemma roof (S : Side) : Wave Z w 0 (fun i=> scaleR S k (u i) (p i)) (fun i=>scaleR S k (v i) (p i)) := by
  have hb (i : Axis) : Continuous fun p => jewel 1 p i := by simp_rw [jewel_one,chip]; fun_prop
  have hy (j : Axis) := ((Wave.intermittent (w:=w) hZ p (fun x=> jewel 1 x j) hp (hb j)).times (debit hk hj hs hZ hp he hh j))
  apply (Wave.constant hZ _).times (v:=0)
  unfold Train.rho
  simp_rw [div_eq_mul_inv]; exact Wave.collect hZ hy
omit he
lemma glacier_t : Beam Z w 0 (fun i=> pulse k (u i) (p i)) (fun i=> pulse k (v i) (p i)) := by
  obtain ⟨η,C,hη,hC,F⟩ := possible_frost hk hj hs
  refine fun a b=> ⟨C,hC,fun i=>?_⟩; rw [pow_zero,mul_one]; exact (fountain_move hk hj hη F (hZ i) _ _ (hh i) (hp i) a b).1
include he ht
lemma tides (S : Side) : Wave Z w 8 (fun i=> (scaleR S k (u i) (p i))⁻¹) (fun i=> (scaleR S k (v i) (p i))⁻¹) := by
  obtain ⟨L,hL,K⟩:=ht; obtain ⟨c,hc,F⟩:=scaleD_L hk hj S
  refine Wave.invert (b:=4) (u:=0) (roof hk hj hs hZ hp he hh _) (fun i=> scaleR_live _ k hk _ (base_subset_realCube zone_pos (hp i)) (he i))
    (fun i=> scaleR_live _ k hk _ (base_subset_realCube zone_pos (hp i)) (he i)) ⟨c*(L^4),by positivity,fun i=>?_⟩
  have hv (v : Train j) : ‖(scaleR S k v (p i))⁻¹‖ ≤ c*L^4 * rim (w i)^4:= by
    rw [mul_assoc, ← mul_pow]; exact (F v _ (hp i) (he i)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (rim_live _).le (K i) _) hc.le)
  exact ⟨hv _,hv _⟩
lemma fll (S : Side) : Beam Z w 2 (fun i=> fieldD S k (u i) (p i)) (fun i=> fieldD S k (v i) (p i)) := Beam.mask_one_w hZ (couloir hk hj hs hZ hp he hh ht S)

omit hh hk hj hs he ht
lemma mass_up (S : Patch) : Wave Z w 0 (fun i=> massFilter S (p i)) (fun i=> massFilter S (p i)) ∧
    Wave Z w 0 (fun i=> massFilter S (-p i)) (fun i=> massFilter S (-p i)) := by
  have hc : Continuous (massFilter S) := by unfold massFilter; exact (Train.area_diff _).continuous.pow _
  exact ⟨Wave.intermittent hZ p _ hp hc,Wave.intermittent hZ p (fun p=> massFilter S (-p)) hp (hc.comp continuous_neg)⟩
lemma sun (S : Side) (a : ℕ) : Beam Z w 0 (fun i=> signal S a (p i)) (fun i=>signal S a (p i)) ∧
    Beam Z w 0 (fun i=> mirage S a (p i)) (fun i=> mirage S a (p i)) := by
  have hh (i t) : Continuous (fun p=> signal S a p i t) := by simp only [signal,tripQ,wedge,Matrix.sum_apply,Matrix.smul_apply]; unfold chip; fun_prop
  exact ⟨fun i j=> Wave.intermittent hZ p _ hp (hh i j), fun i j=> Wave.intermittent hZ p _ hp ((hh j i).comp continuous_neg)⟩
lemma flowP {i t} (S : Flight i t) (a : ℕ) : Beam Z w 0 (fun i=> flux S a (p i)) (fun i => flux S a (p i)) := by
  have hh : Continuous (massFilter S.patch) := by unfold massFilter; exact (Train.area_diff _).continuous.pow _
  have ht (i j) : Continuous (fun p=> hinges S a p i j) := by
    simp only [hinges,Matrix.smul_apply]; refine hh.smul ?_
    unfold mask; simp only [Matrix.diagonal_apply]; split
    · unfold inventory rail twirl; fun_prop
    exact continuous_const
  exact fun i j=> Wave.intermittent hZ p _ hp ((ht j i).comp continuous_neg)

end Tickets
end YM.RG08.Drift
