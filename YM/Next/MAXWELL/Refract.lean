import YM.Next.MAXWELL.Canopy
import YM.Next.MAXWELL.Leading

/-!
# Extract the polarized vector test

Only the −5 triangular residue. Get `monoT` logically via
all positions and uncontracted Sheet detection, not any choice of inverse
for the 10 covariance. Then symmetry *itself* gives linearity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j l d : ℕ}

section Cluster
variable (c : G.ColorIndex) {x y : ℝ → E4} {u z : E4}

lemma tri_panel (hx : Tendsto x little (𝓝 0)) (hy : Tendsto y little (𝓝 0))
    (hz : z≠0) (he : u≠0) (hh : ∀ (t : ℝ), x t-y t=t • u)
    (D : Panels 0 1) (p q : Flavor 0) (X : Sheet 0) (hX : ∀ p, fare c p q (0-z)=p X) :
    Tendsto (fun t : ℝ => (↑(t^5):ℂ)*triangle G (x t) (y t) z (canopy G 0 1 D) (team G p p) (team G q q)) little
      (𝓝 (↑((G.lieDim:ℝ)*4*fare c (D X) p u*p X):ℂ)) := by
  let B := Module.finBasis ℝ (Sheet 0)
  let J t (u) := (triangle G (x t) (y t) z u (team G p p) (team G q q))
  let C' := (G.lieDim:ℝ)*4
  have hr : Tendsto (fun t : ℝ => ∑ i, (↑(t^5):ℂ)* J t (team G (B.coord i) (D (B i)))) little
      (𝓝 (∑ i, (↑(C'*(fare c (B.coord i) q (0-z) * fare c (D (B i)) p u)*fare c p q (0-z)):ℂ))) :=
    tendsto_finsetSum _ fun i _ => tri_path c hx hy hz he hh _ _ _ _
  rw [show canopy G 0 1 D=∑ i,team G (B.coord i) (D (B i)) from rfl]
  simp only [map_sum,LinearMap.sum_apply,Finset.mul_sum]
  have ht (L : Sheet 0) : fare c (D L) p u = ∑ i, B.coord i L*fare c (D (B i)) p u := by
    conv_lhs => rw [← B.sum_repr L]
    rw [← fare_pair _ _ _ he]; simp only [map_sum,map_smul,LinearMap.sum_apply];
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [ht]; simp_rw [hX] at hr
  simp only [Finset.mul_sum, Finset.sum_mul,← mul_assoc,Complex.ofReal_sum]
  simp only [← mul_assoc] at hr; exact hr

include c
lemma tri_panel_far (hx : Tendsto x little (𝓝 0)) (hy : Tendsto y little (𝓝 0))
    (hz : z≠0) (he : u≠0) (hh : ∀ (t : ℝ), x t-y t=t • u)
    (D : Panels 0 1) (p q : Flavor 0) :
    Tendsto (fun t : ℝ => (↑(t^5):ℂ)*triangle G z (x t) (y t) (canopy G 0 1 D) (team G p p) (team G q q)) little
      (𝓝 0) := by
  let B := Module.finBasis ℝ (Sheet 0)
  rw [show canopy G 0 1 D=∑ i,team G (B.coord i) (D (B i)) from rfl]
  simp only [map_sum,LinearMap.sum_apply,Finset.mul_sum]
  have ht := tendsto_finsetSum (f:=fun i t => _) Finset.univ (fun i _ => tri_path_far c hx hy hz he hh (B.coord i) (D (B i)) p q)
  rwa [Finset.sum_const_zero] at ht

lemma tri_focus {T : Module.End ℂ (WickPol G)} {D : Flavor 0 → Panels 0 1} (H : silence G d T)
    (hd : 4≤d) (ht : ∀ x, canopy G 0 1 (D x)=T (team G x x)) (p q : Flavor 0) {u : E4} (hu : u≠0) (X : Sheet 0) :
    fare c (D p X) q u * q X = fare c (D q X) p u * p X := by
  let x := fun t : ℝ => t • u
  let y := fun _ : ℝ => (0:E4)
  let z := basis timeAxis
  have hx : Tendsto x little (𝓝 0) := by
    have hh := tendsto_id (x:=𝓝 (0:ℝ))
    unfold x; simpa only [id_eq,little,zero_smul] using (hh.smul_const u).mono_left nhdsWithin_le_nhds
  have hy : Tendsto y little (𝓝 0) := tendsto_const_nhds
  have hz : z≠0 := (norm_ne_zero_iff.mp (by simp [z]))
  have he t : x t-y t=t • u := sub_zero _
  have he' (t : ℝ) : y t-x t=t • (-u) := by rw [← neg_sub (x t), he,smul_neg]
  obtain ⟨w,hw⟩ := point_fares c X (sub_ne_zero.mpr (Ne.symm hz))
  let A b := team G (b:Flavor 0) b
  let f t := triangle G (x t) (y t) z (T (A p)) (A q) (A w) + triangle G (y t) (x t) z (T (A q)) (A p) (A w) +
    triangle G z (y t) (x t) (T (A w)) (A q) (A p)
  have hr := ((tri_panel c hx hy hz hu he (D p) q w X hw).add
    (tri_panel c hy hx hz (neg_ne_zero.mpr hu) he' (D q) p w X hw)).add
      (tri_panel_far (G:=G) c hy hx hz (neg_ne_zero.mpr hu) he' (D w) q p)
  simp only [ht,← mul_add,fare_sign c _ _ hu,add_zero] at hr
  have hs : Tendsto (fun t : ℝ => (↑(t^5):ℂ)*f t) little (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hx.eventually (isOpen_ne.mem_nhds (show (0:E4)≠z from hz.symm)), self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ha ho
    have Ho := tri_ok (y:=y t) (smul_ne_zero (show t ≠ 0 from (show 0<t from ho).ne') hu) ha hz.symm
    have hb := triangle_stat Ho H (team_label (G:=G) p p hd) (team_label (G:=G) q q hd) (team_label (G:=G) w w hd)
    rw [tri_around Ho (team G p p) (T (team G q q)), tri_switch Ho (team G p p) (team G q q)] at hb
    rw [show f t = 0 from hb,mul_zero]
  have hv := tendsto_nhds_unique hr hs
  let k := (G.lieDim:ℝ)*4
  have hK : k ≠ 0 := by
    have hh : 0<G.lieDim := lt_of_le_of_lt (Nat.zero_le _) c.isLt
    dsimp [k]; positivity
  have hm := Complex.ofReal_inj.mp ((Complex.ofReal_add ..).trans (hv.trans Complex.ofReal_zero.symm))
  change k*_ * q X + k* -fare c (D q X) p u * p X = 0 at hm
  rw [mul_neg, neg_mul, ← sub_eq_add_neg, mul_assoc,mul_assoc,sub_eq_zero] at hm
  apply mul_left_cancel₀ hK; simpa only [k,mul_assoc] using hm
end Cluster

section receipt
variable {T : Module.End ℂ (WickPol G)}
variable (c : G.ColorIndex) (H : silence G d T) (hd : 4≤d)

private lemma witness (a : Flavor 0) (h : a≠0) : ∃ x : Sheet 0,a x ≠ 0 := by
  by_contra! ht; exact h (LinearMap.ext ht)
private lemma dual_witness (x : Sheet 0) (hx : x≠0) : ∃ a : Flavor 0,a x ≠ 0 := by
  by_contra! ht; exact hx (flavor_ext fun u i l => by rw [ht,map_zero])

include H hd c
lemma tri_takes (D : Flavor 0 → Panels 0 1) (hD : ∀ x, canopy G 0 1 (D x)=T (team G x x)) (a : Flavor 0) (ha : a≠0) :
    ∃ b : Flavor 1,D a=monoT a b := by
  obtain ⟨x,hx⟩ := witness a ha
  let f := D a
  have he (X : Sheet 0) (ht : a X=0) : f X=0 := by
    by_cases hw:X=0
    · rw [hw,map_zero]
    apply ranging c (f X) 0; intro z hz p
    have hp (p : Flavor 0) (h : p X ≠ 0) : fare c (f X) p z = 0 :=
      (mul_eq_zero.mp ((tri_focus c H hd hD a p hz X).trans (by rw [ht,mul_zero]))).resolve_right h
    by_cases hh : p X = 0
    · obtain ⟨q,hq⟩ := dual_witness X hw
      have hk := hp (p+q) (by rwa [LinearMap.add_apply,hh,zero_add])
      rw [← fare_pair c _ _ hz,map_add,fare_pair,fare_pair, hp q hq,add_zero] at hk; exact hk
    exact hp _ hh
  refine ⟨(a x)⁻¹ • f x, LinearMap.ext fun u => ?_⟩
  let r := a u*(a x)⁻¹
  have ht := he (u-r • x) (by rw [map_sub,map_smul, smul_eq_mul,sub_eq_zero]; unfold r; field_simp)
  rw [map_sub,map_smul,sub_eq_zero] at ht
  change f u = a u • ((a x)⁻¹ • _)
  rw [smul_smul]; exact ht

set_option maxHeartbeats 600000 in
lemma receives (hD : ∀ p : Flavor 0,∃ D : Panels 0 1, canopy G 0 1 D=T (team G p p)) :
    ∃ f : Flavor 0 →ₗ[ℝ] Flavor 1, (∀ p, T (team G p p)=team G p (f p)) ∧
      (∀ p q z, z≠0 → fare c (f p) q z=fare c (f q) p z) := by
  choose D ht using hD
  have hh (p : Flavor 0) : ∃ b : Flavor 1,D p=monoT p b ∧ (p=0→b=0) := by
    classical
    by_cases he : p=0
    · subst p
      refine ⟨0,canopy_faithful c (by decide) ?_,fun _ => rfl⟩
      rw [ht,shelter]; change T (duetL G 0 0 0 0)=duetL G 0 1 0 0; simp
    obtain ⟨b,h⟩ := tri_takes (G:=G) c H hd _ ht p he
    exact ⟨b,h,by simp [he]⟩
  choose f hf h0 using hh
  have hw (p q : Flavor 0) (z : E4) (hz : z≠0) : fare c (f p) q z=fare c (f q) p z := by
    by_cases he : p=0
    · subst p
      rw [h0 _ rfl,← fare_pair _ _ _ hz,← fare_pair _ _ _ hz]; simp
    by_cases hh : q=0
    · subst q
      rw [h0 _ rfl,← fare_pair _ _ _ hz,← fare_pair _ _ _ hz]; simp
    have hg : ∃ x, p x≠0 ∧ q x≠0 := by
      obtain ⟨x,hx⟩ := witness p he
      by_cases h : q x=0
      · obtain ⟨y,hy⟩ := witness q hh
        by_cases ht : p y=0
        · exact ⟨x+y,by simpa [ht],by simpa [h]⟩
        exact ⟨y,ht,hy⟩
      exact ⟨x,hx,h⟩
    obtain ⟨x,hx,hy⟩ := hg
    have hk := tri_focus c H hd ht p q hz x
    rw [hf,hf] at hk
    change fare c (p x • f p) q z*q x = fare c (q x • f q) p z*p x at hk
    rw [← fare_pair _ _ _ hz,← fare_pair _ _ _ hz,map_smul,map_smul,LinearMap.smul_apply,LinearMap.smul_apply,fare_pair,fare_pair,smul_eq_mul,smul_eq_mul] at hk
    apply mul_right_cancel₀ hy; apply mul_left_cancel₀ hx; convert hk using 1 <;> ring
  refine ⟨{ toFun := f, map_add' p q := ?_, map_smul' a p := ?_ },?_,hw⟩
  · apply sub_eq_zero.mp; apply ranging c _ 0; intro z hz t
    rw [← fare_pair _ _ _ hz,map_sub,LinearMap.sub_apply,map_add,LinearMap.add_apply,fare_pair,fare_pair,fare_pair,
      hw _ _ _ hz,hw p t _ hz,hw q t _ hz,← fare_pair _ _ _ hz,map_add,fare_pair,fare_pair,sub_self]
  · apply sub_eq_zero.mp; apply ranging c _ 0; intro z hz t
    rw [← fare_pair _ _ _ hz,map_sub,LinearMap.sub_apply,map_smul, LinearMap.smul_apply, fare_pair,fare_pair,hw _ _ _ hz,hw p t _ hz,
      ← fare_pair _ _ _ hz,map_smul,fare_pair]; exact sub_self _
  intro p; rw [← ht,hf,shelter]; rfl
end receipt
end YM.Maxwell.Free
