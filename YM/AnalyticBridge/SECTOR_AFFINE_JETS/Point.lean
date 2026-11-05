import YM.AnalyticBridge.SECTOR_AFFINE_JETS.MarkedGram

/-!
# Column budget for applying the inverse (e.g. to the affine shift)

Here jets can include clipping **extensions**, so only claim through
k. `Point` only requires rowwise external-mark cost at one location,
compatible with `Polar` on matrices in the sector. It will suffice even
for shift results integrated over Haar-valued Y. These are not growth
bounds on entire affine vectors in a Frobenius norm.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset

open Filter Function Lattice Wilson RG Precision Pressure Tree
open YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD
open YM.Push.Uniform (Allows bolt composeCost Requests)
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}
variable {n k : ℕ} {C M K σ a s d t : ℝ}
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
section calculus
variable {f : E → F} {g : F → H} {x : E}
structure Through (n : ℕ) (f : E → F) (x : E) (C : ℝ) : Prop where
  smooth : ContDiffAt ℝ n f x
  pay i : i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ C

namespace Through
lemma control (h : Allows n f x C) : Through n f x C := ⟨h.analytic.of_le le_top, h.norm_le⟩
lemma nonneg (h : Through n f x C) : 0 ≤ C := (norm_nonneg _).trans (h.pay 0 (Nat.zero_le _))
lemma mono (h : Through n f x C) (hC : C ≤ M) : Through n f x M := ⟨h.smooth, fun i hi => (h.pay i hi).trans hC⟩
lemma germ {f' : E → F} (h : Through n f x C) (he : f =ᶠ[𝓝 x] f') : Through n f' x C := by
  refine ⟨h.smooth.congr_of_eventuallyEq he.symm,fun i hi => ?_⟩
  rw [← (he.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; exact h.pay i hi
lemma scale (h : Through n f x C) (t : ℝ) : Through n (fun z => t • f z) x (|t| *C) := by
  refine ⟨h.smooth.const_smul _, fun i hi => ?_⟩
  change ‖iteratedFDeriv ℝ i (t • f) _‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (smooth_of_le h.smooth hi),norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h.pay _ hi) (abs_nonneg _)

/-- Input scaled by normalized height. Gain one power from nonempty
list/order, don't require paying the zeroth input at all other field
arguments of f. -/
lemma contract (h : Through n f 0 C) (hs : 0 ≤ s) (hu : s ≤ 1)
    (hf : ‖f 0‖ ≤ M*t) (hb : C*s ≤ M*t) :
    Through n (fun z => f (s • z)) 0 (M*t) := by
  let L := s • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ s := by unfold L; rw [norm_smul, Real.norm_of_nonneg hs]; exact mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le
  have he : ContDiffAt ℝ n f (L 0) := by rw [L.map_zero]; exact h.smooth
  refine ⟨he.comp 0 L.contDiff.contDiffAt,fun i hi => ?_⟩
  by_cases hj : i=0
  · subst i; simpa only [norm_iteratedFDeriv_zero, smul_zero] using hf
  change ‖iteratedFDeriv ℝ i (f ∘ L) _‖ ≤ _
  rw [Push.Uniform.iter_lin_at (smooth_of_le he hi),L.map_zero]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (mul_le_mul (h.pay i hi) ((pow_le_pow_left₀ (norm_nonneg L) hL i).trans
    (show s^i ≤ s by simpa only [pow_one] using pow_le_pow_of_le_one hs hu (show 1 ≤ i by omega))) (pow_nonneg (norm_nonneg L) _) h.nonneg).trans hb

private lemma opens (h : ContDiffAt ℝ (↑n : ℕ∞ω) f x) : ∃ t, x∈t ∧ IsOpen t ∧ ContDiffOn ℝ n f t := by
  obtain ⟨u,hu,H⟩ := h.contDiffOn (m:=n) le_rfl (by simp)
  obtain ⟨v,hv,hv',hh⟩ := _root_.mem_nhds_iff.mp hu
  exact ⟨v,hh,hv',H.mono hv⟩
lemma comp (hg : Through n g (f x) K) (hf : Through n f x C) : Through n (fun u => g (f u)) x (composeCost n K C) := by
  have hs : ContDiffAt ℝ n (g ∘ f) x := hg.smooth.comp x hf.smooth
  refine ⟨hs, fun k hk => ?_⟩
  obtain ⟨t,ht,ht',H⟩ := opens hg.smooth
  obtain ⟨u,hu,hu',H'⟩ := opens hf.smooth
  obtain ⟨s,he,he',hm⟩ := _root_.mem_nhds_iff.mp (inter_mem (hu'.mem_nhds hu)
    (hf.smooth.continuousAt.preimage_mem_nhds (ht'.mem_nhds ht)))
  have hx : 1 ≤ 1+C := le_add_of_nonneg_right hf.nonneg
  change ‖iteratedFDeriv ℝ k (g ∘ f) _‖ ≤ _
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv he'.uniqueDiffOn (smooth_of_le hs hk) hm]
  apply le_trans (norm_iteratedFDerivWithin_comp_le H (H'.mono fun i hi => (he hi).1)
    (by exact_mod_cast hk) ht'.uniqueDiffOn he'.uniqueDiffOn (fun y hy => (he hy).2) hm (C:=K) (D:=1+C) ?_ ?_) ?_
  · intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv ht'.uniqueDiffOn (smooth_of_le hg.smooth (hi.trans hk)) ht]; exact hg.pay _ (hi.trans hk)
  · intro i hi hj
    rw [iteratedFDerivWithin_eq_iteratedFDeriv he'.uniqueDiffOn (smooth_of_le hf.smooth (hj.trans hk)) hm]
    exact (hf.pay _ (hj.trans hk)).trans (le_trans (le_add_of_nonneg_left zero_le_one) (le_self_pow₀ hx (by omega)))
  have hK := hg.nonneg
  unfold composeCost; gcongr
end Through
end calculus
section point
/-- External direction occurrences paid at a site. Used on normalized
coordinate parameters for the width estimates. -/
structure Point (B : PriceCoords G c) (p : Site c) (σ : ℝ) (n : ℕ) (u : PriceCoords G c → E) (C : ℝ) : Prop where
  smooth : ContDiffAt ℝ n u B
  bound (l : List (Coord G c)) : l.length ≤ n → (marks G c σ).pay l p * ‖jet bolt u l B‖ ≤ C

namespace Point
variable {B : PriceCoords G c} {p q : Site c} {u v : PriceCoords G c → E}

lemma nonneg (h : Point B p σ n u C) : 0 ≤ C := (mul_nonneg ((marks G c σ).pay_pos [] p).le (norm_nonneg _)).trans
  (h.bound [] (show ([] : List _).length ≤ n from Nat.zero_le _))
lemma mono (h : Point B p σ n u C) (hσ : s ≤ σ) (hC : C ≤ M) : Point B p s n u M :=
  ⟨h.smooth, fun l hl => le_trans (mul_le_mul_of_nonneg_right (marks_le _ hσ l _) (norm_nonneg _))
    ((h.bound l hl).trans hC)⟩
lemma germ (h : Point B p σ n u C) (he : u =ᶠ[𝓝 B] v) : Point B p σ n v C := by
  refine ⟨h.smooth.congr_of_eventuallyEq he.symm, fun l hl => ?_⟩
  rw [← identical _ he l]; exact h.bound l hl
lemma zero (hM : 0 ≤ M) : Point B p σ n (0 : PriceCoords G c → E) M := by
  refine ⟨contDiffAt_const, fun l hl => ?_⟩
  rw [FreeResolvent.Affine.zero_null,norm_zero,mul_zero]; exact hM
lemma scale (h : Point B p σ n u C) (w : ℝ) : Point B p σ n (fun y => w • u y) (|w| *C) := by
  let L := w • ContinuousLinearMap.id ℝ E
  refine ⟨h.smooth.const_smul w,fun l hl => ?_⟩
  change (marks G c σ).pay l p * ‖jet _ (fun y => L (u y)) l B‖ ≤ _
  rw [jet_linear _ _ L (smooth_of_le h.smooth hl), show L (jet bolt u l B)=w • _ from rfl]
  rw [norm_smul,Real.norm_eq_abs,mul_left_comm]; exact mul_le_mul_of_nonneg_left (h.bound l hl) (abs_nonneg _)
lemma add (h : Point B p σ n u C) (h' : Point B p σ n v M) : Point B p σ n (fun y => u y + v y) (C+M) := by
  refine ⟨h.smooth.add h'.smooth,fun l hl => ?_⟩
  rw [jet_add _ _ (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl)]
  have he := add_le_add (h.bound l hl) (h'.bound l hl); rw [← mul_add] at he
  exact (mul_le_mul_of_nonneg_left (norm_add_le ..) ((marks G c σ).pay_pos ..).le).trans he
lemma neg (h : Point B p σ n u C) : Point B p σ n (-u) C := by
  have he := h.scale (-1)
  simp only [neg_smul,one_smul,abs_neg,abs_one,one_mul] at he; exact he
lemma sub (h : Point B p σ n u C) (h' : Point B p σ n v M) : Point B p σ n (fun y => u y-v y) (C+M) := by
  change Point _ _ _ _ (u-v) _; rw [sub_eq_add_neg]; exact h.add h'.neg
lemma line {L : E →L[ℝ] F} (h : Point B p σ n u C) (hL : ‖L‖ ≤ M) :
    Point B p σ n (fun y => L (u y)) (M*C) := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth, fun l hl => ?_⟩
  rw [jet_linear _ _ L (smooth_of_le h.smooth hl)]
  have hx := mul_le_mul_of_nonneg_left (h.bound l hl) ((norm_nonneg L).trans hL); rw [mul_left_comm] at hx
  exact le_trans (mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) ((marks G c σ).pay_pos ..).le) hx
lemma color {w : PriceCoords G c → G.Color} (h : Point B p σ n w C) (i : G.ColorIndex) : Point B p σ n (fun y => (w y) i) C := by
  let L := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hl : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y => by
    rw [one_mul]; change |y i| ≤ _; rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ y i]
    simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) y)
  have he := h.line hl; rw [one_mul] at he; exact he
lemma multiply {v : PriceCoords G c → F} (J : E →L[ℝ] F →L[ℝ] H) (hJ : ‖J‖ ≤ K)
    (h : Point B p σ n u C) (h' : Point B p σ n v M) :
    Point B p σ n (fun y => J (u y) (v y)) ((2:ℝ)^n*(K*C*M)) := by
  refine ⟨smooth_product J h.smooth h'.smooth,fun l hl => ?_⟩
  rw [leibniz _ J _ (smooth_of_le h.smooth hl) (smooth_of_le h'.smooth hl)]
  have hc := h.nonneg; have hm := h'.nonneg; have hj := (norm_nonneg J).trans hJ
  apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) ((marks G c σ).pay_pos ..).le)
  rw [Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum (g:=fun _=>K*C*M) (fun i _ => ?_))
  · rw [Finset.sum_const,Finset.card_univ,FreeResolvent.TestD.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (by positivity)
  let x := jet bolt u (lo l i) B
  let y := jet bolt v (hi l i) B
  let L := marks G c σ
  calc L.pay l p * ‖J x y‖ ≤ L.pay l p * (K*‖x‖*‖y‖) := by
          refine mul_le_mul_of_nonneg_left ((J x).le_opNorm _ |>.trans ?_) (L.pay_pos ..).le
          exact mul_le_mul_of_nonneg_right ((J.le_opNorm x).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))) (norm_nonneg _)
       _ = K*(L.pay (lo l i) p * ‖x‖)*(L.pay (hi l i) p * ‖y‖) := by rw [L.pay_masks l i]; ring
       _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (h.bound _ ((len_low l i).trans hl)) hj)
          (h'.bound _ ((len_high l i).trans hl)) (mul_nonneg (L.pay_pos ..).le (norm_nonneg _)) (mul_nonneg hj hc)

lemma sum_price {ι : Type} (v : Finset ι) {f : ι → PriceCoords G c → E} (C : ι → ℝ)
    (hp : ∀ i∈v, Point B p σ n (f i) (C i)) : Point B p σ n (fun x => ∑ i ∈ v, f i x) (∑ i∈v, C i) := by
  refine ⟨ContDiffAt.sum (fun i hi => (hp i hi).smooth),fun l he => ?_⟩
  rw [jet_sum _ _ _ _ (fun i hi => smooth_of_le (hp i hi).smooth he)]
  have ha := (marks G c σ).pay_pos l p
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) ha.le).trans ?_
  rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i hi => (hp i hi).bound l he

lemma shift (h : Point B p σ n u C) (ho : separation q p ≤ k) (hσ : 0 ≤ σ) :
    Point B q σ n u (Real.exp (n*σ*k)*C) := by
  refine ⟨h.smooth,fun l hl => ?_⟩
  let L := marks G c σ
  have hv := (Mark.position_move (native c) (coordRoot (G:=G)) hσ).transfer zero_le_one l q p
  rw [one_pow,one_mul] at hv
  have hx : L.pay l q ≤ Real.exp (n*σ*k)*L.pay l p := hv.trans (mul_le_mul_of_nonneg_right ?_ (L.pay_pos ..).le)
  rotate_left
  · apply Real.exp_monotone
    refine mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hσ) ?_ ((native c).nonneg ..) (by positivity)
    change (separation q p:ℝ) ≤ _; exact_mod_cast ho
  apply (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans; rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.bound l hl) (Real.exp_pos _).le

lemma of_support (h : Through n u B C) {R : ℕ} (ht : Requests Set.univ u coordRoot p R) (hσ : 0 ≤ σ) :
    Point B p σ n u (Real.exp (n*σ*R)*C) := by
  refine ⟨h.smooth, fun l hl => ?_⟩
  by_cases he : jet bolt u l B=0
  · rw [he,norm_zero,mul_zero]; exact mul_nonneg (Real.exp_pos _).le h.nonneg
  have hz (i : Coord G c) (hx : i∈l) : (native c).d p (coordRoot i) ≤ R := by
    change ((separation p _):ℝ) ≤ _
    obtain ⟨j,rfl⟩ := List.get_of_mem hx
    have hv : separation p (coordRoot (l.get j)) ≤ R := by
      by_contra hy
      exact he (ht.zero (Filter.univ_mem) (smooth_of_le h.smooth hl) l.get j hy)
    exact_mod_cast hv
  have hf : ‖jet bolt u l B‖ ≤ C :=
    (Push.Uniform.entry_bound (p:=B) (f:=u) l.get).trans (h.pay l.length hl)
  have ha := FreeResolvent.Affine.plumb (native c) p coordRoot l hσ (R:ℝ) hz
  refine mul_le_mul (ha.trans (Real.exp_monotone ?_)) hf (norm_nonneg _) (Real.exp_pos _).le
  gcongr
end Point
end point
end YM.AnalyticBridge.SectorAffine.Offset
