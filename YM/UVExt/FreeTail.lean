import YM.UVExt.FreeTailBounds
import YM.Next.FREE_KERNELS.Rack

/-! At the fixed physical period full-cutoff convergence of the cumulative diagonal symbol and
other associated kinetic data. This is a linear-stack consequence, not claiming that matching
absolute estimates alone control differences of labelled nonlinear interactions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG
open scoped Topology BigOperators ComplexConjugate

namespace UV
lemma slide_sub (P : Patch) (a : Axis) (f g : Momentum → ℂ) (p : Momentum) :
    slide P a f p - slide P a g p = slide P a (f-g) p := by
  have he := Train.bound_shuttle P a f g (-1) p
  rw [show f-g=(fun p => f p + -g p) from rfl]; simpa only [Pi.sub_apply,neg_one_mul,sub_eq_add_neg] using he.symm

variable {G : Gauge} {A : Levels G}
lemma tail_bridge (A : Levels G) (N M m d : ℕ) (hn : m+d≤N) (hm : m+d≤M) (k : ℝ) (a : Axis) :
    (Train.levelD k (location A N m) a - Train.levelD k (location A M m) a) = feed (flying A d m) a
      (Train.levelD k (location A N (m+d)) a - Train.levelD k (location A M (m+d)) a) := by
  induction d generalizing m with
  | zero => funext p; simpa only [flying,Nat.add_zero] using (feed_top _ _ _ _).symm
  | succ d ih =>
    have hN : m<N := by omega
    have hM : m<M := by omega
    have h1 : m+1+d = m+(d+1) := by omega
    let P := (A.clock.op m 0).patch
    have heq n (hv : m<n) : location A n m=Train.hop P (A.fits.mono (Nat.le_succ _)) (A.fits.stepSlow _) (location A n (m+1)) := by
      exact loc_land A n m hv
    have heq' : flying A (d+1) m = Train.hop P (A.fits.mono (Nat.le_succ _)) (A.fits.stepSlow _) (flying A d (m+1)) := rfl
    funext p
    rw [Pi.sub_apply,heq _ hN,heq _ hM,heq']
    rw [Train.D_feedback, Train.D_feedback, bind_feeds]
    have he := ih (m+1) (by omega) (by omega)
    rw [add_sub_add_right_eq_sub, slide_sub]
    -- note definitional type mismatch P.J
    change slide P a (Train.levelD k (location A N (m+1)) a-Train.levelD k (location A M (m+1)) a) p= _
    have he' : (Train.levelD k (location A N (m+1)) a-Train.levelD k (location A M (m+1)) a)
      = feed (flying A d (m+1)) a (Train.levelD k (location A N (m+(d+1))) a - Train.levelD k (location A M (m+(d+1))) a) := by
      exact he.trans (congr_arg (fun i=>feed (flying A d (m+1)) a (Train.levelD k (location A N i) a-Train.levelD k (location A M i) a)) h1)
    exact congr_arg (fun f=>slide P a f p) he'


lemma J_bound (A : Levels G) (d m : ℕ) : A.clock.J (m+d) ≤ A.clock.J m + d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => have hh := A.fits.stepSlow (m+d); rw [show m+d.succ=m+d+1 from rfl]; exact hh.trans (by omega)

lemma mass_bound (A : Levels G) (d m : ℕ) : (d:ℝ)^2 + 2*d + 1 ≤ 2*((flying A d m).mass.val:ℝ) := by
  induction d generalizing m with
  | zero => simp [flying, Train.mass]
  | succ d ih =>
    let u := (A.S.block m).val
    let v := (flying A d (m+1)).mass.val
    have heN : (3:ℕ) ≤ u := A.S.block_large m
    have hv : (1:ℕ) ≤ v := (flying A d (m+1)).mass.property
    have he := (Nat.cast_le (α:=ℝ)).mpr heN
    specialize ih (m+1)
    have hf : (flying A (d+1) m).mass.val = u*v := rfl
    rw [hf,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    push_cast at he
    cases d with
    | zero =>
      norm_num; nlinarith [mul_nonneg (sub_nonneg.mpr he) (Nat.cast_nonneg (α:=ℝ) v), (Nat.one_le_cast (α:=ℝ)).mpr hv]
    | succ d =>
      push_cast at *; have hV := Nat.cast_nonneg (α:=ℝ) v
      nlinarith [mul_nonneg (sub_nonneg.mpr he) hV, Nat.cast_nonneg (α:=ℝ) d]

lemma stage_small (A : Levels G) (m : ℕ) : Tendsto (fun d => (((A.clock.J (m+d):ℝ)+4) / ((flying A d m).mass.val:ℝ))) atTop (𝓝 0) := by
  have hb : Tendsto (fun d : ℕ => (d:ℝ)+1) atTop atTop := ?_
  let C : ℝ := 4+(A.clock.J m:ℝ)
  have ht := tendsto_const_nhds.div_atTop (a:=2*C) hb
  apply squeeze_zero (g:=fun (d:ℕ)=>(2*C/((d:ℝ)+1))) (fun (d:ℕ)=> by positivity) (fun (d:ℕ)=> show _ ≤ (2*C / ((d:ℝ)+1)) from ?_) ht
  · rw [div_le_div_iff₀ (side_pos _) (by positivity)]
    have h := mass_bound A d m; have hj : (A.clock.J (m+d):ℝ) ≤ A.clock.J m + (d:ℝ) := by exact_mod_cast J_bound A d m
    calc
      _ ≤ (C+d)*(d+1) := ?_
      _ ≤ _ := by unfold C at *; nlinarith [Nat.cast_nonneg (α:=ℝ) (A.clock.J m),Nat.cast_nonneg (α:=ℝ) d, Nat.cast_nonneg (α:=ℝ) ((flying A d m).mass.val)]
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (d:ℝ)+1)
    unfold C; simpa [add_comm,add_left_comm, add_assoc] using add_le_add_right hj 4
  exact tendsto_atTop_mono (f:= Nat.cast) (by intros; linarith) tendsto_natCast_atTop_atTop

lemma alias_all_gap {p : Momentum} (hp : p∈baseCube) (hv : p≠0) :
    ∃ b : ℝ, 0 < b ∧ ∀ L : Side, Odd L.val → ∀ l : Site L, b ≤ ‖blow 1 p l‖ := by
  obtain ⟨b,hb,h⟩ := alias_gap
  let t := lengthSq p; have hv' : 0 < t := lengthSq_pos hv
  refine ⟨min b (meter.low^2*t),lt_min hb (mul_pos (pow_pos meter.low_pos _) hv'),fun L ho l => ?_⟩
  by_cases hl : l=0
  · rw [hl,blow_zero]; exact (min_le_right ..).trans (divisor_lower (L * 1) hp)
  exact (min_le_left ..).trans (h _ L ho _ hp _ hl)

lemma far_lid {j : ℕ} (v : Train j) {q : Momentum} (e : physical q) (a : Axis) : ‖v.lid a q‖ ≤ 1 := by
  unfold Train.lid yen
  let z := narrow v.mass q; have hz : physical z := narrow_real _ e
  have hn : physical (-z) := (physical_iff _).mpr fun i => by simpa only [Pi.neg_apply,Complex.neg_im,neg_eq_zero] using (physical_iff _).mp hz i
  have H {p : Momentum} (hp : physical p) : ‖v.drive a p‖ ≤ 1 := by
    unfold Train.drive Train.smooth; rw [norm_mul,norm_mul,norm_pow]
    apply mul_le_one₀ (mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (area_real_le _ hp)) (norm_nonneg _) (extra_real_le _ hp)) (norm_nonneg _) (rail_real_le _ hp a)
  rw [norm_mul]; exact mul_le_one₀ (H hz) (norm_nonneg _) (H hn)

set_option maxHeartbeats 400000 in
lemma tail_limitD {A : Levels G} (m : ℕ) (a : Axis) (k : ℝ) {p : Momentum} (hp : p∈baseCube) (hn : p≠0) :
    CauchySeq (fun N => (location A N m).levelD k a p) := by
  obtain ⟨b,hb,hA⟩ := alias_all_gap hp hn
  obtain ⟨W,hW,hY⟩ := alias_decay
  obtain ⟨Q,hQ,hq⟩ := decay_cost
  apply Metric.cauchySeq_iff'.mpr; intro ε hε
  let η : ℝ := ε / 4 * (b / (W*Q))
  have hη : 0 < η := by unfold η; positivity
  obtain ⟨δ,hδ,hR⟩ := relative_radius k hη
  let w d := A.clock.J (m+d)
  let ρ : ℕ→ℝ := fun d => δ / ((w d:ℝ)+4)
  obtain ⟨D,hD,hd⟩ := drain_bound k
  have hh d : 0 < ρ d := by unfold ρ; positivity
  let h d := 2*(D*(δ^2) + meter.low⁻¹^2) * (ρ d)⁻¹^2
  let g d := (((flying A d m)|>.mass.val:ℝ)^2)⁻¹ * h d
  have ht : Tendsto (fun i=> g i*(W*Q) + ε/4) atTop (𝓝 (ε/4)) := by
    convert (((stage_small A m).pow 2).const_mul (2*(D*δ^2+meter.low⁻¹^2)*δ⁻¹^2) |>.mul_const (W*Q)).add (tendsto_const_nhds (x:=ε/4)) using 1
    · unfold g h ρ w; funext i; simp; rw [←inv_pow]; ring_nf; simp
    simp
  obtain ⟨d,Hd⟩ := (ht.eventually (gt_mem_nhds (show ε/4<ε by linarith))).exists
  refine ⟨m+d,fun N hN=>?_⟩
  let T := location A N (m+d)
  let v := flying A d m; let L := v.mass; have hL := side_pos L
  let f (x : Momentum) := T.levelD k a x - (divisor 1 x)⁻¹
  let z (l : Site L) := aliasAt p l; let y l := yen (v.drive a) (z l)
  have hcap d : 2 ≤ A.clock.J (m+d) := le_trans (by decide) (A.clock.adm _)
  have hf x : (location A (m+d) (m+d)).levelD k a x=(divisor 1 x)⁻¹ := by simp only [location, tsub_self,flying, Train.levelD, feed_top,Train.levelNoise,Train.nozzle,Train.stream,List.map_nil,List.sum_nil,mul_zero,add_zero]
  have eq : dist ((location A N m).levelD k a p) ((location A (m+d) m).levelD k a p) = ‖feed v a f p‖ := by
    rw [dist_eq_norm,show _ -_=feed v a (Train.levelD k T a-Train.levelD k (location A (m+d) (m+d)) a) p from congr_fun (tail_bridge A N _ m d hN le_rfl k a) p]
    exact congr_arg (fun f=>‖feed v a f p‖) (funext fun i => by rw [Pi.sub_apply,hf]; try rfl)
  have hCost (l : Site L) : ‖y l*f (z l)‖*((L.val:ℝ)^2)⁻¹ ≤ (g d + η / b)*W*decay 2 l := by
    have hz := hY v (by have := hcap 0; omega) _ (base_subset_realCube zone_pos hp) l a
    have hp' := alias_base hp l v.mass_odd
    have hy : ‖y l‖ ≤ W*decay 2 l := hz
    have hu := hA L v.mass_odd l
    change b ≤ ‖(L.val:ℂ)^2 * divisor 1 (z l)‖ at hu
    have hb' : b / (L.val:ℝ)^2 ≤ ‖divisor 1 (z l)‖ := by apply (div_le_iff₀' (by positivity)).mpr; rwa [norm_mul,norm_pow,Complex.norm_natCast] at hu
    have hxy : 0 < ‖divisor 1 (z l)‖ := lt_of_lt_of_le (by positivity : 0<b/(L.val:ℝ)^2) hb'
    have hc : ‖f (z l)‖*((L.val:ℝ)^2)⁻¹ ≤ g d + η / b := by
      by_cases he : ∀ i : Axis, ‖z l i‖ ≤ ρ d
      · have hr := hR (w d) (hcap d) (z l) hp' (by intro H; simp [H] at hxy) he (location A N (m+d)) a
        let u := divisor 1 (z l); let x := T.levelD k a (z l); have hu : ‖x*u-1‖ ≤ η := hr
        rw [show f (z l)=(x*u-1)/u from by unfold f x u; field_simp [norm_pos_iff.mp hxy]; try ring,norm_div, div_mul_eq_mul_div,div_le_iff₀ hxy]
        unfold g h
        let i : ℝ := ((L.val:ℝ)^2)⁻¹
        have hi : 0 ≤ i := by unfold i; positivity
        have hv : b*i≤‖u‖ := hb'
        apply (mul_le_mul_of_nonneg_right hu hi).trans _
        calc
          η*i = η/b*(b*i) := by field_simp
          _ ≤ (g d + η/b)* ‖u‖ := by
            apply mul_le_mul (le_add_of_nonneg_left _) hv (by positivity) (by unfold g h; positivity)
            unfold g h; positivity
      obtain ⟨i,hi⟩ := not_forall.mp he
      have hQ' : ρ d ≤ ‖z l i‖ := le_of_not_ge hi
      have hmotor := far_lid T hp'.1 a
      apply le_trans _ (le_add_of_nonneg_right (by positivity : 0 ≤ η/b))
      unfold g; change ‖_‖ * ((L.val:ℝ)^2)⁻¹ ≤ ((L.val:ℝ)^2)⁻¹ * _
      rw [mul_comm (((L.val:ℝ)^2)⁻¹)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hdiv (M : Side) : ‖(divisor M (z l))⁻¹‖ ≤ meter.low⁻¹^2 * (ρ d)⁻¹^2 := by
        have ht : (ρ d)^2 ≤ lengthSq (z l) := le_trans (sq_le_sq₀ (hh _).le (norm_nonneg _) |>.mpr hQ') (Finset.single_le_sum (f:=fun i => ‖(z l) i‖^2) (fun _ _ => by positivity) (Finset.mem_univ i))
        have hv := (mul_le_mul_of_nonneg_left ht (sq_nonneg meter.low)).trans (divisor_lower M hp')
        rw [norm_inv,← mul_pow,← mul_inv,inv_pow]; unfold z at *; apply inv_anti₀ (by positivity [meter.low_pos])
        convert hv using 1; rw [mul_pow]
      have hf : D*(δ^2)*(ρ d)⁻¹^2 ≥ D := by
        unfold ρ; rw [inv_div,div_pow,div_eq_mul_inv]; field_simp; nlinarith only [Nat.cast_nonneg (α:=ℝ) (w d)]
      have hu := (norm_mul ..).trans_le (mul_le_mul hmotor (hdiv T.mass) (norm_nonneg _) zero_le_one)
      unfold z at *; unfold f h; rw [Train.pole_split]
      exact (norm_sub_le ..).trans (by linarith [hdiv (1:Side), hd T (hcap d) (aliasAt p l) hp' a, norm_add_le (T.lid a (aliasAt p l)*(divisor T.mass (aliasAt p l))⁻¹) (T.drain k a (aliasAt p l))])
    rw [norm_mul,mul_assoc, mul_assoc (g d + η/b),mul_comm (g d + η/b)]; exact mul_le_mul hz hc (by positivity) (by positivity [decay_pos l 2])
  rw [eq]; unfold feed shuttle; rw [norm_mul, norm_inv,norm_pow,Complex.norm_natCast, mul_comm]
  apply lt_of_le_of_lt _ Hd
  apply (mul_le_mul_of_nonneg_right (norm_sum_le ..) (by positivity : 0≤((L.val:ℝ)^2)⁻¹)).trans
  calc
    (∑ l : Site L, ‖_‖) * _ = ∑ l : Site L, (‖y l*f (z l)‖*((L.val:ℝ)^2)⁻¹) := Finset.sum_mul ..
    _ ≤ ∑ l : Site L, (g d + η/b)*W*decay 2 l := Finset.sum_le_sum fun l _ => hCost l
    _ ≤ (g d + η/b)*W*Q := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hq L) (by unfold g h; positivity)
    _ = g d*(W*Q)+ε/4 := by unfold η; field_simp
end UV
end YM.Next.Free
