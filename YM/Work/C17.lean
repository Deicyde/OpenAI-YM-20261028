import YM.Analysis.Polydisc
import YM.Bid.Tar
import YM.Shift.Breath

/-!
# Small imaginary boosts at an adjacent spacelike pair

Full coordinates, time last. `shade_diff_augment` and `enters` below are
for the *ordered* adjacent differences (argument indices explicitly given,
so we can also use them in the opposite tube).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C17
open Function Set Filter Mink Boundary Bid Complex
open scoped Topology InnerProductSpace

variable {n : ℕ}

private lemma dawn_cont : Continuous (@dawn n) := by
  unfold dawn place points
  simp_rw [show position = _ from funext fun x => funext fun t => (Mink.combine_at x t).symm]
  fun_prop

private lemma dawn_at (y : Heights n) (i) : dawn y i = position 0 (y i) := rfl

private lemma strict_slope (y : Heights n) (i j : Fin n) (h : y i < y j) :
    dawn y j - dawn y i ∈ inside := by
  change ‖spatial _‖ < time _
  simpa [dawn_at, sub_eq_add_neg] using h

private lemma switch_fixed {P : NearPair n} {y : Heights n} (h : P.spectator y) :
    P.switch (dawn y) = dawn y := by
  apply PiLp.ext; intro i
  change P.switch (dawn y) i = dawn y i
  rw [P.switch_at, dawn_at, dawn_at]; congr 1
  have he : y P.i=y P.j := h.1
  by_cases hi : i=P.i
  · simp [NearPair.s, hi, he]
  by_cases hj : i=P.j
  · simp [NearPair.s, hj, he]
  simp only [NearPair.s, Equiv.swap_apply_of_ne_of_ne hi hj]

private lemma fleck_of_spectator {P : NearPair n} {y : Heights n} (h : P.spectator y) :
    P.Fleck y := by
  have hm : y ∈ sunrise n := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hj|hj
    · by_cases hp : i≠P.i ∨ j≠P.j
      · exact (h.2 i j hj hp).le
      push Not at hp
      rw [hp.1,hp.2,h.1]
    rw [hj]
  have he := switch_fixed h
  have hs : dawn y ∈ shores n := by
    simp only [shores,mem_iInter]
    intro i j hij
    change ‖spatial _‖ ≤ time _
    simpa [dawn_at, sub_eq_add_neg] using hm (show i≤j by omega)
  have hc (x : Points n) : glow x (dawn y) ∈ closure (tube n) := by
    haveI : (𝓝[east n] y).NeBot := awaits hm
    have H : Continuous (fun t : Heights n => glow x (dawn t)) :=
      (home n).comp (continuous_const.prodMk dawn_cont)
    apply mem_closure_of_tendsto ((H.tendsto y).mono_left (@nhdsWithin_le_nhds _ _ y (east n)))
    filter_upwards [self_mem_nhdsWithin] with t ht
    change shade _ ∈ fields n
    simpa using etched ht
  refine ⟨h, hs, by rw [he]; exact hs, hc, fun x => ?_⟩
  have H : Continuous P.name := (home n).comp ((P.switch.continuous.comp (cont_Re n)).prodMk
    (P.switch.continuous.comp (cont_sh n)))
  have hu : MapsTo P.name (tube n) (P.name ⁻¹' tube n) := by
    intro i hi
    change P.name (P.name i) ∈ tube n
    rwa [P.name_name]
  have hx : P.switch (P.switch x) = x := P.switch.symm_apply_apply x
  have hh := hu.closure H (hc (P.switch x))
  simpa only [NearPair.name,re_glow,im_glow,hx,he] using hh

private theorem choose_direction (x : E4) (hx : x ∈ spacelike) :
    ∃ e : Ray, e.crossT x ∈ inside := by
  let T := ‖spatial x‖
  have hh : |time x| < T := (lateral x).mp hx
  have hp : 0<T := (abs_nonneg _).trans_lt hh
  let u : Ray := ⟨T⁻¹ • spatial x,by rw [norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp),inv_mul_cancel₀ hp.ne']⟩
  have hb : u.along x=T := by
    simp only [u,Ray.along,real_inner_smul_right,real_inner_self_eq_norm_sq,pow_two]
    change T⁻¹ * (T*T) = T; field_simp
  refine ⟨u,?_⟩
  change ‖spatial _‖ < time _
  rw [u.liesT,u.ticksT,norm_smul,u.property,mul_one,Real.norm_eq_abs,hb]
  exact hh

private lemma shade_at (x : Full n) (i a) : shade x i a = (x (i,a)).im := rfl
private lemma glow_at (x y : Points n) (i a) : glow x y (i,a) = ↑(x i a) + ↑(y i a)*I := rfl

private lemma shade_augment (e : Ray) (b : ℝ) (x : Full n) (i : Fin n) :
    shade (augment e (↑b*I) x) i = shade x i + (Real.sin b) • e.crossT (reality x i) +
      (Real.cos b-1) • e.scalesT (shade x i) := by
  ext a
  simp [shade_at, augment, glow_at, Complex.sinh_mul_I, Complex.cosh_mul_I, Complex.mul_im,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re]

private lemma shade_diff_augment (e : Ray) (b : ℝ) (x : Full n) (i j : Fin n) :
    shade (augment e (↑b*I) x) j - shade (augment e (↑b*I) x) i =
      (shade x j - shade x i) + (Real.sin b) • e.crossT (reality x j - reality x i) +
      (Real.cos b-1) • e.scalesT (shade x j - shade x i) := by
  simp only [shade_augment, map_sub, smul_sub]
  abel

private lemma add_into {x y : E4} {r : ℝ} (hx : x ∈ cone) (hy : y ∈ inside) (hr : 0 < r) :
    x + r • y ∈ inside := by
  change ‖spatial _‖ < time _
  rw [rest_add, clock_add, rest_mul, clock_mul]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact add_lt_add_of_le_of_lt hx (mul_lt_mul_of_pos_left hy hr)

/-- Small-angle neighbourhood argument for ordered boost coordinates. At
least one of the height gap and the `sin` coefficient must already point
strictly in. In the second case factor OUT `sin b`; the remaining coefficient
of `W` is `-sin/(1+cos)`, continuous near zero and zero there. So we even enter from
nearby points with merely *closed* cone gaps, for b strictly positive. Using
a single product neighbourhood keeps this uniform all the way down to zero.
-/
private lemma enters (q : Full n) (A : ℝ → Full n → Full n)
    (Y V W : Fin n → Fin n → Full n → E4) (hy : ∀ i j, Continuous (Y i j))
    (hv : ∀ i j, Continuous (V i j)) (hw : ∀ i j, Continuous (W i j))
    (hf : ∀ b p i j, shade (A b p) j - shade (A b p) i =
      (Y i j p + Real.sin b • V i j p) + (Real.cos b-1) • W i j p)
    (h0 : ∀ i j : Fin n, i.val+1=j.val → Y i j q ∈ inside ∨ V i j q ∈ inside) :
    ∀ᶠ p : ℝ × Full n in 𝓝 (0,q), 0<p.1 → shade (A 0 p.2) ∈ shores n → A p.1 p.2 ∈ tube n := by
  let a : ℝ × Full n := (0,q)
  have He : ∀ᶠ p in 𝓝 a, ∀ i j : Fin n, i.val+1=j.val → 0<p.1 → Y i j p.2 ∈ cone →
      shade (A p.1 p.2) j - shade (A p.1 p.2) i ∈ inside := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i.val+1=j.val
    · rcases h0 i j hij with hh|hh
      · let d (p : ℝ × Full n) := shade (A p.1 p.2) j - shade (A p.1 p.2) i
        have hd : Continuous d := by
          unfold d; simp_rw [hf]; fun_prop
        have hn : d a ∈ inside := by simpa [d,a,hf] using hh
        filter_upwards [(hd.tendsto a).eventually (open_inside.mem_nhds hn)] with p hp using
          fun _ _ _ => hp
      · let D (p : ℝ × Full n) := 1+Real.cos p.1
        let d (p : ℝ × Full n) := V i j p.2 + (-Real.sin p.1 / D p) • W i j p.2
        have hD : D a ≠ 0 := by norm_num [D,a]
        have hC : Continuous D := by unfold D; fun_prop
        have hd : ContinuousAt d a := by
          unfold d; fun_prop (disch := assumption)
        have hn : d a ∈ inside := by simpa [a,d] using hh
        have ht : a.1 < Real.pi := Real.pi_pos
        filter_upwards [hd.eventually (open_inside.mem_nhds hn),
          (continuous_fst.tendsto a).eventually (gt_mem_nhds ht),
          (hC.tendsto a).eventually (eventually_ne_nhds hD)] with p hp ht' hD'
        intro _ hb hy'
        have hr : 0 < Real.sin p.1 := Real.sin_pos_of_pos_of_lt_pi hb ht'
        have hw' : Real.sin p.1 * (-Real.sin p.1 / D p) = Real.cos p.1 - 1 := by
          change D p ≠ 0 at hD'
          rw [← mul_div_assoc, div_eq_iff hD']
          unfold D
          linarith [Real.sin_sq_add_cos_sq p.1]
        have h := add_into hy' (show d p ∈ inside from hp) hr
        rwa [hf, ← hw', mul_smul, add_assoc, ← smul_add]
    exact Eventually.of_forall (fun _ h => False.elim (hij h))
  filter_upwards [He] with p hp
  intro hh hj
  simp only [tube, mem_preimage, shores, fields, mem_iInter, mem_setOf] at hj ⊢
  intro i j hij
  apply hp i j hij hh
  simpa only [hf, Real.sin_zero, Real.cos_zero, sub_self, zero_smul, add_zero] using hj i j hij

private theorem local_paths {P : NearPair n} {y : Heights n} (hy : P.Fleck y) (x : Points n)
    (hx : x ∈ P.gap) : ∃ (e : Ray) (t : ℝ), travelable e P t (glow x (dawn y)) := by
  obtain ⟨e,he⟩ := choose_direction (x P.j - x P.i) hx
  let q := glow x (dawn y)
  let A (b : ℝ) (w : Full n) := augment e (↑b*I) w
  let B (b : ℝ) (w : Full n) := P.name (augment e (-↑b*I) w)
  have ha (w) : A 0 w = w := by simp [A,augment]
  have hb (w) : B 0 w = P.name w := by simp [B,augment]
  let Y (i j : Fin n) (w : Full n) := shade w j - shade w i
  let V (i j : Fin n) (w : Full n) := e.crossT (reality w j - reality w i)
  let W (i j : Fin n) (w : Full n) := e.scalesT (Y i j w)
  have hcY (i j : Fin n) : Continuous (Y i j) := by unfold Y; fun_prop
  have hcV (i j : Fin n) : Continuous (V i j) := by unfold V; fun_prop
  have hcW (i j : Fin n) : Continuous (W i j) := by unfold W; fun_prop
  have hI (i j : Fin n) (hij : i.val+1=j.val) (hw : i ≠ P.i ∨ j≠P.j) :
      Y i j q ∈ inside := by
    simpa only [Y,q,im_glow] using strict_slope y i j (hy.willing.2 i j (show i < j by omega) hw)
  have HA : ∀ᶠ p : ℝ × Full n in 𝓝 (0,q), 0 < p.1 → shade (A 0 p.2) ∈ shores n →
      A p.1 p.2 ∈ tube n := by
    refine enters q A Y V W hcY hcV hcW (fun b p i j => shade_diff_augment e b p i j)
      (fun i j hij => ?_)
    by_cases hw : i ≠ P.i ∨ j≠P.j
    · exact .inl (hI i j hij hw)
    right
    push Not at hw
    simpa only [V,q,re_glow,hw.1,hw.2] using he
  have HB : ∀ᶠ p : ℝ × Full n in 𝓝 (0,q), 0 < p.1 → shade (B 0 p.2) ∈ shores n →
      B p.1 p.2 ∈ tube n := by
    refine enters q B (fun i j => Y (P.s i) (P.s j)) (fun i j p => -V (P.s i) (P.s j) p)
      (fun i j => W (P.s i) (P.s j)) (fun _ _ => hcY ..) (fun _ _ => Continuous.neg (hcV ..))
      (fun _ _ => hcW ..) (fun b p i j => ?_) (fun i j hij => ?_)
    · unfold B NearPair.name; rw [im_glow,P.switch_at,P.switch_at]
      simpa only [Complex.ofReal_neg, Real.sin_neg, Real.cos_neg,Y,V,W,smul_neg,neg_smul] using
        shade_diff_augment e (-b) p (P.s i) (P.s j)
    by_cases hw : i ≠ P.i ∨ j≠P.j
    · left
      have hf : P.switch (shade q) = shade q := by simpa only [q,im_glow] using switch_fixed hy.willing
      simpa only [Y, ← P.switch_at, hf] using hI i j hij hw
    right
    push Not at hw
    simpa only [hw.1,hw.2,NearPair.s,Equiv.swap_apply_left,Equiv.swap_apply_right,V,q,
      re_glow,map_sub,neg_sub] using he
  obtain ⟨r,hr,s,hs,hRS⟩ := mem_nhds_prod_iff.mp (HA.and HB)
  obtain ⟨u,hu,hR⟩ := Metric.mem_nhds_iff.mp hr
  obtain ⟨t,ht,hu'⟩ := exists_between hu
  have hroot {b : ℝ} (hp : 0<b) (hq : b≤t) {w : Full n} (hw : w∈s) :
      (shade (A 0 w) ∈ shores n → A b w ∈ tube n) ∧
      (shade (B 0 w) ∈ shores n → B b w ∈ tube n) := by
    have h : b∈r := hR (by simpa [Real.dist_eq,abs_of_pos hp] using hq.trans_lt hu')
    have h' := hRS (mk_mem_prod h hw)
    exact ⟨h'.1 hp, h'.2 hp⟩
  have hx' := hroot ht le_rfl (mem_of_mem_nhds hs)
  refine ⟨e,t,ht,hx'.1 ?_,hx'.2 ?_,?_,?_⟩
  · simpa only [ha,q,im_glow] using hy.here
  · simpa only [hb,q,NearPair.name,im_glow] using hy.there
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hs,self_mem_nhdsWithin] with w hw hW
    intro b hbt
    change A b w ∈ tube n
    rcases hbt.1.eq_or_lt with h0|h0
    · rwa [←h0,ha]
    apply (hroot h0 hbt.2 hw).1
    rw [ha]; exact total_south n hW
  filter_upwards [mem_nhdsWithin_of_mem_nhds hs,self_mem_nhdsWithin] with w hw hW
  intro b hbt
  change B b w ∈ tube n
  rcases hbt.1.eq_or_lt with h0|h0
  · rw [←h0,hb]; exact hW
  apply (hroot h0 hbt.2 hw).2
  rw [hb]; exact total_south n hW

/-- One height profile per pair with one flattened step. All other gaps
are strictly positive (in absolute height coordinates). `n=2` gives
identically zero heights in this choice.
-/
private theorem height_path (P : NearPair n) :
    ∃ y : ℕ → Heights n, Tendsto (dawn ∘ y) atTop (𝓝 0) ∧ ∀ m, P.spectator (y m) := by
  let a (i : Fin n) := if i=P.j then P.i.val else i.val
  let d : Heights n := fun i => (a i : ℝ)
  have hP := P.next
  have hh : P.spectator d := by
    constructor
    · simp [d,a]
    intro i j hij he
    change (a i:ℝ)<(a j:ℝ)
    apply Nat.cast_lt.mpr
    dsimp only [a]; split_ifs <;> omega
  let p (m : ℕ) : ℝ := ((m+1:ℕ):ℝ)⁻¹
  have hp : Tendsto p atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  let y (m : ℕ) := p m • d
  have hy : Tendsto y atTop (𝓝 0) := by
    simpa only [zero_smul,y] using hp.smul (tendsto_const_nhds (x:=d))
  refine ⟨y,?_,fun m => ?_⟩
  · have hz : dawn (0:Heights n)=0 := by
      apply PiLp.ext; intro i
      change position 0 0= (0:E4)
      apply Mink.ext_by <;> simp
    simpa only [hz] using (dawn_cont.tendsto (0:Heights n)).comp hy
  have hm : 0 < p m := by unfold p; positivity
  constructor
  · change p m * d P.i = p m * d P.j; rw [hh.1]
  intro i j hij he
  exact mul_lt_mul_of_pos_left (hh.2 i j hij he) hm

theorem answer : YM.Bid.C17 := by
  intro n P
  obtain ⟨y,hy,h⟩ := height_path P
  refine ⟨y,hy,fun m => ?_⟩
  have he := fleck_of_spectator (h m)
  exact ⟨he,local_paths he⟩



end YM.Work.C17
