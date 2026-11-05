import YM.Bid.Loan

/-!
# From Paper.Clocks to the reference readout

A one-step cone estimate using the paid remainder of the *same* entries.
Fine-index notation in `cone_step`: step `i+1 → i`; the possibly very large
cone constant on the fine side is paid down by `Bank`. On the coarse side,
`roomCost` can absorb a square of the price from the fine side (the index
condition used for this is `stepSlow`).
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.G08

open Function RG Lattice Labels Source Bid
open scoped BigOperators

variable {G : Gauge} {d : ℕ}

/- Elementary ℓ¹ estimates (don't use the default norm on frame coefficients). -/

lemma size_nonneg (F : Labels.Frame G d) (u : F.Coeff) :
    0 ≤ F.coeffSize u := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma size_triangle (F : Labels.Frame G d) (u v : F.Coeff) :
    F.coeffSize u ≤ F.coeffSize v + F.coeffSize (u-v) := by
  unfold Labels.Frame.coeffSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  linarith only [norm_sub_norm_le (u i) (v i)]

lemma size_sub_rev (F : Labels.Frame G d) (u v : F.Coeff) :
    F.coeffSize (u-v) = F.coeffSize (v-u) := by
  unfold Labels.Frame.coeffSize
  exact Finset.sum_congr rfl (fun i _ => norm_sub_rev (u i) (v i))

lemma size_separates (F : Labels.Frame G d) (u : F.Coeff) (h : F.coeffSize u ≤ 0) : u = 0 := by
  funext i
  have hi : ‖u i‖ ≤ F.coeffSize u :=
    Finset.single_le_sum (f := fun i => ‖u i‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact norm_eq_zero.mp (le_antisymm (hi.trans h) (norm_nonneg _))

lemma size_core (F : Labels.Frame G d) (u : F.Coeff) :
    F.coeffSize (F.core u) ≤ F.coeffSize u := by
  unfold Labels.Frame.coeffSize
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖(Function.update u 0 0) i‖ ≤ ‖u i‖
  by_cases hi : i = 0
  · rw [hi, Function.update_self, norm_zero]; exact norm_nonneg _
  · rw [Function.update_of_ne hi]

lemma core_vowel (F : Labels.Frame G d) (L : Side) (u : F.Coeff) :
    F.core (vowel F L u) = vowel F L (F.core u) := by
  funext i
  change Function.update (vowel F L u) 0 0 i = _ * (Function.update u 0 0) i
  by_cases hi : i = 0
  · rw [hi, Function.update_self, Function.update_self, mul_zero]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]; rfl

lemma size_vowel (F : Labels.Frame G d) (L : Side) (u : F.Coeff) :
    F.coeffSize u ≤ F.coeffSize (vowel F L u) ∧
    F.coeffSize (vowel F L u) ≤ (L.val : ℝ)^d * F.coeffSize u := by
  have he (i : F.Index) :
      ‖vowel F L u i‖ = (L.val : ℝ)^(d-(F.grades i).1)*‖u i‖ := by
    unfold vowel; rw [norm_mul, Complex.norm_pow, Complex.norm_natCast]
  have hL : 1 ≤ (L.val : ℝ) := by exact_mod_cast L.property
  unfold Labels.Frame.coeffSize
  constructor
  · refine Finset.sum_le_sum fun i _ => ?_
    rw [he]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hL)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [he]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (Nat.sub_le ..)) (norm_nonneg _)

/- A perturbation estimate, to be used both on the whole vector and on `core`. -/
lemma lead_bounds (F : Labels.Frame G d) (C : ℝ) (hC : 1 ≤ C)
    (B : F.Coeff ≃ₗ[ℂ] F.Coeff)
    (hb : ∀ x, F.coeffSize (B x) ≤ C*F.coeffSize x ∧ F.coeffSize (B.symm x) ≤ C*F.coeffSize x)
    (u y : F.Coeff) (he : 2*C*F.coeffSize (u-B y) ≤ F.coeffSize y) :
    F.coeffSize y ≤ 2*C*F.coeffSize u ∧ F.coeffSize u ≤ 2*C*F.coeffSize y := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have h₁ : F.coeffSize y ≤ C * (F.coeffSize u + F.coeffSize (u-B y)) := calc
    F.coeffSize y = F.coeffSize (B.symm (B y)) := by rw [B.symm_apply_apply]
    _ ≤ C * F.coeffSize (B y) := (hb (B y)).2
    _ ≤ C * (F.coeffSize u + F.coeffSize (u-B y)) := by
      rw [size_sub_rev F u (B y)]
      exact mul_le_mul_of_nonneg_left (size_triangle F _ _) hC0
  have h₂ : F.coeffSize (u-B y) ≤ C*F.coeffSize y := calc
    _ ≤ 2*C*F.coeffSize (u-B y) :=
      le_mul_of_one_le_left (size_nonneg F _) (by linarith only [hC])
    _ ≤ F.coeffSize y := he
    _ ≤ C*F.coeffSize y := le_mul_of_one_le_left (size_nonneg F _) hC
  refine ⟨?_,?_⟩
  · nlinarith only [he,h₁]
  calc
    F.coeffSize u ≤ _ := size_triangle F u (B y)
    _ ≤ C*F.coeffSize y + C*F.coeffSize y := add_le_add (hb y).1 h₂
    _ = 2*C*F.coeffSize y := by ring

/- Two numerical checks showing how the stage reserves are used. -/
lemma bank_slack {C D s X : ℝ} (hc : 1 ≤ C) (hd : C ≤ D) (hs : 1 ≤ s)
    (h : 100000*D^6*(1+s)^2 ≤ X) :
    0 ≤ X⁻¹^(3:ℕ) ∧ 2*C*(X⁻¹^(3:ℕ))*(1+s) ≤ 1 := by
  have hd' : 1 ≤ D := hc.trans hd
  have hc' : C ≤ D^6 := hd.trans (by
    simpa using pow_le_pow_right₀ hd' (show 1 ≤ 6 by decide))
  have hs' : 1+s ≤ (1+s)^2 := by
    have H : 1 ≤ 1+s := by linarith only [hs]
    simpa using pow_le_pow_right₀ H (show 1 ≤ 2 by decide)
  have hy : 2*C*(1+s) ≤ X := le_trans (mul_le_mul
    (show 2*C ≤ 100000*D^6 from mul_le_mul (by norm_num) hc'
      (zero_le_one.trans hc) (by norm_num))
    hs' (by linarith only [hs]) (by positivity)) h
  have hx : 1 ≤ X := by nlinarith only [hy,hc,hs]
  have hx' : 0 < X := zero_lt_one.trans_le hx
  refine ⟨pow_nonneg (inv_nonneg.mpr hx'.le) _,?_⟩
  calc
    _ = (2*C*(1+s))/X^3 := by rw [div_eq_mul_inv,inv_pow]; ring
    _ ≤ 1 := (div_le_one₀ (pow_pos hx' _)).mpr (hy.trans (by
        simpa using pow_le_pow_right₀ hx (show 1 ≤ 3 by decide)))

lemma room_slack {C D s : ℝ} (hc : 1 ≤ C) (hd : C ≤ D) (h : 64*D^2 ≤ s) :
    4*C^2 ≤ s ∧ 2*C ≤ s := by
  have hx : C^2 ≤ D^2 := pow_le_pow_left₀ (zero_le_one.trans hc) hd _
  constructor <;> nlinarith only [hc,hx,h]

/- The one-step cone calculation. `u,r` are coarse; `v,t` are fine. -/
lemma cone_step (W : Worth) (H : History G) (hr : roomCost H.levels W)
    (hb : Bank W H.levels) (i : ℕ) (F : Labels.Frame G d) (u v : F.Coeff) (r t : ℝ)
    (hdir : direction H W i F u v r t)
    (htcone : t ≤ (H.levels.params (i+1)).columns * F.coeffSize (F.core v)) :
    r ≤ (H.levels.params i).columns * F.coeffSize (F.core u) ∧
    F.coeffSize v ≤ (H.levels.params (i+1)).columns * F.coeffSize u ∧
    F.coeffSize u ≤ (H.levels.params (i+1)).columns * ((H.S.block i).val : ℝ)^d *
        F.coeffSize v := by
  let L := H.S.block i
  let z := H.levels.clock.J (i+1)
  let C := W.K z
  let s := (H.levels.params (i+1)).columns
  let e := barunit L
  let y := vowel F L v
  have hC : 1 ≤ C := W.prices _
  have hcc : 0 ≤ 2*C := by linarith only [hC]
  have hcz : C ≤ W.K (z+1) := W.growth z.le_succ
  have hb' : 100000*(W.K (z+1))^6*(1+s)^2 ≤ puffs L := hb i
  obtain ⟨he0, he⟩ : 0 ≤ e ∧ 2*C*e*(1+s) ≤ 1 :=
    bank_slack hC hcz (H.levels.params (i+1)).columns_ge hb'
  have hfine : 2*C ≤ s := (room_slack hC hcz (hr (i+1))).2
  have hcoarse : 4*C^2 ≤ (H.levels.params i).columns :=
    (room_slack hC (W.growth (H.levels.fits.stepSlow i)) (hr i)).1

  obtain ⟨-,ht,B,hB,hE,hR⟩ := hdir
  have hcost : ∀ x, F.coeffSize (B x) ≤ C*F.coeffSize x ∧ F.coeffSize (B.symm x) ≤ C*F.coeffSize x :=
    fun x => ⟨(hB x).1,(hB x).2.1⟩
  have hm : F.coeffSize (F.core v) + t ≤ (1+s)*F.coeffSize (F.core v) := by
    rw [add_mul,one_mul]; exact add_le_add_right htcone _
  have hscale : 2*C*(e*(F.coeffSize (F.core v) + t)) ≤ F.coeffSize (F.core y) := calc
    _ ≤ 2*C*(e*((1+s)*F.coeffSize (F.core v))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm he0) hcc
    _ = (2*C*e*(1+s))*F.coeffSize (F.core v) := by ring
    _ ≤ 1*F.coeffSize (F.core v) := mul_le_mul_of_nonneg_right he (size_nonneg F _)
    _ ≤ F.coeffSize (F.core y) := by
      rw [one_mul, show F.core y = vowel F L (F.core v) from core_vowel F L v]
      exact (size_vowel F L (F.core v)).1
  have herr : 2*C*F.coeffSize (u-B y) ≤ F.coeffSize (F.core y) :=
    le_trans (mul_le_mul_of_nonneg_left hE hcc) hscale

  obtain ⟨hlead,hu⟩ := lead_bounds F C hC B hcost u y (herr.trans (size_core F _))
  have herr' : 2*C*F.coeffSize (F.core u - B (F.core y)) ≤ F.coeffSize (F.core y) := by
    rw [← (hB y).2.2, ← map_sub]
    exact le_trans (mul_le_mul_of_nonneg_left (size_core F _) hcc) herr
  have hlead' := (lead_bounds F C hC B hcost (F.core u) (F.core y) herr').1
  obtain ⟨hv₁,hv₂⟩ := size_vowel F L v

  refine ⟨?_, ?_, ?_⟩
  · have ht' : e*t ≤ C*F.coeffSize (F.core y) := calc
      e*t ≤ e*(F.coeffSize (F.core v) + t) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (size_nonneg F _)) he0
      _ ≤ 2*C*(e*(F.coeffSize (F.core v) + t)) := le_mul_of_one_le_left
        (mul_nonneg he0 (add_nonneg (size_nonneg F _) ht)) (by linarith only [hC])
      _ ≤ F.coeffSize (F.core y) := hscale
      _ ≤ C*F.coeffSize (F.core y) := le_mul_of_one_le_left (size_nonneg F _) hC
    calc
      r ≤ C*F.coeffSize (F.core y) + e*t := hR
      _ ≤ C*F.coeffSize (F.core y) + C*F.coeffSize (F.core y) := add_le_add_right ht' _
      _ = 2*C*F.coeffSize (F.core y) := by ring
      _ ≤ 2*C*(2*C*F.coeffSize (F.core u)) := mul_le_mul_of_nonneg_left hlead' hcc
      _ = 4*C^2*F.coeffSize (F.core u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoarse (size_nonneg F _)
  · calc
      F.coeffSize v ≤ F.coeffSize y := hv₁
      _ ≤ 2*C*F.coeffSize u := hlead
      _ ≤ s*F.coeffSize u := mul_le_mul_of_nonneg_right hfine (size_nonneg F _)
  · calc
      F.coeffSize u ≤ 2*C*F.coeffSize y := hu
      _ ≤ 2*C*((L.val : ℝ)^d*F.coeffSize v) := mul_le_mul_of_nonneg_left hv₂ hcc
      _ ≤ s*((L.val : ℝ)^d*F.coeffSize v) :=
        mul_le_mul_of_nonneg_right hfine (mul_nonneg (by positivity) (size_nonneg F _))
      _ = s*(L.val : ℝ)^d*F.coeffSize v := (mul_assoc ..).symm

theorem answer : YM.Bid.G08 := by
  intro G W H hr hb N p d k F P S A hp
  have hcone (i : ℕ) (hki : k ≤ i) (hi : i ≤ N) (v : F.Coeff) :
      P.paid i v ≤ (H.levels.params i).columns * F.coeffSize (F.core (P.inits i v).x) := by
    induction hi using Nat.decreasingInduction with
    | self =>
      rw [(hp.outfeet v).1]; exact (hp.thick v).trans
        (le_mul_of_one_le_left (size_nonneg F _) (H.levels.params N).columns_ge)
    | of_succ m hm ih =>
      exact (cone_step W H hr hb m F _ _ _ _ (hp.owns m hki hm v)
        (ih (hki.trans m.le_succ))).1
  have hsteps (i : ℕ) (hki : k ≤ i) (hi : i < N) (v : F.Coeff) :=
    (cone_step W H hr hb i F _ _ _ _ (hp.owns i hki hi v)
      (hcone (i+1) (hki.trans i.le_succ) hi v)).2

  -- A zero at reference forces a zero at the cutoff; the map is a
  -- linear endomorphism of a finite-dimensional complex vector space.
  let Q : F.Coeff →ₗ[ℂ] F.Coeff :=
    IsLinearMap.mk' (fun v => (P.inits k v).x) (hp.linear k le_rfl hp.ahead).1
  have hQ : Injective Q := by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro v hv
    have hzero (m : ℕ) (hkm : k ≤ m) (hm : m ≤ N) : (P.inits m v).x = 0 := by
      induction m, hkm using Nat.le_induction with
      | base => exact hv
      | succ m hkm ih =>
        have he := (hsteps m hkm hm v).1
        rw [ih (m.le_succ.trans hm)] at he
        apply size_separates F _
        simpa [Labels.Frame.coeffSize] using he
    exact ((hp.outfeet v).1.symm).trans (hzero N hp.ahead le_rfl)
  let T : TransferData F H N p :=
    ⟨P.inits, LinearEquiv.ofBijective Q ⟨hQ, LinearMap.injective_iff_surjective.mp hQ⟩⟩
  refine ⟨T,rfl,{
    ref := hp.ahead
    format := fun m hl hu v => (hp.knees m hl hu v).1
    cap := ?_
    back := fun m hl hu v => (hsteps m hl hu v).1
    front := fun m hl hu v => (hsteps m hl hu v).2
    linear := hp.linear
    bare_coord := fun v => (hp.outfeet v).1
    bare_germ := fun v => (hp.outfeet v).2
    encode := hp.charges
    unnormalized := hp.steps
    reads := fun _ => rfl
    unit_coord := hp.units
    realForm := fun v => (hp.moves k le_rfl hp.ahead v).1
    orients := fun s v => (hp.moves k le_rfl hp.ahead v).2 s }⟩
  intro m hl hu v
  obtain ⟨a,b,ha,hb₀,hab,hw⟩ := (hp.knees m hl hu v).2
  exact ⟨a,b,ha,hb₀,hab.trans (hcone m hl hu v),hw⟩

end YM.Work.G08
