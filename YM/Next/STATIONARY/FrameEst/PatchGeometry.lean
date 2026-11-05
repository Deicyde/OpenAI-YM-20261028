import YM.Next.STATIONARY.FrameEst.Center

set_option autoImplicit false
/-! # Principal floor. Uniform discrete window via Jordan & small band.
Mean and frame offset projection used only IN Nave real slice. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {P : Patch} {L c f : Side} {p q k : Momentum}

private theorem minimal_rep (h : Odd L.val) (t : ZMod L.val) : -(↑(L.val/2):ℤ) ≤ t.valMinAbs ∧ t.valMinAbs ≤ (L.val/2:ℕ) := by
  obtain ⟨j,hj⟩ := h
  have he := ZMod.valMinAbs_mem_Ioc t; simp only [Set.mem_Ioc] at he; omega
lemma min_abs_for (h : Odd L.val) (a : ℤ) (hx : -(↑(L.val/2):ℤ) ≤ a ∧ a≤(L.val/2:ℕ)) : ZMod.valMinAbs (a:ZMod L.val)=a := by
  obtain ⟨i,hi⟩ := h; apply (ZMod.valMinAbs_spec _ _).2
  exact ⟨rfl,by simp only [Set.mem_Ioc]; omega⟩

-- `pulse1` average over centered L positions. Bound at principal using
-- just the real part; end-to-end connector sum = rephase of same average.

def pulse1 (L : Side) (k : ℂ) := (inch L:ℂ) * ∑ i : ZMod L.val, exp (I*(k*i.valMinAbs))
lemma cons_pulse (L : Side) (p : Momentum) : (inch L:ℂ)^4 *∑ z : Site L,mode p (lift z)=∏ j, pulse1 L (p j) := by
  simp only [pulse1, prod_mul_distrib, Fintype.prod_sum]; congr 1
  · simp [Axis]
  apply sum_congr rfl; intro z _; unfold mode; rw [Finset.mul_sum,Complex.exp_sum]; rfl
lemma pulse_lower (h : Odd L.val) (he : star k=k) (i : Axis) (hp : |(k i).re|≤Real.pi*inch L) : 1/16≤ ‖pulse1 L (k i)‖ := by
  let xi := (k i).re
  let V z := Real.cos (xi*(z:ZMod L.val).valMinAbs)
  have hw z : k i*((z:ZMod L.val).valMinAbs)=↑(xi*(z:ZMod L.val).valMinAbs:ℝ) := by push_cast; rw [show (xi:ℂ)=k i from strip_unit he i]
  have hv : (pulse1 L (k i)).re = inch L * ∑ z,V z := by
    simp only [pulse1,hw,Complex.mul_re, ofReal_re, re_sum, ofReal_im,zero_mul,sub_zero]; congr 2
    funext j; rw [mul_comm I]; rw [Complex.exp_mul_I,← Complex.ofReal_cos, ← Complex.ofReal_sin]; simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]; rfl
  refine le_trans (b:=(pulse1 L (k i)).re) ?_ (le_trans (le_abs_self _) (abs_re_le_norm _))
  rw [hv]
  have hj (z : ℤ) (p : 0≤z ∧ z < (L.val/4:ℕ) +1) : (z:ZMod L.val).valMinAbs=z := min_abs_for h _ (by omega)
  have hl (a : ZMod L.val) : 0≤V a := by
    have hk := minimal_rep (L:=L) h a
    have hc : |xi*a.valMinAbs| ≤ Real.pi/2 := by
      rw [abs_mul]; calc
        _ ≤ (Real.pi*inch L)*(L.val/2:ℝ) := by
          have hh : (|((a.valMinAbs : ℤ):ℝ)|)*2 ≤ L.val := by rw [← Int.cast_abs]; exact_mod_cast (show |a.valMinAbs| *2≤(L.val:ℤ) by rw [← Int.natCast_natAbs]; omega)
          exact mul_le_mul hp (by linarith) (abs_nonneg _) (mul_nonneg Real.pi_pos.le (inch_pos _).le)
        _ = _ := by rw [mul_assoc Real.pi]; have hh := inch_unit L; rw [← mul_div_assoc, hh]; ring
    exact Real.cos_nonneg_of_mem_Icc (abs_le.mp hc)
  let j : Fin (L.val / 4 + 1) ↪ ZMod L.val := ⟨fun i => (i.val:ZMod L.val),fun a b he => Fin.ext (by
    have hi := hj (a.val:ℤ) (by omega); have hh := hj (b.val:ℤ) (by omega); rw [Int.cast_natCast, show (a.val:ZMod L.val)= b.val from he] at hi; rw [Int.cast_natCast] at hh; exact_mod_cast (hi.symm.trans hh))⟩
  have hm (a) : (1/2:ℝ) ≤ V (j a) := by
    have hi := hj (a.val:ℤ) (by omega); rw [Int.cast_natCast] at hi
    have hx : (↑a.val:ℝ)*4≤L.val := by exact_mod_cast (show a.val*4 ≤ L.val by omega)
    unfold V
    rw [show ZMod.valMinAbs (j a)=_ from hi,Int.cast_natCast]
    let s := xi*(a.val:ℝ)
    have he : |s|≤Real.pi/3 := by
      unfold s; rw [abs_mul,abs_of_nonneg (a:=(a.val:ℝ)) (Nat.cast_nonneg _)]
      calc
        _ ≤ (Real.pi*inch L)*(L.val/4:ℝ) := mul_le_mul hp (by linarith) (Nat.cast_nonneg _) (mul_nonneg Real.pi_pos.le (inch_pos _).le)
        _ ≤ _ := by rw [mul_assoc Real.pi, ← mul_div_assoc, inch_unit]; linarith [Real.pi_pos]
    rw [← Real.cos_pi_div_three]; change Real.cos (Real.pi/3) ≤ Real.cos s
    rw [← Real.cos_abs s];
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg s) (by linarith [Real.pi_pos]) he
  apply le_trans _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (show univ.map j ⊆ univ from Finset.subset_univ _) (fun a _ _ => hl a)) (inch_pos L).le)
  rw [Finset.sum_map]
  have HX : ∑ _ : Fin (L.val/4+1),(1/2:ℝ) ≤ ∑ i : Fin (L.val/4+1), V (j i) := Finset.sum_le_sum fun i _ => hm i
  apply le_trans _ (mul_le_mul_of_nonneg_left HX (inch_pos L).le)
  simp only [Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];
  have HY : (L.val:ℝ) ≤ 4 * (↑(L.val/4+1):ℝ) := by exact_mod_cast (show L.val≤4*(L.val/4+1) by omega)
  nlinarith only [HY,inch_unit L,inch_pos L]

def rollMean (P : Patch) (k : Momentum) := ∑ a : P.Points,(P.weight a:ℂ)*mode k a.val
def limitMean (J : ℕ) := (((1/16:ℝ))^4)^J
lemma limitMean_pos (J : ℕ) : 0<limitMean J := by unfold limitMean; positivity
lemma preview_coord (h : Nave p) (L : Side) (a : Axis) : |(aliasAt p (0:Site L) a).re| ≤ Real.pi*inch L := by
  rw [alias_re]; simp only [show lift (0:Site L) a=0 by simp [Lattice.lift],Int.cast_zero,mul_zero,add_zero]; rw [abs_mul,abs_of_pos (inch_pos L),mul_comm Real.pi]; exact mul_le_mul_of_nonneg_left (h a) (inch_pos _).le
lemma roll_strict (h : Nave p) (he : star p=p) : limitMean P.J ≤ ‖rollMean P (aliasAt p (0:Site P.L))‖ := by
  let k := aliasAt p (0:Site P.L)
  unfold rollMean limitMean; rw [lottery_exp,cons_pulse, norm_pow,norm_prod]; apply pow_le_pow_left₀ (by positivity)
  calc
    _ = ∏ _ : Axis,(1/16:ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => pulse_lower P.odd_side (k:=k) (by unfold k; rw [← alias_conj,he]) i (preview_coord h P.L i))

lemma connector_strict (h : Nave p) (he : star p=p) (l : Axis) : (1/16:ℝ)*P.L.val ≤ ‖∑ i : Fin P.L.val,mode (aliasAt p (0:Site P.L)) (i.val • step l)‖ := by
  let L := P.L
  let k := aliasAt p (0:Site L)
  have hk : star k=k := by unfold k; rw [← alias_conj,he]
  let n := L.val/2
  let z (i : Fin L.val) : ℤ := (i.val:ℤ)-n
  let f (i : Fin L.val) : ZMod L.val := z i
  have hL : Odd L.val := P.odd_side
  have hu (i : Fin L.val) : (f i).valMinAbs=z i := min_abs_for hL _ (by obtain ⟨k,hk⟩ := hL; unfold z n; omega)
  let s : Fin L.val ≃ ZMod L.val := Equiv.ofBijective f <| by
    rw [Fintype.bijective_iff_injective_and_card]; refine ⟨fun i j h => Fin.ext ?_, by simp⟩
    have hi : z i=z j := (hu i).symm.trans ((congr_arg ZMod.valMinAbs h).trans (hu j)); unfold z at hi; omega
  have hb : (inch L:ℂ) * ∑ i : Fin L.val,mode k (i.val • step l) = pulse1 L (k l) * mode k (n • step l) := by
    unfold pulse1; rw [← Equiv.sum_comp s, mul_assoc, Finset.sum_mul]; congr 1; apply sum_congr rfl; intro i _
    rw [show s i=f i from rfl, hu]
    rw [show (exp (I*(k l*z i)))=mode k (z i • step l) by
      unfold mode; simp [Pi.single_apply,mul_ite], ← mode_shift]; congr 1
    simp [z,sub_smul]
  have H := congr_arg (fun x : ℂ => ‖x‖) hb
  simp only [norm_mul,norm_real,Real.norm_of_nonneg (inch_pos L).le, mode_real k _ hk, mul_one] at H
  have hh := pulse_lower hL hk l (preview_coord h _ l)
  rw [← H] at hh
  calc
    (1/16:ℝ)*P.L.val ≤ _ := mul_le_mul_of_nonneg_right hh (show 0 ≤ (P.L.val:ℝ) by positivity)
    _ = _ := by rw [mul_right_comm, inch_unit L,one_mul]
end YM.Stationary
end

/-!
# `coast` price for connector-as-operator. At a fixed shift k in L rows,
use absolute weights once per fixed column and average squared, not an
ℓ² sum over all anchors before projecting. Uniform in P/J pre-L with
joint contour tilt priced only in coarse strip.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {α β γ : Type} [Fintype α] [DecidableEq α] {p q k : Momentum} {σ C A : ℝ}
lemma jensen_bill {ι : Type} [Fintype ι] (w : ι → ℝ) (h : ∀ i,0 ≤ w i) (hp : ∑ i,w i=1) (f : ι → ℝ) :
    (∑ i,w i*f i)^2 ≤ ∑ i,w i*f i^2 := by
  let s := ∑ i,w i*f i
  have ht := Finset.sum_nonneg (s:=univ) (f:=fun i=> w i*(f i-s)^2) fun i _ => mul_nonneg (h i) (sq_nonneg _)
  have he i : w i*(f i-s)^2=w i*f i^2 - (w i*f i)*(2*s)+w i*s^2 := by ring
  simp_rw [he,Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hp] at ht
  unfold s at *; nlinarith only [ht]
lemma odds_bill {ι : Type} [Fintype ι] (w : ι → ℝ) (h : ∀ i,0≤w i) (hp : ∑ i,w i=1) (f : ι→ℂ) :
    ‖∑ i,(w i:ℂ)*f i‖^2 ≤ ∑ i,w i*‖f i‖^2 := by
  have hx (i) : ‖(w i:ℂ)*f i‖=w i*‖f i‖ := by rw [norm_mul,norm_real,Real.norm_of_nonneg (h i)]
  refine (le_trans ?_ (jensen_bill w h hp fun i => ‖f i‖))
  simp_rw [← hx]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2

variable (P)
-- rectangular average at a given (α→orientation) shift

def coast (u : α→Axis) (j : ℕ) (p : Momentum) : CompM α (Co P.L α) :=
    of fun i a => ∑ x,(P.weight x:ℂ)*scrap p (Pi.single a 1) (x.val+j • step (u i)) i
lemma scrap_basis (v : Phase (Co P.L α)) (p : Momentum) (z : Cover) (i) :
    scrap p v z i=∑ j : Co P.L α, scrap p (Pi.single j 1) z i*v j := by simp [scrap,mul_ite,ite_mul,Pi.single_apply]
lemma coast_earn (u : α→Axis) (j : ℕ) (p : Momentum) (v : Phase (Co P.L α)) (i) :
    (coast P u j p*ᵥ v) i=∑ x,(P.weight x:ℂ)*scrap p v (x.val+j • step (u i)) i := by
  conv_rhs => arg 2; intro x; rw [scrap_basis P, Finset.mul_sum]
  unfold coast Matrix.mulVec dotProduct; simp only [Matrix.of_apply, Finset.sum_mul]; rw [sum_comm]
  simp only [mul_assoc]
lemma coast_plays (u : α→Axis) (j : ℕ) : Poster σ (coast P u j) := by
  refine ⟨fun h a b => ?_,fun h _ => Matrix.ext fun i l => ?_⟩
  · unfold coast; simp only [Matrix.of_apply, scrap, mode]
    fun_prop
  unfold coast; simp only [Matrix.of_apply,scrap_reset h]

def coast_tax (j : ℕ) (σ : ℝ) := Real.exp (σ * (4+4*(j+5:ℝ)))
lemma curve_coast (u : α→Axis) (k : ℕ) (hk : k≤P.L.val) (hp : p∈strip σ) : vflux (coast P u k p)≤ coast_tax P.J σ * (inch P.L)^2 := by
  let A := (coast_tax P.J σ)
  have ha : 0<A := Real.exp_pos _
  apply flux_take (mul_nonneg ha.le (sq_nonneg _)) _
  intro v
  apply (pow_le_pow_iff_left₀ (slug_nonneg _) (mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (slug_nonneg _)) (by decide : 2≠0)).1
  have hm i : ∑ x,(P.weight x)* (A^2*‖v (wrap _ (x.val+k • step (u i)),i)‖^2) = A^2*((inch P.L)^4 * ∑ j : Site P.L,‖v (j,i)‖^2) := by
    simp_rw [mul_left_comm (P.weight _) (A^2), ← Finset.mul_sum, map_add]
    exact congr_arg _ (lottery_residue P _ fun r => ‖v (r,i)‖^2)
  have he (i) : ‖(coast P u k p*ᵥ v) i‖^2≤ (A^2*(inch P.L)^4)*∑ j : Site P.L,‖v (j,i)‖^2 := by
    rw [coast_earn, mul_assoc, ← hm i]
    exact (odds_bill P.weight P.weight_nonneg P.weight_sum _).trans (sum_le_sum fun x _ => by
      rw [← mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (scrap_oath P v hp x _ _ hk) _) (P.weight_nonneg _))
  rw [slug_sq]; apply (sum_le_sum fun i _ => he i).trans_eq
  change ∑ i, _= (A*inch P.L^2*slug v)^2
  rw [← Finset.mul_sum, Finset.sum_comm, mul_pow,slug_sq, Fintype.sum_prod_type]; ring

section bond
variable (G)

def meanRay (p : Momentum) := ∑ i : Fin P.L.val,coast P (fun a : Loc G 1 => axisEquiv.symm a.1) i.val p
def jar (p : Momentum) := coast P (fun _ : Loc G 0 => 0) 0 p
lemma jar_plays : Poster σ (jar G P) := coast_plays ..
lemma mean_plays : Poster σ (meanRay G P) := by
  let F := fun i => coast P (fun a : Loc G 1 => axisEquiv.symm a.1) i
  refine ⟨fun h i j => ?_,fun hp h => ?_⟩
  · unfold meanRay; simp_rw [Matrix.sum_apply]
    exact DifferentiableAt.fun_sum fun i _ => (coast_plays ..).shape h _ _
  exact Finset.sum_congr rfl fun i _ => (coast_plays ..).shifts hp h
lemma mean_bills (h : p∈strip σ) : vflux (meanRay G P p)≤ coast_tax P.J σ *inch P.L := by
  let f := fun i : Fin P.L.val => coast P (fun a : Loc G 1 => axisEquiv.symm a.1) i.val p
  let t := coast_tax P.J σ
  have ht (s : Finset (Fin P.L.val)) : vflux (∑ i∈s,f i) ≤ s.card * (t*(inch P.L)^2) := by
    induction s using Finset.induction with
    | empty => simp [flux_zero]
    | insert i s he ih =>
      rw [Finset.sum_insert he,card_insert_of_notMem he,Nat.cast_add_one,add_mul,one_mul,add_comm _ (t*_)]
      exact (flux_plus ..).trans (add_le_add (curve_coast P _ _ i.isLt.le h) ih)
  apply (ht Finset.univ).trans_eq; rw [card_univ, Fintype.card_fin]
  change _ = t*_; linear_combination t*(inch P.L)*(inch_unit P.L)
variable {P G}
lemma jar_aim (l : Site P.L) (u : Phase (Loc G 0)) : jar G P p *ᵥ tiled p l u = rollMean P (aliasAt p l) • u := by
  unfold jar; ext1 i; simp only [coast_earn, scrap_tiled,rollMean,zero_smul,add_zero,Pi.smul_apply,smul_eq_mul,Finset.sum_mul,mul_assoc]

def capBond (k : Momentum) (P : Patch) (i : Loc G 1) := rollMean P k * ∑ j : Fin P.L.val, mode k (j.val • step (axisEquiv.symm i.1) : Cover)
lemma mean_aim (l : Site P.L) (u : Phase (Loc G 1)) : meanRay G P p *ᵥ tiled p l u = fun i => capBond (aliasAt p l) P i * u i := by
  unfold meanRay; rw [sum_mulVec]; ext1 i; rw [Finset.sum_apply]
  simp only [capBond,coast_earn, scrap_tiled, mode_shift, rollMean, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
lemma mean_floor (h : Nave p) (he : star p=p) (v : Phase (Loc G 1)) : (limitMean P.J/16)*P.L.val * slug v ≤ slug (meanRay G P p *ᵥ tiled p 0 v) := by
  rw [mean_aim]
  let u := (limitMean P.J/16)*P.L.val
  have hv : 0≤u := mul_nonneg (div_nonneg (limitMean_pos _).le (by norm_num)) (Nat.cast_nonneg _)
  have ht (i : Loc G 1) : u ≤ ‖capBond (aliasAt p (0:Site P.L)) P i‖ := by
    unfold capBond; rw [norm_mul]
    have heq : u= limitMean P.J*((1/16:ℝ)*P.L.val) := by unfold u; ring
    rw [heq]
    exact mul_le_mul (roll_strict h he) (connector_strict h he _) (by positivity) (norm_nonneg _)
  apply (pow_le_pow_iff_left₀ (mul_nonneg hv (slug_nonneg _)) (slug_nonneg _) (by decide : 2≠0)).1
  rw [mul_pow, slug_sq, slug_sq, mul_sum]
  refine sum_le_sum fun i _ => ?_; simp only [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv (ht i) _) (sq_nonneg _)
end bond
end YM.Stationary
end

/-!
# Arc trace under repacking & product layout. Vertical operator M, cell
indices joined. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {ι α β γ δ j k : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]

-- Beach pairing among two Solids. Used for slab union.
section blocks

def spades (U : CompM α α) (V : CompM β β) := Matrix.fromBlocks U 0 0 V
lemma spades_one : spades (1:CompM α α) (1:CompM β β)=1 := by ext (i|i) (j|j) <;> simp [spades,one_apply]
lemma spade_prod (U X : CompM α α) (V Y : CompM β β) : spades U V * spades X Y=spades (U*X) (V*Y) := by simp [spades,fromBlocks_multiply]
lemma spade_heft (U : CompM α α) (V : CompM β β) : (spades U V)ᴴ=spades Uᴴ Vᴴ := by ext (i|i) (j|j) <;> simp [spades]
lemma spade_slim (U : CompM α α) (V : CompM β β) : (spades U V)ᵀ=spades Uᵀ Vᵀ := by ext (i|i) (j|j) <;> simp [spades]
lemma spade_inv {U : CompM α α} {V : CompM β β} (h : IsUnit U.det) (he : IsUnit V.det) : (spades U V)⁻¹=spades U⁻¹ V⁻¹ := by
  apply inv_eq_right_inv; rw [spade_prod, mul_nonsing_inv _ h,mul_nonsing_inv _ he,spades_one]
lemma spade_spin {U : CompM α α} {V : CompM β β} (h : Skates U) (he : Skates V) : Skates (spades U V) := ⟨by rw [spade_heft,spade_prod,h.slides,he.slides,spades_one]⟩

def Slab.spade (X : Slab α) (Y : Slab β) : Slab (α ⊕ β) where
  tile p := spades (X.tile p) (Y.tile p)
  whole p := by rw [spades, Matrix.det_fromBlocks_zero₁₂]; exact (X.whole _).mul (Y.whole _)
lemma Slab.spadeD (X : Slab α) (Y : Slab β) : (X.spade Y).dual=X.dual.spade Y.dual := by
  unfold dual spade; congr 1; funext p; rw [spade_slim, spade_inv (by rw [det_transpose]; exact X.whole _) (by rw [det_transpose]; exact Y.whole _)]
lemma Slab.Bright.spade {X : Slab α} {Y : Slab β} (h : X.Bright) (he : Y.Bright) : (X.spade Y).Bright := by
  refine ⟨fun hp => ?_⟩
  obtain ⟨U,hU,hx⟩ := (h.pose hp).flee; obtain ⟨V,hV,hb⟩ := (he.pose hp).flee
  exact ⟨_,spade_spin hU hV,by dsimp [Slab.spade]; rw [spade_prod,hx,hb]⟩
lemma spade_assemble (v : Phase (α⊕β)) : v=Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by funext i; cases i <;> rfl
lemma spade_apply (U : CompM α α) (V : CompM β β) (x y) : spades U V*ᵥ Sum.elim x y=Sum.elim (U *ᵥ x) (V *ᵥ y) := by rw [spades, fromBlocks_mulVec]; simp
lemma spade_norm (x : Phase α) (y : Phase β) : slug (Sum.elim x y)^2=slug x^2+slug y^2 := by
  rw [slug_sq,slug_sq,slug_sq,Fintype.sum_sum_type]; rfl
lemma spade_flux {U : CompM α α} {V : CompM β β} {C : ℝ} (h : vflux U≤C) (he : vflux V≤C) : vflux (spades U V)≤C := by
  have hc := (flux_nonneg _).trans h
  refine flux_take hc _ fun v => ?_
  rw [spade_assemble v,spade_apply]
  apply (pow_le_pow_iff_left₀ (slug_nonneg _) (mul_nonneg hc (slug_nonneg _)) (by decide : 2≠0)).1
  rw [spade_norm,mul_pow,spade_norm,mul_add, ← mul_pow,← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (slug_nonneg _) (flux_tester h _) _) (pow_le_pow_left₀ (slug_nonneg _) (flux_tester he _) _)
lemma Slab.serial_spade {X U : Slab α} {Y V : Slab β} {p q} {K H} {C : ℝ} (h : serial X U p q K C) (he : serial Y V p q H C) : serial (X.spade Y) (U.spade V) p q (spades K H) C := by
  unfold serial carryM; dsimp only [spade]; rw [spade_inv (X.whole p) (Y.whole p), spade_prod,spade_prod]; exact spade_flux h he
lemma Slab.Height.spade {X : Slab α} {Y : Slab β} {σ C} (h : X.Height σ C) (he : Y.Height σ C) : (X.spade Y).Height σ C := by
  refine ⟨fun p hp => ?_⟩
  obtain ⟨A,hA,hr,ht⟩ := h.feel p hp; obtain ⟨B,hB,hq,hH⟩ := he.feel p hp
  refine ⟨A.spade B,fun q h (i) (j) => ?_,fun q hp => ?_,fun q hp => ?_⟩
  · cases i <;> cases j <;> first | exact hA q h _ _ | exact hB q h _ _ | exact differentiableAt_const _
  · change spades _ _ = spades _ _; rw [hr _ hp,hq _ hp]
  have hZ := Slab.serial_spade (ht q hp).1 (hH q hp).1; have hu := Slab.serial_spade (ht q hp).2 (hH q hp).2; rw [spades_one] at hZ hu; exact ⟨hZ,hu⟩
lemma Slab.spade_rate (X : Slab α) (Y : Slab β) {p u v} : (X.spade Y).rate p (Sum.elim u v)^2=X.rate p u ^2+Y.rate p v^2 := by
  unfold rate spade; rw [show (({tile:=_,whole:=_} : Slab _).tile p)=spades (X.tile p) (Y.tile p) from rfl,spade_inv (X.whole p) (Y.whole p),spade_apply,spade_norm]
end blocks

section maps
-- matrix packing conventions for two arbitrary Co. X input interleaving. Uses e,g,u **from actual finite labels**
variable [Fintype j] [DecidableEq j] [Fintype k] [DecidableEq k] (e : α ≃ β) (g : γ ≃ δ) (u : j ≃ k) {R : Type} [CommRing R]
def repackM (U : Matrix α γ R) := Matrix.submatrix U e.symm g.symm
lemma repack_multiply (U : Matrix α γ R) (V : Matrix γ j R) : repackM e u (U*V)=repackM e g U*repackM g u V := by
  ext i j
  simp only [repackM,Matrix.submatrix_apply,Matrix.mul_apply]
  exact (Equiv.sum_comp g.symm _).symm
lemma repack_rotate (U : Matrix α γ R) : repackM g e Uᵀ=(repackM e g U)ᵀ := rfl
lemma repack_dot (x y : α→R) : dotProduct x y=dotProduct (x∘e.symm) (y ∘ e.symm) := by unfold dotProduct; rw [← Equiv.sum_comp e.symm]; rfl
lemma repack_act (U : Matrix α γ R) (x : γ→R) : repackM e g U *ᵥ (x ∘ g.symm)=(U *ᵥ x) ∘ e.symm := by
  ext1 i; simp only [Matrix.mulVec,dotProduct,repackM, Matrix.submatrix_apply,Function.comp_apply]; exact Equiv.sum_comp g.symm (fun a => U (e.symm i) a * x a)
lemma repack_det (U : Matrix α α R) : (repackM e e U).det=U.det := by unfold repackM; rw [Matrix.det_submatrix_equiv_self]
lemma repack_unit : repackM e e (1:Matrix α α R)=1 := by ext; simp [repackM, Matrix.one_apply]

end maps
end YM.Stationary
end

/-! # Assemble static color stencils and cross row.
All act on `chargeM` at exactly given period. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L c f n m : Side} {p q r : Momentum}
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {ι j k h : ℕ}

section paint
variable {R : Type} [CommRing R]

def pick (x : Loc G ι → R) (i : G.ColorIndex) (a : TypeFace ι) := x (a,i)
def tintedLocal (G : Gauge) (V : Matrix (TypeFace j) (TypeFace k) R) : Matrix (Loc G j) (Loc G k) R := Matrix.of fun i l => if i.2=l.2 then V i.1 l.1 else 0
lemma tinted_at (V : Matrix (TypeFace j) (TypeFace k) R) (v : Loc G k→R) (a : Loc G j) :
    (tintedLocal G V*ᵥ v) a = (V*ᵥ pick v a.2) a.1 := by
  simp only [Matrix.mulVec,dotProduct,tintedLocal, Matrix.of_apply,Fintype.sum_prod_type]
  simp_rw [ite_mul,zero_mul,sum_ite_eq, Finset.mem_univ,if_true]; rfl
lemma tinted_plus (V W : Matrix (TypeFace j) (TypeFace k) R) : tintedLocal G (V+W)=tintedLocal G V+tintedLocal G W := by ext i j; unfold tintedLocal; by_cases h : i.2=j.2 <;> simp [h]
lemma tinted_pay (V : Matrix (TypeFace j) (TypeFace k) R) (W : Matrix (TypeFace k) (TypeFace h) R) : tintedLocal G (V*W)=tintedLocal G V*tintedLocal G W := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro i; ext1 x; rw [Matrix.toLin'_apply,Matrix.toLin'_apply,tinted_at, ← mulVec_mulVec, ← mulVec_mulVec,tinted_at];
  have he (x : G.ColorIndex) : pick (tintedLocal G W *ᵥ i) x=W *ᵥ pick i x := funext fun y => tinted_at W i (y,x)
  rw [he]
lemma tinted_flip (V : Matrix (TypeFace j) (TypeFace k) R) : tintedLocal G Vᵀ=(tintedLocal G V)ᵀ := by ext i j; simp [tintedLocal,eq_comm]

end paint

def patron (G : Gauge) (V : Matrix (Body j c) (Body k f) ℝ) := billsM (pocket _) (pocket _) (uniformM (G:=G) V)
lemma patron_fee (V : Matrix (Body j c) (Body k f) ℝ) (i : Corn (Lines G f k)) : patron G V *ᵥ i=uniformM V i := bill_pay ..
lemma patron_mul (V : Matrix (Body j c) (Body k f) ℝ) (W : Matrix (Body k f) (Body h m) ℝ) : patron G (V*W)=patron G V*patron G W := by
  apply testers; intro i y
  rw [patron_fee, ← mulVec_mulVec,patron_fee,patron_fee]
  apply congr_arg _; ext1 z; change ((V*W) *ᵥ _) _= (V *ᵥ _) _; rw [← mulVec_mulVec]; rfl
lemma patron_star (V : Matrix (Body j c) (Body k f) ℝ) : patron G Vᵀ=(patron G V)ᵀ := by
  apply testers; intro i l
  conv_rhs => rw [dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [patron_fee,patron_fee,dotColor,dotColor]
  simp_rw [uniformC,dotProduct_mulVec,Matrix.vecMul_transpose]

lemma inflow (V : CompM α β) (u v) : dotProduct u (V *ᵥ (v:Phase β))=dotProduct (Vᵀ *ᵥ (u:Phase α)) v := by rw [dotProduct_mulVec, mulVec_transpose]
lemma Leads.byVec (V : Matrix α β ℝ) : Leads (fun z => approached V *ᵥ z) := by intro i j; dsimp only; rw [mulVec_add,mulVec_smul]
lemma prom_vec (V : Matrix α β ℝ) (p) : approached V*ᵥ axes p=axes (V*ᵥ p) := by ext1 i; simp [Matrix.mulVec,dotProduct,approached,axes]

def shades_of (i : G.ColorIndex) {k : ℕ} : Phase (Lines G m k) →ₗ[ℂ] (Co m (TypeFace k) → ℂ) := LinearMap.pi fun p => LinearMap.proj (p.1,p.2,i)

lemma patron_contract (V : Matrix (Body j c) (Body k f) ℝ) (y : Phase (Lines G f k)) (i : G.ColorIndex) :
    shades_of i (approached (patron G V)*ᵥ y)=approached V *ᵥ (shades_of i y) := by
  refine Leads.buys (p:=fun y => shades_of i (approached (patron G V)*ᵥ y)) (q:=fun y => approached V *ᵥ (shades_of i y)) (fun u v => ?_) (fun u v => ?_) ?_ y
  · simp only [Matrix.mulVec_add,Matrix.mulVec_smul,map_add,map_smul]
  · simp only [Matrix.mulVec_add,Matrix.mulVec_smul,map_add,map_smul]
  intro a
  rw [prom_vec,patron_fee,show shades_of i (axes a)=axes (parts G k (arm _ _ _ a) i) from rfl, prom_vec]; rfl
lemma tune_palette (p : Site m) (V : Phase (Loc G k)) (i) : shades_of (G:=G) i (tune p V)=tune p (pick V i) := rfl

lemma palette_ship (V : Row (TypeFace j) (TypeFace k)) (he : V.safe) :
    Jaunt (approached (patron G (V.acts c))) (fun p => tintedLocal G (V.read p)) 0 := by
  intro p q h w; rw [add_zero]
  ext1 i
  have hm := patron_contract (V.acts c) (tune p w) i.2.2
  rw [tune_palette,Jaunt.row V he _ _ h,add_zero] at hm
  exact (congr_fun hm (i.1,i.2.1)).trans (by change cell p i.1 * _=cell p i.1 * _; rw [tinted_at])

lemma exterior_calm (V : Row (TypeFace j) (TypeFace k)) {σ C : ℝ} (h : V.strip σ C) (hs : 0<σ) : Poster σ fun p => tintedLocal G (V.read p) := by
  refine ⟨fun he a b => ?_, fun hp _ => ?_⟩
  · simp only [tintedLocal,Matrix.of_apply]; split
    exact (Firm.of_series (V.constant_strip h _ _) hs).1.hol _ he
    exact differentiableAt_const _
  obtain ⟨x,rfl⟩ := hp; rw [V.periods]
end YM.Stationary
end
