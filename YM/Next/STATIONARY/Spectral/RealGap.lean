import YM.Next.STATIONARY.Films.Frame


set_option autoImplicit false
/-!
# Hear budgets from weights for entire real arrays; n all ≤ available d. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α β γ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {A : Audience α} {G : Gauge} {P : Patch} {K : KernelChoices} {C D σ : ℝ} {m n : ℕ} {p q : Momentum}

variable {E : Eye ι (Acts G P)} (h : Spotlight P E σ C)
section glow
include h
lemma soft_ears {v : Fin m→ Momentum} {a : Fin m→ι} (he : ∀ i,v i∈ strip σ) {p} (hq : p∈strip σ) {u : Phase (Acts G P)} (hz : Veil C u 1) (F : α→ BassInput G P →ℝ) (hp : Tested A (StaffP G P (muralRoom P.J*C)) F (m+1) D) :
    Hearing A 1 (fun i => beat (F i) 0 (m+1) (Fin.snoc (lens (inviton E a v) v) (imprintsC G P p u))) ((2:ℝ)^(m+1)*D) := by
  let V := lens (inviton E a v) v; let M := imprintsC G P p u
  have hx : ∑ i, (Fin.snoc (fun _ : Fin m => 0) 1 : Fin (m+1) → ℕ) i=1 := by rw [snocked_sum]; simp
  exact Eq.mp (congr_arg (fun x => Hearing A x _ _) hx) (through_charge hp (snockedR (Shiny (StaffP G P (muralRoom P.J*C))) V _ (h.bright_lens v a he) (shiny_steps _ hz (h.brighten hq) : Shiny _ M 1)) (hx.trans_le (by omega)))
lemma weight_staff : 0≤muralRoom P.J*C := mul_nonneg (zero_le_one.trans (mural_one _)) h.full_price
end glow

section prices
lemma prismLite {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {R : X→ℕ→Prop} {u : α→X→G.Color} (h : Gallop A R u n C) (k : G.ColorIndex) : Gallop A R (fun i x => u i x k) n C := by
  obtain ⟨T,ht,hT⟩ := color_beak k
  simp_rw [← ht]; exact (h.line T).raises le_rfl ((mul_le_mul_of_nonneg_right hT h.stamp).trans_eq (one_mul C))
lemma hatch_cost (P : Patch) (i) : (balcony (Site P.L)).weight i ≤ portrait P.J * (balcony P.Points).weight (hatch P i) := by
  change _⁻¹ ≤ portrait _ * _⁻¹
  rw [← div_eq_mul_inv]; have hp : 0 < (Fintype.card P.Points:ℝ) := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hp).mpr; rw [site_card]; push_cast; rw [← inv_pow]; exact medium P
lemma hatch_ears {W : P.Points→ℂ} (h : Hearing (balcony P.Points) n W C) : Hearing (balcony (Site P.L)) n (fun i => W (hatch P i)) (portrait P.J*C) := by
  have ht : Injective (hatch P) := fun i j hx => by rw [← wrap_lift i,← wrap_lift j,show lift i=lift j from congr_arg Subtype.val hx]
  exact Hearing.crops univ _ ht.injOn (painted _) (fun i _ => ⟨le_rfl,hatch_cost _ _⟩) (by simp) h
end prices

def lantern (G : Gauge) (j n : ℕ) (c : ℝ) := Real.sqrt (Fintype.card (Loc G 1))*((2:ℝ)^(n+1)*|springs G j (n+1) (muralRoom j*c)|)
def hatchRate (G : Gauge) (j n : ℕ) (c : ℝ) := (Real.sqrt (Fintype.card (Loc G 0)))*(portrait j*((2:ℝ)^(n+1)*|rocket_fare G j (n+1) (muralRoom j*c)|))

section posts
variable (hp : P.Branches K G)
include hp h
lemma CharterR.costs : Charges (Slab.basic (Loc G 1)) (slabW G P.L) (CharterR false E) σ (feeHead (fun k => lantern G P.J k C)) := by
  classical
  refine serial_caps (CharterR.green _ h.fresh) (fun n _ i v w p ht _ => ?_)
  let F := chartersR false P G; let T := (mentor F E (fun _ => visibly P true)) n v i p
  let y := (2:ℝ)^(n+1)* |springs G P.J (n+1) (muralRoom P.J*C)|
  refine serial.mono (stands_rate T (X:=Slab.basic (Loc G 1)) (C:=lantern G P.J n C) (by unfold lantern; positivity) ?_) (fee_ge (fun k => lantern G P.J k C) ‹n≤2›)
  intro u hu
  have hh (a) : ‖(T*ᵥ u) a‖ ≤ y := by
    have he := wrist_sits (A:=balcony Unit) (n:=n+1) hp ((weight_staff h)) (axisEquiv.symm (a:Loc G 1).1)
    have hi : Tested (balcony Unit) (StaffP G P (muralRoom P.J*C)) (fun _ => F a) (n+1) _ := (prismLite he a.2).reaches _ (by omega) le_rfl
    have hg := soft_ears (a:=i) h w ht (store_mono (seen_affect (P:=P) true (h.brighten ht) hu) h.price) (fun _ : Unit=>F a) (hi.raises (le_abs_self _)) |>.rasp (show 1≤2 by omega)
    rw [show (T*ᵥ u) a=_ from mentors F u a (B:=E) (x:=v) (b:=i) (p:=p) (T:=fun _ => visibly P true)]; simpa using hg
  rw [Slab.basic_rate]; unfold lantern; have hn : 0≤y := by unfold y; positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) hn)
  rw [slug_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hh i) 2)).trans_eq (by simp [y])
lemma Chromatic.costs : Charges (Slab.basic (Co P.L (Loc G 0))) (slabW G P.L) (Chromatic false E) σ ((P.L.val:ℝ)^2*feeHead (fun k => hatchRate G P.J k C)) := by
  classical
  refine serial_caps (Chromatic.green _ h.fresh) (fun n hn i v w p ht _ => ?_)
  let T := (mentor (leafletR false P G) E (fun _ => visibly P true)) n v i p
  refine serial.mono (stands_rate T (X:=Slab.basic (Co P.L (Loc G 0))) (C:=(P.L.val:ℝ)^2*hatchRate G P.J n C) (by have h := painted P.J; unfold hatchRate; positivity) ?_) (mul_le_mul_of_nonneg_left (fee_ge (fun k => hatchRate G P.J k C) hn) (sq_nonneg _))
  intro u hu
  let y := portrait P.J*((2:ℝ)^(n+1)* |rocket_fare G P.J (n+1) (muralRoom P.J*C)|)
  have hy : 0≤ y := by unfold y; apply mul_nonneg (zero_le_one.trans (painted _)); positivity
  have he (a : Loc G 0) : ∑ j : Site P.L, ‖(T *ᵥ u) (j,a)‖^2 ≤ (P.L.val:ℝ)^4*y^2 := by
    have hi := (prismLite (n:=n+1) (rocket_sits hp (weight_staff h)) a.2).reaches _ (by omega : 0<n+1) le_rfl
    let F := fun (i : P.Points) (x : BassInput G P) => rocketBox false x i a.2
    have hg := hatch_ears (soft_ears (a:=i) h w ht (store_mono (seen_affect (P:=P) true (h.brighten ht) hu) h.price) F (hi.raises (le_abs_self _))) |>.ample rfl
    unfold Audience.weightedSum at hg; dsimp only [Audience.balcony] at hg; rw [← mul_sum,inv_mul_le_iff₀ (by positivity [Fintype.card_pos (α:=Site P.L)]),site_card,Nat.cast_pow] at hg
    simp_rw [T,mentors]; exact hg
  rw [Slab.basic_rate]
  apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (sq_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hy))
  rw [slug_sq,Fintype.sum_prod_type, sum_comm]; apply (sum_le_sum (fun i _ => he i)).trans
  change _ ≤ ((P.L.val:ℝ)^2*(Real.sqrt _*y))^2; rw [mul_pow _ (_*y),mul_pow (Real.sqrt _) y,Real.sq_sqrt (Nat.cast_nonneg _)]
  apply le_of_eq; simp only [sum_const, card_univ,nsmul_eq_mul]; ring
end posts
end YM.Stationary
end

/-!
# Uncompleted joint precision symbol: exact identities killing longitudinal.
No orientation simplification of path weights. H may be non-Schwarz away
from real p; strip bindings fixed.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L c : Side} {p q : Momentum} {σ A ε C : ℝ}

lemma coast_orth {i : ℕ} (hp : star p=p) (u : Loc G i → Axis) (P) (n) : (coast P u n (-p))ᵀ=(coast P u n p)ᴴ := by
  ext i j; simp only [Matrix.transpose_apply,Matrix.conjTranspose_apply,coast,Matrix.of_apply,star_sum]
  apply sum_congr rfl; intro a _; simp only [star_mul,scrap,star_inv₀,mode_inverse]
  have hx (x : Cover) : star (mode p x)=(mode p x)⁻¹ := by simpa only [hp,mode_opposite] using mode_adjoint p x
  simp only [hx,Pi.single_apply,Complex.star_def,conj_ofReal,apply_ite conj]; split <;> simp [mul_comm]
lemma coast_alive (h : star p=p) : (netY G P (-p))ᵀ=(netY G P p)ᴴ := by
  unfold netY; rw [transpose_add,Matrix.transpose_mul,Matrix.transpose_neg,Matrix.transpose_mul,page_rear 0 h,Matrix.conjTranspose_add,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, downX_star,downY_star]; congr 2
  simp only [meanRay,transpose_sum,Matrix.conjTranspose_sum,coast_orth h]
lemma road_bill : Poster σ (netY G P) := by
  let Z := meanRay G P
  have h : Poster σ (-Z) := by
    convert (Poster.plus_nec (mean_plays G P) (-1)) using 1
    simp [Z]
  exact (h.forge (Poster.web _)).amounts ((page_linen _).forge (Poster.web _))
lemma gift_lane (B : Bed) (w) (h : B.metric.strip (inch P.L*σ) A) (hp : 0<σ) : Poster σ (giftQ G P B w) := by
  have hh : Poster σ (netY G P) := road_bill
  exact (((Poster.web (downX G P.L)ᵀ).forge (Poster.furnish_ok (rug_played B h (mul_pos (inch_pos _) hp)))).forge (Poster.web _)).amounts ((hh.reverse.forge hh).plus_nec _)
lemma shade_lane : Poster σ (shadeR G P) :=
    ((Poster.web (-(downX G P.L)ᵀ)).forge ((page_linen _).furnish_ok)).shares ((Poster.web (downY G P.L)ᵀ).forge (jar_plays _ _))

-- Poster real hermitian extension
lemma poster_adjoint {α : Type} [Fintype α] [DecidableEq α] (m : ℕ→Side) (hm : Tendsto (fun i=> (m i).val) atTop atTop) {K : Momentum→CompM α α}
    {X : ∀ i, Matrix (Co (m i) α) (Co (m i) α) ℝ} (h : ∀ i,Jaunt (approached (X i)) K 0) (hs : 0<σ) (hp : Poster σ K) (he : ∀ i,(X i)ᵀ=X i) {p} (hv : star p=p) : (K p)ᴴ=K p := by
  have hu i (a : Site (m i)) (q : Momentum) (heq : rolls (mon a) q) : (K q)ᴴ=K q := by
    have hi := h i
    let M := approached (X i)
    have ht : Jaunt M K 0 := h i
    have hh : Mᵀ=M := by rw [show Mᵀ=approached (X i)ᵀ from rfl,he]
    have hw := ht.takes; rw [hh] at hw
    have hh' : K q=(K (-q))ᵀ := ht.offset hw q heq
    -- actual matrix is REAL. recover negative after polarSign
    have hg (x : Phase α) : star (K q *ᵥ x)=K (-q) *ᵥ star x := by
      apply (ray_pick (α:=α) (-a))
      have hx := ht a q heq x; rw [add_zero] at hx
      have hy := ht (-a) (-q) heq.flip_sign (star x); rw [add_zero] at hy
      rw [← starlight, ← hx,← hy,← starlight,Matrix.star_mulVec]
      have hh : Mᴴ = Mᵀ := (prom_adj _).symm
      rw [hh, vecMul_transpose]
    ext m n
    have he : star (K q n m)=K (-q) n m := by
      let b : Phase α := Pi.single m 1
      have hB : star b=b := by funext i; by_cases h : i=m <;> simp [b, *]
      have hb : star (K q*ᵥ b)=K (-q) *ᵥ b := by rw [hg,hB]
      simpa [b,mulVec_single] using congr_fun hb n
    simp only [Matrix.conjTranspose_apply]; rw [he]; exact (congr_fun (congr_fun hh' m) n).symm
  obtain ⟨k,z,hz,hy⟩ := mesh_stride m hm p hv
  ext i j
  have hi : ContinuousAt (fun p => star (K p j i)) p := (hp.shape (Work.F07.realStrip _ hs hv) j i).continuousAt.star
  have hh : ContinuousAt (fun p => K p i j) p := (hp.shape (Work.F07.realStrip _ hs hv) i j).continuousAt
  exact tendsto_nhds_unique_of_eventuallyEq (hi.tendsto.comp hz) (hh.tendsto.comp hz) (Eventually.of_forall fun a => congr_fun (congr_fun (hu a (k a) (z a) (hy a)) i) j)

lemma bound_rug {B : Bed} {w : Clip} (hS : 0<σ) (hM : B.metric.strip σ A) (hp : ∀ n, Floor B w n ε C) (h : star p=p) : (rug G B p)ᴴ=rug G B p := by
  let X i := patron G (Precision.K (B.metric.acts (walent i)))
  refine poster_adjoint walent walentes (X:=X) (fun i => rug_plane _ _ (B.metric.rights _ _ hM hS.le)) hS (rug_played B hM hS) ?_ h
  intro i; unfold X Precision.K; rw [← patron_star,transpose_mul,transpose_mul,transpose_transpose,(hp _).symmetric.1, Matrix.mul_assoc]
lemma gift_herm {B : Bed} {w : Clip} (κ : ℝ) (hs : 0<σ) (he : B.metric.strip σ A) (hp : ∀ n, Floor B w n ε C) (h : star p=p) : (giftQ G P B κ p)ᴴ=giftQ G P B κ p := by
  let t := P.L
  have ht : (posterBlock t (rug G B) p)ᴴ=posterBlock t (rug G B) p := by
    ext ⟨i,j⟩ ⟨b,a⟩
    simp only [posterBlock,Matrix.conjTranspose_apply,fiber, Matrix.of_apply]; by_cases H : i=b
    · subst b; simp only [↓reduceIte]; exact congr_fun (congr_fun (bound_rug (G:=G) hs he hp (p:=aliasAt p i) (by rw [← alias_conj,h])) j) a
    rw [if_neg H, if_neg (Ne.symm H),star_zero]
  let X := plankTile t (Loc G 1) p
  have hh : Skates X := tile_ice h
  have hz : (furnish t (rug G B) p)ᴴ=furnish t (rug G B) p := by
    unfold furnish; rw [conjTranspose_mul, conjTranspose_mul]; unfold X at hh; rw [hh.reverse, ht, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hx := coast_alive (G:=G) (P:=P) h
  unfold giftQ; rw [hx,downX_star, Matrix.conjTranspose_add,conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hz, Matrix.conjTranspose_conjTranspose]; simp only [Complex.star_def, Complex.conj_ofReal, Matrix.mul_assoc, Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rfl
end YM.Stationary
end

/-!
# Choose high representative by adding gauge with full completed cost.

Identity `gift_mute` complex by symbol calculus (from patch analytic
receipts for evaluation later). Does not spend a power of volume/L at this stage.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L : Side} {p q : Momentum} {σ A κ : ℝ}

lemma rent_appeal (k : Momentum) (a : Axis) (n : ℕ) : (∑ i : Fin n, mode k (i.val • step a))*Exterior.q k a = Exterior.q (n • k) a := by
  have hi (p : Momentum) : Exterior.q p a = mode p (step a)-1 := by unfold Exterior.q; rw [factor]
  rw [hi,hi,mode_scale]
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last,succ_nsmul,mode_shift,add_mul,IH]; ring
lemma rent_cloak (l : Site P.L) (i : Loc G 1) : capBond (aliasAt p l) P i * Exterior.q (aliasAt p l) (axisEquiv.symm i.1) = rollMean P (aliasAt p l)*Exterior.q p (axisEquiv.symm i.1) := by
  rw [capBond,mul_assoc, rent_appeal,Bloch.alias_scale]; unfold Exterior.q; rw [← factor,← factor,mode_phase,mode_periodic,mul_one]
lemma curtain (p : Momentum) (x : Phase (Loc G 0)) (a : Loc G 1) : (pageD G 0 p *ᵥ x) a=Exterior.q p (axisEquiv.symm a.1)*x (vac,a.2) := by
  unfold pageD; rw [tinted_at]; unfold Matrix.mulVec dotProduct; rw [Finset.sum_eq_single vac]
  ·
    conv_lhs => rw [show a.1=coord (axisEquiv.symm a.1) from (axisEquiv.apply_symm_apply a.1).symm]
    simp only [sym_one]; rfl
  · intro i _ h; exact False.elim (h (vac_only i))
  simp
lemma mean_stern (p : Momentum) : (meanRay G P p)*(furnish P.L (pageD G 0) p)=pageD G 0 p*jar G P p := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; rw [Matrix.toLin'_apply,Matrix.toLin'_apply]
  rw [← alias_pack p x, Matrix.mulVec_sum, Matrix.mulVec_sum]; refine sum_congr rfl fun i _ => ?_
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, furnish_gear, mean_aim, jar_aim]; ext1 a
  simp only [Matrix.mulVec_smul,Pi.smul_apply,curtain,smul_eq_mul]; rw [← mul_assoc, rent_cloak,mul_assoc]; ring
lemma rug_blind (B : Bed) (p) : furnish P.L (rug G B) p*furnish P.L (pageD G 0) p=0 := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro v; rw [Matrix.toLin'_apply,Matrix.toLin'_apply]
  rw [← alias_pack p v, Matrix.mulVec_sum, Matrix.zero_mulVec]; apply sum_eq_zero; intro i _
  rw [← Matrix.mulVec_mulVec, furnish_gear,furnish_gear, Matrix.mulVec_mulVec]
  rw [rug, Matrix.mul_assoc ((pageD G 1 _)ᵀ* tessH _ _ _), page_zero, Matrix.mul_zero, zero_mulVec]; funext a; simp [tiled]
lemma net_blind (p : Momentum) : netY G P p*shadeR G P p=0 := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply,← Matrix.mulVec_mulVec,shade_split,net_split, Matrix.mulVec_neg, Matrix.mulVec_neg, zero_mulVec, mulVec_mulVec,mulVec_mulVec,mean_stern,sub_self]
lemma gift_mute (B : Bed) (p κ) : giftQ G P B κ p*shadeR G P p=0 := by
  have h : downX G P.L*shadeR G P p= -furnish P.L (pageD G 0) p := by
    apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, shade_split,neg_mulVec]; unfold downX; rw [sliceX]; rfl
  unfold giftQ; rw [Matrix.add_mul,Matrix.smul_mul, Matrix.mul_assoc (_ * _),h,Matrix.mul_neg, Matrix.mul_assoc, rug_blind, Matrix.mul_zero,neg_zero, Matrix.mul_assoc,net_blind,Matrix.mul_zero,smul_zero,add_zero]

lemma printer_ramp (P : Patch) (h : Nave p) {l : Site P.L} (hp : l≠0) : 2*inch P.L ≤ shadeK (aliasAt p l) := by
  have he := pdist_pos hp
  have hx : (1:ℝ) ≤ pdist l := by exact_mod_cast he
  exact (le_mul_of_one_le_right (by positivity [inch_pos P.L]) hx).trans (h.heights hp P.odd_side)

/-- Representative estimate existence and zero of χ. -/
lemma greenroom (G : Gauge) (P : Patch) (h : Nave p) (he : star p=p) (v : Phase (ParcelG G P.L)) :
    ∃ a : Phase (Co P.L (Loc G 0)), ∃ b : Phase (Co P.L (Loc G 1)),
       v-shadeR G P p *ᵥ a=Sum.elim (plankTile P.L (Loc G 1) p*ᵥ b) 0 ∧
        ∀ i≠0,(pageD G 0 (aliasAt p i))ᴴ *ᵥ stackSlice i b=0 := by
  let u := downX G P.L*ᵥ v
  let r := downY G P.L*ᵥ v
  let H := jar G P p
  let K i := aliasAt p (i:Site P.L)
  let T := plankTile P.L (Loc G 0) p
  let U := plankTile P.L (Loc G 1) p
  let x := crewAlias p u
  classical
  have hp (i : Site P.L) : ∃ z : Phase (Loc G 0), i ≠ 0 → (pageD G 0 (K i))ᴴ *ᵥ (stackSlice i x + pageD G 0 (K i)*ᵥ z)=0 := by
    by_cases hZ : i=0
    · exact ⟨0,by simp [hZ]⟩
    have hi := (lt_of_lt_of_le (by positivity [inch_pos P.L]) (printer_ramp P h hZ) : 0<shadeK (K i))
    obtain ⟨z, hz⟩ := padlock (p:=K i) (by unfold K; rw [← alias_conj,he]) hi.ne' (stackSlice i x)
    exact ⟨z,fun _ => hz⟩
  choose z hz using hp
  let A (i : Co P.L (Loc G 0)) := z i.1 i.2
  let d := (inch P.L:ℂ)^2 * rollMean P (K 0)
  let M := T *ᵥ A
  let c : Phase (Loc G 0) := (-r - H*ᵥ M)
  have ht : rollMean P (K 0)≠0 := norm_pos_iff.mp ((limitMean_pos _).trans_le (roll_strict h he))
  have hu : d≠0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (inch_pos P.L).ne')) ht
  let Y := A+partitionA (L:=P.L) 0 (d⁻¹ • c)
  let B := x + posterBlock P.L (pageD G 0) p *ᵥ Y
  let y := T *ᵥ Y
  have hH : r+H*ᵥ y=0 := by
    unfold y Y; rw [mulVec_add, Matrix.mulVec_add H,tile_part, Matrix.mulVec_smul, jar_aim]
    rw [smul_smul,show (inch P.L:ℂ)^2*_=d from rfl, smul_smul,mul_inv_cancel₀ hu,one_smul]
    change r+(H*ᵥ M+c)=_; unfold c; abel
  refine ⟨y,B,?_,fun i hi => ?_⟩
  · rw [shade_split, ← show Sum.elim u r=v from downXY v];
    have hu' : U*ᵥ x=u := tile_crew u
    have ht : furnish P.L (pageD G 0) p *ᵥ y= U *ᵥ (posterBlock P.L (pageD G 0) p *ᵥ Y) := funds_tile ..
    change Sum.elim u r - Sum.elim (-_) (-_)=Sum.elim (U *ᵥ B) _; rw [ht,show U *ᵥ B=u+U *ᵥ (posterBlock P.L (pageD G 0) p*ᵥ Y) by unfold B; rw [mulVec_add,hu']]
    ext1 i; cases i with
    | inl j => simp
    | inr j => simp; exact congr_fun hH j
  rw [show stackSlice i B = stackSlice i x + stackSlice i (posterBlock P.L (pageD G 0) p*ᵥ Y) from rfl,posterBlock_at];
  rw [show stackSlice i Y=z i by funext j; simp [stackSlice,Y,partitionA, Ne.symm hi,A]]; exact hz i hi
end YM.Stationary
end

/-!
# Tilt price of the mean and quotient floor estimate. Uniform BOTH
weights and true representative at … Not assuming rank shell.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L c : Side} {p q : Momentum} {σ κ ε D A C : ℝ}

section tilt

def coreCost (j : ℕ) (σ : ℝ) := coast_tax j σ*Real.exp (σ*4)

lemma topPay (h : p∈strip σ) : serial (Slab.basic _) (altarTile P.L (Loc G 1)) p p (meanRay G P p) (coreCost P.J σ) := by
  have he : serial (Slab.basic _) (Slab.basic _) p p (meanRay G P p) (coast_tax P.J σ*inch P.L) := by unfold serial carryM; simp only [Slab.basic, inv_one,Matrix.one_mul,Matrix.mul_one]; exact mean_bills G P h
  have H := he.bond (cruise p h); rw [Matrix.mul_one] at H; refine H.mono (le_of_eq ?_); unfold coreCost; field_simp [inch_pos P.L|>.ne']
end tilt

-- abstract estimate sums real all nonprincipal. Explicit budget
section high
def highCost {G : Gauge} (p : Momentum) (v : Phase (Co L (Loc G 1))) :=
    ∑ i ∈ univ.erase (0:Site L), hill p i^2*slug (stackSlice i v)^2

def broad (G : Gauge) (P : Patch) (p : Momentum) (v : Phase (Co P.L (Loc G 1))) : Phase (ParcelG G P.L) := Sum.elim (plankTile P.L (Loc G 1) p*ᵥ v) 0
lemma turf_norm (v : Phase (Co P.L (Loc G 1))) : (slabW G P.L).rate p (broad G P p v) ^2=highCost p v + hill p (0:Site P.L)^2 * slug (stackSlice 0 v)^2 := by
  unfold slabW broad; rw [Slab.spade_rate, Slab.basic_rate, slug_zero,rate_sq_tile, zero_pow (by decide),add_zero]; exact (Finset.sum_erase_add _ _ (mem_univ _)).symm
lemma broad_mean (p : Momentum) (v : Phase (Co P.L (Loc G 1))) : slug (netY G P p*ᵥ broad G P p v)=slug (meanRay G P p *ᵥ (plankTile _ _ p*ᵥ v)) := by rw [broad, net_split, mulVec_zero,zero_sub,slug_neg]
lemma lower_grain (B : Bed) (p : Momentum) (κ : ℝ) (hp : star p=p) (v : Phase (Co P.L (Loc G 1))) :
    let z := broad G P p v
    (dotProduct (star z) (giftQ G P B κ p *ᵥ z)).re= ∑ i : Site P.L, (dotProduct (star (stackSlice i v)) (rug G B (aliasAt p i) *ᵥ stackSlice i v)).re
         + κ * slug (netY G P p *ᵥ z)^2 := by
  intro z; have hz : downX G P.L*ᵥ z= plankTile _ _ p*ᵥ v := by unfold downX; rw [sliceX]; rfl
  unfold giftQ
  rw [add_mulVec,dotProduct_add, Matrix.smul_mulVec,dotProduct_smul,coast_alive hp,← mulVec_mulVec z _ (netY _ _ p),vested,slug_self, Complex.add_re, smul_eq_mul, Complex.mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero]
  rw [downX_star,← mulVec_mulVec, ← mulVec_mulVec, vested, hz,sleeve p hp]; rw [re_sum]; simp_rw [crew_tile]

lemma hot (B : Bed) {w : Clip} (hp : star p=p) (h : Nave p) (hs : 0<σ) (hε : 0<ε) (hu : B.metric.strip σ A)
    (he : ∀ n, Floor B w n ε D) (v : Phase (Co P.L (Loc G 1))) (hv : ∀ i≠0,(pageD G 0 (aliasAt p i))ᴴ *ᵥ stackSlice i v=0) :
    (ε/2)*highCost p v ≤ ∑ i : Site P.L, (dotProduct (star (stackSlice i v)) (rug G B (aliasAt p i) *ᵥ stackSlice i v)).re := by
  let F (i : Site P.L) := rug G B (aliasAt p i)
  have ht i : star (aliasAt p i)=aliasAt p (i:Site P.L) := by rw [← alias_conj,hp]
  unfold highCost; rw [mul_sum];
  apply le_trans ?_ (sum_le_sum_of_subset_of_nonneg (Finset.erase_subset (0:Site P.L) univ) (fun i _ _ => (mul_nonneg hε.le (sq_nonneg _)).trans (rug_test hu hs he (ht i) _)))
  refine sum_le_sum fun i hi => ?_
  have hz := (Finset.mem_erase.mp hi).1
  let s := stackSlice i v
  have hx := rug_test hu hs he (ht i) s
  have hD := pure_grade (ht i) G s
  have hb : (pageD G 0 (aliasAt p i))ᴴ *ᵥ s=0 := hv _ hz
  rw [hb,slug_zero,zero_pow (by decide),zero_add,mul_pow] at hD
  rw [hD] at hx
  have hH := printer_ramp P h hz
  have hR := hill_sq p i
  have hu : hill p i^2 ≤ 2*(shadeK (aliasAt p i))^2 := by nlinarith [inch_pos P.L]
  refine le_trans ?_ hx; change ε/2*(hill p i^2*slug s^2)≤_
  calc
    _ ≤ ε/2 * ((2*(shadeK (aliasAt p i))^2)*slug s^2) := by gcongr
    _ = _ := by ring

lemma mean_ess (p : Momentum) (he : star p=p) (hv : Nave p) (v : Phase (Co P.L (Loc G 1))) :
    let M := meanRay G P p
    let T := plankTile P.L (Loc G 1) p
    let Z := stackSlice 0 v
    ((limitMean P.J/16*inch P.L)*slug Z)^2 ≤ 2*slug (M*ᵥ (T*ᵥ v))^2 + 2*(coreCost P.J 1)^2 * highCost p v := by
  intro M T Z
  let A := partitionA (L:=P.L) 0 Z
  have hx : (limitMean P.J/16*inch P.L)*slug Z≤ slug (M*ᵥ (T*ᵥ A)) := by
    have H : T*ᵥ A=(inch P.L:ℂ)^2 • tiled p (0:Site P.L) Z := tile_part ..
    rw [H,mulVec_smul,slug_scale,norm_pow, norm_real, Real.norm_of_nonneg (inch_pos _).le]
    apply (mul_le_mul_of_nonneg_left (mean_floor hv he Z) (sq_nonneg (inch P.L))).trans'
    apply le_of_eq; linear_combination -limitMean P.J/16*(inch P.L)*slug Z*(inch_unit P.L)
  let Y := v-A
  have ht : ((altarTile P.L (Loc G 1)).rate p (T*ᵥ Y))^2=highCost p v := by
    unfold T; rw [rate_sq_tile, ← Finset.sum_erase_add _ _ (a:=0) (Finset.mem_univ _), show stackSlice 0 Y=0 by
      funext i; simp [stackSlice,Y,A,Z,partitionA], slug_zero,zero_pow (by decide),mul_zero,add_zero]
    refine sum_congr rfl fun i hi => ?_; have he := (Finset.mem_erase.mp hi).1; rw [show stackSlice i Y=stackSlice i v by funext j; simp [stackSlice,Y,A,partitionA,Ne.symm he]]
  have hμ : 0≤limitMean P.J/16*inch P.L*slug Z := by have he := limitMean_pos P.J; have hv := inch_pos P.L; have hp := slug_nonneg Z; positivity
  have ha := Slab.serial_at (topPay (G:=G) (P:=P) (Work.F07.realStrip _ zero_lt_one he)) (T*ᵥ Y)
  rw [Slab.basic_rate] at ha
  have hp := pow_le_pow_left₀ (slug_nonneg _) ha 2
  rw [mul_pow,ht] at hp
  have hv : M *ᵥ (T*ᵥ A)=M *ᵥ (T*ᵥ v)+ -(M *ᵥ (T*ᵥ Y)) := by unfold Y; simp_rw [mulVec_sub]; abel
  rw [hv] at hx
  have hm := hx.trans (slug_plus ..); rw [slug_neg] at hm
  change slug (M *ᵥ (T *ᵥ Y))^2≤ _ at hp
  nlinarith only [hm,hμ,sq_nonneg (slug (M*ᵥ (T*ᵥ v))-slug (M*ᵥ (T*ᵥ Y))),hp]
end high
end YM.Stationary
end

/-!
# Uniform quotient floor (real W). Includes p=0. Full gap adds the analytic
square estimate AND cost of RΓ^{-1}. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Tree
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L c : Side} {p q : Momentum} {σ A ε C D κ : ℝ}
private lemma account_fee (v u X Y Z : ℝ) (hv : 0<v) (hu : 0<u) (hX : 0≤X) (hY : 0≤Y) (hZ : 0 ≤ Z) :
    ∃ k : ℝ, 0<k ∧ ∀ a b c d p, 0≤a → 0≤b → d ≤ a+X*c → c≤Y*a+Z*b → v*a+u*b ≤ p → k*d≤p := by
  let K := max ((1+X*Y)/v) (X*Z/u)
  have hK : 0<K := lt_of_lt_of_le (by positivity : 0<(1+X*Y)/v) (le_max_left ..)
  refine ⟨K⁻¹, inv_pos.mpr hK, fun a b c d p ha hb he hx hp => ?_⟩
  rw [inv_mul_eq_div, div_le_iff₀ hK]
  calc
    _ ≤ (1+X*Y)*a+(X* Z)*b := by nlinarith [mul_le_mul_of_nonneg_left hx hX]
    _ ≤ (K*v)*a+(K*u)*b := add_le_add (mul_le_mul_of_nonneg_right ((div_le_iff₀ hv).mp (le_max_left ..)) ha) (mul_le_mul_of_nonneg_right ((div_le_iff₀ hu).mp (le_max_right ..)) hb)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hp hK.le]

lemma sterling (h : Nave p) (L : Side) : hill p (0:Site L)^2 ≤ ((2*Real.pi)^2+1)*(inch L)^2 := by
  rw [hill_sq]; have hy := h.preview (L:=L); have hp := pow_le_pow_left₀ (slug_nonneg _) hy 2; unfold shadeK; nlinarith
lemma through_quotient (G : Gauge) (J : ℕ) (κ ε : ℝ) (h : 0<κ) (he : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ (P : Patch), P.J=J → ∀ (B : Bed) (c : Clip) (σ A C : ℝ), 0<σ → B.metric.strip σ A → (∀ n,Floor B c n ε C) →
    ∀ p : Momentum, Nave p → star p=p → ∀ v : Phase (ParcelG G P.L), ∃ u : Phase (Co P.L (Loc G 0)),
      η * ((slabW G P.L).rate p (v-shadeR G P p*ᵥ u))^2 ≤ (dotProduct (star v) (giftQ G P B κ p*ᵥ v)).re := by
  let l := limitMean J/16
  let x := ((2*Real.pi)^2+1)/l^2
  let y := 2 * coreCost J 1 ^2
  have hl : 0<l := div_pos (limitMean_pos J) (by norm_num)
  obtain ⟨η,hs,hK⟩ := account_fee (ε/2) κ x y 2 (by linarith) h (by unfold x; positivity) (by unfold y; positivity) (by norm_num)
  refine ⟨η,hs,fun P hP B c σ A C ht hk hz p hw hv v => ?_⟩
  obtain ⟨u,b,hb,hB⟩ := greenroom G P hw hv v
  let R := shadeR G P p; let M := giftQ G P B κ p
  let z := v-R*ᵥ u
  let Q := (slabW G P.L)
  have hZ : z=broad G P p b := hb
  have hu : Mᴴ=M := gift_herm _ ht hk hz hv
  have h' : M*ᵥ (R*ᵥ u)=0 := by rw [mulVec_mulVec, gift_mute,zero_mulVec]
  have hW : dotProduct (star z) (M*ᵥ z)=dotProduct (star v) (M*ᵥ v) := by
    unfold z; rw [Matrix.mulVec_sub,h',sub_zero,star_sub,sub_dotProduct]
    have he : dotProduct (star (R*ᵥ u)) (M*ᵥ v)=0 := by nth_rewrite 1 [← hu]; rw [vested, h',star_zero,zero_dotProduct]
    rw [he, sub_zero]
  refine ⟨u, ?_⟩
  change η * (Q.rate p z)^2 ≤ (dotProduct (star v) (M*ᵥ v)).re
  rw [← hW,hZ, show M=giftQ G P B κ p from rfl,lower_grain _ _ _ hv]
  let Z := slug (stackSlice 0 b)
  let μ := inch P.L
  apply hK (highCost p b) (slug (netY G P p*ᵥ broad G P p b)^2) ((l*μ*Z)^2)
  · unfold highCost; positivity
  · positivity
  · rw [show Q=slabW G P.L from rfl,turf_norm]; apply add_le_add_right
    change _ * Z^2 ≤ _
    calc
      _ ≤ (((2*Real.pi)^2+1)*μ^2)*Z^2 := mul_le_mul_of_nonneg_right (sterling hw _) (sq_nonneg _)
      _ = _ := by unfold x; field_simp
  · rw [broad_mean]; unfold l y μ Z; rw [← hP]; have hy := mean_ess (P:=P) p hv hw b; linarith only [hy]
  exact add_le_add_left (hot B hv hw ht he hk hz b hB) _
end YM.Stationary
end

/-!
# Γ scales (modified full-site). Acts on aliases at p.
One must condition inverse on tight width, not just qualitative Poster equality.
Actually this analytic symbol has no poles on lattice real p; for `poster`s
we'll retain only where the MASS denominator has no pole. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {L c f : Side} {p q r : Momentum} {σ A C μ : ℝ}

def soda (μ : ℝ) (p : Momentum) := stone p+(μ:ℂ)^2
def damp (μ : ℝ) (p : Momentum) := (μ:ℂ)^2 * (soda μ p)⁻¹
def satin (μ : ℝ) (p : Momentum) := (μ:ℂ)^2 * damp μ p^9
def throne (μ : ℝ) (p : Momentum) := stone p+satin μ p

lemma tonic_symbol (S : Side) : Jaunt (approached (tonic (1:Config G S))) (fun p => stone p • 1) 0 := by
  have ht := page_read (G:=G) S 0
  rw [tonic,mailed_zero,transpose_neg,Matrix.mul_neg,Matrix.neg_mul,neg_neg,prom_mul]
  convert ht.takes.hoist ht using 1; try rfl
  exact funext fun _ => (codex_value _).symm

-- use inverse calculus with ACTUAL meshes at all p.
lemma prom_one' {α : Type} [DecidableEq α] : approached (1:Matrix α α ℝ)=1 := by ext; simp [approached,Matrix.one_apply,apply_ite ((↑):ℝ→ℂ)]
lemma tonic_soda (S : Side) : Jaunt (approached (ammo μ (1:Config G S))) (fun p => soda μ p • 1) 0 := by
  rw [ammo,prom_addition,prom_tone,prom_one',Complex.ofReal_pow]
  convert (tonic_symbol (G:=G) S).plus (Jaunt.noop (m:=S) |>.smul ((μ:ℂ)^2)) using 1; ext1 p; simp only [Pi.add_apply,Pi.smul_apply,soda,add_smul]
lemma soda_ne (h : 0<μ) (he : star p=p) : soda μ p≠0 := by
  unfold soda; rw [stone_real he,← Complex.ofReal_pow,← Complex.ofReal_add]; exact_mod_cast (peb_pos p h).ne'
lemma inverse_stamp (a : ℂ) {α : Type} [DecidableEq α] [Fintype α] (h : a≠0) : (a • (1:CompM α α))⁻¹=a⁻¹ • 1 := by
  apply inv_eq_right_inv; rw [Matrix.mul_smul,Matrix.mul_one,smul_smul,inv_mul_cancel₀ h,one_smul]
lemma tonic_pebble (S : Side) (h : 0<μ) : Jaunt (approached (pebble μ (1:Config G S))) (fun p => damp μ p • 1) 0 := by
  let K := ammo μ (1:Config G S)
  have hv : IsUnit K.det := Ne.isUnit (ammo_safe (1:Config G S) h).det_pos.ne'
  have ht : IsUnit (approached K).det := cash_safe (U:=fun _ : Corn (Fin 1) => K) hv
  have hh := (tonic_soda (μ:=μ) (G:=G) S).backway ht
  have hp : approached (pebble μ (1:Config G S))=(μ:ℂ)^2 • (approached K)⁻¹ := by
    rw [pebble,prom_tone, ofReal_pow]; exact congr_arg ((μ:ℂ)^2 • ·) (card_flip (U:=fun _ : Corn (Fin 1) => K) hv)
  intro p q he v; rw [hp,smul_mulVec, hh p q he]; dsimp only; rw [inverse_stamp _ (soda_ne h (he.metric (real_frequency p))), smul_mulVec, Matrix.one_mulVec];
  ext1 i; simp [tune,damp,Matrix.smul_mulVec]; ring
lemma tonic_cannon (S : Side) (h : 0<μ) : Jaunt (approached (cannon μ (1:Config G S))) (fun p=> satin μ p • 1) 0 := by
  let K := pebble μ (1:Config G S)
  have hp (n : ℕ) : Jaunt (approached (K^n)) (fun p => damp μ p^n • 1) 0 := by
    induction n with
    | zero => simp_rw [pow_zero,one_smul,prom_one']; exact Jaunt.noop
    | succ i IH => rw [pow_succ,prom_mul]; convert IH.hoist (tonic_pebble (G:=G) S h) using 1; ext1 p; rw [Matrix.mul_smul,mul_one,smul_smul,pow_succ,mul_comm];
  rw [cannon,prom_tone,ofReal_pow]; convert (hp 9).smul ((μ:ℂ)^2) using 1; ext1 p; simp only [Pi.smul_apply,satin,smul_smul]
lemma tonic_throne (S : Side) (h : 0<μ) : Jaunt (approached (grenade μ (1:Config G S))) (fun p=> throne μ p • 1) 0 := by rw [grenade,prom_addition]; convert (tonic_symbol (G:=G) S).plus (tonic_cannon S h) using 1; ext1 p; simp [throne,add_smul]

-- qualitative transfer to cover just continuous at reals. Use poster existential width postL; won't use for bounding Kin. Can compare by continuity and rolls front all p, even if exponent unavailable.
lemma soda_roll (hp : rolls p q) : soda μ p=soda μ q := by
  unfold soda; congr 1; unfold stone dotProduct; refine sum_congr rfl fun i _ => ?_
  simp only [Exterior.q,← factor,hp.exp,hp.neg.exp]
lemma throne_roll (hp : rolls p q) : throne μ p=throne μ q := by have h1 := soda_roll (μ:=μ) hp; unfold throne satin damp; rw [h1, show stone p=stone q from add_right_cancel h1]

end YM.Stationary
end

/-!
# Gauge regulator real-strict relative. Alias-unit orientations retained,
choose `soda` NOT `G_g` mass in S(T) candidate. Supports harmonic. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {L : Side} {p q : Momentum} {μ κ : ℝ}

-- real cost intake
private lemma terrain_min (x : ℝ) (h : 0≤x) (he : 0<μ) :
    (1/(2^10):ℝ)*(x+μ^2) ≤ x+μ^2*(μ^2*(x+μ^2)⁻¹)^9 := by
  have hp : 0 < x+μ^2 := by positivity
  by_cases hm : x < μ^2
  · have hv : (1/2:ℝ) ≤ μ^2*(x+μ^2)⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hp]; linarith
    have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0≤(1/2:ℝ)) hv 9) (sq_nonneg μ); linarith
  push Not at hm; have ht : 0≤ μ^2*(μ^2*(x+μ^2)⁻¹)^9 := by positivity
  linarith
lemma throne_pays (hp : star p=p) (he : 0<μ) :
    (1/(2^10):ℝ)*pebWeight p μ ≤ ‖throne μ p‖ := by
  have hh := terrain_min (shadeK p^2) (sq_nonneg _) he
  apply hh.trans
  unfold throne satin damp soda; rw [stone_real hp]
  norm_cast
  exact le_abs_self _
def throneF (G : Gauge) (μ : ℝ) (p : Momentum) : CompM (Loc G 0) (Loc G 0) := throne μ p • 1

def throneK (G : Gauge) (L : Side) := furnish L (throneF G (inch L))
lemma throne_basis (a : Phase (Co L (Loc G 0))) (i) : stackSlice i (posterBlock L (throneF G (inch L)) p*ᵥ a) = (throne (inch L) (aliasAt p i)) • stackSlice i a := by rw [posterBlock_at,throneF,Matrix.smul_mulVec,one_mulVec]

lemma bass_bill (p : Momentum) (hp : star p=p) (a : Phase (Co L (Loc G 0))) :
    ∑ i : Site L, (hill p i ^2*slug (stackSlice i (crewAlias p a)))^2 ≤ 2^20 * slug (throneK G L p*ᵥ a)^2 := by
  have hi := tile_ice (L:=L) (α:=Loc G 0) hp
  rw [show slug (throneK G L p*ᵥ a) = slug (crewAlias p (throneK G L p*ᵥ a)) from (hi.back.lives _).symm,throneK,crew_funds,slug_slots,mul_sum];
  apply sum_le_sum; intro i _
  rw [throne_basis,slug_scale]
  have H := throne_pays (p:=aliasAt p i) (by rw [← alias_conj,hp]) (inch_pos L)
  have he : pebWeight (aliasAt p i) (inch L)=hill p i^2 := (hill_sq ..).symm; rw [he] at H
  let b := slug (stackSlice i (crewAlias p a))
  let c := ‖throne (inch L) (aliasAt p i)‖
  change _ / _ * _ ≤ c at H
  change (hill p i^2 * b)^2≤2^20*(c*b)^2
  have hw : hill p i^2*b≤ (2^10)*(c*b) := calc
    _ ≤ ((2^10:ℝ)*c)*b := mul_le_mul_of_nonneg_right (by linarith only [H]) (slug_nonneg _)
    _ = _ := by ring
  exact (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (slug_nonneg _)) hw 2).trans_eq (by ring)

lemma Rfine_cost (P : Patch) (a : Phase (Co P.L (Loc G 0))) (h : star p=p) :
    (altarTile P.L (Loc G 1)|>.rate p (-(furnish P.L (pageD G 0) p*ᵥ a)))^2 ≤ 2^20*slug (throneK G P.L p*ᵥ a)^2 := by
  apply le_trans ?_ (bass_bill p h a)
  let F := furnish P.L (pageD G 0) p*ᵥ a
  rw [Slab.rate,Matrix.mulVec_neg,slug_neg, show slug _=(altarTile P.L (Loc G 1)).rate p F from rfl]
  rw [← tile_crew (p:=p) F,rate_sq_tile]; unfold F; rw [crew_funds]; refine sum_le_sum fun i _ => ?_
  rw [posterBlock_at, pure_density (hp:=by rw [← alias_conj,h]),hill_sq]
  let q := aliasAt p i
  let s := slug (stackSlice i (crewAlias p a))
  have he : (shadeK q*s)^2 ≤ (shadeK q ^2+inch P.L^2)*s^2 := by nlinarith [mul_nonneg (sq_nonneg (inch P.L)) (sq_nonneg s)]
  apply le_trans (mul_le_mul_of_nonneg_left he (by positivity)); unfold q s; ring_nf; rfl
lemma Rcoarse_cost (P : Patch) (a : Phase (Co P.L (Loc G 0))) (h : star p=p) :
    slug (jar G P p*ᵥ a)^2 ≤ coast_tax P.J 1^2 * (2^20*slug (throneK G P.L p*ᵥ a)^2) := by
  apply le_trans ((pow_le_pow_left₀ (slug_nonneg _) (flux_tester (curve_coast P (fun _ : Loc G 0 => 0) 0 (Nat.zero_le _) (Work.F07.realStrip _ zero_lt_one h)) a) 2))
  rw [mul_assoc, mul_pow];
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); apply le_trans _ (bass_bill p h a)
  rw [show slug a=slug (crewAlias p a) from ((tile_ice (L:=P.L) (α:=Loc G 0) h).back.lives a).symm]; rw [mul_pow, slug_slots, mul_sum];
  apply sum_le_sum; intro i _; rw [mul_pow (hill p i ^2)]; have hh := inch_pos P.L; gcongr; exact hill_inch p i

def brake_cost (J : ℕ) := Real.sqrt (2^20*(1+coast_tax J 1^2))
lemma Rjoint_cost (P : Patch) (a : Phase (Co P.L (Loc G 0))) (h : star p=p) :
    (slabW G P.L).rate p (shadeR G P p*ᵥ a) ≤ brake_cost P.J * slug (throneK G P.L p*ᵥ a) := by
  unfold brake_cost; apply (pow_le_pow_iff_left₀ (show 0 ≤ (slabW G P.L).rate p _ from slug_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (slug_nonneg _)) (by decide : 2≠0)).1
  rw [shade_split,slabW, Slab.spade_rate,Slab.basic_rate,slug_neg,mul_pow,Real.sq_sqrt (by positivity)]; have h1 := Rfine_cost P a h; have h2 := Rcoarse_cost P a h; linarith only [h1,h2]
end YM.Stationary
end

/-!
# Calibrate `sodaSafe` with power of actual μ = L^-1. Enables analytic arcs
pre-L after coarse currency. With stable real lower. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {ι : Type} [Fintype ι] [DecidableEq ι] {p q : Momentum} {σ η μ : ℝ} {L : Side}
lemma slash (x : Phase ι) {y} (u : Phase ι) (p : Phase ι) : ‖dotProduct x y - dotProduct u p‖ ≤
    slug (x-u)*slug y +slug u * slug (y-p) := by
  rw [show dotProduct x y-dotProduct u p=dotProduct (x-u) y+dotProduct u (y-p) by rw [sub_dotProduct, dotProduct_sub]; abel]
  exact (norm_add_le ..).trans (add_le_add (slug_dot ..) (slug_dot ..))
lemma shade_stone (p : Momentum) (t : ℝ) (hp : ‖p-ground p‖≤t) (ht : t≤1) : ‖stone p-stone (ground p)‖ ≤ 4*t*(shadeK p+4*t)+shadeK p*(4*t) := by
  have hx : slug (Exterior.q (-ground p))= shadeK p := by rw [quanta (ground_real p),slug_star]; rfl
  have hg (p : Momentum) (hp : ‖p-ground p‖≤t) : slug (Exterior.q p-Exterior.q (ground p)) ≤4*t := (qCost (p:=ground p) (r:=p) (ground_real p) (hp.trans ht)).trans (by linarith)
  have hv : slug (Exterior.q (-p)-Exterior.q (-ground p))≤4*t := by
    rw [← ground_neg_at p]; apply hg; rw [ground_neg_at,sub_neg_eq_add,neg_add_eq_sub,norm_sub_rev]; exact hp
  have hh := hg p hp
  have heq : slug (Exterior.q p) ≤ shadeK p+4*t := by
    rw [show Exterior.q p= Exterior.q (ground p)+(Exterior.q p-Exterior.q (ground p)) by abel]; exact (slug_plus ..).trans (add_le_add_right hh _)
  unfold stone; apply (slash ..).trans; rw [hx];
  exact add_le_add (mul_le_mul hv heq (slug_nonneg _) ((slug_nonneg _).trans hv)) (mul_le_mul_of_nonneg_left hh (slug_nonneg _))
lemma soda_safe_cube (h : 0<μ) (he : μ≤1) (hp : p∈strip (μ*(1/128))) : (1/2:ℝ)*pebWeight p μ ≤ ‖soda μ p‖ := by
  have ht : ‖soda μ (ground p)‖ = pebWeight p μ := by
    unfold soda; rw [stone_real (ground_real _), shadeK, ground_up, ← Complex.ofReal_pow, ← Complex.ofReal_add,norm_real]; exact Real.norm_of_nonneg (peb_pos p h).le
  have hc : soda μ p-soda μ (ground p)=stone p-stone (ground p) := by unfold soda; rw [add_sub_add_right_eq_sub]
  have hx := norm_sub_norm_le (soda μ (ground p)) (soda μ p)
  rw [ht,norm_sub_rev,hc] at hx
  have hv := shade_stone _ _ (ground_near hp).le (by linarith : μ*(1/128)≤1); unfold pebWeight at *
  nlinarith only [hv,hx, sq_nonneg (shadeK p-μ),sq_nonneg μ]
lemma soda_glass (h : 0<μ) (he : μ≤1) (hp : p∈ strip (μ*(1/128))) : soda μ p ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (mul_pos (by norm_num) (peb_pos p h)) (soda_safe_cube h he hp))
lemma throne_rate {G : Gauge} (h : 0<μ) (he : μ≤1) : Poster (μ*(1/128)) (throneF G μ) := by
  constructor
  · intro p hp i j
    refine (DifferentiableAt.mul (?_ : DifferentiableAt ℂ (throne μ) p) (differentiableAt_const _))
    unfold throne satin damp; apply DifferentiableAt.add; · unfold stone dotProduct Exterior.q; fun_prop
    refine DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.pow ?_ _)
    refine DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.inv (h:=soda μ) ?_ (soda_glass h he hp)); unfold soda stone dotProduct Exterior.q; fun_prop
  intro p q hp hq; unfold throneF; rw [throne_roll hp]
end YM.Stationary
end

/-!
# Completing the gap. The analytic statement for any Height is periodic
arc on ALL grids; here stable transfer from explicit canonical trajectory.
Ledger independent still needs pre-L vertex scale for self-contained application. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {X α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {ε η H κ σ D A C : ℝ} {G : Gauge} {p r : Momentum} {P : Patch} {L c f : Side}
lemma committee {p} (U : Slab α) (x y : Phase α) : U.rate p x≤ U.rate p y + U.rate p (x-y) := by
  have ht := slug_plus ((U.tile p)⁻¹ *ᵥ y) ((U.tile p)⁻¹ *ᵥ (x-y)); unfold Slab.rate
  rw [← Matrix.mulVec_add,add_sub_cancel] at ht
  exact ht
private lemma on_the_tab (η C B : ℝ) (h : 0<η) (hc : 0≤C) (he : 0≤B) :
    ∃ y : ℝ,0<y ∧ ∀ p a b d, 0 ≤ a → 0 ≤ b → 0 ≤ p → η*a^2 + b^2 ≤ d → p≤C*(b+B*a)+a → y*p^2 ≤ d := by
  let r := C*B+1
  have hr : 0 < r := by unfold r; positivity
  let K := max (2*C^2) (2*r^2/η)
  have hK : 0 < K := lt_of_lt_of_le (by positivity : 0<2*r^2/η) (le_max_right ..)
  refine ⟨K⁻¹,inv_pos.mpr hK, fun p a b d hp hh hs hy hx=> ?_⟩
  have hv : p≤C*b+r*a := hx.trans_eq (by unfold r; ring)
  rw [inv_mul_eq_div, div_le_iff₀ hK]; calc
    p^2 ≤ 2*C^2*b^2+2*r^2*a^2 := (pow_le_pow_left₀ hs hv 2).trans (by nlinarith only [sq_nonneg (C*b-r*a)])
    _ ≤ K*b^2+K*η*a^2 := add_le_add (by unfold K; gcongr; exact le_max_left ..) (mul_le_mul_of_nonneg_right ((div_le_iff₀ h).mp (le_max_right ..)) (sq_nonneg _))
    _ ≤ d*K := by nlinarith only [mul_le_mul_of_nonneg_left hy hK.le]

lemma secure_cash (h : 0<η) (hc : 0≤C) (he : 0≤D) : ∃ y : ℝ,0<y ∧ ∀ (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (U : CompM α α) (S : Slab α) (p : Momentum), (S.tile (-p))ᵀ=(S.tile p)ᴴ → ∀ (P : CompM α β) (V : CompM β α),
      serial (Slab.basic _) S p p V D →
      (∀ x, ∃ v,η*(S.rate p (x-P*ᵥ v))^2 ≤ (dotProduct (star x) (U *ᵥ x)).re) →
      (∀ x, S.rate p (P*ᵥ x)≤ C*slug ((V*P)*ᵥ x)) →
       Stable (carryM S.dual S p p (U+Vᴴ*V)) y := by
  obtain ⟨y,hy,H⟩ := on_the_tab η C D h hc he
  refine ⟨y,hy,fun α β _ _ _ _ U S p hS P V hp hu hx => ?_⟩
  apply stable_real; intro i
  let M := S.tile p
  let x := M *ᵥ i
  obtain ⟨u,hv⟩ := hu x
  rw [← S.pole hS, Matrix.add_mulVec,dotProduct_add,Complex.add_re, ← Matrix.mulVec_mulVec,vested,slug_self]; change _ ≤ (dotProduct (star x) (U *ᵥ x)).re+slug (V *ᵥ x)^2
  let a := P *ᵥ u
  let b := x-a
  apply H (slug i) (S.rate p b) (slug (V*ᵥ x)) _ (slug_nonneg _) (slug_nonneg _) (slug_nonneg _) (add_le_add_left hv _)
  have hw : S.rate p a ≤ C*slug (V *ᵥ a) := by simpa only [a,mulVec_mulVec] using hx u
  have hh := committee (p:=p) S x a; rw [show S.rate p x=slug i from Slab.cover_rate ..] at hh
  have hb := Slab.serial_at hp b; rw [Slab.basic_rate] at hb
  have hR : slug (V *ᵥ a)≤ slug (V *ᵥ x) + D * S.rate p (x-a) := by
    have ht := slug_plus (V *ᵥ x) (- (V *ᵥ b))
    rw [show V*ᵥ x + -(V *ᵥ b)=V *ᵥ a by unfold b; rw [Matrix.mulVec_sub]; abel,slug_neg] at ht
    exact ht.trans (add_le_add_right hb _)
  exact hh.trans (add_le_add_left (hw.trans (mul_le_mul_of_nonneg_left hR hc)) _)

abbrev Tactics (G : Gauge) (P : Patch) := Momentum→CompM (Co P.L (Loc G 0)) (ParcelG G P.L)

def forceK (G : Gauge) (P : Patch) (F : Tactics G P) (w : ℝ) (B : Bed) (p : Momentum) := giftQ G P B w p + (F (-p))ᵀ * F p


lemma stadium (G : Gauge) (j : ℕ) (κ D ε : ℝ) (hh : 0<κ) (hc : 0 ≤ D) (hε : 0<ε) : ∃ y : ℝ,0<y∧∀ (P : Patch), P.J=j→ ∀ (B : Bed) (b : Clip) (F : Tactics G P)
    (σ Ω A : ℝ), 0<σ → B.metric.strip (inch P.L*σ) Ω → (∀ n,Floor B b n ε A) → Poster σ F →
    (∀ p, star p=p → F p*shadeR G P p=throneK G P.L p) → (∀ p, star p=p → (F (-p))ᵀ=(F p)ᴴ) →
    (∀ p∈strip σ,serial (Slab.basic _) (slabW G P.L) p p (F p) D) →
    ∀ p, star p=p → Stable (carryM ((slabW G P.L).dual) (slabW G P.L) p p (forceK G P F κ B p)) y := by
  obtain ⟨η,hη,H⟩ := through_quotient G j κ ε hh hε
  obtain ⟨Y,hY,J⟩ := secure_cash hη (show 0≤brake_cost j from Real.sqrt_nonneg _) hc
  refine ⟨Y,hY,fun P hP B b F σ Ω A hs hb hp hx he hw hL p hv => ?_⟩
  obtain ⟨x,hr,hq⟩ := Nave.roll p
  let t := slabW G P.L
  have hf : t.Bright := (Slab.Bright.spade altar_bright Slab.Bright.basic)
  have ht : star x=x := hq.symm.metric hv
  have hz : x∈strip σ := Work.F07.realStrip _ hs ht
  have hB : forceK G P F κ B x=forceK G P F κ B p := (Poster.amounts (gift_lane B _ hb hs) (hx.reverse.forge hx)).shifts hq hz
  rw [← hB]
  apply hf.dual.stable hf hq; rw [forceK,hw x ht]
  refine J _ _ _ _ _ (slab_real ht) (shadeR G P x) (F x) (hL x hz) (H P hP B b _ Ω A (mul_pos (inch_pos _) hs) hb hp x hr ht) fun u => ?_
  rw [he x ht]; exact hP ▸ Rjoint_cost P u ht
end YM.Stationary
end
