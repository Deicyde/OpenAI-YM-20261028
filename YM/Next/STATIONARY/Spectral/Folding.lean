import YM.Next.STATIONARY.Spectral.Slabs

set_option autoImplicit false
/-! # Rough profiles and distributed shifts. Ledger in slab coordinates;
`Deck` presentations can cost via ANY scalar-pair test. Unitary on real, tilt
on complex retained (must not spend L margin for dephasing errors).
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {ι L : Side} {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {σ η C D : ℝ} {p q r : Momentum}

namespace Slab
def rate (X : Slab α) (p : Momentum) (i : Phase α) := slug ((X.tile p)⁻¹ *ᵥ i)
lemma cover_rate (X : Slab α) (p : Momentum) (i) : X.rate p (X.tile p *ᵥ i)=slug i := by unfold rate; rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (X.whole _),Matrix.one_mulVec]
lemma rebate (X : Slab α) (p : Momentum) (i) : X.tile p *ᵥ ((X.tile p)⁻¹ *ᵥ i)=i := by rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (X.whole _),one_mulVec]
lemma serial_of {X : Slab α} {Y : Slab β} {U : CompM α β} (hp : 0 ≤ C) (h : ∀ i,X.rate p (U *ᵥ i) ≤ C * Y.rate q i) : serial X Y p q U C := by
  apply flux_take hp; intro i
  have H := h (Y.tile q *ᵥ i); rw [cover_rate] at H; unfold carryM; rw [← mulVec_mulVec, ← mulVec_mulVec]; exact H
lemma serial_at {X : Slab α} {Y : Slab β} {U : CompM α β} (h : serial X Y p q U C) (i) : X.rate p (U *ᵥ i) ≤ C * Y.rate q i := by
  have H := flux_tester h ((Y.tile q)⁻¹ *ᵥ i)
  unfold carryM at H; rw [← mulVec_mulVec,Y.rebate, ← mulVec_mulVec] at H; exact H
lemma cost_of {X : Slab α} {Y : Slab β} {U : CompM α β} (hp : 0≤C)
    (h : ∀ u v, ‖dotProduct u (U *ᵥ v)‖ ≤ C * X.rate (-p) u * Y.rate q v) : serial X.dual Y p q U C := by
  apply flux_price hp; intro u v
  have H := h (X.tile (-p)*ᵥ u) (Y.tile q*ᵥ v)
  rw [cover_rate,cover_rate] at H; unfold carryM
  rw [Slab.inverse_dual, ← mulVec_mulVec, ← mulVec_mulVec,dotProduct_mulVec, Matrix.vecMul_transpose]; exact H
lemma basic_rate : (basic α).rate p=slug := by ext1 i; simp [rate,basic]
lemma pole {X : Slab α} (h : (X.tile (-p))ᵀ=(X.tile p)ᴴ) (U : CompM α α) (x) :
    dotProduct (star (X.tile p*ᵥ x)) (U*ᵥ (X.tile p*ᵥ x))=dotProduct (star x) (carryM X.dual X p p U*ᵥ x) := by
  unfold carryM; rw [inverse_dual,h,← mulVec_mulVec,← mulVec_mulVec,star_mulVec,dotProduct_mulVec]
  simp only [Matrix.vecMul_vecMul,dotProduct_mulVec, Matrix.mul_assoc]
end Slab

def crewAlias (p : Momentum) (l : Phase (Co L α)) := (plankTile L α p)⁻¹ *ᵥ l
lemma rate_alias (p : Momentum) (l : Phase (Co L α)) : (altarTile L α).rate p l = slug (fun i : Co L α => (hill p i.1:ℂ)*crewAlias p l i) := by
  unfold Slab.rate altarTile; rw [winders,← mulVec_mulVec, ← mulVec_mulVec]; rw [(tile_ice (by simp : star (0:Momentum)=0)).lives]
  congr 1; funext i; unfold Matrix.mulVec dotProduct; rw [Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq,id_eq,Pi.inv_apply,spice, inv_inv]; rfl
  · intro b hb hp; simp only [Matrix.diagonal_apply_ne _ hp.symm,zero_mul]
  simp

lemma plank_charge (L : Side) (x : Site L) : (inch L)* Laurent.size (lift x) ≤ 4 := by
  have hp : Laurent.size (lift x) ≤ ∑ _ : Axis,L.val := by
    apply sum_le_sum; intro i hi; have h := lift_centers x i
    omega
  simp at hp
  change inch L * _ ≤ _
  trans inch L * ((4*L.val:ℕ):ℝ)
  · gcongr; exact (inch_pos _).le
  push_cast; nlinarith only [inch_unit L]

lemma plank_cap (p : Momentum) (h : p∈strip σ) : vflux (plankTile L α p)≤ Real.exp (σ*4) := by
  let G i := mode ((L.val:ℂ)⁻¹ • p) (lift (i : Co L α).1)
  have hh : plankTile L α p = diagonal G*plankTile L α 0 := by
    ext i j; simp [plankTile,G,aliasBlock,Matrix.diagonal_mul, alias_comp]; split <;> simp [mul_left_comm]
  rw [hh, (tile_ice (by simp : star (0:Momentum)=0)).slide_v,flux_diagonal, pi_norm_le_iff_of_nonneg (Real.exp_pos _).le]
  intro i; unfold G
  have hp : 0 < σ := (abs_nonneg _).trans_lt (h 0)
  calc
    _ ≤ Real.exp ((inch L*σ)*_) := reward _ _ _ (fun j => by
      rw [show (L.val:ℂ)⁻¹ = (inch L:ℂ) by simp [inch],Pi.smul_apply, smul_eq_mul, Complex.mul_im,ofReal_re, ofReal_im,zero_mul,add_zero,abs_mul,abs_of_pos (inch_pos _)]
      exact mul_le_mul_of_nonneg_left (h j).le (inch_pos _).le)
    _ ≤ _ := by apply Real.exp_monotone; nlinarith [plank_charge L i.1]
lemma plank_back (p : Momentum) (h : p∈strip σ) : vflux ((plankTile L α p)⁻¹)≤ Real.exp (σ*4) := by
  rw [tile_back,show counterTile L α p=(plankTile L α (star p))ᴴ by unfold counterTile plankTile; rw [conjTranspose_smul,star_pow,Complex.star_def,conj_ofReal]; rfl, star_limit]; exact plank_cap _ (fun i => by simpa [Complex.star_def] using h i)
lemma cruise (p : Momentum) (h : p∈strip σ) : serial (Slab.basic (Co L α)) (altarTile L α) p p 1 (Real.exp (σ*4)*(inch L)⁻¹) := by
  unfold serial carryM; simp only [Slab.basic,inv_one,mul_one,one_mul,altarTile,contour,id_eq]; rw [(tile_ice (by simp : star (0:Momentum)=0)).back.slide_v]
  have hi : vflux (diagonal (spice L α p)) ≤ (inch L)⁻¹ := by
    rw [flux_diagonal,pi_norm_le_iff_of_nonneg (by positivity [inch_pos L])]
    intro i; rw [spice,norm_inv,norm_real,Real.norm_eq_abs,abs_of_pos (hill_pos _ _)]
    exact inv_le_inv₀ (hill_pos _ _) (inch_pos _) |>.mpr (hill_inch p _)
  exact (flux_power ..).trans (mul_le_mul (plank_cap p h) hi (flux_nonneg _) (Real.exp_pos _).le)
end YM.Stationary
end

/-!
# Alias reading and basis on physical profiles
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ι L c f : Side}
    {σ η C D : ℝ} {p q r : Momentum}

-- mesh at fine. p-cell label d(c)=sum; aliasAt general representatives.
private lemma land_cover (x : Cover) : rolls (mon (wrap L x)) ((L.val:ℂ)⁻¹ • reciprocal x) := by
  have he := (alias_roll (L:=L) 0 x 0).symm; simpa only [aliasAt, zero_add,mon_zero,smul_zero,add_zero] using he

def currency (g : Ratio c f) (a : Site c) (b : Site g.count) := wrap f (lift a+c.val • lift b)
lemma currency_real (g : Ratio c f) (a : Site c) (b : Site g.count) : rolls (mon (currency g a b)) (aliasAt (mon a) b) := by
  refine (land_cover (L:=f) (lift a+c.val • lift b)).trans ?_
  refine ⟨0,?_⟩
  ext i
  simp only [aliasAt, mon,Pi.add_apply,Pi.smul_apply,smul_eq_mul,reciprocal,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,
    Pi.zero_apply, Int.cast_zero,mul_zero,add_zero,Int.cast_add,Int.cast_mul, Int.cast_natCast, g.exact_size,Nat.cast_mul]
  field_simp [side_ne c,side_ne g.count]

-- raw cells from alias v. literal coefficient tie to tune
section lamps
variable {g : Ratio c f}
def poured (g : Ratio c f) (d : Site c) (v : Phase (Co g.count α)) : Phase (Co f α) := tune d v ∘ splitCo g α

def stackSlice (a : Site L) (v : Phase (Co L α)) : Phase α := fun j => v (a,j)

def tiled (p : Momentum) (l : Site L) (v : Phase α) : Phase (Co L α) := fun z => mode (aliasAt p l) (lift z.1)*v z.2

lemma slice_tile (p : Momentum) (a : Phase (Co L α)) : aliasBlock L α p *ᵥ a = ∑ l,tiled p l (stackSlice l a) := by
  funext z; unfold Matrix.mulVec dotProduct aliasBlock; rw [Fintype.sum_prod_type,Finset.sum_apply]; simp [ite_mul,tiled,stackSlice]

lemma pose_fine (g : Ratio c f) (p : Site c) (l : Site g.count) (v : Phase α) : poured g p (tiled (mon p) l v)=tune (currency g p l) v := by
  funext i; unfold poured tune tiled; simp only [Function.comp_apply,split_co, Equiv.toFun_as_coe]
  let q := aliasAt (mon p) l
  let y := g.parent i.1; let r := g.residue i.1
  have hx : cell p y *mode q (lift r)=cell (currency g p l) i.1 := by
    unfold cell; rw [(currency_real g p l).exp]
    rw [mesh_alias g p l (show wrap f (lift i.1)=wrap f (g.count.val • lift y+lift r) by rw [wrap_lift,map_add]; exact (g.unpack_at i.1).symm),mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one]
  rw [← mul_assoc, hx]

-- unnormalized inverse alias

def untier (p : Momentum) (v : Phase (Co L α)) := (inch L:ℂ)^2 • crewAlias p v
lemma aliasLift (u : Phase (Co L α)) : aliasBlock L α p *ᵥ untier p u = u := by
  have ht : plankTile L α p *ᵥ crewAlias p u=u := by unfold crewAlias; rw [mulVec_mulVec,mul_nonsing_inv _ (tile_solid _),one_mulVec]
  simpa only [untier,plankTile,Matrix.smul_mulVec, Matrix.mulVec_smul] using ht

lemma alias_pack (p : Momentum) (v : Phase (Co L α)) : ∑ l,tiled p l (stackSlice l (untier p v))=v := by rw [← slice_tile,aliasLift]
lemma packed_fin (g : Ratio c f) (p : Site c) (v : Phase (Co g.count α)) : poured g p v=∑ l,tune (currency g p l) (stackSlice l (untier (mon p) v)) := by
  conv_lhs => rw [← alias_pack (mon p) v]
  simp_rw [← pose_fine g]; funext i; unfold poured tune; rw [Function.comp_apply, Finset.sum_apply, Finset.sum_apply,Finset.mul_sum]; rfl
end lamps
end YM.Stationary
end

/-!
# Folding preserving a zero-arc reading. Still works for complex periods
inside the intake strip; reciprocal relation includes jumps. Antisymmetric
blade symbol inherits this convention; axisPair as before. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ι L c f : Side}
    {σ η C D : ℝ} {p q r : Momentum}

-- row presentation extraction exactly

def posterBlock (L : Side) (F : Momentum → CompM α β) (p : Momentum) := fiber (fun l : Site L => F (aliasAt p l))
def furnish (L : Side) (F : Momentum→ CompM α β) (p : Momentum) : CircM L α β := plankTile L α p*posterBlock L F p*(plankTile L β p)⁻¹
lemma posterBlock_at (F : Momentum→CompM α β) (p : Momentum) (v : Phase (Co L β)) (l : Site L) : stackSlice l (posterBlock L F p*ᵥ v)=F (aliasAt p l)*ᵥ stackSlice l v := by
  ext1 i; simp only [stackSlice,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,posterBlock,fiber,Matrix.of_apply]
  simp [ite_mul]
lemma draping (F : Momentum→ CompM α β) (v : Phase (Co L β)) : untier p (furnish L F p *ᵥ v)=posterBlock L F p *ᵥ untier p v := by
  unfold untier furnish crewAlias
  rw [mulVec_smul,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec, ← Matrix.mul_assoc _ _ ((plankTile L β p)⁻¹),← Matrix.mul_assoc _ _ (posterBlock L F p), Matrix.nonsing_inv_mul _ (tile_solid _),Matrix.one_mul]
lemma apt_sign (v : Phase α) (x : Cover) (l : Site L) : tiled (p+reciprocal x) l v=tiled p (l+wrap L x) v := by ext1 i; simp only [tiled, (alias_roll p x l).exp]

def partitionA (l : Site L) (v : Phase α) : Phase (Co L α) := fun i => if l=i.1 then v i.2 else 0
lemma tiled_gear (p : Momentum) (l : Site L) (v : Phase α) : tiled p l v=aliasBlock L α p*ᵥ partitionA l v := by
  rw [slice_tile]; ext1 i; rw [Finset.sum_apply,Finset.sum_eq_single l]
  · simp [partitionA,tiled,stackSlice]
  · intro b _ hp; simp [partitionA,tiled,stackSlice,Ne.symm hp]
  simp
lemma untier_gear (p : Momentum) (l : Site L) (v : Phase α) : untier p (tiled p l v)=partitionA l v := by
  unfold untier crewAlias; rw [tiled_gear,← mulVec_smul, ← smul_mulVec, show (inch L:ℂ)^2 • _= _ from (rfl : ((inch L:ℂ)^2 • aliasBlock L α p)=plankTile L α p),mulVec_mulVec,show (plankTile L α p)⁻¹ * ((inch L:ℂ)^2 • aliasBlock L α p)=1 from nonsing_inv_mul (plankTile L α p) (tile_solid _),one_mulVec]

lemma furnish_gear (F : Momentum→CompM α β) (p : Momentum) (l : Site L) (v : Phase β) :
    furnish L F p*ᵥ tiled p l v=tiled p l (F (aliasAt p l)*ᵥ v) := by
  conv_lhs => rw [← aliasLift (p:=p) (furnish L F p*ᵥ _),draping,untier_gear]
  rw [tiled_gear]; congr 1; ext1 i
  have H := posterBlock_at F p (partitionA l v) i.1
  change stackSlice i.1 (posterBlock L F p *ᵥ partitionA l v) i.2=_; rw [H]; by_cases hp : l=i.1
  · subst l; rw [partitionA,if_pos rfl,show stackSlice i.1 (partitionA i.1 v)=v by ext1 j; simp [stackSlice,partitionA]]
  rw [partitionA,if_neg hp, show stackSlice i.1 (partitionA l v)=0 by ext1 j; simp [stackSlice,partitionA,hp],mulVec_zero]; rfl

lemma alias_inside (h : p∈strip σ) (l : Site L) : aliasAt p l∈strip (inch L*σ) := by
  intro i; rw [alias_discount]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,reciprocal,mul_im,add_im]; norm_num; rw [abs_of_pos (inch_pos _)]; exact mul_lt_mul_of_pos_left (h i) (inch_pos _)
lemma Poster.furnish_ok {F : Momentum→CompM α β} (he : Poster (inch L*σ) F) : Poster σ (furnish L F) := by
  refine ⟨fun h => ?_, fun hp h => ?_⟩
  · rename_i p
    have hx : BillD (posterBlock L F) p := by
      intro i j; simp only [posterBlock,fiber, Matrix.of_apply]; split
      next hz => exact BillD.enter (f:=fun p => aliasAt p i.1) (he.shape (alias_inside h i.1)) (show DifferentiableAt ℂ (fun p => aliasAt p i.1) p by unfold aliasAt; fun_prop) i.2 j.2
      exact differentiableAt_const _
    exact BillD.bond (BillD.bond (tile_lit _) hx) (BillD.take (tile_lit _) (tile_solid _))
  rename_i p q
  obtain ⟨x,rfl⟩ := hp
  let t := p+reciprocal x
  have hh : t ∈ strip σ := fun i => by simpa [t,reciprocal] using (h i)
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro v
  change furnish L F p*ᵥ v=furnish L F _*ᵥ v
  rw [← alias_pack t v,mulVec_sum,mulVec_sum]; refine sum_congr rfl fun l _ => ?_
  rw [furnish_gear F _ l, show t=p+reciprocal x from rfl, apt_sign,apt_sign,furnish_gear,he.shifts (alias_roll p x l) (alias_inside hh l)]

section parceling
variable {G : Gauge} {F : Momentum→CompM α β} {U : CircM f α β} (g : Ratio c f)
-- reindex to U
lemma Jaunt.press (h : Jaunt U F 0) (hp : Poster (inch g.count*σ) F) (hs : 0<σ) :
    Jaunt (U.submatrix (splitCo g α).symm (splitCo g β).symm) (furnish g.count F) 0 := by
  intro p q he v
  rw [add_zero, ← hp.furnish_ok.shifts he (Work.F07.realStrip _ hs (real_frequency p))]
  let A := splitCo g α; let B := splitCo g β
  have hv : U *ᵥ poured g p v = poured g p (furnish g.count F (mon p) *ᵥ v) := by
    rw [packed_fin g p v,mulVec_sum,packed_fin]
    refine sum_congr rfl fun l _ => ?_
    rw [h (currency g p l) _ (currency_real g p l), add_zero, draping, posterBlock_at]
  ext1 x
  have hz := congr_fun hv (A.symm x)
  change (U*ᵥ poured g p v) (A.symm x)= tune p _ (A (A.symm x)) at hz
  rw [A.apply_symm_apply] at hz; rw [← hz]
  unfold poured; simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,Function.comp_apply]
  rw [← Equiv.sum_comp B.symm]; refine sum_congr rfl fun i _ => ?_; rw [show splitCo g β (B.symm i) = i from B.apply_symm_apply _]
end parceling
end YM.Stationary
end

/-!
# Counting at true fine positions in a coarse arc.

Use `scrap` for the cover offset relative to cell; harmonic path charges count
on P.L block NOT on c*f period. Includes coarse residue remainders at negative
reaches. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {L c f : Side} {α β : Type} {η A : ℝ} {p r : Momentum}

def rent (L : Side) (x : Cover) : Cover := Classical.choose (cover_of_eq (lift (wrap L x)) x (wrap_lift _))
lemma rent_balance (L : Side) (x : Cover) : x=lift (wrap L x)+ L.val • rent L x := Classical.choose_spec (cover_of_eq (lift (wrap L x)) x (wrap_lift _))
lemma rent_unique {x z : Cover} (h : x=lift (wrap L x)+L.val • z) : z=rent L x := by
  have he : (L.val:ℤ) • z=(L.val:ℤ) • rent L x := by exact_mod_cast add_left_cancel (h.symm.trans (rent_balance L x))
  funext i; have he := congr_fun he i
  simp only [Pi.smul_apply,zsmul_eq_mul] at he; exact mul_left_cancel₀ (show (L.val:ℤ)≠0 by exact_mod_cast L.property.ne') he
lemma rent_raw (v x : Cover) (z : Site L) (he : x=lift z+L.val • v) : wrap L x=z ∧ rent L x=v := by
  have hv : wrap L x=z := by
    rw [he,map_add,map_nsmul,wrap_lift]; suffices H : L.val • wrap L v=0 by rw [H, add_zero]
    funext i; rw [Pi.smul_apply,nsmul_eq_mul]; simp [Per]
  exact ⟨hv,(rent_unique (hv.symm ▸ he)).symm⟩
lemma rent_lift (x : Site L) : rent L (lift x)=0 := by refine Eq.symm (rent_unique ?_); rw [wrap_lift,nsmul_zero, add_zero]


lemma rent_cost (L : Side) (x : Cover) : (Laurent.size (rent L x):ℝ)≤4+inch L * Laurent.size x := by
  let q := lift (wrap L x)
  have he : L.val • rent L x=x+(-q) := by linear_combination -rent_balance L x
  have hx : L.val * Laurent.size (rent L x)≤Laurent.size x+Laurent.size q := by
    rw [show L.val * Laurent.size (rent L x)=Laurent.size (L.val • rent L x) by
      unfold Laurent.size; simp [Int.natAbs_mul,Finset.mul_sum]]
    rw [he]; exact (size_add ..).trans_eq (by rw [size_neg])
  have hp : (L.val:ℝ)*Laurent.size (rent L x) ≤ Laurent.size x+(Laurent.size q:ℝ) := by exact_mod_cast hx
  have ht := plank_charge L (wrap L x)
  calc
    _ = inch L*((L.val:ℝ)*Laurent.size (rent L x)) := by rw [← mul_assoc,inch_unit,one_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hp (inch_pos _).le).trans (by rw [mul_add,add_comm]; change inch L*(Laurent.size q:ℝ)+_ ≤ _; exact add_le_add_left ht _)
-- position lens from cell profile

def scrap (p : Momentum) (v : Phase (Co L α)) (x : Cover) (i : α) := mode p (rent L x) * v (wrap L x,i)
lemma scrap_reset (h : rolls (α:=Axis) (p:=p) r)
    (v : Phase (Co L α)) (x : Cover) (i) : scrap p v x i=scrap r v x i := by rw [scrap,h.exp,scrap]

lemma scrap_bank (p : Momentum) (v : Phase (Co L α)) (x y : Cover) (i) : scrap p v (x+L.val • y) i=scrap p v x i * mode p y := by
  have he := rent_balance L x
  have hx : x+L.val • y=lift (wrap L x)+ L.val • (rent L x + y) := by rw [smul_add, ← add_assoc, ← he]
  obtain ⟨h,hq⟩ := rent_raw _ _ _ hx
  rw [scrap,scrap,h,hq,mode_shift,mul_right_comm]
lemma scrap_tiled (p : Momentum) (l : Site L) (u : Phase α) (x : Cover) (i) : scrap p (tiled p l u) x i = mode (aliasAt p l) x*u i := by
  conv_rhs => rw [rent_balance L x]
  simp only [mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one,scrap,tiled]
  ring

lemma scrap_pour (g : Ratio c f) (p i : Site c) (q : Momentum) (he : rolls (mon p) q) (v : Phase (Co g.count α)) (x : Cover) (b : α) :
    poured g p v (wrap f x+g.embed i,b)=cell p i*scrap q v x b := by
  let l:= wrap g.count x; let y:= rent g.count x; let z := i+wrap c y
  have h : wrap f x+g.embed i=g.assemble (z,l) := by
    conv_lhs => rw [rent_balance g.count x]
    unfold z l y Ratio.assemble; simp only [map_add]; rw [show g.embed (i+_) = g.embed i+_ from g.root.map_add .., Ratio.root_embed,g.embed_wrap]; abel
  unfold poured tune scrap
  rw [Function.comp_apply,split_co,h,g.assemble_parent,g.assemble_res]
  unfold z; rw [cell_add,cell_wrap,he.exp, mul_assoc]
lemma rent_pay (P : Patch) (x : Cover) (hp : x∈box ((P.J+5)*P.L.val)) : (Laurent.size (rent P.L x):ℝ) ≤ 4+4*((P.J:ℝ)+5) := by
  obtain ⟨h,hk⟩ := box_test.mp hp
  let V := (P.J+5)*P.L.val
  have hy : Laurent.size x ≤ 4*V := by
    trans ∑ _ : Axis, V
    · apply sum_le_sum; intro i _; unfold V; have hp := h i; have hx := hk i; omega
    simp
  apply (rent_cost ..).trans; apply add_le_add_right
  have hv : (Laurent.size x:ℝ) ≤ 4*((P.J:ℝ)+5)*P.L.val := by
    have ht : (Laurent.size x:ℝ) ≤ (↑(4*V):ℝ) := by exact_mod_cast hy;
    unfold V at ht; push_cast at ht; linarith
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (inch_pos _).le
    _ = 4*((P.J:ℝ)+5) := by
      rw [mul_comm (inch P.L),mul_assoc _ _ (inch P.L),mul_comm _ (inch P.L),inch_unit,mul_one]
end YM.Stationary
end
