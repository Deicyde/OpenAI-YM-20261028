import YM.Next.STATIONARY.Spectral.RealGap


set_option autoImplicit false
/-!
# Two-end weighted budget for static forms. Avoid cubic hit with high-alias
summation: apply Operator bound for a contracted test. Decouple opposite
momenta explicitly; no gate of small REAL phases in operator norm. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {J : ℕ} {P : Patch} {L c f : Side} {p q : Momentum} {σ η C D : ℝ}

section bill
-- flip payment; ensure inversion even if L even via character

def rearSheet (L : Side) (α : Type) : Equiv.Perm (Co L α) := Equiv.prodCongr (Equiv.neg _) (Equiv.refl _)
def skateTurn (L : Side) (α : Type) [DecidableEq α] : CompM (Co L α) (Co L α) := submatrix 1 id (rearSheet L α)
lemma pivot_left (p : Momentum) : (plankTile L α (-p))ᵀ=skateTurn L α * (plankTile L α p)⁻¹ := by
  ext ⟨i,a⟩ b
  rw [mul_apply, sum_eq_single (-i,a)]
  · have hh : (skateTurn L α) (i,a) (-i,a)=1 := by simp [skateTurn, rearSheet, Matrix.one_apply]
    rw [hh,one_mul,tile_back]
    simp only [Matrix.transpose_apply, counterTile, returned,plankTile, Matrix.smul_apply,aliasBlock, Matrix.of_apply, Matrix.conjTranspose_apply]; split <;> rename_i H
    · congr 1
      rw [(show rolls (aliasAt (-p) i) (-aliasAt p (-i)) by have he := (alias_counter p (-i)); simpa using he).exp, alias_adj,mode_inverse]
    simp
  · rintro ⟨j,b⟩ _ h
    rw [show skateTurn L α (i,a) (j,b)=0 from Matrix.one_apply_ne (show (i,a)≠ rearSheet L α (j,b) from by
      intro hk; apply h; change (i,a)=(-j,b) at hk; apply Prod.ext; · have hh := congr_arg Prod.fst hk; change i=-j at hh; rw [hh]; simp
      have hl := congr_arg Prod.snd hk.symm; exact hl),zero_mul]
  simp

lemma skate_unit : Skates (skateTurn L α) := by
  unfold skateTurn; constructor; ext i j; rw [mul_apply]
  simp only [Matrix.conjTranspose_apply,Matrix.submatrix_apply, Matrix.one_apply]; simp [mul_ite,apply_ite star]
  simp only [eq_comm (a:=i) (b:=j)]

lemma skate_diagonal (p : Momentum) : diagonal (spice L α (-p))*skateTurn L α = skateTurn L α*diagonal (spice L α p) := by
  ext ⟨i,a⟩ ⟨j,b⟩; simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,skateTurn, rearSheet, Matrix.submatrix_apply, Matrix.one_apply, id_eq,Prod.mk.injEq,Equiv.prodCongr_apply,Prod.map_apply, Equiv.neg_apply,Equiv.refl_apply]; split <;> rename_i h
  · simp [spice,h,hill_turn]
  simp
lemma tensorCarry (p : Momentum) (F : Momentum→CompM α β) :
    let T := plankTile L α 0
    let H := plankTile L β 0
    let D := diagonal (spice L α p)
    let E := diagonal (spice L β p)
    carryM (altarTile L α).dual (altarTile L β) p p (furnish L F p) = ((T⁻¹)ᵀ * skateTurn L α) * (D*posterBlock L F p * E)* H⁻¹ := by
  intro T H D E; unfold carryM; rw [Slab.inverse_dual]; simp only [altarTile,contour,id_eq]
  let A := plankTile L α p; let B := plankTile L β p
  rw [transpose_mul,transpose_mul,pivot_left, Matrix.diagonal_transpose]
  simp only [furnish,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (plankTile L α p)⁻¹, Matrix.nonsing_inv_mul _ (tile_solid p), Matrix.one_mul, ← Matrix.mul_assoc (plankTile L β p)⁻¹,Matrix.nonsing_inv_mul _ (tile_solid p),Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),skate_diagonal]
  simp only [Matrix.mul_assoc]; rfl
lemma tensor_flux (p : Momentum) (F : Momentum→CompM α β) : vflux (carryM (altarTile L α).dual (altarTile L β) p p (furnish L F p))= vflux (diagonal (spice L α p)*posterBlock L F p * diagonal (spice L β p)) := by
  rw [show carryM _ _ _ _ _ = _ from tensorCarry p F]
  have ht := tile_ice (L:=L) (α:=α) (p:=0) (by simp)
  have hh := tile_ice (L:=L) (α:=β) (p:=0) (by simp)
  have hT : Skates ((plankTile L α 0)⁻¹ᵀ) := by
    have U := ht.back
    have he := congr_arg Matrix.transpose (mul_eq_one_comm.mp U.slides)
    rw [transpose_mul, Matrix.transpose_one] at he; exact ⟨he⟩
  rw [hh.back.slide_v, (hT.bond skate_unit).slide_u]
lemma poster_flux {F : Site L→ CompM α β} (hp : 0≤C) (he : ∀ i,vflux (F i)≤C) : vflux (fiber F) ≤ C := by
  refine flux_take hp _ fun i => ?_
  apply (pow_le_pow_iff_left₀ (slug_nonneg _) (mul_nonneg hp (slug_nonneg _)) (by decide : 2≠0)).1
  rw [slug_slots,mul_pow,slug_slots, mul_sum]; refine sum_le_sum fun k _ => ?_
  have hS : stackSlice k (fiber F*ᵥ i)= F k*ᵥ stackSlice k i := by ext1 x; simp [stackSlice, Matrix.mulVec,dotProduct,fiber,Fintype.sum_prod_type,ite_mul]
  rw [hS, ← mul_pow]; exact pow_le_pow_left₀ (slug_nonneg _) (flux_tester (he _) _) _
lemma woven_price (F : Momentum→CompM α β) (h : 0≤C) (hp : ∀ l : Site L, vflux (F (aliasAt p l))≤C*(hill p l)^2) : serial (altarTile L α).dual (altarTile L β) p p (furnish L F p) C := by
  unfold serial; rw [tensor_flux]; let A (l : Site L) := ((hill p l:ℂ)⁻¹)^2 • F (aliasAt p l)
  have he : diagonal (spice L α p)*posterBlock L F p*diagonal (spice L β p)=fiber A := by
    ext ⟨i,a⟩ ⟨j,b⟩; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; unfold posterBlock; by_cases hp : i=j <;> simp [A,spice,fiber,hp] <;> ring
  rw [he]; refine poster_flux h fun l => ?_
  unfold A; rw [flux_cost,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hill_pos p l).le]; apply (mul_le_mul_of_nonneg_left (hp l) (sq_nonneg _)).trans
  apply le_of_eq; field_simp [hill_pos p l|>.ne']
end bill
end YM.Stationary
end

/-!
# Price at symbol for giftQ without R. Uniform j on both energies,
both null/coexact, finite opacity. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {P : Patch} {G : Gauge} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {L : Side} {σ A C ε : ℝ} {p q r : Momentum}

section plane
def fest (α β : Type) [Fintype α] [Fintype β] := (Fintype.card α:ℝ)*Fintype.card β
lemma fest_pos : 0≤fest α β := by unfold fest; positivity
lemma flux_fest (F : CompM α β) (hb : 0≤A) (h : ∀ i j, ‖F i j‖≤A) : vflux F ≤ fest α β*A := by
  apply flux_price (mul_nonneg fest_pos hb)
  intro u v
  unfold dotProduct Matrix.mulVec
  simp only [dotProduct]; apply le_trans (norm_sum_le ..)
  have he i : ‖u i*∑ j : β,F i j * v j‖ ≤ slug u*((Fintype.card β:ℝ)*(A*slug v)) := by
    rw [norm_mul]; apply mul_le_mul (slug_atom u i) _ (norm_nonneg _) (slug_nonneg _); apply le_trans (norm_sum_le ..)
    calc _ ≤ ∑ _ : β,(A*slug v) := sum_le_sum fun j _ => (by rw [norm_mul]; exact mul_le_mul (h i j) (slug_atom v j) (norm_nonneg _) hb)
         _ = _ := by simp
  exact (sum_le_sum (s:=univ) fun i _ => he i).trans_eq (by unfold fest; simp; ring)

lemma fareH {B : Bed} (hp : p∈strip σ) (h : B.metric.strip σ A) (ha : 0≤A) : vflux (tessH G B p) ≤ fest (Loc G 2) (Loc G 2)*A := by
  refine flux_fest _ ha fun i j => ?_; unfold tessH tintedLocal; simp only [Matrix.of_apply]; split
  · have hh : 0<σ := (abs_nonneg _).trans_lt (hp 0); exact (Firm.of_series (B.metric.constant_strip h _ _) hh).2 _ hp
  rw [norm_zero]; exact ha

def pageTax (G : Gauge) (i : ℕ) := fest (Loc G (i+1)) (Loc G i) * 4
theorem page_tax (p : Momentum) (i : ℕ) : vflux (pageD G i p) ≤ pageTax G i* slug (Exterior.q p) := by
  unfold pageTax; rw [mul_assoc]; apply flux_fest _ (by positivity [slug_nonneg (Exterior.q p)])
  intro a b; unfold pageD tintedLocal; simp only [Matrix.of_apply]; split; swap; · rw [norm_zero]; have ht := slug_nonneg (Exterior.q p); positivity
  unfold symbol wedge; rw [Matrix.sum_apply]; apply (norm_sum_le ..).trans
  calc
   _ ≤ ∑ _ : Axis, slug (Exterior.q p) := sum_le_sum fun j _ => by
     rw [Matrix.smul_apply, norm_smul]; unfold Exterior.left; simp only [Matrix.of_apply]; split <;> rename_i H
     · split <;> rename_i he; · simpa only [parity,norm_pow,norm_neg,norm_one,one_pow,mul_one] using slug_atom (Exterior.q p) j
       rw [norm_zero,mul_zero]; exact slug_nonneg _
     rw [norm_zero,mul_zero]; exact slug_nonneg _
   _ = _ := by simp
lemma lightPage (hp : p∈strip σ) (i : ℕ) : vflux (pageD G i p) ≤ pageTax G i * (2*(Real.exp σ+1)) := by
  have hb i : ‖Exterior.q p i‖ ≤ Real.exp σ+1 := by
    unfold Exterior.q; apply (norm_sub_le ..).trans; rw [norm_exp]; refine add_le_add (Real.exp_monotone ?_) (norm_one .. |>.le)
    rw [I_mul_re]; exact (neg_le_abs ..).trans (hp i).le
  refine (page_tax p i).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg fest_pos (by norm_num)))
  apply (pow_le_pow_iff_left₀ (slug_nonneg _) (by positivity) (by decide : 2≠0)).1
  rw [slug_sq]; exact (sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hb i) 2).trans_eq (by simp; ring)
lemma basic_serial {X : CompM α β} (h : vflux X≤C) : serial (Slab.basic α) (Slab.basic β) p q X C := by unfold serial carryM; simpa only [Slab.basic,inv_one,Matrix.one_mul, Matrix.mul_one]
lemma slide_basic (α : Type) [Fintype α] [DecidableEq α] : (Slab.basic α).dual=Slab.basic α := by unfold Slab.dual Slab.basic; congr 1; simp
end plane

section bounds

def bridgeCost (G : Gauge) (Ω : ℝ) := (pageTax G 1*5)^2*(fest (Loc G 2) (Loc G 2)*Ω)
lemma rugPay (B : Bed) (hp : B.metric.strip (inch L*σ) A) (he : p∈strip σ) (hh : σ≤1) (ha : 0≤A) :
    serial (altarTile L (Loc G 1)).dual (altarTile L _) p p (furnish L (rug G B) p) (bridgeCost G A) := by
  have ht : p∈strip 1 := fun i => (he i).trans_le hh
  have hc : 0≤ pageTax G 1 := mul_nonneg fest_pos (by norm_num)
  let T l := pageD G 1 (aliasAt p (l:Site L))
  refine woven_price _ (mul_nonneg (sq_nonneg _) (mul_nonneg fest_pos ha)) fun l => ?_
  have h1 : vflux (T l) ≤ pageTax G 1*(5*hill p l) := (page_tax (aliasAt p l) _).trans (mul_le_mul_of_nonneg_left (hill_tilt l ht) hc)
  have h2 : vflux ((pageD G 1 (-(aliasAt p l)))ᵀ) ≤ pageTax G 1*(5*hill p l) := by
    rw [back_flux, ← show pageD G 1 (aliasAt (-p) (-l))=pageD G 1 (-aliasAt p l) from congr_arg (tintedLocal G) (rolls_symbol (alias_counter p l) 1), ← hill_turn p l]
    exact (page_tax ..).trans (mul_le_mul_of_nonneg_left (hill_tilt _ (negResident ht)) hc)
  have hK := fareH (G:=G) (alias_inside he l) hp ha
  unfold rug
  exact ((flux_power ..).trans (mul_le_mul ((flux_power ..).trans (mul_le_mul h2 hK (flux_nonneg _) ((flux_nonneg _).trans h2))) h1 (flux_nonneg _) (mul_nonneg ((flux_nonneg _).trans h2) ((flux_nonneg _).trans hK)))).trans_eq (by unfold bridgeCost; ring)

def sideCost (G : Gauge) (j : ℕ) := coreCost j 1+pageTax G 0 * (2*(Real.exp 1+1))
lemma net_pay (hp : p ∈ strip 1) : serial (Slab.basic (Loc G 1)) (slabW G P.L) p p (netY G P p) (sideCost G P.J) := by
  unfold netY
  have he := (serial.neg (topPay (G:=G) (P:=P) hp)).bond (serial_butt (altarTile P.L (Loc G 1)) (Slab.basic (Loc G 0)))
  have hh := (basic_serial (p:=p) (lightPage (G:=G) hp 0)).bond (serial_brim (altarTile P.L (Loc G 1)) (q:=p) (Slab.basic (Loc G 0)))
  refine (he.plus hh).mono (le_of_eq ?_)
  simp [sideCost]

def giftCost (G : Gauge) (j : ℕ) (A : ℝ) (κ : ℂ) := bridgeCost G A + ‖κ‖*(sideCost G j)^2
lemma gift_pay (B : Bed) (hp : B.metric.strip (inch P.L*σ) A) (he : p∈ strip σ) (hh : σ≤1) (ha : 0≤A) (κ : ℂ) :
    serial (slabW G P.L|>.dual) (slabW G P.L) p p (giftQ G P B κ p) (giftCost G P.J A κ) := by
  have hz := rugPay (G:=G) B hp he hh ha; have hf : p∈ strip 1 := fun i => (he i).trans_le hh
  have hc : ∀ q, serial (altarTile P.L _) (slabW G P.L) q q (downX G P.L) 1 := fun q => serial_butt (altarTile P.L _) _
  have hn q (h : q∈ strip 1) : serial (Slab.basic _) (slabW G P.L) q q (netY G P q) (sideCost G P.J) := net_pay h
  have hx := (hc (-p)).slide; have hL := (hn _ (negResident hf)).slide; rw [neg_neg] at hx hL; rw [slide_basic] at hL
  unfold giftQ; refine (((hx.bond hz).bond (hc p)).plus ((hL.bond (hn p hf)).costs κ)).mono ?_; unfold giftCost; rw [one_mul,mul_one,sq]
end bounds
end YM.Stationary
end

/-!
# Pre-L scores of scenery films. Scalar Hessians never charge per chart
multiplicity outside this P. Valid at output momentum -roll, not shrinking
support. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {A : Audience α} {G : Gauge} {P : Patch} {K : KernelChoices} {C D σ : ℝ} {m n : ℕ} {p q : Momentum}

variable {E : Eye ι (Acts G P)} (h : Spotlight P E σ C)
include h
lemma soft_fight {F : BassInput G P→ℝ} {T : Eye β (Acts G P)} {v : Fin n→ Momentum} {i : Fin n→ι} {p} {u w : Phase β}
    (h₀ : ∀ i, v i∈strip σ) (hv : p∈strip σ) (hw : sunshift v p∈strip σ) (hx : Veil C (T p w) 1) (hb : Veil C (T (-sunshift v p) u) 1)
    (hp : Tested (balcony Unit) (StaffP G P (muralRoom P.J*C)) (fun _ => F) (n+2) D) :
    ‖dotProduct u (sailor F E T n v i p *ᵥ w)‖ ≤ (2:ℝ)^(n+2)*D := by
  let q := -sunshift v p
  rw [sailing F u w q rfl]
  let V := lens (inviton E i v) v
  let K := imprintsC G P q (T q u)
  let M := imprintsC G P p (T p w)
  let L := (Fin.snoc (Fin.snoc V K : Fin (n+1) → _) M : Fin (n+2) → _)
  let J := Fin.snoc (fun _ : Fin n => 0) 1 (α:=fun _ => ℕ)
  let Y := (Fin.snoc J 1 : Fin (n+2) → ℕ)
  have hy : ∑ i,Y i=2 := by unfold Y J; rw [snocked_sum,snocked_sum]; simp
  let R := Shiny (StaffP G P (muralRoom P.J*C))
  have hr : ∀ a, R (L a) (Y a) := snockedR R (Fin.snoc V K : Fin (n+1) → _) J (snockedR R V _ (h.bright_lens v i h₀) (shiny_steps _ hb (h.brighten (negResident hw)))) (show R M 1 from shiny_steps _ hx (h.brighten hv))
  have he := through_charge hp hr hy.le |>.rasp hy.le
  simpa using he

omit h in
lemma Gallop.fixedsum {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {M : β→α→ X→Y} {K : β→ℝ} {R : X→ℕ→Prop} (hs : ∀ j,Gallop A R (M j) n (K j)) : Gallop A R (fun i x => ∑ j,M j i x) n (∑ j,K j) := by
  suffices hv : ∀ s : Finset β, Gallop A R (fun i x => ∑ j∈s,M j i x) n (∑ j∈s,K j) from hv univ
  intro s; induction s using Finset.induction with
  | empty => simp only [sum_empty]; exact Gallop.goes _ le_rfl
  | insert a s h ih => simpa only [sum_insert h] using (hs a).doubles ih

omit h in
def theaterH (K : ℕ→ℝ) (n : ℕ) := (2:ℝ)^(n+2)*(4*|K (n+2)|)
variable (hp : P.Branches K G)
include hp
lemma BoomF.costs (k : ℝ) : Charges (slabW G P.L |>.dual) (slabW G P.L) (BoomF false k E) σ
    (feeHead (theaterH (fun n => cashBook G P.J n (muralRoom P.J*C) k))) := by
  let X := fun n => cashBook G P.J n (muralRoom P.J*C) k
  classical
  refine serial_caps (BoomF.green _ _ E h.fresh) (fun n hn i v w p ht hz => ?_)
  let T := (sailor (paperFace false k) E (fun _ => visibly P true)) n v i p
  apply serial.mono (stands_echo T (X:=slabW G P.L) (Y:=slabW G P.L) (C:=theaterH X n) (by unfold theaterH; positivity) ?_) (fee_ge (theaterH X) hn)
  intro u a hu ha
  have hf := books_paid (A:=balcony Unit) (n:=n+2) hp (weight_staff h) k
  have hm : Gallop (balcony Unit) (StaffP G P (muralRoom P.J*C)) (fun _ => paperFace false k) (n+2) (4*|X (n+2)|) := by
    simpa only [Finset.sum_const,card_univ,show Fintype.card Axis=4 from rfl,nsmul_eq_mul,Nat.cast_ofNat] using! Gallop.fixedsum (M:=fun j _ x => presentsBox false k x j) (K:=fun _ => |X (n+2)|) (fun i => (hf i).raises le_rfl (le_abs_self _))
  exact soft_fight h w ht hz (store_mono (seen_affect (P:=P) true (h.brighten ht) ha) h.price) (store_mono (seen_affect (P:=P) true (h.brighten (negResident hz)) hu) h.price) (hm.reaches _ (by omega) le_rfl)
lemma CoastF.costs (k : ℝ) : Charges (Slab.basic _) (Slab.basic _) (CoastF false k E) σ
    (feeHead (theaterH (fun n => cashDamage G P.J n (muralRoom P.J*C) k))) := by
  let X := fun n => cashDamage G P.J n (muralRoom P.J*C) k
  classical
  refine serial_caps (CoastF.green _ _ E h.fresh) (fun n hn i v w p ht hz => ?_)
  let T := (sailor (badgeFace false k) E (fun _ => velvetX P)) n v i p
  let Y := Slab.basic (Loc G 1)
  have he : Y.dual=Y := slide_basic _
  refine Eq.mp (congr_arg (fun x => serial x Y _ p _ _) he) ((stands_echo T (X:=Y) (Y:=Y) (C:=theaterH X n) (by unfold theaterH; positivity) ?_).mono (fee_ge (theaterH X) hn))
  intro u a hu ha; unfold Y at *; rw [Slab.basic_rate] at hu ha
  have hf := books_damage (A:=balcony Unit) (n:=n+2) hp (weight_staff h) k
  have hm : Gallop (balcony Unit) (StaffP G P (muralRoom P.J*C)) (fun _ => badgeFace false k) (n+2) (4*|X (n+2)|) := by
    simpa only [Finset.sum_const,card_univ,show Fintype.card Axis=4 from rfl,nsmul_eq_mul,Nat.cast_ofNat] using! Gallop.fixedsum (M:=fun j _ x => inuresBox false k x j) (K:=fun _ => |X (n+2)|) (fun i => (hf i).raises le_rfl (le_abs_self _))
  exact soft_fight h w ht hz (store_mono (seen_oath (P:=P) ha le_rfl) h.payload) (store_mono (seen_oath (P:=P) hu le_rfl) h.payload) (hm.reaches _ (by omega) le_rfl)
end YM.Stationary
end

/-!
# Inverse WP for centered films; momentum-measure real and analytic lift.
Uses only X that belongs to actual fields throughout family. Branch proof
at zero; hence only ingredients for upper budget are standing costs of its
MODELED factors not assumption of inversion. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Tree
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate Matrix.Norms.Frobenius
variable {G : Gauge} {P : Patch} {p q : Momentum} {σ C A ε D B : ℝ}

section market
variable {m n : ℕ→Side}
structure Armada (m n : ℕ→Side) (P : Patch) (K : KernelChoices) where
    binds i : (n i).val=(m i).val*P.L.val
namespace Armada
variable {K : KernelChoices} (w : Armada m n P K)
abbrev boot (i : ℕ) : StepData (m i) (n i) := ⟨P,K,w.binds i⟩
end Armada
end market

/-- Reality of rectangular at all real p, from only ticket at each period. -/
lemma judge {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : Momentum→CompM α β} {m : ℕ→Side} (hm : Tendsto (fun i => (m i).val) atTop atTop) {F : ∀ i, Matrix (Co (m i) α) (Co (m i) β) ℝ} (h : ∀ i, Jaunt (approached (F i)) k 0) (hs : Poster σ k) (hw : 0<σ) (hx : star p=p) : (k (-p))ᵀ=(k p)ᴴ := by
  have he i {a : Site (m i)} {p} (he : rolls (mon a) p) (x : Phase β) : k (-p)*ᵥ star x=star (k p *ᵥ x) := by
    apply ray_pick (-a); rw [← starlight]
    have hh := h i a p he x; have hv := h i (-a) _ he.flip_sign (star x)
    rw [add_zero] at hh hv; rw [← hv,← hh,star_mulVec,← starlight]
    rw [show (approached _)ᴴ=(approached (F i))ᵀ from (prom_adj _).symm, vecMul_transpose]
  obtain ⟨l,y,hy,hp⟩ := mesh_stride m hm p hx; ext u v
  have ht : ContinuousAt (fun p => k (-p) v u) p := ((hs.shape (negResident (Work.F07.realStrip _ hw hx)) v u).continuousAt).comp continuous_neg.continuousAt
  have hh : ContinuousAt (fun p => star (k p v u)) p := ((hs.shape (Work.F07.realStrip _ hw hx) v u).continuousAt).star
  refine tendsto_nhds_unique_of_eventuallyEq (ht.tendsto.comp hy) (hh.tendsto.comp hy) <| Eventually.of_forall fun i => ?_
  let b : Phase β := Pi.single u 1
  have hz : star b=b := by ext1 a; by_cases H : a=u <;> simp [b, *]
  have hw := he i (hp i) b; rw [hz] at hw; simpa [b,mulVec_single] using congr_fun hw v

section real
variable {K : KernelChoices}

lemma fired {m n : Side} (S : StepData m n) (t : S.Choices) (h : S.patch.Branches S.kernel G) :
    postroom (G:=G) S t (inch S.patch.L) * spreadM S=grenade (inch S.patch.L) (1:Config G n) := by
  let U := (1:Joint G m n); let V := fedora (G:=G) S t
  let hp := fedora_style h t
  have he : dress V U=U := dressed_one hp
  have hu : Thaw (fun _ : ℝ => U) 0 := Thaw.fixed _ _
  have hU : Apparel V U := (atire_out hp hu rfl).self_of_nhds
  have hc : Explosives S t 1 U := (explosive S t h root_customs hu rfl).self_of_nhds
  unfold postroom; rw [arsenal S t _ V U hU (he.symm ▸ hc),he,Matrix.mul_assoc,shear_pole t h]; exact count_ammo S t (inch S.patch.L) h hc

lemma ticket_own {c f : Side} {S : StepData c f} {F : Tactics G S.patch} {t : S.Choices} {U : PathData G} {p : Clip}
    (B : Bed) {σ A Λ δ E₀ : ℝ} (h : S.patch.Branches S.kernel G) (hv : U.Bounds p σ A Λ) (hy : Attached B U)
    (sw : Bid.Sworn B f G) (hp : Floor B p f ε D) (he : Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S t (inch S.patch.L)))) F 0) (hw : 0<δ) (hB : B.metric.strip (inch S.patch.L*δ) E₀) :
    Jaunt (approached (repackM (clothe G S) (clothe G S) (commonM S t p U (inch S.patch.L)))) (forceK G S.patch F S.kernel.penalty B) 0 := by
  classical
  let X := clothe G S
  let M := postmark S t p U
  let R := frontR G S B
  let V := postroom (G:=G) S t (inch S.patch.L)
  let Y := unitSplit G S 0
  have hx : commonM S t p U (inch S.patch.L)=R+Vᵀ*V := by rw [show commonM _ _ _ _ _=_ from leaflet S t p U _,show postmark _ _ _ _=R from post_shares G S B t h hv hp hy sw]
  rw [hx,show repackM X X (R+Vᵀ*V)=repackM X X R+repackM X X (Vᵀ*V) from rfl,prom_addition,repack_multiply _ Y, repack_rotate, prom_mul]
  have ha := gift_turn (G:=G) (S:=S) B hw hB
  exact ha.plus (he.takes.hoist he)

lemma compass {m n : ℕ→Side} {F : Tactics G P} (w : Armada m n P K) (hs : 0<σ) (h : P.Branches K G) (hp : Poster σ F)
    (t : ∀ i,(w.boot i).Choices) (he : ∀ i,
      let S := w.boot i
      Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S (t i) (inch P.L)))) F 0)
    (hm : Tendsto (fun i => (m i).val) atTop atTop) :
    ∀ p, star p=p → F p*shadeR G P p=throneK G P.L p := by
  intro p hv
  apply Poster.fuses m hm (hp.forge shade_lane) (((throne_rate (G:=G) (inch_pos P.L) (inch_le _))).furnish_ok) hs (by norm_num) _ hv
  intro i x
  classical
  let Z : ℝ := inch P.L
  let S := w.boot i; let A := clothe G S; let Y := unitSplit G S 0
  let M := postroom (G:=G) S (t i) Z
  let N := spreadM S (G:=G)
  let V := (grenade Z (1:Config G (n i)))
  have hx : M*N=V := fired S (t i) h
  have hr := Jaunt.hoist (he i) (shade_turn (G:=G) (S:=w.boot i));
  have hR : Jaunt ((approached (repackM Y A M))*(approached (repackM A Y N))) (fun p => F p * shadeR G P p) 0 := hr
  have hV : Jaunt (approached (repackM Y Y V)) (throneK G P.L) 0 := Jaunt.press S.ratio (tonic_throne (G:=G) (n i) (inch_pos P.L)) (throne_rate (G:=G) (inch_pos P.L) (inch_le _)) (by norm_num : 0<(1/128:ℝ))
  rw [← prom_mul, ← repack_multiply Y, hx] at hR; exact hR.offset hV _ (rolls.refl _)

end real

section budgets
lemma post_cert (G : Gauge) (j : ℕ) (K : KernelChoices) (ε σ Ω A : ℝ)
    (ht : 0<ε) (he : 0<σ) (hb : σ≤1) (hΩ : 0≤Ω) (hA : 0≤A) :
    ∃ η C : ℝ, 0<η ∧ η ≤ σ ∧ 0≤C ∧
     ∀ (P : Patch), P.J=j → P.Branches K G → ∀ (B : Bed) (p : Clip) (D) (F : Tactics G P) (m n : ℕ→Side) (w : Armada m n P K), Tendsto (fun i => (m i).val) atTop atTop →
      B.metric.strip (inch P.L * σ) Ω → (∀ n, Floor B p n ε D) → Poster σ F → (∀ p∈strip σ, serial (Slab.basic _) (slabW G P.L) p p (F p) A) →
      (t : ∀ i,(w.boot i).Choices) → (∀ i,
        let S:=w.boot i
        Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S (t i) (inch P.L)))) F 0) →
      Freezer (slabW G P.L|>.dual) (slabW G P.L) (forceK G P F K.penalty B) η C := by
  obtain ⟨y,hY,H⟩ := stadium G j K.penalty A ε K.penalty_pos hA ht
  let u := giftCost G j Ω K.penalty
  let v := u+A*A
  have hv : 0≤v := add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg fest_pos hΩ)) (mul_nonneg (norm_nonneg _) (sq_nonneg _))) (mul_nonneg hA hA)
  obtain ⟨η,C,hη,h₀,h₁,Gp⟩ := shelter σ v 6 y he hv (by norm_num) hY
  refine ⟨η,C,hη,h₀,h₁, fun P hP hu B p D F m n w hm hS hx hy hf t hw => ?_⟩
  let U := slabW G P.L
  have hz : Poster σ (forceK G P F K.penalty B) := Poster.amounts (gift_lane B _ hS he) (hy.reverse.forge hy)
  have hp : U.Height σ 6 := Slab.Height.mono (Slab.Height.spade (altar_range ..) ((Slab.Height.basic).mono le_rfl (by norm_num : (1:ℝ)≤6))) hb le_rfl
  have hr : ∀ p∈strip σ,serial U.dual U p p (forceK G P F K.penalty B p) v := by
    intro q hz; let d := negResident hz
    have hN := (hf (-q) d).slide; rw [neg_neg,slide_basic] at hN
    unfold v u; rw [← hP]; exact (gift_pay B hS hz hb hΩ _).plus (hN.bond (hf q hz))
  have hg := H P hP B p F σ Ω D he hS hx hy (compass w he hu hy t hw hm) (fun _ hv => judge hm hw hy he hv) hf
  exact Gp _ U.dual U hp.dual hp _ hz hr hg
end budgets
end YM.Stationary
end

/-!
# Arc equality within cost strip. Hermitian metrics retained. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {σ η C D : ℝ}
lemma Poster.meets {A B : Momentum → CompM α β} (ha : Poster σ A) (hb : Poster σ B) (he : ∀ x : Momentum, star x=x → A x=B x) (p : Momentum) (hp : p∈ strip σ) : A p=B p := by
  let x := ground p
  let y : Momentum := axes fun i => (p i).im
  let f (t : ℂ) := x+t • y
  have hf : Differentiable ℂ f := by unfold f; fun_prop
  have hx : ∀ z : ℂ, ‖z‖≤1 → f z∈strip σ := by
    intro z hz j
    simp only [f,x,y,ground,axes, Pi.add_apply,Pi.smul_apply,smul_eq_mul, Complex.add_im,ofReal_im,mul_im,ofReal_re,mul_zero,zero_add,abs_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) ((abs_im_le_norm z).trans hz)) (hp j)
  let g := Metric.closedBall (0:ℂ) 1
  have hv : g ⊆ f ⁻¹' strip σ := fun z h => hx z (by simpa [g] using h)
  ext i j
  let F (K : Momentum→ CompM α β) (z : ℂ) := K (f z) i j
  have hh K (h : Poster σ K) : AnalyticOnNhd ℂ (F K) g := fun z hz => by
    apply analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [((Work.F07.stripOpen σ).preimage hf.continuous).mem_nhds (hv hz)] with z hp; exact (h.shape hp i j).comp _ (hf z)
  have H : ∃ᶠ z in 𝓝[≠] (0:ℂ), F A z=F B z := by
    have hp : Tendsto ((↑):ℝ→ℂ) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
      rw [tendsto_nhdsWithin_iff]; constructor
      · simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a:=(0:ℝ)) (s:={(0:ℝ)}ᶜ))
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (show (x:ℂ)≠0 by exact_mod_cast (show x≠0 from hx))
    by_contra! h
    have hg z : F A (z:ℝ)= F B (z:ℝ) := congr_fun (congr_fun (he (f z) (by simp [f,x,y, ground_real])) i) j
    obtain ⟨z,hz⟩ := (hp.eventually h).exists
    exact hz (hg z)
  have hl : F A Complex.I=F B Complex.I := (hh A ha).eqOn_of_preconnected_of_frequently_eq (hh B hb) (convex_closedBall ..).isPreconnected (Metric.mem_closedBall_self (by norm_num)) H (by simp [g])
  have hM : f I=p := by funext i; simp [f,x,y,ground,axes]; rw [mul_comm I,Complex.re_add_im]
  unfold F at hl; rw [hM] at hl; exact hl

lemma Poster.skinny {A : Momentum→CompM α β} (h : Poster σ A) (hp : η≤σ) : Poster η A := (Play.mono (Play.current (ι:=Axis) h) hp).tab
-- all period arc coherence implies static inverse control usable by ANY
-- implementation of that scene in Film
lemma Poster.renew {A B : Momentum→CompM α β} {m : ℕ→Side} (h : Poster σ A) (hb : Poster σ B)
    (hp : 0<σ) (hv : Tendsto (fun i => (m i).val) atTop atTop) (he : ∀ i,∃ U:CircM (m i) α β, Jaunt U A 0∧Jaunt U B 0) : Set.EqOn A B (strip σ) := by
  intro i hi
  exact h.meets hb (fun p hv' => Poster.fuses m hv h hb hp hp (fun i p => by obtain ⟨Y,H,K⟩ := he i; exact H.offset K _ (rolls.refl _)) hv') i hi
lemma Freezer.passes {X Y : Slab α} {K F : Momentum → CompM α α} (h : Freezer X Y K σ C) (he : Set.EqOn K F (strip σ)) : Freezer X Y F σ C :=
    ⟨fun i hi => he hi ▸ h.period _ hi, fun i hi => he hi ▸ h.price _ hi⟩
end YM.Stationary
end
