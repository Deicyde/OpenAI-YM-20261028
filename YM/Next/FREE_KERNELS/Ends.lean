import YM.Next.FREE_KERNELS.ZeroAlias

/-!
# Joining and reflecting the aliases

No periodicity requirement on each alias under p-translation; there is an
exact permutation law on overlap cubes. Frequency reality here sufficient
for real coefficient export.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {α β γ : Type*} {j t : ℕ}
lemma neg_moves (p : Momentum) (x : Cover) : -(p+reciprocal x)=-p+reciprocal (-x) := by rw [reciprocal_negate]; abel

lemma fieldD_period (S : Side) (k : ℝ) (v : Train j) (p : Momentum) (x : Cover) :
    (scaleD S k v (p+reciprocal x))=scaleD S k v p := by
  funext i; unfold scaleD; rw [Train.D_stable]
lemma fieldR_period (S : Side) (k : ℝ) (v : Train j) : Stable (scaleR S k v) := by
  intro p x; unfold scaleR; rw [rho_period]

lemma fieldD_even (S : Side) (k : ℝ) (v : Train j) (p : Momentum) : scaleD S k v (-p)=scaleD S k v p := by
  funext i; unfold scaleD; rw [Train.D_even]
lemma fieldR_even (S : Side) (k : ℝ) (v : Train j) (p : Momentum) : scaleR S k v (-p)=scaleR S k v p := by unfold scaleR; rw [rho_even]
lemma fieldD_silver (S : Side) (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : physical p) (i) : Silver (scaleD S k v p i) := ((Silver.side _).pow _).inv.mul (Train.D_cost _ hk _ _ hp)
lemma fieldR_silver (S : Side) (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : physical p) : Silver (scaleR S k v p) := ((Silver.side _).pow _).mul (Silver.sum _ _ (fun i _ => (jewel_price _ i hp).div (Train.D_cost k hk _ i hp)))

def shade (A : Matrix α β ℂ) := A.map star
lemma shade_star (A : Matrix α β ℂ) : shade A=Aᴴ.transpose := rfl
@[simp] lemma shade_add (A B : Matrix α β ℂ) : shade (A+B)=shade A+shade B := by ext a b; simp [shade]
@[simp] lemma shade_sub (A B : Matrix α β ℂ) : shade (A-B)=shade A-shade B := by ext a b; simp [shade]
@[simp] lemma shade_nil [DecidableEq α] : shade (1 : Matrix α α ℂ)=1 := by ext a b; simp [shade,Matrix.one_apply]
@[simp] lemma shade_zero : shade (0 : Matrix α β ℂ)=0 := by ext a b; simp [shade]
@[simp] lemma shade_mul [Fintype β] (A : Matrix α β ℂ) (B : Matrix β γ ℂ) : shade (A*B)=shade A*shade B := by rw [shade_star,conjTranspose_mul,Matrix.transpose_mul,shade_star,shade_star]
@[simp] lemma shade_weight (c : ℂ) (A : Matrix α β ℂ) : shade (c • A) = star c • shade A := by ext a b; simp [shade]
lemma shade_trans (A : Matrix α β ℂ) : shade Aᵀ=(shade A)ᵀ := rfl
lemma shade_mask (r : ℕ) (c : Axis → ℂ) : shade (mask r c)=mask r (star c) := by rw [shade_star,mask_adj,mask_trans]
lemma shade_signal (S : Side) (r : ℕ) {p : Momentum} (hp : physical p) : shade (signal S r p)=signal S r (-p) := by rw [shade_star,← mirage_herm S _ hp,mirage,Matrix.transpose_transpose]
lemma shade_mirage (S : Side) (r : ℕ) {p : Momentum} (hp : physical p) : shade (mirage S r p)=mirage S r (-p) := by
  unfold mirage; rw [shade_trans,shade_signal _ _ (star_neg p |>.trans (congr_arg Neg.neg hp))]
lemma shade_flux (P : Flight j t) (r : ℕ) {p : Momentum} (hp : physical p) : shade (flux P r p)=flux P r (-p) := by
  unfold flux; rw [shade_trans,shade_star,← flux_herm P (-p) (star_neg p |>.trans (congr_arg Neg.neg hp)),Matrix.transpose_transpose]; rfl
lemma shade_D (S : Side) (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : physical p) :
    shade (fieldD S k v p)=fieldD S k v (-p) ∧ shade (fieldI S k v p)=fieldI S k v (-p) := by
  have h := fieldD_even S k v p; have ht (i : Axis) := (fieldD_silver S k hk v hp i).fixed
  unfold fieldD fieldI; rw [shade_mask,shade_mask,h]; constructor
  · congr 1; exact funext ht
  congr 1; funext i; rw [Pi.star_apply]; rw [star_inv₀,ht]
lemma shade_pulse (k : ℝ) (hk : 0 < k) (v : Train j) {p : Momentum} (hp : p∈realCube zone) : shade (pulse k v p) = pulse k v (-p) := by
  simpa only [shade, neg_neg] using (heart_real k hk v (realCube_neg hp)).1

namespace Flight
variable (k : ℝ) (hk : 0<k) (P : Flight j t)

lemma tabE_period : Stable (tabE k P) :=
  shuttle_stable P.L (fun p => yen (massFilter P.patch) p*total k P p) (fun p x => by
    dsimp only
    have hs : Stable (massFilter P.patch) := fun a x => by unfold massFilter; rw [Train.area_period]
    rw [yen_stable hs]; unfold total; rw [fieldD_period])
lemma tabE_even (p : Momentum) : tabE k P (-p)=tabE k P p := by
  unfold tabE
  rw [← Equiv.sum_comp (Equiv.neg (Site P.L)) (fun i => yen _ (aliasAt (-p) i)*total _ _ (aliasAt (-p) i))]; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.neg_apply,alias_reverse p P.odd,yen_symm,total,fieldD_even]
lemma massFilter_even (p : Momentum) : massFilter P.patch (-p)=massFilter P.patch p := by
  unfold massFilter area; simp only [Pi.neg_apply,plank_even P.patch.L P.odd]

include hk
lemma tabE_silver {p : Momentum} (hp : physical p) : Silver (tabE k P p) := Silver.sum _ _ fun i _ =>
  (P.filter_silver (alias_real hp i)).mul (Silver.sum _ _ fun a _ => fieldD_silver _ k hk _ (alias_real hp i) a)
lemma script_shift {p q : Momentum} (hp : p∈realCube zone) (x y : Cover) (hx : p+reciprocal x∈realCube zone)
    (hq : q∈realCube zone) (hy : q+reciprocal y∈realCube zone) :
    scriptA k P (p+reciprocal x) (q+reciprocal y)=scriptA k P p q ∧
      scriptT k P (p+reciprocal x) (q+reciprocal y)=scriptT k P p q := by
  have hHp := (overlap_heart k hk P.land hp x hx).1
  have hHq := (overlap_heart k hk P.wing hq y hy).1
  have hs (S : Side) (r : ℕ) (p : Momentum) (x : Cover) : signal S r (p+reciprocal x)=signal S r p := by rw [signal,tripQ_stays]; rfl
  have hg : Stable (massFilter P.patch) := fun a x => by unfold massFilter; rw [Train.area_period]
  have hw : weightsE k P (p+reciprocal x) (q+reciprocal y) = weightsE k P p q := by
    unfold weightsE total; rw [neg_moves, hg,fieldD_period,tabE_period]
  have hy : chainY k P (p+reciprocal x) (q+reciprocal y)=chainY k P p q := by
    unfold chainY; rw [yen_stable hg,fieldR_period,fieldR_period]
  unfold scriptA scriptT cloud; rw [hy,hw]
  unfold rotor pipe mirage signal flux fieldD fieldI; simp_rw [neg_moves,hinges_stays,hHp,hHq,tripQ_stays,fieldD_period]; rw [fieldR_period]; simp

lemma script_reflect {p q : Momentum} (hp : p∈realCube zone) (hq : q∈realCube zone) :
    shade (scriptA k P p q)=scriptA k P (-p) (-q) ∧ shade (scriptT k P p q)=scriptT k P (-p) (-q) := by
  have ha := shade_pulse k hk P.land hp; have hb := shade_pulse k hk P.wing hq
  obtain ⟨hg₁,hg₂⟩ := shade_D 1 k hk P.land hp.1
  obtain ⟨ht,_⟩ := shade_D P.L k hk P.wing hq.1
  have h (v) (hr : physical v) : star (massFilter P.patch v)=massFilter P.patch (-v) := by unfold massFilter; rw [star_pow,Train.area_conj, show star v=v from hr]
  have hs : star (weightsE k P p q)=weightsE k P (-p) (-q) := by
    unfold weightsE
    have he : Silver (total k P q) := Silver.sum _ _ fun i _ => fieldD_silver _ k hk _ hq.1 i
    have hr : total k P (-q)=total k P q := by unfold total; rw [fieldD_even]
    rw [tabE_even,hr,star_div₀,star_mul, (tabE_silver k hk P hp.1).fixed,he.fixed,h _ (realCube_neg hq).1,mul_comm]
  have hP := (fieldR_silver 1 k hk P.land hp.1).fixed
  have hy : star (chainY k P p q)=chainY k P (-p) (-q) := by
    unfold chainY; rw [fieldR_even,fieldR_even,yen_symm,star_div₀,star_mul,(P.filter_silver hq.1).fixed,hP,(fieldR_silver _ k hk _ hq.1).fixed,mul_comm]
  unfold scriptA scriptT rotor pipe cloud
  simp only [shade_add,shade_mul,shade_signal _ _ hp.1,shade_signal _ _ hq.1,shade_flux _ _ hq.1,shade_weight,ha,hb,hg₁,hg₂,ht,hs,shade_mirage _ _ hp.1,shade_sub,shade_nil,hy]
  rw [fieldR_even,star_inv₀,hP]; simp

lemma knots_shift {p : Momentum} (hp : p∈realCube zone) (x : Cover) (hx : p+reciprocal x∈realCube zone) (l : Site P.L) :
    pilot k P (p+reciprocal x) l=pilot k P p (l+wrap P.L x) ∧ wire k P (p+reciprocal x) l=wire k P p (l+wrap P.L x) := by
  by_cases h : x=0
  · rw [h, show reciprocal (0:Cover)=0 by ext; simp [reciprocal]]; simp
  obtain ⟨h₁,h₂⟩ := overlap_regular h hp hx
  obtain ⟨y,hy⟩ := alias_exchange p l x
  have he : aliasAt (p+reciprocal x) l ∈ realCube zone := alias_in_real zone_pos hx l P.odd
  rw [pilot_match k hk P hp h₁,pilot_match k hk P hx h₂,wire_match k hk P hp h₁,wire_match k hk P hx h₂,hy]
  exact script_shift k hk P hp x y hx (alias_in_real zone_pos hp _ P.odd) (hy ▸ he)
lemma knots_reflect {p : Momentum} (hp : p∈realCube zone) (l : Site P.L) : shade (pilot k P p l)=pilot k P (-p) (-l) ∧ shade (wire k P p l)=wire k P (-p) (-l) := by
  by_cases he : p=0
  · subst p; by_cases h : l=0
    · subst l; simp
    rw [neg_zero,pilot_none P k h,wire_none P k h,pilot_none P k (neg_ne_zero.mpr h), wire_none P k (neg_ne_zero.mpr h)]; simp
  have hn := realCube_neg hp
  have ht := neg_ne_zero.mpr he
  rw [pilot_match k hk P hp he,pilot_match k hk P hn ht,wire_match k hk P hp he,wire_match k hk P hn ht,alias_reverse p P.odd]
  exact script_reflect k hk P hp (alias_in_real zone_pos hp _ P.odd)
end Flight
end YM.Next.Free
