import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Growth
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Patch
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Selected (and A-flat) gap, on all admitted volumes

From shell inequality purchased with E02
use just the localized diagonal linear price F01 in one canonical
orientation.

Choose gauges per LINK (not per row on the LHS of that
price).

Certified perturbation for each contributing row using those
gauges, paid back on the unrotated D so licenses global counting.

Any
symbolic fine choices with certified output flags after delay pass this
calculation (even without realizability).

This is a price on ALL of the
active vector space (AxisChart on the tree in the case of non-frozen;
arbitrary directions there, not just contractible or based perturbations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Gap
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Tree
open YM.Work.F01 YM.Push.SectorMeasure YM.Bid YM.Next.Fluctuations Matrix
open YM.Next.SectorChange.Motion LocalJet Gaussian Rows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

@[simp] lemma freshly_read (A : Stores S) (F : Forest S.ratio) (W : Stencils S) (a : LogArray G (Active A x F)) (i : Active A x F) :
    fresh x W A F a i.val.val = a i := by
  unfold fresh
  rw [dif_pos i.val.property,dif_pos i.property]

lemma power_active (A : Stores S) (F : Forest S.ratio) (W : Stencils S) (a : LogArray G (Active A x F)) :
    powerCost (fresh x W A F a)= ∑ i, ‖a i‖^2 := by
  let e (i : Active A x F) := i.val.val
  have he : Injective e := fun _ _ eq => Subtype.ext (Subtype.ext eq)
  let h := fresh x W A F a
  unfold powerCost
  calc
    _ = ∑ i ∈ univ.image e, ‖h i‖^2 := by
      symm; refine sum_subset (subset_univ _) fun i hi hh => ?_
      unfold h fresh
      split <;> rename_i h'
      · split
        next H => exact (hh (mem_image.mpr ⟨⟨⟨i,h'⟩,H⟩,mem_univ _,rfl⟩)).elim
        simp
      · simp
    _ = _ := by rw [sum_image (fun _ _ _ _ => @he _ _)]; simp only [h,e,freshly_read]

lemma energy_canonical (T : Tube G S) {P : Teller G} (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (a : Prices G (Active A x F)) (hT : P.Funds S T) :
    let W := shots S x; let t:=fresh x W A F (tape a); let γ := S.kernel.penalty
    slip^2 * (T.high.direct * (∑ i : Cell f, ‖plaquetteJet S V 1 i t‖^2)+γ*(∑ i, ‖blockJet V k 1 i t‖^2)) ≤
        a ⬝ᵥ (Rows.gram T x V k W A F *ᵥ a) := by
  intro W t γ
  let D := move T x V k W A F
  unfold Rows.gram W
  change _ ≤ a ⬝ᵥ ((Dᵀ * D) *ᵥ a)
  rw [← mulVec_mulVec,dotProduct_transpose_mulVec, price_square]
  obtain ⟨l,m,H,-⟩ := hT.feeds
  dsimp only [D,W]; rw [moved _ _ _ _ _ _ _ H a, tape.apply_symm_apply, selected_all _ _ _ _ _ _ _ (funds_branch hT)]
  let X := (slip • bump T x V k t)
  have hi (i : Cell f) : (slip^2*T.high.direct)*‖plaquetteJet S V 1 i t‖^2 =
      ‖X (1,.inl (i,false))‖^2 := by
    simp only [X,bump,faceKick,Sum.elim_inl, Bool.false_eq_true, ↓reduceIte,Pi.smul_apply,norm_smul,
      Real.norm_of_nonneg slip_pos.le, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,Real.sq_sqrt T.high.quadratic_pos.le,mul_assoc]
  have hb (i : Bond c) : (slip^2*γ)*‖blockJet V k 1 i t‖^2 = ‖X (1,.inr i)‖^2 := by
    simp only [X,bump,noiseKick,Sum.elim_inr,Pi.smul_apply,norm_neg,norm_smul,
      Real.norm_of_nonneg slip_pos.le, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,Real.sq_sqrt S.kernel.penalty_pos.le,mul_assoc,γ]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply le_trans _ (single_le_sum (f:=fun s => ∑ i, ‖X (s,i)‖^2) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ 1))
  rw [mul_add,← mul_assoc,← mul_assoc, Finset.mul_sum,Finset.mul_sum,Fintype.sum_sum_type]
  simp_rw [hi,hb]
  apply add_le_add_left
  unfold Twin
  conv_rhs => rw [Fintype.sum_prod_type]
  exact sum_le_sum fun i _ => single_le_sum (f:=fun b : Bool => ‖X (1,.inl (i,b))‖^2) (fun _ _ => sq_nonneg _) (mem_univ false)

def lots (P : Patch) (r : ℕ) : ℝ := Fintype.card (Site P.L) * (grain r * Fintype.card Axis) * grain r
def fineCap (P : Patch) (r : ℕ) : ℝ := Fintype.card PlaqAxes * Fintype.card (Site P.L)* lots P r
def sideCap (P : Patch) (r : ℕ) : ℝ := Fintype.card Axis * lots P r

lemma buys (S : StepData c f) (a : Directions G f) (r : ℕ) :
    (∑ i : Cell f, settle S (S.ratio.parent i.1) r a^2) ≤ fineCap S.patch r * powerCost a ∧
    (∑ i : Bond c, settle S i.1 r a^2) ≤ sideCap S.patch r * powerCost a := by
  unfold fineCap sideCap
  have hh := samples S a r
  change _ ≤ lots S.patch r * powerCost a at hh
  have hi {n : Side} {F : Site n → ℝ} (E : Type) [Fintype E] :
      (∑ i : Site n × E, F i.1)=(Fintype.card E:ℝ) * ∑ i, F i := by rw [Fintype.sum_prod_type]; simp [mul_sum]
  change (∑ i : Site f × PlaqAxes, _) ≤ _ ∧ (∑ i : Site c × Axis, _) ≤ _
  rw [hi (F:=fun i => settle S (S.ratio.parent i) r a^2),hi (F:=fun i => settle S i r a^2), sum_parent S.ratio (fun i => settle S i r a^2)]
  constructor
  · change ((Fintype.card PlaqAxes:ℝ)*((Fintype.card (Site S.patch.L):ℝ)*_)) ≤ _
    simp_rw [mul_assoc]; gcongr
  rw [mul_assoc]; gcongr

private def debit (S : StepData c f) {Y : Type} [Fintype Y] (D : Y → G.Color) (i : Y → Site c) (r : ℕ)
    (a : Directions G f) (ε : ℝ) (y : Y) : ℝ := ‖D y‖ + ε * settle S (i y) r a

private lemma debit_sum (S : StepData c f) {Y : Type} [Fintype Y] (D : Y → G.Color) (i : Y → Site c) (r : ℕ)
    (a : Directions G f) (ε : ℝ) {C : ℝ} (h : ∑ x, settle S (i x) r a^2 ≤ C * powerCost a) :
    (∑ x, debit S D i r a ε x^2) ≤ 2*(∑ x, ‖D x‖^2) + (2*ε^2*C)*powerCost a := by
  let b (x) : ℝ := ε * settle S (i x) r a
  apply le_trans (b:=∑ x, (2*‖D x‖^2+(2*ε^2)*settle S (i x) r a^2)) ?_ ?_
  · apply sum_le_sum; intro x _; have hs := sq_nonneg (‖D x‖- b x); unfold b at hs; unfold debit; nlinarith
  rw [sum_add_distrib,← Finset.mul_sum, ← Finset.mul_sum, mul_assoc (2*ε^2)]
  gcongr

private lemma prices (S : StepData c f) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices)
    (h : S.patch.Branches S.kernel G) (r : ℝ) {ε m : ℝ} (he : 0 < ε) (hm : 0 < m)
    (HC : ∀ U : Config G f, Pressure.Stores.SliceSet S F U → ∀ e : Bond f, usable S U (S.ratio.parent e.1) k →
      Cops (S:=S) U 1 (S.prediction U k) e m)
    (H : ∀ i : Active A r F, Sponsored A F k V i ε)
    (a : LogArray G (Active A r F)) :
    let t := fresh r (shots S r) A F a
    let β := curlFactor S.patch.L (box (macroR S.patch)) m
    let q := probeFactor S.patch.L
    powerCost t ≤ β * (2*(∑ i : Cell f, ‖plaquetteJet S V 1 i t‖^2) + (2*ε^2*fineCap S.patch 1)*powerCost t)+
      q * (2*(∑ i, ‖blockJet V k 1 i t‖^2)+(2*ε^2*sideCap S.patch (predReach S.patch))*powerCost t) := by
  intro t β q
  let f₀ (i : Cell f) : G.Color := plaquetteJet S V 1 i t
  let y₀ (i : Bond c) : G.Color := blockJet V k 1 i t
  let X := debit S f₀ (fun i => S.ratio.parent i.1) 1 t ε
  let Y := debit S y₀ Prod.fst (predReach S.patch) t ε
  let eF : Cell f ≃ Body 2 f := Equiv.prodCongr (Equiv.refl _) plaqEquiv
  let eI : Bond c ≃ Body 1 c := Equiv.prodCongr (Equiv.refl _) axisEquiv
  let X' := X ∘ eF.symm; let Y' := Y ∘ eI.symm
  have hF i : 0 ≤ X i := add_nonneg (norm_nonneg _) (mul_nonneg he.le (settle_nonneg ..))
  have hI i : 0 ≤ Y i := add_nonneg (norm_nonneg _) (mul_nonneg he.le (settle_nonneg ..))
  have ht (i : Bond f) : ‖t i‖ ≤ m * (∑ z ∈ box (macroR S.patch), ∑ p : PlaqAxes,
      X' (wrap f z+S.ratio.embed (S.ratio.parent i.1), plaquette p)) + Y' (pole (S.ratio.parent i.1,i.2)) := by
    by_cases hu : t i = 0
    · rw [hu,norm_zero]; apply add_nonneg (mul_nonneg hm.le (sum_nonneg fun _ _ => sum_nonneg fun _ _ => hF _)) (hI _)
    have hl : ∃ j : Active A r F, j.val.val=i := by
      unfold t fresh at hu
      split at hu
      · rename_i hi; split at hu
        next hb => exact ⟨⟨⟨_,hi⟩,hb⟩,rfl⟩
        next hb => exact (hu rfl).elim
      · exact (hu rfl).elim
    obtain ⟨l,rfl⟩ := hl
    obtain ⟨w,hW⟩ := H l
    let b := Flat.labels (swing w t)
    have ha (p : Bond f) (hp : p∈ F.trunks) : collect G b p=0 := by
      unfold b; rw [Flat.collected,swing_eval]; change G.adjoint _ (fresh r (shots S r) A F a p)=0
      unfold fresh; rw [dif_neg (not_not.mpr hp),map_zero]
    have hh := link_bound S h F k b ha m hm.le l.val.val (fun U hU => HC U hU _)
    change ‖collect G b l.val.val‖ ≤ _ at hh
    nth_rw 1 [show collect G b=swing w t from Flat.collected _,swing_size] at hh
    obtain ⟨hz,hb⟩ := hW t
    refine hh.trans (add_le_add (mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => ?_)) hm.le) ?_)
    · refine sum_le_sum (fun p _ => ?_)
      unfold X' Function.comp eF
      -- plaqEquiv.symm (plaquette p)
      simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply]
      rw [show plaqEquiv.symm (plaquette p)=p from plaqEquiv.symm_apply_apply p]
      exact hz i hi p
    unfold Y' Function.comp eI pole
    simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply]
    rw [show axisEquiv.symm (coord _)=_ from axisEquiv.symm_apply_apply _]
    exact hb
  apply (sum_estimate S.ratio _ X' Y' (fun i => ‖t i‖) m (fun _ => norm_nonneg _) ht).trans
  have hsX := eF.symm.sum_comp (fun x => X x^2)
  have hsY := eI.symm.sum_comp (fun x => Y x^2)
  unfold X' Y'; change β*(∑ b, X (eF.symm b)^2)+q*(∑ b,Y (eI.symm b)^2) ≤ _
  rw [hsX,hsY]
  refine add_le_add (mul_le_mul_of_nonneg_left (debit_sum _ _ _ _ _ _ (buys S t 1).1) (by unfold β curlFactor; positivity))
    (mul_le_mul_of_nonneg_left (debit_sum _ _ _ _ _ _ (buys S t _).2) (by unfold q probeFactor; positivity))
/-- Absorb perturbation and give a price before period. -/
private lemma arn (m q P Q c k : ℝ) (h : 0≤m) (hq : 0 ≤ q) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hc : 0<c) (hk : 0<k) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧ ∀ x y z : ℝ, 0≤x → 0≤y → 0≤z →
      z ≤ m*(2*x+(2*ε^2*P)*z)+q*(2*y+(2*ε^2*Q)*z) →
      η*z ≤ c*x+k*y := by
  let n := 1 + 2*m*P+2*q*Q
  have hn : 1 ≤ n := by unfold n; nlinarith only [mul_nonneg h hP,mul_nonneg hq hQ]
  let ε := (2*n)⁻¹
  let η := min c k / (4*(m+q+1))
  have hε : 0<ε := inv_pos.mpr (by linarith)
  have hη : 0<η := div_pos (lt_min hc hk) (by positivity)
  have hf : n*ε = 1/2 := by unfold ε; field_simp
  have hm : ε ≤ 1 := by nlinarith
  have he : m*(2*ε^2*P)+q*(2*ε^2*Q) ≤ 1/2 := by
    calc
      _ ≤ n*ε^2 := by unfold n; nlinarith only [sq_nonneg ε]
      _ ≤ n*ε := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      _ = _ := hf
  have hl : η*(4*m) ≤ c ∧ η*(4*q) ≤ k := by
    have hz : η*(4*(m+q+1))=min c k := div_mul_cancel₀ _ (by positivity)
    exact ⟨((mul_le_mul_of_nonneg_left (by linarith) hη.le).trans_eq hz).trans (min_le_left ..),
      ((mul_le_mul_of_nonneg_left (by linarith) hη.le).trans_eq hz).trans (min_le_right ..)⟩
  refine ⟨ε,η,hε,hη,fun x y z hx hy hv hh => ?_⟩
  have hj := mul_le_mul_of_nonneg_right he hv
  have ht : z ≤ 4*m*x+4*q*y := by linarith
  apply (mul_le_mul_of_nonneg_left ht hη.le).trans
  rw [mul_add,← mul_assoc,← mul_assoc]
  simp only [← mul_assoc] at hl ⊢
  exact add_le_add (mul_le_mul_of_nonneg_right hl.1 hx) (mul_le_mul_of_nonneg_right hl.2 hy)

private lemma armed (S : StepData c f) (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (T : Tube G S)
    {Pt : Teller G} (hT : Pt.Funds S T) (V : Config G c) (x : ℝ) {η m ε : ℝ} (hε : 0< ε) (he : 0<m) (hi : 0 < η)
    (HC : ∀ U : Config G f, Pressure.Stores.SliceSet S F U → ∀ e : Bond f, usable S U (S.ratio.parent e.1) k →
      Cops (S:=S) U 1 (S.prediction U k) e m)
    (H : ∀ i : Active A x F, Sponsored A F k V i ε)
    (h : let β := curlFactor S.patch.L (box (macroR S.patch)) m; let q := probeFactor S.patch.L
      ∀ t u z : ℝ, 0≤t → 0≤u → 0≤z →
      z ≤ β*(2*t+(2*ε^2*fineCap S.patch 1)*z)+q*(2*u+(2*ε^2*sideCap S.patch (predReach S.patch))*z) →
        η*z ≤ T.high.direct*t+S.kernel.penalty*u) (a : Prices G (Active A x F)) :
    (slip^2 * η)*(a ⬝ᵥ a) ≤ a ⬝ᵥ (Rows.gram T x V k (shots S x) A F *ᵥ a) := by
  rw [price_square,← power_active A F (shots S x)]
  have hr := prices S A F V k (funds_branch hT) x hε he HC H (tape a)
  apply le_trans _ (energy_canonical T V k A F a hT)
  rw [mul_assoc]; gcongr
  exact h _ _ _ (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _) hr

private lemma temp_deploy (G : Gauge) (P : Patch) {δ : ℝ} (hd : 0 < δ) : ∀ᶠ x : ℝ in atTop, permit P*temp x ≤ δ := by
  have h0 : ∀ᶠ x : ℝ in atTop, permit P * fiery G x (1:Side) ≤ largeT G x 1 := Work.E01.fiery_le G 1 _
  filter_upwards [h0, (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hd)] with x hx he
  simpa [fiery,betaF] using hx.trans he

/-- Uniform fixed-L,j G,Teller gap also when precision is evaluated on
nonrealizable sectors. Uses only the flag recording. `P=Teller` chosen
before L, but η here post-L. No determinant/covariance hypothesis. -/
theorem not_flat (G : Gauge) (P : Patch) (Pt : Teller G) (hS : P.Branches Pt.bind G) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ a : Prices G (Active A x F), η*(a ⬝ᵥ a) ≤ a ⬝ᵥ (Rows.gram T x V k (shots S x) A F *ᵥ a) := by
  obtain ⟨m,hm,H⟩ := Work.E02.answer G P.L P.J Pt.bind
  let L := P.L; let n := curlFactor L (box (macroR P)) m; let q := probeFactor L
  obtain ⟨ε,η,hε,hη,h⟩ := arn n q (fineCap P 1) (sideCap P (predReach P)) Pt.top.clip.direct Pt.bind.penalty
    (by unfold n curlFactor; positivity) (by unfold q probeFactor; positivity)
    (by unfold fineCap lots grain; positivity) (by unfold sideCap lots grain; positivity)
    Pt.top.clip.quadratic_pos Pt.bind.penalty_pos
  obtain ⟨δ,hδ,hs⟩ := sponsorship P Pt.bind G hS hε
  refine ⟨slip^2 * η,mul_pos (pow_pos slip_pos _) hη, ?_⟩
  filter_upwards [temp_deploy (G:=G) P hδ, Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+1)] with x hx hB
  intro c f S T hP hp hT A F k V hv a
  have hF : c.val ≤ f.val := S.sizes ▸ le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
  apply armed S F A k T hT V x hε hm hη
  · intro U h e he
    apply H c f S hT.knobs (congr_arg RG.Patch.L hP) (congr_arg RG.Patch.J hP) ?_ ?_ F U h 1 e k he
    · rw [hP]; unfold allot at hB; omega
    · omega
  · exact hs S F A V k x hP hT.knobs (by omega) (by omega) hv hx
  rw [hP,hT.knobs,hT.high]; exact h

/-- A_flat separately: every A (incl exact empty one), even without a
temperature delay since the rotation prices already hold at identity.
Each input already satisfies `PriceGap` analogue without the ℓ_R row
and over the complete address list in application with empty A. -/
theorem stood (G : Gauge) (P : Patch) (Pt : Teller G) :
    ∃ η : ℝ, 0 < η ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=P → 100*macroR P ≤ f.val → 1<c.val → Pt.Funds S T →
    ∀ (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k:S.Choices), ∀ a : Prices G (Active A x F),
      η*(a ⬝ᵥ a) ≤ a ⬝ᵥ (Rows.gram T x 1 k (shots S x) A F *ᵥ a) := by
  obtain ⟨m,hm,H⟩ := Work.E02.answer G P.L P.J Pt.bind
  let L := P.L; let n := curlFactor L (box (macroR P)) m; let q := probeFactor L
  obtain ⟨ε,η,hε,hη,h⟩ := arn n q (fineCap P 1) (sideCap P (predReach P)) Pt.top.clip.direct Pt.bind.penalty
    (by unfold n curlFactor; positivity) (by unfold q probeFactor; positivity)
    (by unfold fineCap lots grain; positivity) (by unfold sideCap lots grain; positivity)
    Pt.top.clip.quadratic_pos Pt.bind.penalty_pos
  refine ⟨slip^2 * η,mul_pos (pow_pos slip_pos _) hη, @fun c f S T hP hc hL hT x A F k a => ?_⟩
  -- binder implicit
  apply armed S F A k T hT 1 x hε hm hη
  · intro U h e he
    apply H _ _ S hT.knobs (congr_arg RG.Patch.L hP) (congr_arg RG.Patch.J hP) (hP.symm ▸ hc) hL F U h 1 e k he
  · intro i
    refine ⟨1, fun a => ?_⟩
    have ht : swing (1:Site _ → G.El) a=a := by funext i; rw [swing_eval,Pi.one_apply,G.adjoint_one]
    simp_rw [ht, Flat.flat_curl,Flat.flat_probe 1 _ _ _ (funds_branch hT), Flat.stationary_labels]
    exact ⟨fun _ _ _ => le_add_of_nonneg_right (mul_nonneg hε.le (settle_nonneg ..)),
      le_add_of_nonneg_right (mul_nonneg hε.le (settle_nonneg ..))⟩
  rw [hP,hT.high,hT.knobs]; exact h

lemma solvent (S : StepData c f) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (W : Stencils S)
    (V : Config G c) (k : S.Choices) (x : ℝ) {η : ℝ} (hη : 0<η)
    (h : ∀ a : Prices G (Active A x F), η*(a ⬝ᵥ a) ≤ a ⬝ᵥ (Rows.gram T x V k W A F *ᵥ a)) :
    (Rows.gram T x V k W A F).PosDef := by
  let A := Rows.move T x V k W A F
  apply posDef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]; unfold Rows.gram; unfold Matrix.IsSymm; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  intro a ha
  simp only [star_trivial]
  apply lt_of_lt_of_le (mul_pos hη ?_) (h a)
  unfold dotProduct
  simp_rw [← sq]
  obtain ⟨i,hi⟩ := Function.ne_iff.mp ha
  exact (lt_of_lt_of_le (sq_pos_of_ne_zero hi) (single_le_sum (f:=fun i => a i ^ 2) (fun i _ => sq_nonneg _) (mem_univ i)))
end YM.Next.SectorChange.Gap
