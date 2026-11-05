import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Buoy

/-!
# Companions on a common marginal

Leaves chain-to-envelope estimates to the field/window
producer (applications also offer a version on unseparated actual ratio
correction entries). More generally here, endpoints may repeat and no
independence assertions on factors. Applicable with some new derivative
costs provided (NOT claiming differentiate-the-integral), proves the
needed quantitative consumption under the integral.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Arc
open Function Filter ProbabilityTheory MeasureTheory Matrix Precision
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Schur
open scoped Topology BigOperators Classical ENNReal
variable {I : Type} [Fintype I] [DecidableEq I]
  {Ξ : Type*} {G : Gauge} {Ω : Type*} [MeasurableSpace Ω]
  (e : Ξ → I × I)

def meets (i : Ξ) (x : I) := (e i).1=x ∨ (e i).2=x

def hits (Y : Finset Ξ) (d : Ξ → ℝ) (x : I) := ∑ i∈Y, if meets e i x then d i else 0

/-- Positions are relative to the genuine covariance. -/
def mast (i : Ξ) (z : Prices G I) := 1+load z (e i).1+load z (e i).2
lemma mast_one (i : Ξ) (z : Prices G I) : 1 ≤ mast e i z := by
  have hh := load_nonneg z (e i).1
  have hl := load_nonneg z (e i).2
  unfold mast; linarith

/-- Buy this hits cap on exponential score tariffs per endpoint.
Cost-per-letter also depends on this in return (not height). -/
def pinch (L : ℝ) := leisure L / 6
lemma pinch_pos {L : ℝ} (hL : 0<L) : 0 < pinch L := by unfold pinch; have := leisure_pos hL; linarith

def tail (L ρ : ℝ) (m : ℕ) := Real.exp (-(pinch L)*(m:ℝ)*ρ^2)
lemma tail_pos (L ρ : ℝ) (m : ℕ) : 0 < tail L ρ m := Real.exp_pos _

variable (Y : Finset Ξ)

def ends : Finset I := Y.biUnion (fun i=>{(e i).1,(e i).2})

lemma wakes (i : Ξ) (h : i∈Y) (x : I) (ht : meets e i x) : x∈ends e Y := Finset.mem_biUnion.mpr ⟨i,h, by simpa [meets] using (Or.imp Eq.symm Eq.symm ht)⟩ -- meets unfolds?
lemma ends_price : (ends e Y).card ≤ Y.card*2 :=
  (Finset.card_biUnion_le).trans (by simpa using Finset.sum_le_sum (s:=Y) (f:=fun i=> ({(e i).1,(e i).2}:Finset I).card) (g:=fun _=> (2:ℕ)) (fun i _=>by
    by_cases h : (e i).1=(e i).2 <;> simp [h]))

variable (w d : Ξ→ℝ) (r : Ξ → Ω × Prices G I → ℝ)
/-- envelope form can be used as a sufficient test (sets
`w_i=x_gamma`, `d_i=2 x_gamma` for order 1 L1; include 4 multiplier
on tariff & pow on w before charging L4). Even if z positions are
coincident on every label, requires NO independence on that overlap.
Arbitrary other conditional variables through Ω. -/
structure Covered (L : ℝ) : Prop where
  pos_w i : i∈Y → 0≤w i
  pos_d i : i∈Y → 0≤d i
  spent x : hits e Y d x ≤ pinch L
  honest i : i∈Y → Measurable (r i)
  quote i (hi : i∈Y) (y) : ‖r i y‖ ≤ w i * Real.exp (d i*mast e i y.2)

variable {Y r w d} {L : ℝ}

lemma Covered.rate {e : Ξ → I × I} (h : Covered e Y w d r L) (i : Ξ) (hi : i∈Y) : d i ≤ pinch L := by
  let x := (e i).1
  apply le_trans ?_ (h.spent x)
  unfold hits
  let v j : ℝ := if meets e j x then d j else 0
  have hv j (hj:j∈Y) : 0 ≤ v j := by unfold v; split; exact h.pos_d j hj; exact le_rfl
  calc
    d i = v i := by unfold v; rw [if_pos (show meets _ _ _ from Or.inl rfl)]
    _ ≤ ∑ j∈Y,v j := Finset.single_le_sum hv hi

lemma two_power (i : Ξ) {a : ℝ} (ha : 0≤a) (z : Prices G I) :
    a*(load z (e i).1+load z (e i).2) ≤
      2 * ∑ x, (if meets e i x then a else 0)*load z x := by
  let f x : ℝ := (if meets e i x then a else 0)*load z x
  have hf x : 0 ≤ f x := mul_nonneg (show 0≤(if meets e i x then a else 0) from by split; exact ha; rfl) (load_nonneg ..)
  have ht x (hx : meets e i x) : a*load z x ≤ ∑ j,f j := (le_of_eq (by simp [f,hx])).trans (Finset.single_le_sum (f:=f) (fun j _=> hf j) (Finset.mem_univ x))
  have hl := ht _ (show meets e i _ from Or.inl (Eq.refl (e i).1))
  have hr := ht _ (show meets e i _ from Or.inr (Eq.refl (e i).2))
  change _≤2*∑ j,f j; linarith

lemma Covered.strike {e : Ξ → I × I} (h : Covered e Y w d r L) (z : Prices G I) :
    (∑ i∈Y,d i * mast e i z) ≤ (Y.card:ℝ)* pinch L + 2*pinch L * enrolled (ends e Y) z := by
  let f i x : ℝ := (if meets e i x then d i else 0)*load z x
  let u i := pinch L+ 2*∑ x,f i x
  have hp i (hi : i∈Y) : d i * mast e i z ≤ u i := by
    have hz := h.rate i hi
    have hv := two_power e i (h.pos_d i hi) z
    unfold mast u; change d i*_ ≤ pinch L+2*(∑ x, _); unfold f; linarith
  apply le_trans (Finset.sum_le_sum hp)
  unfold u
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm,Finset.sum_const,nsmul_eq_mul]
  have hs x : ∑ i∈Y,f i x = hits e Y d x * load z x := by unfold f hits; rw [Finset.sum_mul]
  simp_rw [hs]
  rw [add_le_add_iff_left,mul_assoc 2]; gcongr 2 * ?_
  calc
    (∑ x:I, hits e Y d x * load z x) = ∑ x∈ends e Y, hits e Y d x * load z x := (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      rw [hits,Finset.sum_eq_zero (fun j hj=>if_neg (fun h=>hi (wakes e _ _ hj i h))),zero_mul]).symm
    _ ≤ _ := by unfold enrolled; rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_right (h.spent i) (load_nonneg _ _))

def wires (Y : Finset Ξ) (r : Ξ → Ω × Prices G I → ℝ) (y : Ω × Prices G I) := ∏ i∈Y,r i y

lemma Covered.net {e : Ξ → I × I} (h : Covered e Y w d r L) (y) :
    ‖wires Y r y‖ ≤ (∏ i∈Y,w i)*Real.exp ((Y.card:ℝ)*pinch L+2*pinch L * enrolled (ends e Y) y.2) := by
  let f i := w i * Real.exp (d i*mast e i y.2)
  have he := h.strike y.2
  unfold wires; rw [norm_prod]
  apply le_trans (Finset.prod_le_prod (s:=Y) (fun i _=>norm_nonneg _) (fun i hi=>h.quote i hi y))
  rw [Finset.prod_mul_distrib,← Real.exp_sum]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Finset.prod_nonneg (fun i hi=>h.pos_w i hi))

lemma Covered.wise {e : Ξ → I × I} (h : Covered e Y w d r L) : Measurable (wires Y r) := Finset.measurable_fun_prod _ (fun i hi=>h.honest i hi)

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

def scores (J : Finset I) (k : ℕ) (z : Prices G I) := (1+enrolled J z)^k
lemma scores_nn (J : Finset I) (k : ℕ) (z : Prices G I) : 0 ≤ scores J k z := pow_nonneg (by linarith only [enrolled_nn J z]) _
@[fun_prop] lemma measurable_scores (J : Finset I) (k : ℕ) : Measurable (α:=Prices G I) (scores J k) := by unfold scores; fun_prop

def dusk (G : Gauge) (q : ℕ) (k : ℕ) : ℝ := (1+(q*Fintype.card G.ColorIndex:ℕ))^(k+1)
lemma dusk_one (G : Gauge) (k q : ℕ) : 1 ≤ dusk G q k := one_le_pow₀ (by have hh : 0≤((q*Fintype.card G.ColorIndex:ℕ):ℝ) := Nat.cast_nonneg _; linarith)

lemma score_power (L : ℝ) (hL : 0<L) (k : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ {I : Type} [Fintype I] [DecidableEq I] (J : Finset I) {C : Gaussian.Table (I × G.ColorIndex)} {η},
    C.PosSemidef → Numeric C η L → Integrable (scores J k) (cloud C) ∧
      (∫ z,scores J k z ∂cloud C) ≤ D*dusk G J.card k := by
  obtain ⟨D,hD,H⟩ := many L hL k; refine ⟨D,hD,?_⟩
  intro I hI _ J C η hC h
  let e : J × G.ColorIndex → I × G.ColorIndex := fun i => (i.1,i.2)
  have he : Function.Injective e := fun i j h' => Prod.ext (Subtype.ext (congr_arg Prod.fst h')) (congr_arg (fun t : I × G.ColorIndex => t.2) h')
  let A := C.submatrix e e
  have hA : Numeric A η L := nominated e he h
  let g (z:Prices G J):=(1+gaugeMark z)^k
  obtain ⟨ht,hb⟩ := H (hC.submatrix e) hA
  have hM (z : Prices G I) : enrolled J z = gaugeMark (pocket e z) := by
    rw [gaugeMark,price_square (ι:=J)]
    unfold enrolled load
    rw [Finset.sum_subtype J (show ∀ i, i∈J ↔ i∈J from fun _=>Iff.rfl)]; rfl
  obtain ⟨hz,hf⟩ := consumes (pocket_eq e hC) g (by unfold g; fun_prop)
  rw [dusk,← Fintype.card_coe J,← Fintype.card_prod (↥J) G.ColorIndex]
  simp_rw [show scores J k (G:=G)=g ∘ pocket e from by funext z; unfold scores g; rw [hM]; rfl]
  exact ⟨hz.mpr ht,hf.trans_le hb⟩

lemma balanced {U P : Finset I} {C : Gaussian.Table (I × G.ColorIndex)} {η : ℝ} {k} (hL : 0<L)
    (h : C.PosSemidef) (hC : Numeric C η L) (D : ℝ) (hD : 0<D)
    (hk : Integrable (scores P (2*k)) (cloud C)) (hm : (∫ z,scores P (2*k) z ∂cloud C) ≤ D * dusk G P.card (2*k)) :
    let t:= 3*pinch L
    let f z := scores P k z*levy U t z
    Integrable f (cloud C) ∧ (∫ z,f z ∂cloud C) ≤ (1+D)*dusk G P.card (2*k)*tuck G^U.card := by
  intro t f
  have ht : 2*t = leisure L := by unfold t pinch; ring
  have hx : t ≥ 0 := by unfold t; have := pinch_pos hL; positivity
  obtain ⟨hi,hb⟩ := held_mgf h hC hL (show 0≤2*t by linarith) ht.le U
  let g (z : Prices G I) := scores P (2*k) z + levy U (2*t) z
  have hp z : ‖f z‖ ≤ g z := by
    change ‖scores P k z*levy U t z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (scores_nn ..) (levy_pos ..).le)]
    have hz := sq_nonneg (scores P k z-levy U t z)
    have hf : scores P k z (G:=G)^2 = scores P (2*k) z := by unfold scores; rw [← pow_mul,Nat.mul_comm k 2]
    have he : levy U t z (G:=G)^2 = levy U (2*t) z := by unfold levy; rw [sq,← Real.exp_add]; congr 1; ring
    unfold g; nlinarith only [hz,mul_nonneg (scores_nn P k z) (levy_pos U t z).le,hf,he]
  have hg : Integrable g (cloud C) := hk.add hi
  have hf : Integrable f (cloud C) := hg.mono' (by unfold f; fun_prop) (ae_of_all _ hp)
  refine ⟨hf,(integral_mono hf hg (fun i=>(le_abs_self _).trans (hp i))).trans ?_⟩
  unfold g; rw [integral_add hk hi]; apply le_trans (add_le_add hm hb)
  set p := dusk G P.card (2*k); set q:ℝ:= tuck G^U.card
  have ht : 1≤p := dusk_one ..
  have hu : 1≤q := one_le_pow₀ (tuck_one _)
  nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ q by linarith),mul_le_mul_of_nonneg_left hu (show 0≤D*p by positivity)]

/-- Even without turning rarity/ratio/scores over to integration over
components, terms with these explicit tests get payment on the true sector
law. Score coordinates P can be arbitrarily larger than the endpoints
(e.g. unselected derivative receipts). H bill could also be compulsory
price/companions already legitimately incurred; combine at point evaluation.
Zero-test availability of all distinct triggers required EVEN after striking
the term. C is not inferred from a matrix of another law or assigned per
factor. All constants common for same L and fixed k.

`w i` may include old-cover or path-polynomial charges and small E parent
coefficient. Endpoint-less optionals can be included with arbitrary pair
and d=0 (or if type empty, beforehand in H).
-/
theorem same_law {G : Gauge} (L : ℝ) (hL : 0<L) (k : ℕ) : ∃ D : ℝ, 1≤D ∧
    ∀ {I : Type} [Fintype I] [DecidableEq I] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {C : Gaussian.Table (I × G.ColorIndex)} {η : ℝ}, C.PosSemidef → Numeric C η L →
      ∀ {Ξ : Type*} {Y : Finset Ξ} {e : Ξ → I × I} (P J : Finset I) {ρ H : ℝ} {w d : Ξ→ℝ} {r : Ξ→Ω × Prices G I→ℝ},
        Covered e Y w d r L → 0≤ρ → 0≤H →
        ∀ v : Ω × Prices G I → ℝ, Measurable v →
          (∀ y, ‖v y‖ ≤ H*scores P k y.2) → (∀ y, v y≠0 → y.2∈triggered J ρ) →
      let U := μ.prod (cloud C)
      let f y := v y*wires Y r y
      Integrable f U ∧
        (∫ y,‖f y‖ ∂U) ≤ H*D*dusk G P.card (2*k)*(tail L ρ J.card*tuck G^J.card) *
          ∏ i∈Y, (Real.exp (pinch L)*tuck G^2*w i) := by
  obtain ⟨D,hD,H⟩ := score_power (G:=G) L hL (2*k)
  refine ⟨1+D,by linarith,?_⟩
  intro I hI _ Ω hΩ μ hμ C η hC hx Ξ Y e P J ρ H0 w d r h hρ hH v hv hb he U0 f
  let X:=ends e Y; let U:=J∪X
  have hm {z : Prices G I} (Y : Finset I) (h : Y ⊆ U) : enrolled Y z ≤ enrolled U z :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _=>load_nonneg ..)
  let t := pinch L
  have ht : 0≤t := (pinch_pos hL).le
  let p := ∏ i∈Y,w i
  have hp : 0 ≤ p := Finset.prod_nonneg h.pos_w
  let R := tail L ρ J.card
  have hR : 0<R := tail_pos ..
  let M := H0*R*p*(Real.exp ((Y.card:ℝ)*t))
  let g (z : Prices G I) := scores P k z*levy U (3*t) z
  have hg y : ‖f y‖ ≤ M*g y.2 := by
    by_cases hz : v y=0
    · change ‖v y*_‖ ≤ _; rw [hz,zero_mul,norm_zero]; unfold M g
      have h1 := scores_nn P k y.2; have h2 := levy_pos U (3*t) y.2; positivity
    have hN : R*levy J t y.2 ≥ 1 := (le_of_eq (show 1=buzzer J ρ y.2 from (Set.indicator_of_mem (he y hz) (fun _=> (1:ℝ))).symm)).trans (buzzing J ht hρ y.2)
    have hs:=h.net y
    have hE : levy J t y.2 * Real.exp ((Y.card:ℝ)*pinch L + 2*pinch L * enrolled X y.2) ≤
        Real.exp ((Y.card:ℝ)*t) * levy U (3*t) y.2 := by
      unfold levy; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
      change _+((Y.card:ℝ)*t+2*t*_)≤ _
      linarith only [mul_le_mul_of_nonneg_left (hm (z:=y.2) J (Finset.subset_union_left)) ht,
        mul_le_mul_of_nonneg_left (hm (z:=y.2) X (Finset.subset_union_right)) ht]
    have h1 := scores_nn P k y.2
    unfold f; rw [norm_mul]
    apply le_trans (mul_le_mul (le_trans (hb y) (le_mul_of_one_le_right (mul_nonneg hH h1) hN)) hs (norm_nonneg _) (by positivity : 0≤H0*_*_))
    change H0*scores _ _ _*(_*_) * (p*Real.exp _) ≤ _
    convert_to H0*scores P k y.2 * R * p *
      (levy J t y.2 * Real.exp ((Y.card:ℝ)*pinch L + 2*pinch L * enrolled X y.2)) ≤
      H0*scores P k y.2 * R * p * (Real.exp ((Y.card:ℝ)*t)*levy U (3*t) y.2) using 1
    · ring
    · unfold M g t; ring
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  obtain ⟨hf,hm⟩ := balanced hL hC hx D hD (H P hC hx).1 (H P hC hx).2 (U:=U) (k:=k) -- e binder? balanced included e erroneously?
  obtain ⟨h1,h2⟩ := consumes (measurePreserving_snd (μ:=μ) (ν:=cloud C)) g (by unfold g; fun_prop)
  have h0 : Integrable (fun y : Ω × Prices G I=>M*g y.2) U0 := (h1.mpr hf).const_mul _
  have hi : Integrable f U0 := h0.mono' (hv.mul h.wise).aestronglyMeasurable (ae_of_all _ hg)
  refine ⟨hi,(integral_mono hi.norm h0 hg).trans ?_⟩
  rw [integral_const_mul,h2]
  have hM : 0 ≤ M := by unfold M; positivity
  have hU : tuck G^U.card ≤ tuck G^(J.card+Y.card*2) := pow_le_pow_right₀ (tuck_one _)
    (Finset.card_union_le _ _|>.trans (Nat.add_le_add_left (ends_price e Y) _))
  set a := (1+D)*dusk G P.card (2*k)
  have ha : 0 ≤ a := by unfold a; have := dusk_one G (2*k) P.card; positivity
  refine le_trans (mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hU ha)) hM) ?_
  unfold M p
  rw [Finset.prod_mul_distrib,Finset.prod_const,pow_add,pow_mul,Real.exp_nat_mul]
  dsimp only [t,R]
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm Y.card]; unfold a
  exact le_of_eq (by ring)
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Arc
