import YM.Next.SCHEDULE.Melt
import YM.UVNext.PRICED_KERNELS.Bridge
import YM.UVNext.PRICED_KERNELS.Tori
import YM.UVNext.PRICED_KERNELS.Trees



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Spend the pre-L function on Phi / A0 / emitted stationary directions

Suffices(-K) and ANY physical tests from Wired. Includes curvature-column
release (`d A0` vs curvature of its input, needed  etc without
paying a link-gauge amplitude). Keep H and A0 and T and path choices; these
are estimates on the real linear operators (covers columns and equilibrium
counting case by acting on any periodic data such as requested by φ).
Stay at the correct scaled/native rate. Can thus buy as after width asks
(e.g. `Loads` and `.wish`) before any L. Also buy ν₁ in its actual color
and tree slice field, independent of sample & including N-i arbitrary.

Further transfer estimates of paths attached to these operators or their
Taylor coefficients aren't given—don't produce any cubic or loop hypotheses
from these. No Γ error results. Not heating a nonlinear kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice Wilson RG RG.Supply Precision Pressure Laurent Exterior Bloch Matrix Tree Bid
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace ContDiff

variable {G : Gauge}
section kernel

def stackFee (α A : ℝ) (ι : Type*) [Fintype ι] : ℝ := Real.exp α * (Fintype.card ι * A)
lemma stackFee_nonneg (s : ℝ) {A : ℝ} (ι : Type*) [Fintype ι] (hA : 0 ≤ A) : 0 ≤ stackFee s A ι := by unfold stackFee; positivity

def trFee (j : ℕ) (s A : ℝ) : ℝ := (1+dC 0 s*hikeC j s) * stackFee s A (TypeFace 1)
lemma trFee_nonneg (j : ℕ) (s : ℝ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ trFee j s A := by
  unfold trFee; have := dC_nonneg 0 s; have := hikeC_pos j s; have := stackFee_nonneg s (TypeFace 1) hA; positivity

def curlFee (s A B : ℝ) := ((Fintype.card (TypeFace 2):ℝ)*A) * stackFee s A (TypeFace 2) * ((Fintype.card (TypeFace 2):ℝ)*B)

variable {P : Before} {a : Levels G} {X : MapPrices} {B V : Horizon a} {l} (h : Wired P a X l B V)
    {m N : ℕ} (hm : m < N) (c f : Side) (hf : f.val=c.val*(a.S.block m).val)
include hm h

/-- The `ϑ` rate is `P.frozen G`, itself determined just by direct and Catalog
FlatBill, NOT any of these path or Φ applications. External
`s` for even widths narrowed there. `U` is any prechosen Forest on this Side;
no dependence on other periods' tree choices. 
-/
theorem directions (U : Forest (again a m c f hf).ratio) (s : ℝ) (hs : 0 ≤ s) :
    let K := P.frozen G; let j := a.clock.J (m+1); let α := K.α j; let A := K.Ω j
    let S := again a m c f hf; let g := S.ratio; let L : ℝ := S.patch.L.val
    let R := V.towers N m
    let F := installed g R.A0
    s ≤ α →
    Annuity (site f _) (parent g _) F (s/L) (stackFee s A (TypeFace 1)/L) ∧
    Annuity (parent g _) (site f _) F.transpose (s/L) (L^3*stackFee s A (TypeFace 1)) ∧
    Annuity (site f _) (parent g _) (installed g R.T) (s/L) (stackFee s A (TypeFace 2)/L^2) ∧
    Annuity (parent g _) (site f _) (installed g R.T).transpose (s/L) (L^2*stackFee s A (TypeFace 2)) ∧
    Annuity (site f _) (parent g _) (extracted S U F) (s/L) (trFee j s A) := by
  intro K j α A S g L R F he
  have ht := h.finalCosts.costs N m hm
  obtain ⟨hR,hB⟩ := ht.2.2.2 [] (Nat.zero_le _)
  have hh : 0 < L := Nat.cast_pos.mpr S.patch.L.property
  have hA : 0 < A := (P.active_plan G).2.2.2.2.2.positive j
  have hF : R.A0.strip s (A/L) := by
    have H := Work.F08.strip_mono (show R.A0.strip α (A/L^(1+List.length ([]:List Axis))) from hR) he le_rfl
    simpa using H
  have hV : R.T.strip s (A/L^2) := by
    exact Work.F08.strip_mono (show R.T.strip α (A/L^2) from hB) he le_rfl
  have hp : Annuity (site f _) (parent g _) F (s/L) (stackFee s A (TypeFace 1)/L) := by
    exact (Annuity.paid_cross (g:=g) hF hs).cut le_rfl (le_of_eq (by unfold stackFee; ring))
  refine ⟨hp,(Annuity.paid_cross_reverse (g:=g) hF hs).cut le_rfl (le_of_eq ?_),
    (Annuity.paid_cross (g:=g) hV hs).cut le_rfl (le_of_eq ?_),
    (Annuity.paid_cross_reverse (g:=g) hV hs).cut le_rfl (le_of_eq ?_),
    extract_price S s hs U F _ (stackFee_nonneg _ _ hA.le) hp⟩
  · unfold stackFee; change Real.exp s*(L^4*(_*(A/L)))=_; field_simp
  · unfold stackFee; ring
  unfold stackFee; change Real.exp s*(L^4*(_*(A/L^2)))=_; field_simp

/-- dA₀ released with L⁻² price on full curvature input, `Z := tildeH_f^{-1} T H'...`
on THIS horizon's diagonal T, at any volume. Does not need ψ credit from another
retained stack. Also release at the maximal collapsed ϑ (`K.α` fine), not an
L-dependent coarse width tending to zero on surrounding stages. -/
theorem d_release (hl : ∀ i, 0 ≤ l i) :
    let K := P.frozen G; let j := a.clock.J (m+1); let i := a.clock.J m
    let α := K.α j; let A := K.Ω j; let H := K.Ω i
    let S := again a m c f hf; let g := S.ratio; let L : ℝ := S.patch.L.val
    let R := V.towers N m
    let Z := (V.H N (m+1)).inverse.acts f * installed g R.T * (V.H N m).metric.acts c
    Annuity (site f _) (parent g _) Z (α/L) (curlFee α A H/L^2) ∧
      Z * d 1 c = d 1 f * installed g R.A0 := by
  intro K j i α A H S g L R Z
  have hf := h.finalCosts.all N (m+1) hm f
  have hc := h.finalCosts.all N m hm.le c
  have hM := universal_diagonal a h.sameTrain hm (hl _) (hl _) c f ‹_›
  let X := V.H N (m+1); let Y := V.H N m
  let T := installed g R.T
  have he : T*Y.metric.acts c*d 1 c=X.metric.acts f*d 1 f*installed g R.A0 := by
    change _ = _ * _
    calc
      _ = T*(Y.metric.acts c*d 1 c) := Matrix.mul_assoc ..
      _ = T*Y.diagonal.acts c*d 1 c := by rw [hc.same,Matrix.mul_assoc]
      _ = X.diagonal.acts f*d 1 f*installed g R.A0 := hM.stays
      _ = _ := by rw [← hf.same]
  have hp := K.alpha_pos j
  have hh := K.alpha_pos i
  have h₁ := Annuity.paid_site (h.finalCosts.rows N (m+1) hm).2.2.1 hp.le f
  have hL : 1 ≤ L := Nat.one_le_cast.mpr S.patch.L.property
  have hL' := zero_lt_one.trans_le hL
  have hg := Annuity.cut h₁ (div_le_self hp.le hL) le_rfl
  have hA := (P.active_plan G).2.2.2.2.2.positive j
  have hH := (P.active_plan G).2.2.2.2.2.positive i
  have hu : α ≤ K.α i := (P.active_plan G).2.2.2.2.2.width (step_paid a m).1
  have ht := h.finalCosts.costs N m hm
  have hV : R.T.strip α (A/L^2) := (ht.2.2.2 [] (Nat.zero_le _)).2
  have hw := Annuity.paid_cross (g:=g) hV hp.le
  have hx := Annuity.cut (Annuity.paid_parent g (h.finalCosts.rows N m hm.le).2.1 hh.le)
    (div_le_div_of_nonneg_right hu hL'.le) le_rfl
  have hp' : 0 ≤ α/L := div_nonneg hp.le hL'.le
  have ht : 0 ≤ Real.exp α*((Fintype.card (TypeFace 2):ℝ)*(A/L^2)) := by have : 0 < A := hA; positivity
  have hi : 0 ≤ Fintype.card (TypeFace 2) * H := by have : 0 < H := hH; positivity
  refine ⟨((hg.times hw hp' ht).times hx hp' hi).cut le_rfl (le_of_eq ?_),?_⟩
  · unfold curlFee stackFee; ring
  change (X.inverse.acts f*T*Y.metric.acts c) * d 1 c = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc,← Matrix.mul_assoc T, he]
  simp only [← Matrix.mul_assoc, show X.inverse.acts f*X.metric.acts f = 1 from mul_eq_one_comm.mp hf.inverse,Matrix.one_mul]
end kernel

section radiation
variable {P : Before} {a : Levels G} {X : MapPrices} {B V : Horizon a} {l}
  (h : Wired P a X l B V) {m N : ℕ} (hm : m < N) {c f : Side} (hf : f.val=c.val*(a.S.block m).val)

lemma gather {κ ι : Type*} {n : Side} [Fintype κ] {p : Foot n ι} {q : Foot n κ} {A : Matrix ι κ ℝ} {C s : ℝ}
    (ha : Annuity p q A s C) (i : ι) {v : κ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (he : ∀ j, |v j| ≤ b*gained s (p i) (q j)) : |(A*ᵥv) i| ≤ C*b := by
  rw [Matrix.mulVec,dotProduct]; refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g:=fun j => gained s (p i) (q j)*|A i j| * b) (fun j _ => ?_)) ?_
  · rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)).trans_eq (by ring)
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (ha i) hb

lemma color_component (x : G.Color) (i : G.ColorIndex) : |x i| ≤ ‖x‖ := calc
  _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ i) x| := by simp only [EuclideanSpace.basisFun_inner]
  _ ≤ _ := (abs_real_inner_le_norm _ _).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])

lemma color_count {u : ℝ} (hu : 0 ≤ u) (x : G.Color) (h : ∀ i : G.ColorIndex, |x i| ≤ u) :
    ‖x‖ ≤ Fintype.card G.ColorIndex * u := by
  rcases Nat.eq_zero_or_pos (Fintype.card G.ColorIndex) with hi|hi
  · haveI : IsEmpty G.ColorIndex := (Fintype.card_eq_zero_iff).mp hi
    have he : x=0 := by ext i; exact isEmptyElim i
    rw [he,norm_zero]; positivity
  let k : ℝ := Fintype.card G.ColorIndex
  have hk : 1 ≤ k := Nat.one_le_cast.mpr hi
  have he : ‖x‖^2 ≤ k*u^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine (Finset.sum_le_sum (g:=fun _ => u^2) (fun i _ => ?_)).trans_eq (by simp [k])
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h _) _
  have hh : 0≤k*u := mul_nonneg (by positivity : 0 ≤ (Fintype.card G.ColorIndex:ℝ)) hu
  refine le_of_sq_le_sq ?_ hh
  rw [mul_pow]; exact he.trans (mul_le_mul_of_nonneg_right (show k ≤ k^2 by nlinarith) (sq_nonneg _))

lemma relative_price {S : StepData c f} (U : Forest S.ratio) -- implicit S need variable or autoImplicit
    (R : Matrix (Body 1 f) (Body 1 c) ℝ) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (h : Annuity (site f _) (parent S.ratio _) (extracted S U R) (tollFine S s) C)
    (i : U.Free) (Q : Dir G c) {b : ℝ} (hb : 0 ≤ b)
    (he : ∀ j : Body 1 c, ‖Q j‖ ≤ b*gained (tollFine S s) i.val.1 (parent S.ratio _ j)) :
    ‖relative U R Q i‖ ≤ Fintype.card G.ColorIndex * ((C+Real.exp s)*b) := by
  have hg k (j : Body 1 c) : |(parts G 1 Q k) j| ≤ b*gained (tollFine S s) i.val.1 (parent S.ratio _ j) :=
    (color_component (Q j) k).trans (he j)
  have hR k := gather h (i.val.1,coord i.val.2) hb (hg k)
  have hp : 0 ≤ (C+Real.exp s)*b := by positivity
  refine color_count hp _ fun k => (abs_sub _ _).trans (le_trans (add_le_add (hR k) (show |(linearCopy S.ratio (collect G Q) i) k| ≤ Real.exp s*b from ?_)) (le_of_eq ?_))
  -- fix hR k
  · unfold linearCopy; split_ifs
    · exact (abs_zero.trans_le (mul_nonneg (Real.exp_pos _).le hb))
    let L := (S.patch.L.val:ℝ)
    let j : Body 1 c := (S.ratio.parent i.val.1,coord i.val.2)
    apply (hg k j).trans; rw [mul_comm (Real.exp s)]; apply mul_le_mul_of_nonneg_left _ hb
    apply Real.exp_monotone
    have hh : 0<L := Nat.cast_pos.mpr S.patch.L.property
    exact (mul_le_mul_of_nonneg_left (embed_parent S.ratio i.val.1) (div_nonneg hs hh.le)).trans
      (le_of_eq (div_mul_cancel₀ s hh.ne'))
  ring

include h hm in
/-- pre-L bound on the actual linear stationary solution in *relative*
color/tangent coordinates. Forest arbitrary and L do not enter the price.
Direction costs e.g. at any exponential width up to α in coarse units.
Thus a Γ buyer can use this separately without assuming ν_1 supports. -/
theorem guessed_cost (U : Forest (again a m c f hf).ratio) (s : ℝ) (hs : 0 ≤ s) :
    let K := P.frozen G; let j := a.clock.J (m+1)
    let g := (again a m c f hf).ratio; let F := installed g (V.towers N m).A0
    ∀ (ρ : Dir G c → AxisChart G U), Guessed U F ρ → s ≤ K.α j → ∀ (Q : Dir G c) (i : U.Free) (b : ℝ), 0 ≤ b →
      (∀ e : Body 1 c, ‖Q e‖ ≤ b * gained (s/(a.S.block m).val) i.val.1 (parent g _ e)) →
        ‖(deriv (fun t : ℝ => ρ (t • Q)) 0) i‖ ≤ Fintype.card G.ColorIndex * ((trFee j s (K.Ω j)+Real.exp s)*b) := by
  intro K j g R ρ hρ he Q i b hb hQ
  rw [(hρ Q).deriv]; exact relative_price (S:=again a m c f hf) U R hs (trFee_nonneg _ _ ((P.active_plan G).2.2.2.2.2.positive j).le)
    ((directions h hm c f hf U s hs he).2.2.2.2) i Q hb hQ

include h hm in
/-- E linear curvature release, no harmonic omitted. -/
theorem curl_cost (hl : ∀ i,0 ≤ l i) (Q : Dir G c) :
    let s := again a m c f hf; let L : ℝ := (a.S.block m).val
    let T := V.towers N m
    let A := installed s.ratio T.A0
    let F : Dir G f := fun i => WithLp.toLp 2 (fun j : G.ColorIndex => (A*ᵥ parts G 1 Q j) i)
    let K := P.frozen G; let j := a.clock.J (m+1); let k := a.clock.J m
    let C := curlFee (K.α j) (K.Ω j) (K.Ω k)
    ∀ (i : Body 2 f) (b : ℝ), 0 ≤ b → (∀ v : Body 2 c, ‖dColor G c 1 Q v‖ ≤ b*gained (K.α j/L) i.1 (parent s.ratio _ v)) →
      ‖dColor G f 1 F i‖ ≤ (Fintype.card G.ColorIndex)*((C/L^2)*b) := by
  intro S L T A F K j k C i b hb he
  obtain ⟨hZ,hI⟩ := d_release h hm c f hf hl
  let Z := (V.H N (m+1)).inverse.acts f * installed S.ratio T.T * (V.H N m).metric.acts c
  have hg (i : ℕ) : 0 < K.Ω i := (P.active_plan G).2.2.2.2.2.positive i
  have hC : 0 ≤ C := by
    have h₁ := stackFee_nonneg (K.α j) (TypeFace 2) (hg j).le
    have ht := hg j; have hm := hg k; unfold C curlFee; positivity
  refine color_count (by positivity) _ fun r => ?_
  have hp (p : Body 1 f) : parts G 1 F r p=(A*ᵥ parts G 1 Q r) p := rfl
  change |(d 1 f *ᵥ parts G 1 F r) i| ≤ _
  rw [funext hp, Matrix.mulVec_mulVec, ← show Z*d 1 c=d 1 f*A from hI,← Matrix.mulVec_mulVec]
  exact gather hZ i hb fun v => (color_component (dColor G c 1 Q v) r).trans (he v)

end radiation
end YM.UVNext.PricedKernels
