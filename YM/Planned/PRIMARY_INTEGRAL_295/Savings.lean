import YM.Planned.PRIMARY_INTEGRAL_295.Trellis
import YM.Planned.PRIMARY_INTEGRAL_295.Unload

/-!
# Stationary polynomial test savings (general weighted input)

Need the *prescribed* tower with its indexed-depth
reserves.

Estimates on the cover, not snapping translations at the torus
size.

Account every coordinate crossing and all harmonic/displacement
weights before choosing block length.

Only at query time will apply these
to actual b-directions tied to stationary moments/labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Trellis
open Function Filter Set Lattice Labels Laurent RG Precision Bloch Exterior Next.Free Place Carrier
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {j t r : ℕ} {L : Side}

-- Parent exposed crossing orientation
lemma cellar_step (ho : Odd L.val) (x : Cover) (a : Axis) :
    cellar L (x+step a)=cellar L x+carryStep a (wrap L x) := by
  let q := wrap L x
  have hb := balance L (x+step a)
  have hx := balance L x
  have he := cover_step ho a q
  have hh : L.val • cellar L (x+step a) = L.val • (cellar L x+carryStep a q) := by
    rw [smul_add]; rw [map_add,wrap_step] at hb; unfold q at *
    calc
      _ = x+step a-lift (wrap L x+step a)  := by
        conv_rhs => lhs; rw [hb]
        abel
      _ = _ := by
        conv_lhs => lhs; lhs; rw [hx]
        rw [add_right_comm _ _ (step a),← he]; abel
  ext1 i; apply mul_left_cancel₀ (show (L.val:ℤ)≠0 from by positivity)
  have ht := congr_fun hh i
  simp only [Pi.smul_apply,nsmul_eq_mul] at ht; exact ht

lemma scost (x : Cover) : (size (cellar L x) : ℝ) ≤ 4 + unitStep L * size x := by
  have he := size_add x (-lift (wrap L x))
  have hu := balance L x
  have hh : x + -lift (wrap L x) = L.val • cellar L x := by
    nth_rw 1 [hu]; abel
  rw [hh,size_neg] at he
  have hx (x : Cover) : size (L.val • x)=L.val*size x := by simp [size, Finset.mul_sum, Int.natAbs_mul]
  rw [hx] at he
  have hz : size (lift (wrap L x)) ≤ 4*L.val := by
    have ht (i : Axis) : (lift (wrap L x) i).natAbs ≤ L.val := by have := lift_centers (wrap L x) i; omega
    simpa only [size,Finset.sum_const,nsmul_eq_mul,Axis,Fintype.card_fin,Finset.card_univ] using! Finset.sum_le_sum (s:=Finset.univ) (fun i _ => ht i)
  have hL : (L.val:ℝ)>0 := Nat.cast_pos.mpr L.property
  have ha : (L.val:ℝ)*(size (cellar L x)) ≤ (size x:ℝ)+4*L.val := by exact_mod_cast he.trans (Nat.add_le_add_left hz _)
  unfold unitStep; field_simp; linarith

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Here C already has the L savings of the specific row. -/
lemma billed {σ C M : ℝ} (hσ : 0 < σ) (hC : 0≤C) {A : Lines L} (hA : A.strip σ C)
    {f : Window E} (hf : Carries f r M) (x : Cover) :
    ‖applyLine A f x‖ ≤ 4*M*widthCost σ r*5^r*C*(1+unitStep L * size x)^r := by
  have hd := hf.1; have hu:=unitStep_pos L; have hp:=widthCost_ge hσ r
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=> ?_
  unfold applyLine; refine (norm_sum_le ..).trans ?_
  let v := M*widthCost σ r*5^r*C*(1+unitStep L*size x)^r
  have he b : ‖stream (member A x i b) (cellar L x) (fun z=> f z b)‖ ≤ v := by
    have h := stream_income hσ (hA (wrap L x,Exterior.coord i) (Exterior.coord b)) (cellar L x) r hf.1 (fun z=> hf.2 z b)
    refine ((norm_tsum_le_tsum_norm h.2.1).trans h.2.2).trans ?_
    have he : liftCost r (cellar L x) ≤ (5*(1+unitStep L * size x))^r := by
      unfold liftCost; refine pow_le_pow_left₀ (by positivity) ?_ _
      linarith only [scost (L:=L) x, mul_nonneg hu.le (Nat.cast_nonneg (size x))]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hf.1)
      (zero_le_one.trans hp)) hC).trans_eq
    unfold v; rw [mul_pow]; ring
  apply (Finset.sum_le_sum (fun b _=> he b)).trans_eq; unfold v; simp [Axis]; ring

variable [CompleteSpace E]
lemma advance_step (ho : Odd L.val) (x : Cover) (s : Axis) {A : Lines L} (hA : Whole A)
    {f : Window E} {D : ℝ} (hf : Carries f r D) :
    offset (applyLine A f) s x=applyLine (forwardC L A s) f x := by
  classical
  obtain ⟨σ,C,hσ,hC⟩ := hA
  let g := cellar L x; let q := wrap L x; let w := carryStep s q
  ext1 i; unfold offset applyLine; simp only [cellar_step ho, Pi.sub_apply, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun b _=> ?_
  let a (x : Site L) := A (x,coord i) (coord b)
  have he x g' := stream_income hσ (show Width σ C (a x) from hC _ _) g' r hf.1 (fun z=> hf.2 z b)
  unfold stream member; simp only [map_add,wrap_step]
  let T (z : Cover) := a (q+step s) (z-w) • f (g+z) b
  let U (z : Cover) := a (q+step s) z • f (g+w+z) b
  let V (z : Cover) := a q z • f (g+z) b
  have H : T ∘ Equiv.addRight w = U := by ext1 z; simp [T,U,add_comm,add_left_comm]
  have ht : Summable T := ((Equiv.addRight w).summable_iff).mp (H.symm ▸ (he (q+step s) (g+w)).2.1.of_norm)
  have hu : ∑' z,U z=∑' z,T z := by rw [← H]; exact (Equiv.addRight w).tsum_eq _
  change (∑' z,U z)-(∑' z,V z) = ∑' z,(a (q+step s) (z-w) - a q z) • f (g+z) b
  rw [hu,← ht.tsum_sub (show Summable V from (he q g).2.1.of_norm)]; exact tsum_congr fun z=> (sub_smul ..).symm

/-- Window-money for all required differences, with exact scale in
both the displacement and amplitude. -/
lemma clock (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4≤t) (r : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    ∃ C:ℝ, 1≤C ∧ ∀ (P : Flight j t) (f : Window E) (M : ℝ), Carries f r M →
      ∀ (l : List Axis), l.length≤j-2 → ∀ x:Cover,
      ‖delta (applyLine (linesOf P k) f) l x‖ ≤ C*M*unitStep P.L^(1+l.length)*(1+unitStep P.L*size x)^r := by
  obtain ⟨σ,C,hσ,hC,h⟩ := priced k hk hj ht
  let B : ℝ := 4*widthCost σ r*5^r*C; have hv:=widthCost_ge hσ r
  have hb : 0≤B := by unfold B; positivity
  refine ⟨1+B,le_add_of_nonneg_right hb,fun P f M hf l hl x=>?_⟩
  let u := unitStep P.L; have hu:=unitStep_pos P.L; have hm := hf.1
  let A:=linesOf P k
  have he (l : List Axis) (hl : l.length≤j-2) : delta (applyLine A f) l=applyLine (advanceC P.L A l) f := by
    induction l with
    | nil=>rfl
    | cons a l ih=>
      rw [delta,advanceC,ih (by simp at hl; omega)]; exact funext fun z => advance_step P.odd z a
        (show Whole (advanceC P.L A l) from ⟨σ,_,hσ,h P l (by simp at hl; omega)⟩) hf
  change ‖delta (applyLine A f) l x‖ ≤ _; rw [he l hl]
  apply (billed hσ (by positivity) (h P l hl) hf x).trans
  calc
    _ = B*M*unitStep P.L^(1+l.length)*(1+unitStep P.L*size x)^r := by unfold B unitStep; rw [inv_pow]; ring!
    _ ≤ _ := by gcongr; linarith
end

/-- `jsT` coefficient version, ALL cover positions. The decomposition is
`sector n` forward on the called one-form + the exact `surplus`. Estimate
for positive polynomial order uses n indexing from 0 (E's S_{n+1}),
stronger degree-n E4 point estimate as well. Doesn't require a constant
sum of the coarse test weights when extending the cover. -/
theorem saves (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4≤t) (r d : ℕ) (hr : d≤r) (hd : d ≤ j-2) :
    ∃ C:ℝ, 1 ≤ C ∧ ∀ (P : Flight j t) (f : Window E) (M : ℝ), Carries f r M →
      let g := applyLine (linesOf P k) f
      (∀ n < d, sector n g∈ rangeLt (Axis→E) (n+1) ∧ ∀ x : E4, ‖sector n g x‖ ≤ C*M*unitStep P.L^(n+1)*(1+‖x‖)^n) ∧
      ∀ x : Cover, ‖surplus g d x‖ ≤ C*M*unitStep P.L^(d+1)*liftCost r x := by
  classical
  obtain ⟨u,hu,h⟩ := clock k hk hj ht r E
  choose B hb he using fun n:ℕ=>price_point (E:=Axis→E) n
  let D := 1+∑ i∈Finset.range d,B i; let A := D*u; let v : ℝ := 2^r
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hb i)))
  have hA := show 1≤A from one_le_mul_of_one_le_of_one_le hD hu
  have hv : 1 ≤ v := one_le_pow₀ (by norm_num)
  refine ⟨A + (d:ℝ)*A + u*v, by linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) (zero_le_one.trans hA),one_le_mul_of_one_le_of_one_le hu hv],fun P f M hM=>?_⟩
  intro g; let L := P.L; let w := unitStep L
  have hp := unitStep_pos P.L; have hP := unitStep_le P.L; have hf:=hM.1
  let p := A + (d:ℝ)*A + u*v
  have hp' : A≤p := by unfold p; linarith [show 0≤(d:ℝ)*A by positivity, one_le_mul_of_one_le_of_one_le hu hv]
  have H n (hn : n<d) (x : E4) : ‖sector n g x‖ ≤ A*M*w^(n+1)*(1+‖x‖)^n := by
    have hi : B n ≤ D := (Finset.single_le_sum (fun i _=> zero_le_one.trans (hb i)) (Finset.mem_range.mpr hn)).trans (le_add_of_nonneg_left zero_le_one)
    have hh (l : List Axis) (hl:l.length=n) : ‖delta g l 0‖ ≤ u*M*w^(n+1) := by
      simpa only [show size (0:Cover)=0 by simp [size],Nat.cast_zero,mul_zero,add_zero,one_pow,mul_one,hl, Nat.add_comm 1] using h P f M hM l (by omega) 0
    have hw := he n g (u*M*w^(n+1)) (by unfold w L; positivity) hh x
    refine hw.trans ?_
    unfold A; have h1 := mul_le_mul_of_nonneg_right hi (show 0≤u*M*w^(n+1)*(1+‖x‖)^n by unfold w L; positivity)
    linarith
  have hnear (x : Cover) (hx : size x ≤ L.val) : 1+unitStep P.L * size x≤2 := by
    have h2 : unitStep P.L * size x ≤ unitStep P.L * (P.L.val:ℝ) := mul_le_mul_of_nonneg_left
      (show (size x:ℝ) ≤ _ from Nat.cast_le.mpr hx) hp.le
    rw [unitStep, inv_mul_cancel₀ (by positivity)] at h2; unfold unitStep; linarith
  constructor
  · intro n hn; refine ⟨sector_band g n,fun x => (H n hn x).trans ?_⟩
    have h := mul_le_mul_of_nonneg_right hp' (show 0 ≤ M*w^(n+1)*(1+‖x‖)^n by unfold w L; positivity)
    unfold p w L at h; linarith
  intro x
  let N := liftCost r x; let B := (size x:ℝ)
  change _ ≤ p*M*w^(d+1)*N
  by_cases hx : size x ≤ L.val
  · let C := u*M*w^(d+1)*v
    apply (accrue d g L.val C (by unfold C w L; positivity) _ x hx).trans
    · have h : u*v≤p := by unfold p; linarith only [hA, mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg (α:=ℝ) d)]
      have hh := mul_le_mul_of_nonneg_right h (show 0≤M*w^(d+1) by unfold w L; positivity)
      have he' : B^d≤N := (pow_le_pow_left₀ (show 0 ≤ B by unfold B; positivity) (show B≤1+B from le_add_of_nonneg_left zero_le_one) d).trans
        (pow_le_pow_right₀ (show 1≤1+B by unfold B; simp) hr)
      unfold C; refine mul_le_mul ?_ he' (by positivity) (by unfold p w L; positivity)
      linarith
    intro l hl y hy; unfold g; apply (h P f M hM l (by omega) y).trans; rw [hl,Nat.add_comm 1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hnear _ hy) r) (by positivity)
  have hN := liftCost_pos r x
  let q := w*(1+B)
  have hh : 1 ≤ w*B := calc
    1 = w*L.val := by unfold w unitStep; field_simp [L.property.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (by unfold B; exact_mod_cast le_of_lt (Nat.lt_of_not_ge hx)) hp.le
  have hq : 1 ≤ q := by unfold q; rw [mul_add, mul_one]; exact hh.trans (le_add_of_nonneg_left hp.le)
  have hq' : w * q^r ≤ w^(d+1)*N := by
    have hh := pow_le_pow_of_le_one hp.le hP (Nat.add_le_add_right hr 1)
    unfold q; rw [mul_pow, ← mul_assoc,← pow_succ']; exact mul_le_mul_of_nonneg_right hh hN
  have he : ‖g x‖ ≤ u*v*M*w*q^r := by
    have he := h P f M hM [] (by simp) x
    apply he.trans
    change _*_*w^(1+([]:List Axis).length)*(1+w*size x)^r ≤ _
    simp only [List.length_nil,Nat.add_zero,pow_one]
    have hv' : 1+w*(size x) ≤ 2*q := by change 1+w*B≤_; unfold q; unfold w at *; rw [mul_add]; linarith
    have he' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold w unitStep; positivity) hv' r)
      (show 0≤u*M*w by unfold w L; positivity)
    rw [mul_pow] at he'; unfold v; linarith
  have hs i (hi : i<d) : ‖sector i g (seat x)‖ ≤ A*M*w*q^r := by
    have hP' := pow_le_pow_right₀ hq (hi.le.trans hr)
    apply (H i hi (seat x)).trans
    calc
      _ ≤ A*M*w^(i+1)*(1+B)^i := by gcongr; exact shade_seat x
      _ = A*M*w*q^i := by unfold q; rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP' (by unfold w L; positivity)
  have hz : (∑ i∈Finset.range d,‖sector i g (seat x)‖) ≤ d * (A*M*w*q^r) := by
    simpa using Finset.sum_le_sum (fun i hi => hs i (Finset.mem_range.mp hi))
  refine (norm_sub_le (g x) (fitting g d x)).trans ((add_le_add he ((norm_sum_le ..).trans hz)).trans ?_)
  let c := u*v + d*A
  have hc : 0≤c := by unfold c; positivity
  apply le_trans (show _ ≤ c*M*(w*q^r) from le_of_eq ?_) _
  · unfold c; ring
  have h1 := mul_le_mul_of_nonneg_left hq' (show 0≤c*M by positivity)
  have h2 : c ≤ p := by unfold c p; linarith
  exact h1.trans (by rw [← mul_assoc]; gcongr)
end YM.Planned.PrimaryIntegral295.Trellis
