import YM.Next.WARD_BIN.Eqs


/-!
# Pole at the UV end (prior to sewing over a history)

Equip the complete basis with weighted top *coordinates*. They will be read exactly
via `Rays`. Prove convergence as coupling/threshold are tuned, with rank retained.
The submatrix may mix engineering degrees; we use the actual tower at the same d.
The dimensions proved here concern the physical equation cylinders' projected
label directions only. They say nothing yet about a continuum kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G06 Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {H : Hol G} {d k n l m : ℕ} {S : Finset Cover}



section scalars
variable {f : CoverConfig G → ℂ}

/-- For bookkeeping cancel exactly the t powers appropriate for the factor
order, constructing a continuous expression. Here `k` requested, j powers of
t from the coefficient itself (`0` for force, `2` for compression).
Keep the grades when forming it. -/
def takePole (H : Hol G) (F : Labels.Frame G d) (k j : ℕ) (hf : Affordable S ((k:ℤ)-j) f) (h : GaugeInvariant f)
    (t : ℝ) := ∑ p∈ Finset.range (d+1),∑ i∈ Finset.range (d+1),
      ((t:ℂ)^(p+j-k)) • F.coords (crownAt H hf h d p i)

lemma pole_cont (H : Hol G) (F : Labels.Frame G d) (k j : ℕ)
    (hf : Affordable S ((k:ℤ)-j) f) (h : GaugeInvariant f) : Continuous (takePole H F k j hf h) := by
  unfold takePole; fun_prop

lemma takePole_eq (H : Hol G) (F : Labels.Frame G d) (k j : ℕ) (hf : Affordable S ((k:ℤ)-j) f) (h : GaugeInvariant f)
    (t : ℝ) (ht : 0<t) : F.scaled t (F.coords (((t:ℂ)^k)⁻¹ • ((t:ℂ)^j) • readout d H hf h)) =
      takePole H F k j hf h t := by
  have he : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold readout takePole; simp_rw [Finset.smul_sum,map_sum]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro p hp
  by_cases hQ : k ≤ i+j
  · rw [map_smul,map_smul,map_smul,map_smul,F.scaled_pure t _ (crowned ..), Complex.ofReal_pow]; dsimp only
    rw [smul_smul,smul_smul, mul_assoc, ← pow_add, show ((t:ℂ)^(j+i)) = (t:ℂ)^k*(t:ℂ)^(i+j-k) by
      rw [← pow_add]; congr 1; omega, inv_mul_cancel_left₀ (pow_ne_zero k he)]
  simp only [crownAt_below hf H h (show (i:ℤ) < (k:ℤ)- j by omega), smul_zero, map_zero]
end scalars

namespace PureBasis
variable (B : PureBasis G d) (R : Rays G d H) (h : R.FitsAt S)

-- Conveniences
abbrev fPaid (i : Count G d) : Affordable S ((↑(B.s i + 1:ℕ):ℤ) - (↑(0:ℕ):ℤ))
    (R.force (B.form i)) := by simpa using R.force_affordable h (B.form i)
abbrev dPaid (i : Count G d) : Affordable S ((↑(B.s i+1 : ℕ):ℤ)-(2:ℕ))
    (R.compression (B.form i)) := by
  rw [show ((↑(B.s i+1 : ℕ):ℤ)-(2:ℕ)) = (B.s i:ℤ)-1 by omega]; exact R.compression_affordable h (B.form i)
abbrev fInv (i : Count G d) := R.force_gauge (B.form i) (B.truth i)
abbrev dInv (i : Count G d) := R.compression_gauge h (B.form i) (B.truth i)

/-- The body at top, dimensionless (`a_N^{-d}` not applied here). -/
def row (β t : ℝ) (i : Count G d) := ((t:ℂ)^(B.s i+1))⁻¹ • R.unpaid (B.form i) β

def xRow (β t : ℝ) (i : Count G d) := ((t:ℂ)^(B.s i+1))⁻¹ •
    (readout d H (B.fPaid R h i) (B.fInv R i) - (β:ℂ)⁻¹ • readout d H (B.dPaid R h i) (B.dInv R h i))



def linearize (F : Labels.Frame G d) (i : Count G d) (p : ℝ × ℝ) :=
    takePole H F (B.s i+1) 0 (B.fPaid R h i) (B.fInv R i) p.1 - (p.2:ℂ) •
      takePole H F (B.s i+1) 2 (B.dPaid R h i) (B.dInv R h i) p.1

lemma weighted (F : Labels.Frame G d) (β t : ℝ) (ht : 0<t) (i) :
    B.linearize R h F i (t,β⁻¹/t^2) = F.scaled t (F.coords (B.xRow R h β t i)) := by
  simp only [linearize,← takePole_eq _ _ _ _ _ _ _ ht]
  unfold xRow
  rw [← map_smul, ← map_smul, ← map_sub,← map_sub]
  rw [smul_sub]
  simp only [pow_zero,one_smul,smul_smul,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_pow]
  have he : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [show (β:ℂ)⁻¹/(t:ℂ)^2 * (_⁻¹ * (t:ℂ)^2) = (((t:ℂ)^(B.s i+1))⁻¹*(β:ℂ)⁻¹) by field_simp]

-- zero at the pole is what matters for rank
abbrev principal (i : Count G d) :=
  ∑ n∈ Finset.range (d+1), crownAt H (B.fPaid R h i) (B.fInv R i) d (B.s i+1) n

lemma actual (F : Labels.Frame G d) (i) : B.linearize R h F i (0,0) = F.coords (B.principal R h i) := by
  simp only [linearize,Complex.ofReal_zero, zero_smul,sub_zero]; unfold takePole principal
  rw [Finset.sum_eq_single (B.s i+1), map_sum]
  · simp
  · intro l hl ht; apply Finset.sum_eq_zero; intro n hn
    rcases lt_or_gt_of_ne ht with g|g
    · have hy : crownAt H (B.fPaid R h i) (B.fInv R i) d l n = 0 := crownAt_below _ _ _ (by omega)
      rw [hy,map_zero,smul_zero]
    simp only [Complex.ofReal_zero, Nat.add_zero, zero_pow (Nat.sub_ne_zero_of_lt g),zero_smul]
  intro ht; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (B.le i))) ht

lemma level (i : Count G d) {l m} (ht : m ≤ B.n i) : gradePart (m,l) (B.principal R h i)=
    if m=B.n i ∧ l=B.s i+1 then (B.basis i).val else 0 := by
  by_cases hP : l=B.s i+1
  · subst l; unfold principal; rw [map_sum,Finset.sum_eq_single m]
    · rw [gradePart_self _ _ (crowned ..)]; simp only [and_true]
      apply Eq.trans (b:= crownAt H (R.force_affordable h (B.form i)) (B.fInv R i) d (B.s i+1) m)
      · exact Subtype.ext ((crownAt_ok H _ _ _ (ht.trans (B.degree i))).trans
          (crownAt_ok H _ _ _ (ht.trans (B.degree i))).symm)
      exact R.computes (B.homogeneous i) (B.basis i).property h (B.degree i) ht
    · intro j hj hV
      exact gradePart_zero _ _ _ (fun hh => hV (congr_arg Prod.fst hh).symm) (crowned _ _ _ _ _ _)
    intro hp; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (ht.trans (B.degree i)))) hp
  rw [if_neg (fun h => hP h.2),principal,map_sum]
  refine Finset.sum_eq_zero fun j _ => gradePart_zero _ _ _ (fun hh => hP (congr_arg Prod.snd hh)) (crowned ..)

abbrev Grid (G : Gauge) (d : ℕ) := Count G d → ℂ

private lemma graded_zero {E I : Type*} [AddCommGroup E] [Module ℂ E] [Fintype I]
    (f : I → E) (S : Submodule ℂ E) (q : Module.Basis I ℂ S) (n a : I → ℕ)
    (G : ℕ → ℕ → Module.End ℂ E) (u : ∀ i l m, m ≤ n i → G m l (f i) = if m=n i ∧ l=a i then ↑(q i) else 0)
    (v : I → ℂ) (hv : ∑ i,v i • f i = 0) : v=0 := by
  classical
  by_contra hx
  let K := {i : I|v i≠0}
  have hK : K.Nonempty := by
    by_contra hK; apply hx; funext j; by_contra h
    exact hK ⟨j,h⟩
  obtain ⟨m,⟨i,hi,hM⟩,H⟩ := wellFounded_lt.has_min (n '' K) (hK.image n)
  subst m
  have hm (j) (hj : v j≠0) : n i ≤ n j := le_of_not_gt (H _ ⟨j,hj,rfl⟩)
  let p (j : I) := if n i=n j ∧ a i=a j then v j else 0
  have he j : G (n i) (a i) (v j • f j)=p j • (q j).val := by
    by_cases hh : v j=0
    · simp [hh,p]
    rw [map_smul,u _ _ _ (hm _ hh)]; unfold p; split <;> simp
  have hg := congr_arg (G (n i) (a i)) hv
  simp_rw [map_sum,map_zero,he] at hg
  have hz : (∑ i,p i • q i)=0 := by
    apply Subtype.ext; simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, ZeroMemClass.coe_zero]; exact hg
  have hp (j) : p j=0 := Fintype.linearIndependent_iff.mp q.linearIndependent p hz j
  exact hi (by simpa [p] using hp i)

lemma linearly (v : Grid G d) (hv : (∑ i, v i • B.principal R h i)=0) : v=0 :=
  graded_zero (B.principal R h) _ B.basis B.n (fun i => B.s i+1) (fun m l => gradePart (m,l))
    (fun i _ _ hi => B.level R h i hi) v hv

/- Common ingress of scale and inverse coupling. `β = 0` allowed in some
bounds but not in Ward identity or the rank result as physically used. -/

def linear (F : Labels.Frame G d) (p : ℝ × ℝ) : Grid G d→L[ℂ] F.Coeff :=
  ∑ i : Count G d, (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : Count G d => ℂ) i).smulRight
    (B.linearize R h F i p)

lemma linear_apply (F : Labels.Frame G d) (p : ℝ × ℝ) (v : Grid G d) :
    B.linear R h F p v = ∑ i : Count G d, v i • B.linearize R h F i p := by
  unfold linear; rw [sum_apply]; rfl

theorem linear_cont (F : Labels.Frame G d) : Continuous (B.linear R h F) := by
  have he (i) : Continuous (B.linearize R h F i) :=
    ((pole_cont ..).comp continuous_fst).sub ((Complex.continuous_ofReal.comp continuous_snd).smul
      ((pole_cont ..).comp continuous_fst))
  apply continuous_finsetSum; intro i _
  exact ((ContinuousLinearMap.smulRightL ℂ (Grid G d) F.Coeff _).continuous).comp (he i)

lemma linear_inj (F : Labels.Frame G d) : Injective (B.linear R h F 0) := by
  intro a b hf
  have he : B.linear R h F 0 (a-b)=0 := by rw [map_sub,hf,sub_self]
  rw [B.linear_apply] at he
  simp_rw [show ∀ i,B.linearize R h F i 0 = _ from fun i => B.actual R h F i,← map_smul, ← map_sum] at he
  exact sub_eq_zero.mp (B.linearly R h (a-b) (F.coords.injective (he.trans (map_zero _).symm)))

lemma lower_event (F : Labels.Frame G d) : ∃ t : ℝ,0<t ∧ ∀ᶠ p : ℝ × ℝ in 𝓝 0,
    ∀ v : Grid G d,t*‖v‖ ≤ ‖B.linear R h F p v‖ := by
  let Q := B.linear R h F
  let L := (Q 0).toLinearMap.leftInverse.toContinuousLinearMap
  let T : ℝ := ‖L‖+1
  have ht : 0 < T := by unfold T; positivity
  have hq (v : Grid G d) : T⁻¹*‖v‖ ≤ ‖Q 0 v‖ := by
    rw [inv_mul_eq_div,div_le_iff₀ ht, mul_comm]
    have hw : L (Q 0 v)=v := LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot_of_injective (B.linear_inj R h F)) v
    exact le_trans (hw ▸ (L.le_opNorm (Q 0 v))) (mul_le_mul_of_nonneg_right (by dsimp only [T];simp) (norm_nonneg _))
  have HH : 0 < T⁻¹/2 := by positivity
  have hx : ∀ᶠ p in 𝓝 0, Q p∈ Metric.ball (Q 0) (T⁻¹/2) := (B.linear_cont R h F).continuousAt (x:=0) (Metric.ball_mem_nhds _ HH)
  refine ⟨_,HH,?_⟩
  filter_upwards [hx] with p hp v
  rw [Metric.mem_ball, dist_comm,dist_eq_norm] at hp
  have hr := ((Q 0-Q p).le_opNorm v).trans (mul_le_mul_of_nonneg_right hp.le (norm_nonneg _))
  have he : ‖Q 0 v‖-‖Q p v‖ ≤ ‖(Q 0-Q p) v‖ := norm_sub_norm_le ..
  change T⁻¹/2*‖v‖ ≤ ‖Q p v‖; linarith only [hq v,hr,he]

-- arbitrary complex combinations; no requirement on uniform norm beyond explicit estimates later

def tree (β t : ℝ) : Grid G d→ₗ[ℂ] (CoverConfig G→ℂ) where
  toFun v := ∑ i,v i • B.row R β t i
  map_add' x y := by simp_rw [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp_rw [RingHom.id_apply, Pi.smul_apply,smul_assoc,Finset.smul_sum]

def xTree (β t : ℝ) : Grid G d→ₗ[ℂ] Label G d where
  toFun v := ∑ i,v i • B.xRow R h β t i
  map_add' x y := by simp_rw [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp_rw [RingHom.id_apply,Pi.smul_apply,smul_assoc,Finset.smul_sum]

lemma top_tree (F : Labels.Frame G d) (β t : ℝ) (ht : 0<t) (v : Grid G d) :
    F.scaled t (F.coords (B.xTree R h β t v)) = B.linear R h F (t,β⁻¹/t^2) v := by
  rw [B.linear_apply]; change F.scaled _ (F.coords (∑ i,v i • _)) = _
  simp only [map_sum,map_smul,B.weighted R h F β t ht]



lemma row_cont (β t : ℝ) (v) : Continuous (B.row R β t v) := by
  obtain ⟨T,H⟩ := R.fitsAt_support
  apply Continuous.const_smul
  exact ((B.fPaid R H v).cont).sub ((B.dPaid R H v).cont.const_smul ((β:ℂ)⁻¹))



include h in
lemma tree_local (β t : ℝ) (v : Grid G d) : LocalOn S (B.tree R β t v) := by
  intro x y he; simp only [tree, row, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply,Rays.unpaid]
  apply Finset.sum_congr rfl; intro i _; rw [(B.fPaid R h i).uses _ _ he,(B.dPaid R h i).uses _ _ he]





include h in
lemma tree_null {q : Side} (β : ℝ) (ht : β≠0) (t : ℝ) (v : Grid G d) (o : Site q)
    (hh : FitsIn S q) (P : Config G q→ℂ) (hp : Envelope P) (hq : ∀ e : R.edg,∀ a U, P (slide (edgeAt e.val o) U a)=P U) :
    moment β (fun U => places o (B.tree R β t v) U * P U) = 0 := by
  let g i := fun U => v i * (places o (B.row R β t i) U * P U)
  have he (U : Config G q) : places o (B.tree R β t v) U * P U = ∑ i : Count G d, g i U := by
    unfold g tree; simp only [places, comp_apply,LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul,mul_assoc]
  have hv (i : Count G d) (U : Config G q) : g i U= (v i * ((t:ℂ)^(B.s i+1))⁻¹) *
      (places o (R.unpaid (B.form i) β) U * P U) := by unfold g places row; simp [mul_assoc]
  unfold moment; simp_rw [he]; rw [integral_finsetSum]; refine Finset.sum_eq_zero fun i _ => ?_
  · simp_rw [hv, integral_const_mul, show (∫ U, places o _ U * P U ∂law _ _ β) = _ from
      R.unpaid_null h (B.form i) β ht P hp hh o hq,mul_zero]
  intro i _
  have hW : Continuous (places o (B.row R β t i)) := (B.row_cont R β t i).comp
    (show Continuous (expandAt o (K:=G.El)) by unfold expandAt; fun_prop)
  exact (bound_int (bound_product (envelope_continuous hW) hp) _).const_mul _
end PureBasis
end YM.WardBin
