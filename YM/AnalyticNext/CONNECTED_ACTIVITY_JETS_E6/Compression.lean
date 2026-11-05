import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rod
import YM.Work.A05

/-!
# Cut vs full and locality for the extracted rows

Both at physical orthonormal color frame (sup for arrays, real Hilbert
for components). Getting an off-diagonal price does not require small
globally tested chart *derivatives*; exploit the actual approximation
by the linear family at every cut. Pre-L use of the unmasked bounds on
Atoms.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Matrix
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}
open Work.F03 Work.E04

section cut
variable {A : PathData G} {p : Clip} {σ C Λ : ℝ}

lemma linear_charge (h : A.Bounds p σ C Λ) (x : Directions G f) (i : Cell f) :
    ‖ellLine A i (toLog x)‖ ≤ C*(4*‖x‖) := by
  let u j := A.row i.2 j
  let T j := (u j).1 • faceCurl (slotFace (u j).2 i.1) (toLog x)
  have hh : SumBudget (rich A σ i.2) C := h.rows _
  have he j : ‖T j‖ ≤ (4*‖x‖)*rich A σ i.2 j := by
    dsimp only [T]; unfold rich
    rw [norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (phi_linear x _) (abs_nonneg _)).trans
    have hx := h.width
    rw [mul_comm (4 * ‖x‖)]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity)))
      (by positivity)
  have ht := budget_mono (budget_scale (by positivity : 0 ≤ 4*‖x‖) hh) (fun _ => norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm ht.2.1).trans (ht.2.2.trans_eq (mul_comm ..))

lemma line_cut (h : A.Bounds p σ C Λ) (R : ℕ) (x : Directions G f) (i : Cell f) :
    ‖ellLine A i (toLog x)-ellCut A R (toLog x) i‖ ≤ C*(4*‖x‖)*Real.exp (-σ*R) := by
  let u j := A.row i.2 j
  let T j := (u j).1 • faceCurl (slotFace (u j).2 i.1) (toLog x)
  let Q j := if (u j).2.length≤R then T j else 0
  have hh : SumBudget (rich A σ i.2) C := h.rows _
  let M := 4*‖x‖*Real.exp (-σ*R)
  have hM : 0 ≤ M := by unfold M; positivity
  have he j : ‖T j-Q j‖ ≤ M*rich A σ i.2 j := by
    unfold Q; split
    next ht => rw [sub_self,norm_zero]; exact mul_nonneg hM (hh.1 _)
    next ht =>
      rw [sub_zero]; dsimp only [T]; unfold rich M
      rw [norm_smul,Real.norm_eq_abs]
      apply (mul_le_mul_of_nonneg_left (phi_linear x _) (abs_nonneg _)).trans
      have he : ∀ v w : ℝ, v*(4*‖x‖) * Real.exp (-σ*R+w)= 4*‖x‖*Real.exp (-σ*R)*(v*Real.exp w) := by
        intro v w; rw [Real.exp_add]; ring
      rw [← he]
      apply le_mul_of_one_le_right (by positivity); apply Real.one_le_exp
      have hh : (R:ℝ) ≤ (u j).2.length := by exact_mod_cast le_of_lt (Nat.lt_of_not_ge ht)
      unfold u at hh; linarith [mul_le_mul_of_nonneg_left hh h.width.le]
  have ht := budget_mono (budget_scale hM hh) (fun _ => norm_nonneg _) he
  unfold ellLine ellCut
  rw [← Summable.tsum_sub (ellLine_summable A h ..) (ecut_sum h ..)]
  exact (norm_tsum_le_tsum_norm ht.2.1).trans (ht.2.2.trans_eq (by unfold M; ring))

/-- Full operator comparison in the bar leg (Z linearization unchanged). -/
def uncutField (T : Tube G S) (x : Directions G f) : Rod c f → G.Color :=
    Sum.elim (xLin T.high T.up (toLog x)) (zLin S (toLog x) 0)

lemma difference (T : Tube G S) (h : T.up.Bounds p σ C Λ) (R : ℕ) (x : Directions G f) (i : Rod c f) :
    ‖uncutField T x i - barField T R x i‖ ≤ C*(4*‖x‖)*Real.exp (-σ*R) := by
  rcases i with p|b
  · have hC : 0 ≤ C := budget_nonneg (h.rows p.1.2)
    dsimp only [uncutField,barField,Sum.elim,bareCut,xLin]; split
    next hi => exact line_cut h ..
    next hi => rw [sub_self,norm_zero]; positivity
  have hn : 0 < Fintype.card PlaqAxes := by decide
  letI : Nonempty PlaqAxes := Fintype.card_pos_iff.mp hn
  have hC : 0 ≤ C := budget_nonneg (h.rows (Classical.arbitrary _))
  rw [show uncutField T x (.inr b) = barField T R x (.inr b) from rfl,sub_self,norm_zero]; positivity
end cut

/-- Cut-linear operator estimates at every cut, not just R=till. Crystal
recipe estimates are different. -/
structure Bounded (T : Tube G S) (σ C : ℝ) : Prop where
  full (x : Directions G f) (i : Rod c f) : ‖uncutField T x i‖ ≤ C*‖x‖
  short (x : Directions G f) (R : ℕ) (i : Rod c f) : ‖barField T R x i‖ ≤ C*‖x‖
  tail (x : Directions G f) (R : ℕ) (i : Rod c f) :
    ‖uncutField T x i - barField T R x i‖ ≤ C*‖x‖*Real.exp (-σ*R)

lemma bounded_stencils (P : Teller G) (D : Patch) (hd : D.Branches P.bind G) :
    ∃ C : ℝ, 0<C ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
      Bounded T P.top.width C := by
  obtain ⟨Y,r,hY,hr,H⟩ := z_chart_cost D P.bind G hd
  let U := 4*(P.top.paths+Real.sqrt P.top.clip.direct) + Y
  let C := U+P.top.paths*4
  have hp := P.top.paths_pos
  have ht := Real.sqrt_pos.mpr P.top.clip.quadratic_pos
  have hu : 0<U := by unfold U; positivity
  have hc : P.top.paths*4 ≤ C := le_add_of_nonneg_left hu.le
  have hy : U ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C,hu.trans_le hy,fun c f S T hS h => ?_⟩
  obtain ⟨a,b,hm,_⟩ := h.feeds
  let k : S.Choices := Classical.arbitrary _
  have hh (x : Directions G f) (i : Rod c f) : ‖uncutField T x i‖ ≤ U * ‖x‖ := by
    rcases i with p|i
    · dsimp only [uncutField, Sum.elim, xLin]; split
      next =>
        refine (linear_charge hm ..).trans ?_
        rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        unfold U; linarith
      next =>
        rw [h.high, norm_smul,Real.norm_of_nonneg ht.le];
        apply (mul_le_mul_of_nonneg_left (phi_linear _ _) ht.le).trans
        rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        unfold U; linarith
    have he := (H c f S hS h.knobs k i (toLog x,0)).1
    simp only [Prod.norm_def,norm_zero, max_eq_left (norm_nonneg _),counted] at he
    exact he.trans (mul_le_mul_of_nonneg_right (by unfold U; linarith) (norm_nonneg _))
  refine ⟨fun x i => (hh x i).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _)),?_,?_⟩
  · intro x R i
    have he := difference T hm R x i
    have hp := norm_sub_le_norm_sub_add_norm_sub (barField T R x i) (uncutField T x i) 0
    rw [sub_zero,sub_zero,norm_sub_rev (barField ..)] at hp
    have hv : Real.exp (-P.top.width*R) ≤ 1 := Real.exp_le_one_iff.mpr (by have := P.top.width_pos; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
    refine hp.trans ((add_le_add (he.trans (mul_le_of_le_one_right ?_ hv)) (hh x i)).trans_eq ?_)
    · have hh := P.top.paths_pos; positivity
    unfold C; ring
  intro x R i
  apply (difference T hm ..).trans; rw [← mul_assoc]
  gcongr

/-- A cut cost for a single impulse at true `distAt`; no path analytic
width or size in volume assumed after projection. -/
lemma input_decays {P : Teller G} {T : Tube G S} (hT : P.Funds S T) {C : ℝ} (hC : 0<C) (h : Bounded T P.top.width C)
    (i : Rod c f) (e : Bond f) (a : G.Color) (R : ℕ) :
    Real.exp (P.top.width * distAt S e (focus S i)) * ‖barField T R (Pi.single e a) i‖ ≤
        (2*C*Real.exp (P.top.width*(predReach S.patch+6:ℝ))) * ‖a‖ := by
  let g := distAt S e (focus S i)
  let w := P.top.width
  let p := predReach S.patch
  have hw : 0 < w := P.top.width_pos
  let v : Directions G f := Pi.single e a
  have hh : ‖v‖ ≤ ‖a‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => by
    by_cases H : i=e
    · subst i; simp [v]
    unfold v; rw [Pi.single_eq_of_ne H,norm_zero]; exact norm_nonneg _)
  have he s (he : s+p+4 < g) : barField T s v i=0 := by
    obtain ⟨X,Y,hv,-⟩ := hT.feeds
    rw [← bar_zero T hv s i]; apply tangent_local T (SectorMeasure.funds_branch hT) s v 0 i
    intro j hj
    have hy : j ≠ e := fun hx => he.not_ge (show distAt S e (focus S i) ≤ s+p+4 from hx ▸ hj)
    unfold v; rw [Pi.single_eq_of_ne hy]; rfl
  change Real.exp (w*g) * _ ≤ (2*C*Real.exp (w*(p+6:ℝ))) * ‖a‖
  by_cases ht : R+p+4<g
  · rw [he _ ht,norm_zero,mul_zero]; positivity
  by_cases hp : g ≤ p+5
  · have H : (g:ℝ) ≤ (p:ℝ)+5 := by exact_mod_cast hp
    have hz : ‖barField T R v i‖ ≤ (2*C)*‖a‖ :=
      (h.short v ..).trans (mul_le_mul (by linarith) hh (norm_nonneg v) (by positivity))
    exact (mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left
      (show (g:ℝ) ≤ (p:ℝ)+6 by linarith) hw.le)) hz (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  let s := g-(p+5)
  have hi : s+p+4 < g := by unfold s; omega
  have hs : s ≤ R := by omega
  have hb : ‖barField T R v i‖ ≤ C * ‖a‖ * Real.exp (-w*s) + C*‖a‖*Real.exp (-w*s) := by
    have he' := norm_sub_le_norm_sub_add_norm_sub (barField T R v i) (uncutField T v i) 0
    rw [sub_zero,sub_zero,norm_sub_rev] at he'
    have h1 := h.tail v R i; have h2 := h.tail v s i; rw [he _ hi,sub_zero] at h2
    apply he'.trans
    have h3 : C*‖v‖ ≤ C*‖a‖ := mul_le_mul_of_nonneg_left hh hC.le
    exact add_le_add (h1.trans (mul_le_mul h3 (Real.exp_monotone (mul_le_mul_of_nonpos_left
      (by exact_mod_cast hs) (neg_nonpos.mpr hw.le))) (Real.exp_pos _).le (by positivity)))
      (h2.trans (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le))
  have hy : (g:ℝ) ≤ (s:ℝ)+(p:ℝ)+6 := by exact_mod_cast (show g≤s+p+6 by unfold s; omega)
  apply (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
  calc
    _ = (2*C* (Real.exp (w*g)*Real.exp (-w*s))) * ‖a‖ := by ring
    _ ≤ _ := by rw [← Real.exp_add]; gcongr; nlinarith
end YM.ConnectedActivityE6.SliceRows
