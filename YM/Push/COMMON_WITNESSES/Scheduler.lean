import YM.Push.COMMON_WITNESSES.GridMerge
import YM.Push.COMMON_WITNESSES.Servings

/-!
# Buying Grill on successive orders using only single-field comparison work

This is not a proof that the comparison bounds are attainable.

It's a
sufficient mechanism THROUGH the common-witness transport.

Note h is chosen
arbitrarily far **before n**, with respect to asks of later orders, and need
one quantitative bound for all these repeats on one estimate.

The primary
budgets here are real prerequisites; derive them (at the same centred grid
h) as soon as reaching Base via `center`.

It would be
incorrect to require a regulator-uniform sup comparison directly with the
primary point-fields in this use.

Only `rootTest` similarity on actual
measures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Lattice MeasureTheory Next.Extract Wilson OS
open scoped Topology BigOperators ContDiff
open Extraction.Spin

variable {G : Gauge} {C : Family G} {h d : ℕ} {f : Extraction.Order}
variable {n : ℕ}

private def coarse (x : Fin n → Cover) (a : Bool) (t i : ℕ) (u : Fin n) := stems x a u + jump t i

private lemma far (x : Fin n → Cover) (hx : Injective x) : ∃ s : ℕ → ℕ → ℕ,
    ∀ i j : ℕ, i<j → ∀ t ≥ s i j, ∀ a b : Bool, Injective
      (Fin.append (coarse x a t i) (coarse x b t j)) := by
  have he (a : Bool) (t i : ℕ) : Injective (coarse x a t i) := by
    intro k j hkj
    have hv : stems x a k=stems x a j := add_right_cancel hkj
    have hw p : (flipBook a)⁻¹.act (stems x a p)=x p := by rw [stems,comp_apply,Signed.inv_act]
    apply hx; rw [← hw,← hw,hv]
  have ht i j : ∃ r : ℕ, i<j → ∀ t ≥ r, ∀ (a b : Bool) (v w : Fin n),
      coarse x a t i v timeAxis < coarse x b t j w timeAxis := by
    by_cases hij : i < j
    swap; · exact ⟨0,fun hh => (hij hh).elim⟩
    have hp (a b : Bool) (v w : Fin n) : ∀ᶠ t in atTop,
        coarse x a t i v timeAxis < coarse x b t j w timeAxis := by
      let g := stems x a v timeAxis - stems x b w timeAxis
      filter_upwards [eventually_gt_atTop g.natAbs] with t ht
      have hw : g < (t:ℤ) := lt_of_le_of_lt (Int.le_natAbs (a:=g)) (by exact_mod_cast ht)
      change _ + (t:ℤ)*i < stems x b w timeAxis + (t:ℤ)*j
      have hh : (i:ℤ)+1 ≤ j := by exact_mod_cast hij
      unfold g at *; nlinarith
    obtain ⟨r,hr⟩ := eventually_atTop.mp (eventually_all.mpr fun a => eventually_all.mpr fun b =>
      eventually_all.mpr fun v => eventually_all.mpr (hp a b v))
    exact ⟨r,fun _ => hr⟩
  choose s hs using ht
  refine ⟨s,fun i j hij t hv a b k l => ?_⟩
  refine Fin.addCases ?_ ?_ k
  · intro k; refine Fin.addCases ?_ ?_ l
    · intro l hh; have heq : coarse x a t i k = coarse x a t i l := by simpa only [Fin.append_left] using hh
      rw [he a t i heq]
    intro l hh; have hh : coarse x a t i k = coarse x b t j l := by simpa only [Fin.append_left,Fin.append_right] using hh
    exact ((hs i j hij t hv a b k l).ne (congr_fun hh timeAxis)).elim
  intro k; refine Fin.addCases ?_ ?_ l
  · intro l hh; have hh : coarse x b t j k = coarse x a t i l := by simpa only [Fin.append_left,Fin.append_right] using hh
    exact ((hs i j hij t hv a b l k).ne (congr_fun hh.symm timeAxis)).elim
  intro l hh; have heq : coarse x b t j k = coarse x b t j l := by simpa only [Fin.append_right] using hh
  rw [he b t j heq]

private lemma seats_work (S : Schedule) (h : ℕ) (x : Fin n → Cover) (hx : Injective x) :
    ∀ᶠ p in atTop, Injective (wrap (S.side h p) ∘ x) := by
  have ht (a : Axis) (i : Fin n) : ∀ᶠ p in atTop,
      -((S.side h p).val:ℤ)< 2*x i a ∧ 2*x i a ≤ (S.side h p).val := by
    filter_upwards [S.period_strict.tendsto_atTop.eventually (eventually_gt_atTop ((2*x i a).natAbs))] with p hp
    have hw : (S.period p).val ≤ (S.side h p).val := by
      change _ ≤ (S.period p).val*(S.denominator h).val; exact Nat.le_mul_of_pos_right _ (S.denominator h).property
    have hh : (2*x i a).natAbs < (S.side h p).val := hp.trans_le hw
    omega
  filter_upwards [eventually_all.mpr fun a => eventually_all.mpr (ht a)] with p hp
  exact fun i j h => hx (wrap_injOn (S.side _ _) (show ∀ a : Axis,_ ∧ _ from fun a => hp a i)
     (show ∀ a : Axis, _ ∧ _ from fun a => hp a j) h)

/-- Root-based per-field input gate. Only ask an approximation at
origin. Need in this version the whole finite orbit, and data such as
*actual* F and bounds at these tolerances. -/
def Prox (C : Family G) (f : Extraction.Order) (d h l : ℕ) (R : ℝ) := f.late fun N p =>
    ∃ hN : h ≤ N, ∀ i : Flavour C d, ∃ P, DirectedField hN i (p:=p) P R (toll l)

lemma Prox.upon {R : ℝ} {l : ℕ} {g : Extraction.Order} (H : Prox C f d h l R) (e : Tails g f) : Prox C g d h l R := by
  unfold Prox at *
  exact e.late H

def PrimaryBill (C : Family G) (f : Extraction.Order) (d h : ℕ) (W : ℝ) := f.late fun N p =>
    ∀ i : Flavour C d, centeredBudget C (herb i) W h N p

/-- h grid needs to be one of these, available already at Base. -/
lemma primary_deep (H : CenterPort C f) (d : ℕ) : ∀ᶠ h in atTop, ∃ W : ℝ, 0 ≤ W ∧ PrimaryBill C f d h W := by
  have ht := (lib C f (Finset.univ : Finset (Flavour C d)) (H.book ..) 0 herb).2
  simpa only [Finset.mem_univ, forall_true_left,PrimaryBill] using ht

/-- Choose tolerance l before any translation requests. -/
lemma buys (h' : C.Makes) (x : Fin n → Cover) (hx : Order.grid C h x ∈ generic n) (u : Caps n) (hu : ∀ i, u i ≤ d)
    (W : ℝ) (hW : 0 ≤ W) (k : ℕ) : ∃ l : ℕ, ∀ (f : Extraction.Order), PrimaryBill C f d h W →
      ∀ R : ℝ, 0≤R → Prox C f d h l R → ∃ A : GrillCosts, ∀ t J, PrefixBill C h x u A f k t J := by
  let α : ℝ := 4*(↑(n+n : ℕ) : ℝ)*(W+1)^(n+n)
  obtain ⟨l,hl,hL⟩ := ((toll_go.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).and
    ((show Tendsto (fun i => α*toll i) atTop (𝓝 0) by simpa only [mul_zero] using toll_go.const_mul α).eventually
    (gt_mem_nhds (toll_pos k)))).exists
  have hδ : toll l≤1 := hl.le
  have hB : 4*((↑(n+n : ℕ) : ℝ)*(toll l*(W+1)^(n+n))) ≤ toll k := by
    apply le_trans ?_ hL.le
    unfold α; ring_nf; rfl
  refine ⟨l,fun f hw R hR hm => ?_⟩
  have hp : Injective x := by
    intro i j he
    exact (generic_conf _ hx) (congr_arg (C.S.gridPoint h) he)
  obtain ⟨s,hs⟩ := far x hp
  let A : GrillCosts := ⟨fun _ => 2*R^n,fun _ => by positivity,fun _ => s⟩
  refine ⟨A,fun t J => ?_⟩
  have he (i j : Fin J) (hq : i<j) (hQ : s i j≤t) (a b : Bool) : ∀ᶠ p in atTop, Injective (Fin.append
      ((wrap (C.S.side h p)) ∘ (coarse x a t i)) ((wrap (C.S.side h p)) ∘ (coarse x b t j))) := by
    have hv := seats_work C.S h _ (hs i j hq _ hQ a b)
    apply hv.mono; intro p h
    convert h using 1; funext v
    exact Fin.addCases (fun _ => by simp only [Fin.append_left,Function.comp_apply]) (fun _ => by simp only [Fin.append_right,Function.comp_apply]) v
  have hy : ∀ (i j : Fin J), ∀ (hQ : i < j) (_ : s i j≤t) (a b : Bool), ∀ᶠ p in atTop,
      Injective (Fin.append ((wrap (C.S.side h p)) ∘ (coarse x a t i)) ((wrap (C.S.side h p)) ∘ (coarse x b t j))) := he
  have hz := eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun hv =>
    eventually_all.mpr fun hl => eventually_all.mpr fun a => eventually_all.mpr (hy i j hv hl a)
  unfold PrefixBill Extraction.Order.late
  unfold PrimaryBill Extraction.Order.late at hw
  unfold Prox Extraction.Order.late at hm
  filter_upwards [hw,hm,f.per.cofinal.eventually hz] with p hp hv hg
  filter_upwards [hp,hv] with i hi hi'
  obtain ⟨v,Z⟩ := hi'
  choose L hL using Z
  apply sample_finite x u hu v L hL h' hi hW hR (toll_pos _).le hδ k A (le_refl _) hB t J
  intro m j hj hj' hh a b
  exact hg (⟨m,hj.trans hj'⟩ : Fin J) (⟨j,hj'⟩ : Fin J) hj hh a b

/-- Quantitative comparison precursor with stations. Requires being able to
pick h arbitrarily far out on this C (especially for these d), BEFORE
label, arity etc. Once picked under given inherited order, can deliver
Prox bills for every approximation task l on demand underneath. NO claim
of such sources. -/
def Study (C : Family G) (f : Extraction.Order) : Prop := OnDemand f fun (i : Slot) u =>
    ∃ h : ℕ, i.2≤h ∧ OnDemand u (fun l t => ∃ R : ℝ, 0≤R ∧ Prox C t i.1 h l R)

/-- Prove our GrillInputs from only real single-field rooted Prox inputs on
the stated stations. No estimating coincident-field kernels (even on one
character). Transfer through any further orders after this answer via the
API at GridMerge. -/
theorem studying (H : CenterPort C f) (h : C.Makes) (hS : Study C f) : GrillInputs C f := by
  apply GrillDemand.inputs
  intro i u
  obtain ⟨m,hm⟩ := eventually_atTop.mp (primary_deep H i.1)
  obtain ⟨v,k,hk,hK⟩ := hS (i.1,max m i.2) u
  obtain ⟨W,hW,b⟩ := hm k ((le_max_left ..).trans hk)
  refine ⟨v,k,(le_max_right ..).trans hk,?_⟩
  intro x g
  by_cases he : serves C k i.1 x.1
  · obtain ⟨l,hl⟩ := buys h _ he.2 _ he.1 W hW x.2
    obtain ⟨r,R,hr,hR⟩ := hK l g
    have hw (t : Extraction.Order) : PrimaryBill C (f.refine t) i.1 k W := by
      unfold PrimaryBill at *; exact (Tails.refine f t).late b
    obtain ⟨A,hA⟩ := hl _ (hw ((u.refine v).refine (g.refine r))) R hr hR
    exact ⟨r,A,fun _ => already fun j => hA j.1 j.2⟩
  exact ⟨Order.full,⟨fun _ => 0,fun _ => le_rfl,fun _ _ _ => 0⟩,fun h => (he h).elim⟩
end YM.Push.Common
