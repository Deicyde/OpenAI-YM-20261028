import YM.Next.SCHEDULE.Stadium

/-!
# Beta ticket for restarts on h stretches

Starts in old Shoot.band, not assumed on a restarted Bolted trajectory.
Checks using the ACTUAL coupling of the step if the error already fits the
PRE-L drift cost and iteration uses the approved enlarged prescription band.
The Ready assignment really gives those numerical gates. Estimate uniform
through any earlier-staged histories. Include also a p^o recurrence check
for E.13665 etc. Does not assert the altered-threshold RG or weak matching
transitions have been constructed or can be, number estimates lease physical
estimates still to find. Negative counterchecks separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Weak
open Filter Function RG RG.Supply Bid Lattice Source Precision Clock Real
open scoped Topology

variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {V : Delays Θ} {Y : Bar V} {I : Wait Y}

private lemma ratios (y x : ℝ) (hx : 0 < x) (h : x/2 ≤ y) :
    |gap y/gap x-1| ≤ 2*|y-x|/x := by
  have hy : 0<y:=lt_of_lt_of_le (half_pos hx) h
  let a:=Real.sqrt x; let b:=Real.sqrt y
  have ha : 0<a:=Real.sqrt_pos.2 hx; have hb : 0<b:=Real.sqrt_pos.2 hy
  have ht : b^2=y:=Real.sq_sqrt hy.le; have hl : a^2=x:=Real.sq_sqrt hx.le
  change |b⁻¹/a⁻¹-1| ≤ _
  rw [show b⁻¹/a⁻¹-1 = (x-y)/(b*(a+b)) by field_simp; nlinarith only [ht,hl],abs_div,
    abs_of_pos (mul_pos hb (by linarith)),abs_sub_comm]
  have hp : x ≤ 2*(b*(a+b)):=by nlinarith only [ha,hb,h,ht]
  apply (div_le_div_iff₀ (by positivity) hx).2
  have he := mul_le_mul_of_nonneg_left hp (abs_nonneg (y-x)); linarith

/-- All restarted steps up to h stay in the ENLARGED band if each
performed step met its reset. Conditional even on this particular
step estimate; no proof of performing / paying a Move. β argument counts
outward from k toward smaller physical indices. -/
lemma Bench.recover {a : Levels G} (h : Paid I a) (hs : G.Simple) {k j : ℕ} {U : Exchange} {F : Focus}
    (R : Bench a j k ((a.clock.factor j).val:ℝ) U F) :
    let x:= a.clock.hatBeta k; let L:=((a.clock.factor j).val:ℝ); let g:=G.slopeConstant; let p:=Instrument.plain.P x
    ∀ b : ℝ, b≤U.weakHeight → ∀ r : ℕ,(r:ℝ)*Real.log L ≤ (b+4)*Real.log p →
      ∀ β : ℕ → ℝ, β 0 ∈ Shoot.band a k →
        (∀ m, m<r → inBand (a.clock.hatBeta (k-m)) (β m) →
          |β (m+1)-β m+g*Real.log L| ≤ (s.melt q j).drift) →
        ∀ m, m ≤ r → inBand (a.clock.hatBeta (k-m)) (β m) ∧
          |gap (β m)/gap (β 0)-1| ≤ 4*g*(b+4)*Real.log p/β 0 := by
  intro x L g p b ha r hr β hβ ht
  have hj : s.first ≤ j := by
    rw [← R.index]
    exact le_trans h.firstZero.ge (a.fits.mono (Nat.zero_le _))
  have hx0 : 4096 ≤ x := R.cases_here.runway.2.2.2.2
  have hl : L=(D.L j).val := by unfold L; rw [h.lengths]
  have hL : 0<Real.log L := by
    apply Real.log_pos; rw [hl]; have he := (D.large j).size; exact_mod_cast (show 1<(D.L j).val by omega)
  have hg : 0<g := Gauge.slopeConstant_pos hs
  have he : 0 ≤ Real.log p := Real.log_nonneg R.cases_here.runway.2.1
  have hv := (mul_le_mul_of_nonneg_right (add_le_add_left ha 4) he)
  have hrr := hr.trans hv
  obtain ⟨hq,-⟩:=R.col r hrr
  have hK : (s.melt q j).drift ≤ g/4 * Real.log L := by
    apply (div_le_iff₀ hL).mp; rw [hl]; exact (D.large j).kick hj
  have ho (m : ℕ) (hh : m≤r) : near x (a.clock.hatBeta (k-m)) :=
    ((R.rooms hs r hrr (k-m) (by omega) (by omega)).2.2).1
  let t (m : ℕ):=2*g*((m:ℝ)*Real.log L)
  obtain ⟨hb1,hb2⟩:=hβ
  change x/2 ≤ β 0 at hb1; change β 0≤2*x at hb2
  have hs0 : 0<x := by linarith
  have hH : ∀ m : ℕ,m ≤ r → |β m-β 0| ≤ t m ∧ inBand (a.clock.hatBeta (k-m)) (β m) ∧ β 0/2 ≤ β m := by
    have hh (m : ℕ) (h : m ≤ r) (h' : |β m-β 0| ≤ t m) : inBand (a.clock.hatBeta (k-m)) (β m) ∧ β 0/2 ≤ β m := by
      obtain ⟨hA,hB⟩:=abs_le.mp h'; obtain ⟨hF,hE⟩:=abs_le.mp (ho m h)
      have hi := (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (show (m:ℝ) ≤ r by exact_mod_cast h) hL.le).trans hrr) hg.le).trans R.cases_here.bill
      have hb : t m ≤ 2*Real.sqrt x := by unfold t; change _ ≤ Real.sqrt x at hi; linarith
      have Hh := Real.sqrt_nonneg x
      have hy : 32*Real.sqrt x ≤ x := by nlinarith [Real.sq_sqrt hs0.le]
      refine ⟨⟨?_,?_⟩,?_⟩ <;> linarith
    intro m hm
    induction m with
    | zero =>
      have hb : |β 0-β 0|≤t 0 := by simp [t]
      exact ⟨hb, hh _ hm hb⟩
    | succ m ih =>
      obtain ⟨h1,h2,-⟩ := ih (by omega)
      have ha := ht m hm h2; obtain ⟨ha,hb⟩:=abs_le.mp ha; obtain ⟨hx,hy⟩:=abs_le.mp h1
      have he := mul_pos hg hL
      have H : |β (m+1)-β 0| ≤ t (m+1) := by
        unfold t at *; rw [abs_le]; push_cast; constructor <;> linarith
      exact ⟨H,hh _ hm H⟩
  intro m hm; obtain ⟨ht,hx',he'⟩:=hH m hm
  have he0 : 0 < β 0 := by linarith
  refine ⟨hx',le_trans (ratios _ _ he0 he') ?_⟩
  have hF := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (show (m:ℝ) ≤ r by exact_mod_cast hm) hL.le).trans hr) hg.le
  unfold t at ht; apply div_le_div_of_nonneg_right _ he0.le; linarith


end YM.Next.Scheduling.Weak
