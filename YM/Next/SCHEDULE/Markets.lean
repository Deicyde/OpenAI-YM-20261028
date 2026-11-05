import YM.Next.SCHEDULE.Circuit
import YM.Work.A05.Window
import YM.Work.B09.Shell

/-!
# Issue path-label derivative bills

PricePoint and Projection actual hit costs for 𝒢 path labels.
For cubic & quartic with actual β ratio at band, these costs with an
extra length reserve attain a size gasket before recursions. Use also
with posterior activation of e.g. contour price requests. Not an account
of the subsequent near-integral costs. This price is period independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Wages Lattice Corona RG RG.Supply Bid Clock Instrument Pressure Precision
open Filter Function
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

-- Invoice independent of all Roll parameters except approved M, L, ancestry q costs.
def tollRate (s : Survey G) (q : Quote) (e : Exchange) (j : ℕ) (d k : ℕ) (L B : ℕ) : ℝ :=
    footprintCost s j e d L B * fund G (s.o.P j) (s.o.k j) k (s.o.A j) (q.widths.width j)

lemma fund_pos (G : Gauge) (P k d) (a σ : ℝ) (h : 0 < σ) : 0 < Wages.fund G P d k a σ := by
  have hs : 0 < Wages.startup G k P d := by
    unfold Wages.startup; have ht:=lt_of_lt_of_le zero_lt_one (slot_ge G P d 0); positivity
  unfold Wages.fund
  apply mul_pos (mul_pos hs (Real.exp_pos _))
  unfold momentCost
  let c:=grade k P d
  have hj:= decay_summable c (σ/4) (by positivity)
  have h:=hj.sum_le_tsum ({0}:Finset ℕ) (fun i _ => by unfold decay; positivity)
  apply lt_of_lt_of_le _ h; simp [decay]

private lemma tollShape (s : Survey G) (q : Quote) (e : Exchange) (j d k L B) :
    tollRate s q e j d k L B=tollRate s q e j d k L 1*(B:ℝ)^ (4:ℕ) := by unfold tollRate footprintCost; push_cast; ring

/-- All costs at the step relevant to testing the Atom from the input.
`d` a booked polynomial power in downstream cover size; any finite power
chosen at the stage fits. If a caller works at order or tests higher than
that booked, they must issue new gates.
-/
structure Loan (s : Survey G) (q : Quote) (e : Exchange) (x y : ℝ) (d j L : ℕ) : Prop where
  fit : let a:=s.o.A j; let σ:=q.widths.width j; a / ↑(plain.body y) ≤ σ/4
  lens : plain.body y ≤ 2*plain.body x
  paths (β : ℝ) : inBand y β → ∀ k∈ Finset.Icc 3 4,
    tollRate s q e j d k L (plain.body x)*(q.classicalCost.cap j)*β*(plain.t y)^k ≤ Real.sqrt (gap y)
  loops (θ : ℝ) : 0 < θ → θ ≤ 1 →
    tollRate s q e j d 2 L (plain.body x)*(2*LevelCost θ y)*(plain.t y)^ (2:ℕ) ≤ Real.sqrt (gap y)

open Real in
lemma Loan.prepare (s : Survey G) (q : Quote) (e : Exchange) (c : ℝ) (d j L : ℕ) (hh : 1 ≤ L) :
    ∀ᶠ x : ℝ in atTop, Loan s q e x (x+c) d j L := by
  let H k B:=tollRate s q e j d k L B
  have hL0 (k) : 0 < H k 1 := by
    unfold H tollRate; exact mul_pos (footprintCost_pos _ _ _ _ _ _ hh zero_lt_one) (fund_pos G _ _ _ _ _ (q.widths.wp j))
  let C:=q.classicalCost.cap j; have hC :0<C:=lt_of_lt_of_le zero_lt_one (q.classicalCost.cp j)
  have ha (k : ℕ) : ∀ᶠ y : ℝ in atTop,
      H k 1*2^ (4:ℕ)*C*4*y*(plain.P y)^ (4:ℕ)*(plain.t y)^ (3:ℕ) ≤ Real.sqrt (gap y) := by
    let Z (y : ℝ):=(plain.P y)^ (7:ℕ)*gap y ^ ((1:ℝ)/2)
    have hx : Tendsto Z atTop (𝓝 0) := by simpa only [Z,Instrument.P,plain,Real.rpow_natCast] using light 2 (↑(7:ℕ):ℝ) ((1:ℝ)/2) (by norm_num)
    let U:= H k 1*(2:ℝ)^ (4:ℕ)*C*4
    have hp:0 < U:=by have := hL0 k; unfold U; positivity
    filter_upwards [(hx.const_mul U).eventually (ge_mem_nhds (show U*0<1 by norm_num)),eventually_gt_atTop (0:ℝ)] with y hf hy
    have he:=gp hy
    let p := plain.P y; let g:=gap y
    have hg : y*g^ (2:ℕ)=1 := by unfold g gap; rw [inv_pow,Real.sq_sqrt hy.le]; field_simp
    have hu : Z y= p^ (7:ℕ)*√g := by unfold Z; rw [Real.sqrt_eq_rpow]
    change U*Z y ≤ 1 at hf
    rw [hu] at hf
    have ht :0 < √g:=Real.sqrt_pos.2 he; have hz : (√g)^ (2:ℕ)=g:=Real.sq_sqrt he.le
    change _*y*p^ (4:ℕ)*(g*p)^ (3:ℕ) ≤ √g
    calc
      _ = U* p^ (7:ℕ)*(y*g^ (2:ℕ))*g := by unfold U; ring
      _ = U*(p^(7:ℕ)*√g)*√g := by rw [hg,mul_one]; nth_rw 1 [← hz]; ring
      _ ≤ √g := (mul_le_mul_of_nonneg_right hf ht.le).trans_eq (one_mul _)
  have hb : ∀ᶠ y : ℝ in atTop,
      H 2 1* (2*plain.P y)^ (4:ℕ)*(2*plain.P y)*(plain.t y)^ (2:ℕ) ≤ √(gap y) := by
    -- take k=2 above, compare 2/(y*t*g)
    have hh0 := (Real.tendsto_sqrt_atTop).eventually_ge_atTop 1
    filter_upwards [ha 2,plain.pitched,eventually_gt_atTop (0:ℝ),hh0] with y ha hp hj hh0
    have ht : 1 ≤ plain.P y := hp.2.2.1
    have hD:0 < plain.P y:= wp _ _
    have he := gp hj
    apply le_trans _ ha
    let p:=plain.P y
    let t:=plain.t y
    have hg : √y = y*gap y := by
      unfold gap; have he:=Real.sqrt_pos.2 hj; field_simp; nlinarith [Real.sq_sqrt hj.le]
    have hk : 1 ≤ C*y*gap y := by
      have hp0:=q.classicalCost.cp j
      calc
        _ ≤ C*1 := by rw [mul_one]; assumption
        _ ≤ C*(y*gap y) := mul_le_mul_of_nonneg_left (hg ▸ hh0) hC.le
        _ = _ := by rw [mul_assoc]
    change H 2 1*(2*p)^ (4:ℕ)*(2*p)*t^ (2:ℕ) ≤ H 2 1*2^ (4:ℕ)*C*4*y*p^ (4:ℕ)*t^ (3:ℕ)
    have hq:0 ≤ H 2 1*2^ (4:ℕ)*p^ (4:ℕ)*p*t^(2:ℕ):= by unfold p; have := hL0 2; positivity
    calc
      _= 2*(H 2 1*2^ (4:ℕ)*p^ (4:ℕ)*p*t^(2:ℕ)) := by ring
      _ ≤ (4*(C*y*gap y))*(H 2 1*2^ (4:ℕ)*p^ (4:ℕ)*p*t^(2:ℕ)) := by gcongr; linarith
      _ = _ := by unfold t p Instrument.t; ring
  have hx : ∀ᶠ y : ℝ in atTop,(plain.body y:ℝ) ≤ plain.P y := by
    filter_upwards [(ceiling_cheaper 2 1 1 one_lt_two zero_lt_one).eventually (ge_mem_nhds zero_lt_one)] with y hy
    rw [Instrument.body]; simp only [plain,pow_one]
    have hh : (1+↑(cover y))/plain.P y≤1 := by simpa [Instrument.P,plain] using hy
    have hv :0<plain.P y:=wp _ _
    change (cover y:ℝ) ≤ plain.P y; linarith [(div_le_iff₀ hv).mp hh]
  have hk : ∀ᶠ y : ℝ in atTop,s.o.A j/↑(plain.body y) ≤ q.widths.width j/4 := by
    have hh := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp counting
    filter_upwards [(tendsto_const_nhds (x:=s.o.A j)).div_atTop hh |>.eventually
      (ge_mem_nhds (show 0 < q.widths.width j/4 from div_pos (q.widths.wp j) (by norm_num)))] with y hy
    simpa [Instrument.body,plain] using hy
  filter_upwards [advance (hx.and ((ha 3).and ((ha 4).and (hb.and ((plain.pitched.and hk)) )))),
    just_near c,plain.support 2 one_lt_two] with x hp hN hP
  let y:=x+c
  obtain ⟨hh0,hx3,hx4,hb,⟨hm,hs0,ht0,hy⟩,hE0⟩:=hp y hN
  obtain ⟨hBx,-⟩:=hp x (Clock.same x)
  have hp := hP _ _ (Clock.same x) hN
  have hc := hp.mass.2
  have he : (plain.body x:ℝ) ≤ 2*plain.P y := le_trans hBx hp.peek.1
  have ht : 0<plain.t y := mul_pos (gp (by linarith)) (wp _ _)
  have hE (k) : tollRate s q e j d k L (plain.body x) ≤ H k 1*(2*plain.P y)^ (4:ℕ) := by
    rw [tollShape]; gcongr
    exact (hL0 k).le
  have hEO k : 0 ≤ H k 1*(2*plain.P y)^ (4:ℕ) := mul_nonneg (hL0 k).le (by positivity)
  refine ⟨hE0,?_,fun β hB k hk => ?_,fun θ hθ hθ' => ?_⟩
  · dsimp only at hc
    exact_mod_cast hc
  · obtain ⟨h1,h2⟩:=Finset.mem_Icc.mp hk
    have hu : β ≤ 4*y := hB.2
    have hz : 0 ≤ β := le_trans (show 0 ≤ y/4 by linarith) hB.1
    have ha : plain.t y^k ≤ plain.t y^ (3:ℕ) := pow_le_pow_of_le_one ht.le hy h1
    have hR : (H k 1* (2*plain.P y)^ (4:ℕ))*C*(4*y)*plain.t y^ (3:ℕ) ≤ Real.sqrt (gap y) := by
      rw [show (H k 1* (2*plain.P y)^ (4:ℕ))*C*(4*y)*plain.t y^ (3:ℕ)=H k 1*2^ (4:ℕ)*C*4*y*(plain.P y)^ (4:ℕ)*(plain.t y)^ (3:ℕ) by ring]
      have he : k=3∨ k=4 := by omega
      rcases he with rfl|rfl
      · exact hx3
      exact hx4
    refine le_trans ?_ hR
    apply mul_le_mul _ ha (pow_nonneg ht.le _) _
    · exact mul_le_mul (mul_le_mul_of_nonneg_right (hE k) hC.le) hu hz (mul_nonneg (hEO k) hC.le)
    exact mul_nonneg (mul_nonneg (hEO k) hC.le) (by linarith)
  have ha : LevelCost θ y ≤ plain.P y := (Real.rpow_le_rpow_of_exponent_le ht0 hθ').trans_eq (Real.rpow_one _)
  have hrP : 0 < LevelCost θ y:=Real.rpow_pos_of_pos (wp _ _) _
  apply le_trans _ hb; exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hE 2) (mul_le_mul_of_nonneg_left ha (by norm_num)) (by positivity) (hEO 2)) (sq_nonneg _)
variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D}

/-- Addition to W issuance; preserves all other charges exactly. Estimate
powers d of cover for receiving CRT at the current level chosen beforehand,
not at R. -/
def Routed (e : ℕ → ℕ → Exchange) (d : ℕ → ℕ) (V : Delays Θ) := ∀ j i, Adj j i →
    ∀ x ≥ V.betaEntry j, Loan s q (e j i) x (x+G.slopeConstant*Real.log (D.L j).val) (d j) j (D.L j).val

lemma Routed.ready (e) (d) (V : Delays Θ) : ∃ W, Boost V W ∧ Routed e d W := by
  have hx j i := Loan.prepare s q (e j i) (G.slopeConstant*Real.log (D.L j).val) (d j) j _ (D.L j).property
  choose x hx using fun i => eventually_atTop.mp ((hx i i).and (hx i (i-1)))
  let W : Delays Θ := { V with betaEntry := fun i => max (V.betaEntry i) (x i) }
  refine ⟨W, ⟨fun i => le_max_left ..,le_rfl,le_rfl,le_rfl⟩,fun j i hg u hh => ?_⟩
  have ht := hx j u (le_trans (le_max_right ..) hh)
  rcases hg.cases_back with rfl|rfl
  · exact ht.1
  exact ht.2

namespace Deployment
variable {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G} {d : ℕ → ℕ}

def coverage {G : Gauge} {k : ℕ} {c f : Side} (s : Survey G) (C : Exchange) (q : Quote) (j d) (H : Ratio c f) (P B : BudgetPoint)
    (T : ℕ → Atom G k) (weight δ : ℝ) :=
    let σ:= (s.melt q j).width
    -- same d-cover cost as E/K; horizon assertion does not consume unknown true length moments
    let X (i : Site f × ℕ) := (T i.2).footprint i.1
    -- certificate through true ORDER. Includes arbitrary path derivative moments all labels jointly
    (∀ (o : Site f) i,P.supBounds o (X (o,i)) (fun U => (T i).unmasked U o) (price P (T i))) ∧
    ∀ S : Site f × ℕ → Support c, (∀ i,Footage H C.radius B.B (X i) (S i)) → ∀ p ∈ Set.Icc 0 C.extra, ∀ y : Site c,
      SumBudget (fun i => weight * (if y∈S i then
        Real.exp ((B.supportExponent + p)*coverNumber B.B (S i)+foundation s C j/4*coverNumber P.B (X i))*
            ((coverNumber P.B (X i):ℝ)+1)^d*Wages.toll P σ (T i.2) else 0)) δ




end Deployment
end YM.Next.Scheduling
