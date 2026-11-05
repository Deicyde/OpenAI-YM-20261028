import YM.Next.SCHEDULE.Air
import YM.Next.SCHEDULE.Calling

/-!
# Booking the common weak-comparison work stretches

One station in *each* plateau, paying simultaneous assigned A and B work
radii. AFTER Bar fixed. Stage transitions before tall station chosen by
existing Wait.ready. Can use all comparisons simultaneously for a fixed
b in range; no rate accumulation per-step. `Tracks` records numeric
prerequisites. It does not assert the additional restarts of actual trajectory
WITH threshold changes/calibration have been implemented. The weak uses
still face meeting all profile budgets, seals, offsets etc. Uniformity includes
all earlier depth windows, not a claim of mask smoothness on different opens.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply Bid Lattice Pressure Precision Real Clock Instrument
open scoped Topology

namespace Weak
variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {V : Delays Θ} {Y : Bar V}

/-- Dominance from other requests, fixed b everywhere. -/
structure Behind (B A : Wait Y) : Prop where
  first : B.readyHere ≤ A.readyHere
  win : B.window ≤ A.window
  psize : B.minLength ≤ A.minLength

def Billed (B : Wait Y) (e : ℕ → ℕ → Exchange) (F : ℕ → Focus) := ∀ j (σ : ℝ),
    let U:= (e j j).weakHeight
    let L:ℝ:=(D.L j).val
    let x := population G.slopeConstant Y.value σ
    B.readyHere j ≤ σ →
      Roster (F j) (Θ.theta j) L U Y.value G.slopeConstant σ ∧ Weak.stop U L x ≤ B.window j σ



theorem Billed.ahead (Gsimple : G.Simple) (B : Wait Y) (e : ℕ → ℕ → Exchange) (f : ℕ → Focus)
    (h : ∀ i, Θ.theta i ≤ (f i).thin) : ∃ A : Wait Y, Behind B A ∧ Billed A e f := by
  let U j := (e j j).weakHeight
  let L (j) := ((D.L j).val:ℝ)
  let g:=G.slopeConstant; have hg:= Gauge.slopeConstant_pos Gsimple
  let x:=population g Y.value
  have hL j : 1<L j := by unfold L; have ht := (D.large j).size; exact_mod_cast (show 1<(D.L j).val by omega)
  have hU (j) : 0 ≤ U j := (e j j).ok.2.2.2.2.1
  choose k hk using fun j => eventually_atTop.mp (Roster.eventual (f j) (Θ.theta j) (L j) (U j) Y.value g (h j) (hU j) hg (hL j))
  let A : Wait Y :=
    { B with
      readyHere := fun j => max (B.readyHere j) (k j)
      window := fun j s => B.window j s + Weak.stop (U j) (L j) (x s)
      sublin j := by
        have hx := within (U j) Y.value g (L j) (hU j) hg (hL j)
        simpa [add_div,x] using (B.sublin j).add hx }
  refine ⟨A,⟨fun _ => le_max_left ..,fun i j => Nat.le_add_right ..,le_rfl⟩,fun i σ hh => ?_⟩
  exact ⟨hk i σ (le_trans (le_max_right ..) hh), Nat.le_add_left ..⟩

/-- Sufficient bench for every *financed* height and aim at the given
stage. L here must be actually pegged to block lengths via Paid. The record
is at `a`, not an independent list of retired widths. Ceiling handles other
requests even if no attainable real b>0 called for there. -/
structure Bench (a : Levels G) (j k : ℕ) (L : ℝ) (e : Exchange) (F : Focus) : Prop where
  index : a.clock.J k=j
  cases_here : Roster F (a.clock.theta j) L e.weakHeight a.clock.bar G.slopeConstant (a.S.scale k)
  col h : (h:ℕ)*Real.log L ≤ spread e.weakHeight (a.clock.hatBeta k) → h ≤ k ∧
    ∀ i : ℕ, k-h ≤ i → i ≤ k+h → a.clock.J i=j



/-- Telescoping through a fixed-stage plateau; exponent uses EXACT
levels, no `o(1)` perturbation. -/
lemma straight (a : Levels G) (j n m : ℕ) (hh : n ≤ m) (h : ∀ i, n < i → i ≤ m → a.clock.J i=j) :
    let L:ℝ := (a.clock.factor j).val
    a.S.scale m=a.S.scale n+(m-n:ℕ)*log L ∧ a.S.a n=L^(m-n)*a.S.a m := by
  induction m,hh using Nat.le_induction with
  | base => simp
  | succ m he ih =>
    obtain ⟨h1,h2⟩:= ih (fun k ha hb => h k ha (by omega))
    intro L
    have hf : a.S.block m=a.clock.factor j := by rw [← h (m+1) (by omega) (by omega)]; exact (a.fits.sameFactor m).symm
    have hL : 0<L := by unfold L; exact_mod_cast (a.clock.factor j).property
    rw [show m+1-n=m-n+1 by omega, Schedule.scale_succ,Schedule.a_step,hf]
    constructor
    · rw [h1,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc]
    rw [h2]; change L^ (m-n)*a.S.a m = L^ (m-n+1)*(a.S.a m/L); rw [pow_succ]; field_simp

/-- Concrete answer at any authorized h, through all periods. Includes
substeps within h, even far from where prices were issued. `side` in ACTUAL
sites at those levels. In particular all criteria about x and nearby states in
Chorus apply even for receiving bootstrapped paths with arbitrary depths. -/
lemma Bench.rooms {a : Levels G} {j k : ℕ} {U : Exchange} {F : Focus} (Gsimple : G.Simple)
    (B : Bench a j k (a.clock.factor j).val U F) :
    let x:= a.clock.hatBeta k; let L:ℝ := (a.clock.factor j).val
    ∀ h : ℕ, h*log L ≤ spread U.weakHeight x → ∀ l : ℕ,k-h ≤ l → l ≤ k →
      a.clock.J l=j ∧ a.S.a l=L^(k-l)*a.S.a k ∧ near x (a.clock.hatBeta l) ∧
        ∀ p : ℕ,F.funds.H*(a.clock.monitor k)^((U.weakHeight+4)*((F.funds.D:ℝ)+1)) ≤ (a.S.side l p).val := by
  intro x L h hh l hu hl
  obtain ⟨he,hb⟩:=B.col h hh
  obtain ⟨h1,h2⟩:=straight a j l k hl (fun i ha hi => hb i (by omega) (by omega))
  have hgh : 0 ≤ G.slopeConstant := (Gauge.slopeConstant_pos Gsimple).le
  have hL : 0 ≤ log L := by apply log_nonneg; unfold L; exact_mod_cast (show 1≤(a.clock.factor j).val from (a.clock.factor j).property)
  have hi := le_trans (mul_le_mul_of_nonneg_right (show (((k-l:ℕ):ℝ)) ≤ h from by exact_mod_cast (show k-l ≤ h by omega)) hL) hh
  have hscale : a.S.scale k - a.S.scale l = ((k-l:ℕ):ℝ)*log L := by rw [h1]; ring
  refine ⟨hb l hu (by omega),h2,?_,?_⟩
  · unfold near
    have hz : x-a.clock.hatBeta l = G.slopeConstant*(((k-l:ℕ):ℝ)*log L) := by
      unfold x Calendar.hatBeta; change a.clock.bar+G.slopeConstant*a.S.scale k - (a.clock.bar+G.slopeConstant*a.S.scale l)=_
      rw [← hscale]; ring
    have ha := B.cases_here.bill
    rw [hz,abs_of_nonneg (by positivity)]; exact le_trans (mul_le_mul_of_nonneg_left hi hgh) ha
  intro p
  obtain ⟨-, hP, -⟩:=Deployment.clock_eqns a.clock k
  have ht := B.cases_here.ample
  rw [hP]
  apply le_trans ht
  have hc : Real.exp (a.S.scale l)=((a.S.denominator l).val:ℝ) := by unfold Schedule.scale Schedule.a; rw [inv_inv, Real.exp_log (by positivity)]
  apply le_trans (b:=Real.exp (a.S.scale l)) ?_ ?_
  · apply Real.exp_monotone
    change a.S.scale k-spread U.weakHeight x ≤ a.S.scale l; linarith
  rw [hc]; exact_mod_cast (Nat.le_mul_of_pos_left (a.S.denominator l).val (a.S.period p).property)
end Weak
end YM.Next.Scheduling
