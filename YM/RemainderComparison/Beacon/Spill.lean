import YM.RemainderComparison.Beacon.Terms
import YM.RemainderComparison.Beacon.Serve
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-!
# Period-independent high-order real layer estimate

Analytic payment furnished by the E6 log and sector methods. Before mask changes,
projection and comparing to Fk etc. Works for any `X` and bit supplied on an admissible
step, not hypothesizing that its E varies with the physical coupling. High is costed
by the actual power, arbitrarily high, *also* large shapes and every mandatory-seed
carrier in the regular part (identified by incidence; other companions are still in
the low part). This is useful in the virtual-period/Taylor comparison. Not yet paying
low analytic approximation, affine resets, or arbitrary marked sectors' version.

This genuine truncation does NOT assert that taking the low component *is* the
analytic vertex substitution Fk. Low still includes profile survivors and long
primitives that can have length below our cutoff; consumes a stationary/Laplace/
profile analysis. Do that in the coefficient convention of the same Wilson path.
Don't manufacture a truncation norm merely from a ratio of evaluated densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Beacon
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Time
open Extra.Iteration PhysicalNext PhysicalNext.Repeat Height Match Song Refrain Beam
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Supply Input Testing PriceCompiler Opera Roof Roost Org
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {M : Metals G} {D : Rolls M.p} {U : Alloy M D} (F : Roost.Factor U)
local notation "B" => U.B
local notation "R" => F.shape

-- comparison-grade threshold, preserving height already paid

def grade (n : ℕ) := 2*n+3
-- true-shape compression after this threshold costs explicitly this larger hull

def depthCap (n : ℕ) (x : ℝ) := (grade n:ℝ) * Pressure.Stores.till x

section amount
variable {C : Levels G} {m n : ℕ} (L : Side) (hL : betaF G (C.clock.hatBeta m) L=C.clock.hatBeta (m+1))
variable (p : RG.Stage) (E : BudgetPoint) (ho : E.order=p.order) (hp : E.power=p.power)
local notation "x" => C.clock.hatBeta m
include hL ho hp
lemma fraction_paid (β w : ℝ) (N : ℕ)
    (hω : ((grow G L x^3)⁻¹*w) ≤ heap G p (1/16)*δE x)
    (hβ : inBand (betaF G x L) β) :
    turnFee E*((grow G L x^(grade N))⁻¹*w) ≤ 2^N*((Real.sqrt β)⁻¹)^N := by
  have h:1< betaF G x L:= hL ▸ C.fits.delayed _
  let a:=grow G L x
  let g:ℝ:=(Real.sqrt β)⁻¹
  have hD:0<a:= Real.rpow_pos_of_pos (zero_lt_one.trans h) _
  have hT:=turnFee_pos E
  have he : turnFee E=away p:= by unfold turnFee away; rw [ho,hp]
  have hx':0 ≤ δE x := Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  have hW:turnFee E*((a^3)⁻¹*w) ≤ 1 := by
    have hh := authorized G p|>.1
    have hM: 0 ≤ credit G p:= (credit_pos ..).le
    have hv:δE x ≤ 1:= coarse_δ C m
    apply (mul_le_mul_of_nonneg_left hω hT.le).trans
    unfold heap; rw [← he, ← mul_assoc,show turnFee E*(1/16*Time.credit G p/turnFee E)=1/16*Time.credit G p by field_simp]; nlinarith only [hv,hM,hh]
  calc
    _ = ((a^2)⁻¹)^N * (turnFee E*((a^3)⁻¹*w)) := by
      unfold grade; rw [pow_add,pow_mul,mul_inv_rev]; unfold a; rw [inv_pow]; ring
    _ ≤ ((a^2)⁻¹)^N*1:= mul_le_mul_of_nonneg_left hW (by positivity)
    _ ≤ _:= by rw [mul_one, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) (grow_gap G L _ β h hβ) _
end amount

section detail
variable {N m n : ℕ} (κ : ℕ)
local notation "L" => (D.L (U.B.a.clock.J (m+1)))
local notation "x" => U.B.a.clock.hatBeta m
local notation "Q" => (F.target (U.B.a.clock.J (m+1)) (U.B.a.clock.J m))
local notation "e" => (F.expense (U.B.a.clock.J (m+1)) (U.B.a.clock.J m))
local notation "Gd" => grow G (D.L (U.B.a.clock.J (m+1))) (U.B.a.clock.hatBeta m)
local notation "o" => Chi.canonical
local notation "Θ" => U.B.a.budget m
local notation "α" => U.B.kin.alpha N m

variable {A Y : RG.Rep G (U.B.a.S.side (m+1) n)}
    (hn : m<N) (hβ : A.beta ∈ band U.B.a (m+1))
    {H : Guide (U.B) (F.shape) N m n A} {J : Guide (U.B) (F.shape) N m n Y}
    (he : Opera.Price U.B F.shape N m n A H) (X : Alliance J H 1 0)

include F hn
lemma force_cap (H : Guide (U.B) (F.shape) N m n A) :
    Cash.armK Q L ((R).μ (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) x 0 (e).degrees ≤ Target.earnings x := by
  have hk:= (B).valid.pays m; let h := F.pledging
  have hz:= h.conducts.income.grow.2 ((B).a.clock.J (m+1)) ((B).a.clock.J m) (step_paid (B).a m) (x) hk _ _ ((B).a.clock.op m n) (ships B N m n) H.laws.data.funds (protocol B hn h.conducts.full) A H
  obtain ⟨l1,d,p,y,a,b,r,c,t,k,u,_,_,_,_,we⟩:= hz; exact we

include he hβ
lemma prune
    (hw : Gd ^ grade κ ≤ Real.exp ((Q).mark L ((R).μ (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) x)) :
    let f:= large H (grade κ) (depthCap κ x) ∘ X.furrow
    Collection.Local (Beam.marquee J Θ) Θ (serve J X o f) (2^κ * ((Real.sqrt A.beta)⁻¹)^κ)
      (Cash.armK Q L ((R).μ (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) x 0 (e).degrees) := by
  intro f; let Z := U.B.a; let p:=Z.params m; let I':= Z.clock.J (m+1); let i:=Z.clock.J m
  let k:=step_paid (B).a m; have ha:= (B).valid.pays m; let h:= F.pledging
  have ht := h.jewels I' x ha i k
  obtain ⟨C',d,v,t,a,b,r,E,q,l,j,⟨W,hv⟩,hT,hp⟩:= ht.2 _ _ _ _ H.laws.data.funds (protocol B hn h.conducts.full) A H
  obtain ⟨hG,-,hz,hq⟩:= h.peak.large I' i k x ha
  obtain ⟨hE,ht',hs⟩:= hq _ _ _ hT W.balance hp
  have hW : Gd ^ grade κ ≤ Real.exp ((Q).ε * depthCap κ x) := by
    have he: Gd ≤ Real.exp ((Q).ε * Pressure.Stores.till x):=
      (le_self_pow₀ hG (show (3:ℕ)≠0 by decide)).trans ht.1
    apply (pow_le_pow_left₀ (zero_le_one.trans hG) he _).trans_eq
    rw [← Real.exp_nat_mul]; unfold depthCap; congr 1; ring
  have hp := F.pledging.agenda _ _ k |>.1
  have hG' := params_eq (B).valid m
  have hσ:preExponent Θ ≤ (e).earn:=
    (congr_arg (fun g : RG.Stage=> g.supportExponent+3) hG').trans_le hp
  have ho:(Θ).order=(M.p.profile i).order := congr_arg RG.Stage.order hG'
  have hu:(Θ).power=(M.p.profile i).power := congr_arg RG.Stage.power hG'
  have hr := filtered X Θ W rfl hσ ho.le hu.le rfl _ _ (paid W hE (M.p.profile i).power hG hv hz ht' (grade κ) (depthCap κ x) hW hw) he
  obtain ⟨w,hW,hv⟩:= hr.cheap
  have hL : betaF G x L=Z.clock.hatBeta (m+1):= (PriceCompiler.beta_eq (B).valid m).symm
  exact { hr with cheap:=⟨w,hW,fun s=>budget_loosen (hv s) (fraction_paid L hL _ _ ho hu _ _ _ (by rw [← mul_assoc]; exact hs) (hL.symm ▸ trial_in hβ))⟩ }
-- Entire output unnormalized, vacuum includes scalar and early kinetic receipt.
-- Local.high is before affine/scalar rebates. Low retains all uncut receipts and
-- still needs actual-to-formal comparison.
omit he hn hβ
def tag (F : Roost.Factor U) (m : ℕ) := Cash.armK (F.target (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) (D.L (U.B.a.clock.J (m+1))) (F.shape.μ (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) (U.B.a.clock.hatBeta m) 0 (F.expense (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)).degrees
structure Split (X : Alliance J H 1 0) (t : Tree.Forest (U.B.a.clock.op m n).ratio) : Prop where
    tail : Collection.Local (Beam.marquee J Θ) Θ (serve J X o (large H (grade κ) (depthCap κ x) ∘ X.furrow)) (2^κ * ((Real.sqrt A.beta)⁻¹)^κ) (tag F m)
    earning : tag F m ≤ (U.B.a.clock.forcedAllowance m)^4
    pledge : U.B.a.clock.forcedAllowance m ≤ ((Real.sqrt A.beta)⁻¹)^κ
    whole : ∃ a b, Collection.Local (posting Θ J) Θ (plusone J X o α) a b ∧ ∀ V,
      let f:=large H (grade κ) (depthCap κ x) ∘ X.furrow
      let β:= A.beta; let d:= Θ; let p:= Beam.marquee J d
      let v₀:=weighty H Chi.canonical t; let r₀:= Height.sleeping J X o f α
      Summable (fun i=> (p.read r₀).regularOccurrence d i V) ∧
      (U.B.a.clock.op m n).push β A.eval V = earlyValue (posting Θ J) (U.B.kin.path N m) (U.B.a.params m).clip Θ (plusone J X o α) β v₀ α V ∧
      (U.B.a.clock.op m n).push β A.eval V = Real.exp (-((p.read (serve J X o f)).additive Θ V)) * earlyValue p (U.B.kin.path N m) (U.B.a.params m).clip Θ r₀ β v₀ α V
include hn he hβ
lemma divided (hl : Lives U.B.bake N (m+1) n A) (t : Tree.Forest (U.B.a.clock.op m n).ratio)
    (hw : Gd ^ grade κ ≤ Real.exp ((Q).mark L ((R).μ (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) x))
    (hx : U.B.a.clock.forcedAllowance m ≤ ((Real.sqrt A.beta)⁻¹)^κ) : Split F κ X t := by
  have ht := prune F κ hn hβ he X hw
  let h:=F.pledging; let hg := h.conducts
  have hf := hg.machine.passes (l:=Set.univ) («Q»:=fun _ : ℝ=>A) hn (fun _ _=> ⟨hl,hβ⟩) |>.1
  have hE:= (Boulevard.lays R U (U.B.a.S.oneStep m n).exact_size X F.inn.chip hn h.jewels hg.full (h.agenda _ _ (step_paid (B).a m)|>.1) hf.decent
    (show Boulevard.SeekR _ U _ _ (U.B.a.S.oneStep m n).exact_size H from he) t)
  refine ⟨ht, (force_cap F hn H).trans_eq (earned _ _), hx,_,_, hE.1,fun V=>?_⟩
  let Φ:= large H (grade κ) (depthCap κ x) ∘ X.furrow
  obtain ⟨hr,hR⟩:= reunite X Θ Φ o α (weighty H o t) A.beta ht hE.1 V
  exact ⟨hr,hE.2 V,(hE.2 V).trans hR⟩

end detail
lemma all_scale (κ : ℕ) (hG : G.Simple) : ∀ᶠ m in atTop,
    ∀ N n, m<N → ∀ R' : RG.Rep G (U.B.a.S.side (m+1) n),
      Lives U.B.bake N (m+1) n R' → R'.beta∈band U.B.a (m+1) →
      ∀ (H : Guide U.B F.shape N m n R'), (Opera.Price U.B F.shape N m n R' H) →
        ∀ (Y) (J : Guide U.B F.shape N m n Y) (X : Alliance J H 1 0) (F' : Tree.Forest (U.B.a.clock.op m n).ratio), Split F κ X F' := by
  filter_upwards [mark_ready U.B.a hG (grade κ),insurance U.B.a hG κ] with m hm hx N n hN R' hV hβ H h Y J X F'
  exact divided F κ hN hβ h X hV F' (hm _ (PriceCompiler.beta_eq U.B.valid m).symm _ _ _ _ (force_cap F hN H)) (hx R'.beta hβ)
lemma begins {N m n : ℕ} {R' : RG.Rep G (U.B.a.S.side (m+1) n)} (hn:m<N)
    (hR : Lives U.B.bake N (m+1) n R') (hp : R'.beta∈band U.B.a (m+1)) :
    ∃ H : Guide U.B F.shape N m n R', Opera.Price U.B F.shape N m n R' H:=
  Opera.feature U.B F.shape hn F.pledging.conducts.full F.pledging.conducts.income hR hp

end YM.RemainderComparison.Beacon
