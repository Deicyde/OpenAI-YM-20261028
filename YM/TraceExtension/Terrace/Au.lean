import YM.TraceExtension.Terrace.Arms
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}(h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> tilesAt C.S
open Relay
include h θ
lemma chest(d:ℕ): ∀ᶠ i:ℕ in atTop,let k:=summit C.path.levels i; 2*(C.S.a i)^d*Tau (A) i 1*allowanceC C d k ≤ Tau (A) i (25000*d+10000):=by
   let P:=C.path.levels; have ht:= (sapTree h P 2 zero_le_two).push ((sapTree h P 1 zero_le_one).sum (coreK P h θ (Eventually.of_forall fun i=> le_refl (summit P i))) h)
   filter_upwards [toll_small (x:= 1) one_pos ht,back_gate P h θ] with i he hZ
   let a:=Tau P i; let k:=summit P i; let c:=(P.params k).columns; intro k₀; unfold allowanceC; rw[alto_norm]
   let D:= C.S.a i/C.S.a k
   change 2*C.S.a i^d*a 1*((C.S.a k^d)⁻¹*(1+c))≤_
   have hD:0<D:= div_pos (C.S.a_pos _) (C.S.a_pos _)
   calc
    _ = a 1 * ((2*(1+c))* D^d):=by unfold D; ring
    _ ≤ a 1*(a 1*(a 20000)^d):=by
       have hp':D ≤ a 20000 := (z_scale P i k)|>.le.trans (Real.exp_monotone (by norm_num [Dust]; exact hZ)); exact mul_le_mul_of_nonneg_left (mul_le_mul he (pow_le_pow_left₀ hD.le hp' _) (pow_nonneg hD.le _) (Tau_pos ..|>.le)) (Tau_pos ..|>.le)
    _ ≤ _:=by
       unfold a; rw [← Tau_pow,← Tau_add,← Tau_add]; apply tau_mono P i; have hp:0≤(d:ℝ):= by positivity
       linarith only [hp]
include K
-- basis ext token weight tent.BUY. accepts any labels at stop m
lemma popping (d:ℕ):∀ᶠ i in atTop,let k:=basin A K i; let f:= Tau (A) i; (∀ (N p:ℕ)(x:C.label d), (C.labels.level d).coeffSize (columns C d k N p x) ≤ (C.S.a i)^d*f 1→ (f (-3))*moneys C d k N p x ≤ fly (A) d k)∧ Real.exp ((C.S.a i/C.S.a k)^4 * Vac.treasury C.path.levels k+6)/(f (-3)) ≤ f 5:=by
    let P:=C.path.levels; let k':= basin P K
    let Q i:= ((C.S.a i/C.S.a (k' i))^d);
    have he:=open_budget P h θ K; have hp:∀ᶠ i:ℕ in atTop,k' i ≤ summit P i:=he.mono fun _ h=>h.le
    have hv:Ticket P 0 (fun i=> (P.params (k' i)).columns* Q i*(fly (A) d (k' i))⁻¹):=((coreK P h θ hp).push ((hullK P K h θ).pows h d)).push (grantK _ h θ hp d)
    have he':= (stakeK (C:=C) K h θ).push (sapTree h P (Real.exp 1) (Real.exp_pos _).le)
    filter_upwards [toll_small (x:=2) two_pos hv,toll_small (x:=2) two_pos he'] with i ht hp k f
    have hm:f (-3)*f 1*f 2 =1:=by unfold f; rw [← Tau_add,← Tau_add];norm_num
    constructor
    · intro N p x hQ
      let z:=(C.labels.level d).coeffSize (columns C d k N p x)
      unfold moneys Next.Rank.Spindle.paid awake; rw [Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]
      let a:= C.S.a k; let q:=a^d; have hx:0<q:=pow_pos (C.S.a_pos _) _; let b:= (P.params k).columns; let y:= fly P d k; have hb:0<b:=zero_lt_one.trans_le (P.params _).columns_ge; have hy:0 < y:= credit ..
      change f (-3)*(b*(q⁻¹ * z)) ≤ y
      refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (inv_nonneg.mpr hx.le)) hb.le) (Tau_pos ..|>.le)).trans ?_
      have hU : (C.S.a i)^d=Q i*q:=by unfold q a Q; rw[div_pow]; exact (div_mul_cancel₀ _ hx.ne').symm
      rw [hU]; apply le_of_mul_le_mul_right _ (inv_pos.mpr hy)
      have hw : f (-3)*f 1*(b*Q i*y⁻¹) ≤ 1:= (mul_le_mul_of_nonneg_left (show b*Q i*y⁻¹≤ f 2 from ht) (mul_nonneg (Tau_pos ..|>.le) (Tau_pos ..|>.le))).trans_eq hm
      refine le_trans (le_of_eq (b:=f (-3)*f 1*(b*Q i*y⁻¹)) ?_) (hw.trans_eq (mul_inv_cancel₀ hy.ne').symm); field_simp;ring
    · change _ ≤ Tau _ _ _; rw [div_le_iff₀, ]
      let t:= stakes C i k; have ht':t*Real.exp 1≤ f 2:=hp; have he : f 5*f (-3)=f 2:=by unfold f; rw [← Tau_add];norm_num
      refine (le_trans (le_of_eq (b:=t*Real.exp 1) (by unfold t stakes; rw[← Real.exp_add]; apply congr_arg; ring)) (ht'.trans he.symm.le))
      exact Tau_pos ..
-- compose duties
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)
include H ht
lemma journey (d:ℕ):∀ᶠ i in atTop,∀ N p,summit (A) i<N →∀ (v:C.label d)(hi:i ≤ N),(C.labels.level d).coeffSize (columns C d (basin (A) K i) N p v)≤ C.S.a i^d*Tau (A) i 1→
    (tilesAt C.S p hi).rootTest (C.beta N p) (C.O N p v 0) ≤ Tau (A) i 5 :=by
    let P:= C.path.levels; filter_upwards[popping h θ K d,open_budget P h θ K, eventually_ge_atTop (C.ref d)] with i hi hj ht' N p hN v hv hx
    exact (tentK C N (basin (A) K i) i p d v (Tau (A) i (-3)) (Tau_pos ..) K H ht.costs ht.back (tracks P K i) ht' (hj.trans hN) (hi.1 N p v hx)).trans hi.2
lemma smithies (d:ℕ):∀ᶠ i in atTop,let k:= summit (A) i; ∀ N p (hn:k < N)(x:C.label d),let T:=tilesAt C.S p ((stellar (A) i).le.trans hn.le);(∀ v:C.label d,Interior (T.chamber 0) (C.O N p v 0)) → (C.labels.level d).coeffSize (columns C d k N p x) ≤ C.S.a i^d * Tau (A) i 1 →
       ∃ g: Config G (C.side k p)→ℂ,(∀ V, ‖g V‖ ≤ Tau (A) i (25000*d+10000))∧ Interior (Push.GridApprox.window 0 (lensScope C d)) g ∧ Push.GridApprox.room (A) i k (lensScope C d)∧ Interior (T.chamber 0) (backTo C.path N p hn.le g)∧ T.rootTest (C.beta N p) (backTo C.path N p hn.le g-C.O N p x 0) ≤ Tau (A) i (-300):=by
    let P:= C.path.levels; let j' := basin P K; let k':=summit P; let y:= lensScope C d
    have hz:= ( (hrate P h).comp (Sstar P)).eventually_ge_atTop (↑y:ℝ)
    filter_upwards [breeze h θ K d,chest h θ d, (Kagura (d:=1) P h θ),open_budget P h θ K,(bondB P K).eventually_ge_atTop (C.ref d),hz] with i hi he ha hq hK hv k N p hN x T ht' hx
    let j:= j' i; let f:=Tau P i; let w:= (C.S.a j)^d*f 400; have hw:0<w:= mul_pos (pow_pos (C.S.a_pos _) _) (Tau_pos ..)
    have hs:=ha y (by rw [pow_one]; exact hv)
    obtain ⟨B,hB,hx',hP,hM⟩:= repast C N k j p d H w x ht i K (tracks P K i) hK hq.le hw hs hi.1 hN ((stellar P i).le.trans hN.le) ht'
    have hS: stockX C d k N p x ≤ 2*(C.S.a i)^d*Tau P i 1:= ((mul_le_mul_of_nonneg_left hx zero_le_two).trans_eq (mul_assoc ..).symm)
    refine ⟨B, fun v=>?_, hB,hs,hP,hM.trans ((mul_le_mul_of_nonneg_right hS (div_nonneg (Real.exp_pos _).le hw.le)).trans hi.2)⟩
    exact (hx' v).trans ((mul_le_mul_of_nonneg_right hS (show 0 ≤ allowanceC C d k by unfold allowanceC; positivity[(P.params k).columns_ge])).trans he)
end YM.Trace.Terrace
