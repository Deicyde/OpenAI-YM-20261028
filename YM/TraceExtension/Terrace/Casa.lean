import YM.TraceExtension.Terrace.Virtu
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Pressure
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> C.path
local notation "H!"=> (C.path.levels.clock.hatBeta)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels) (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W)
variable {d m k i N p:ℕ}
local notation "V!"=> C.labels.level d
include P h θ K ht hM
def nativeC (C:Family G)(d i j k:ℕ):= let x:=C.path.levels.clock.hatBeta k;let w:= x⁻¹*((fly C.path.levels d j/2)/(‖alto C.path j d‖*(x^3/gainChart C.path k j))); stakes C i j/w
structure Bill (C:Family G)(N p d k:ℕ) (g:Film G (C.side k p))(v x:C.label d) : Prop where
   norms : (C.labels.level d).coeffSize v ≤ 1
   bias : (C.labels.level d).coeffSize (v-columns C d k N p x) ≤ C.path.levels.clock.threshold k ^ (2:ℕ)*AgeK C.path.levels (-(1/4:ℝ)) k
   root (i j l:ℕ): Stock.Tabs.opens C.path.levels 1 i j→ C.ref d ≤ j→ j < k → room C.path.levels i k l →∀ hk:i ≤ k,∀ hp:k≤N, Interior (Push.GridApprox.window 0 l) g→
       (tilesAt C.S p (hk.trans hp)).rootTest (C.beta N p) (backTo C.path N p hp (alto C.path k d • g)- C.O N p x 0) ≤ nativeC C d i j k
lemma purchasing (d:ℕ)(v:ℝ)(hp:0< v)(he:supportQ C.path.levels): ∀ᶠ k:ℕ in atTop,∀ᶠ p:ℕ in atTop,∀ (N:ℕ), k<N →∀ (X: Coefficient (C.labels.level d) (C.side k p))(g:Film G (C.side k p)), AtomD (C.localSection d) C.params (C.path.rep N p k) X g (C.path.levels.clock.forcedAllowance k) (v*Shunt.grantS (C.path.levels.clock.hatBeta k)) (C.path.levels.clock.hatBeta k)→∃ s:C.label d,Bill C N p d k g X.x s:=by
    let T:= C.labels.level d; let U:=A
    filter_upwards [Meltdown U he h,eventually_ge_atTop (C.ref d), (hrate _ h).eventually (book_pay v hp.le), bias_pay _ θ h v hp.le] with k hi hs hx hT
    filter_upwards [hM.bias d k hs] with p hb N hN X g hG
    let Z:= H! k; let Y:= Z^ (3:ℕ);let F:= Shunt.grantS Z;have hz:0<Z:= bell ..;have hy:0 < Y:=pow_pos hz _
    obtain ⟨b,hB,hb'⟩:= hG.charge; obtain ⟨L,hL,hP⟩:= hG.pays
    have ht':4*(1+((A).params k).columns)*(v*F) ≤ Y:=le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right (θ.share k) _) (by positivity)) (show 0≤v*F from mul_nonneg hp.le (mul_nonneg (sq_nonneg _) (wake ..|>.le)))) hx.2
    have hu: Z*fly (A) d k≤ Z⁻¹ * Y:=by
       have hu:=mul_le_mul_of_nonneg_left (fly_le C k d) hz.le; change Z * _ ≤ Z⁻¹*Z^3; rw [show Z⁻¹*Z^3=Z^2 from by field_simp]; apply hu.trans; rw[mul_one]; simpa only[pow_one] using (pow_le_pow_right₀ (A|>.fits.delayed k|>.le) (show 1 ≤2 by norm_num))
    let u₀:= alto C.path k d; have hR: Buff (C:=C) (N:=N) (u₀ • g) L b X Z:=⟨hG.shape,hb',hL,hP, fun U=> ((congr_arg (u₀*·) (hG.birth U)).trans (by change u₀*(_*g U)=_* (u₀*g U);ring))⟩
    obtain ⟨s,ht₁,h₃⟩:= riches C N k p d P X ht K hN hs Y (cameo (A) k) (v*F) hR (mul_pos hp (show 0<F from mul_pos (by rw [← Tanya (A) k]; exact sq_pos_of_pos ((A).budget k).threshold_pos) (wake ..))) hB ht' hi hu (hb _ hN.le)
    have hv: T.coeffSize X.x ≤ 1:= le_trans (le_add_of_nonneg_right (rem_nonneg hb')) (hB.trans hx.1)
    refine ⟨s,hv, ?_ , fun i j l hf hl hp hg h' hw hV=> h₃ i j l hf hl hp hg (hV.scale _)⟩
    apply le_trans _ hT; rw [le_div_iff₀ (cameo_pos ..),mul_comm]; exact ht₁
omit ht hM P
lemma tends_price (d:ℕ): ∀ᶠ i in atTop, C.S.a i^d * nativeC C d i (basin (A) K i) (summit (A) i) ≤ Tau (A) i (-430):=by
    let Q:=C.path.levels; let j:= basin Q K; let k:= summit Q; let t i:= Q.clock.hatBeta (k i); let v i:=(Q.S.a i/Q.S.a (j i))^d; let B i:= stakes C i (j i)* (2*v i* t i^4)* (fly Q d (j i))⁻¹
    have hZ:Ticket Q 0 B:=(((stakeK _ h θ).push (((sapTree h Q 2 zero_le_two).push ((hullK Q K h θ).pows h d)).push ((stickK Q h θ).pows h 4))).push (grantK _ h θ (open_budget Q h θ K |>.mono fun _ i=>i.le) d))
    filter_upwards [gainsK (C:=C) h θ K, toll_small (x:=70) (by norm_num) hZ] with i hi he
    let g:= gainChart (T!) (k i) (j i); have hg:0<g:= Real.exp_pos _; let h₀:=C.S.a (j i); let q:= h₀^d; have hq:0<q:=pow_pos (C.S.a_pos _) _;let y:=t i; let a:= fly Q d (j i); let X:= stakes C i (j i)
    have hy:0<y:= bell ..; have ha:0<a:=credit ..; have hp:(C.S.a i)^d=v i*q:=by unfold v; rw[div_pow]; exact (div_mul_cancel₀ _ hq.ne').symm
    apply le_of_mul_le_mul_right _ hg; refine le_trans ?_ (mul_le_mul_of_nonneg_left hi (Tau_pos (A) i (-430)|>.le)); refine le_trans ?_ (he.trans_eq ?z); case z=> rw [← Tau_add]; norm_num; rfl
    unfold nativeC; rw [hp]; change v i * q * (X / (y⁻¹*(a/2/(‖alto (T!) _ _‖*(y^ (3:ℕ)/g))))) * g ≤ B i; rw [alto_norm]; change v i*q* (X/(y⁻¹ * (a/2/(q⁻¹*(y^ (3:ℕ)/g)))))*g ≤ X*(2*v i*y^4)*a⁻¹; apply le_of_eq; field_simp
end YM.Trace.Terrace
