import YM.TraceExtension.Slate.Pave
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
local notation "F'"=> C.labels.level d
local notation "p!"=> C.params
lemma cost_range (F:Frame G d)(z:F.Coeff): ‖F.core z‖≤‖z‖:=by
   refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>?_
   by_cases hi:i=0; subst i; simp only [Frame.core, LinearMap.coe_mk,AddHom.coe_mk, update_self,norm_zero]; positivity
   change ‖Function.update z 0 0 i‖ ≤ _; rw [update_of_ne hi]; exact norm_le_pi_norm _ _
-- Peg scales; absolute fee measured before overlay. Bias. For all sides.p.period.
abbrev barter (L:Levels G)(k:ℕ):= ((L.budget k).threshold^ (2:ℕ))⁻¹
abbrev loss (L:Levels G)(k:ℕ):= AgeK L (-(1/4:ℝ)) k
abbrev brevi (v:Logs C d)(k:ℕ)(p:ℕ×ℕ):= spine C d k p.1 p.2 (v.v k p)
abbrev hence (Z:Arch C)(v:Logs C d)(k:ℕ):=swale Z d k (v.x k)
abbrev MintC (q:Guilds C)(d k:ℕ)(p:ℕ×ℕ):= DCard p! (C.labels.level d) (H! k) (q k p.1 p.2)
variable {t:Tickets C}(hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
lemma rift {f:Films C}{w:ProbesC C d}{v: Logs C d}(hv: TravelsC (𝓛:Filter (ℕ×ℕ)) f w v.v v.x): ∀ᶠ k in atTop,∀ᶠ i:ℕ×ℕ in b!, ‖ (F').core (barter A k • w k i)-brevi v k i‖ ≤ loss (A) k:=by
    filter_upwards [hv.state] with k ht; filter_upwards [ht] with i hi
    let b:= ((A).budget k).threshold; let g:=(b^ (2:ℕ))⁻¹; have hb:0<b:=((A).budget k).threshold_pos; let t:=Cturn C d k i.1 i.2 (v.v k i)
    change ‖(F').core (g • w k i)- g • (F').core t‖ ≤ _
    rw [show (F').core (g • w k i)= g • (F').core (w k i) from ((F').core.restrictScalars ℝ).map_smul _ _,← smul_sub,←map_sub (F'|>.core),norm_smul, Real.norm_of_nonneg (by unfold g; positivity)]
    apply (mul_le_mul_of_nonneg_left ((cost_range ..).trans ((Push.Local.norm_le_size ..).trans hi.bias)) (by unfold g; positivity)).trans_eq; change g*(b^2*loss (A) k)= _; unfold g; field_simp
include hz in
lemma TravelsC.hi {f:Films C}{w:ProbesC C d}{v:Logs C d}(hv:TravelsC (𝓛:Filter (ℕ×ℕ)) f w v.v v.x): ∀ᶠ k in atTop,Tendsto (brevi v k) b! (𝓝 (hence Z v k)):=by
    filter_upwards [eventually_ge_atTop (C.ref d),hv.lands] with k hk he; exact topPitch hz hk he
include P hb hu h in
lemma tally {q:Guilds C} (hp:Credible q b!) (hd:d≤5){v:Logs C d}(ht:Loan q b! v) : ∀ᶠ k:ℕ in atTop,∀ᶠ p:ℕ×ℕ in b!, ‖brevi v k p - MintC q d k p‖ ≤ loss (A) k:=by
    filter_upwards [hp,rift (f:=Tales q) (v:=v) ht,Unwrap hu, hu] with k hi he hh ht'; filter_upwards [hi,he,hh,ht',(link_mesh hb).eventually_gt_atTop k] with i hi he hh ht' hv
    let f:= (F'); let R:=C.path.rep i.1 i.2 k; let u:= q k i.1 i.2; let p:= (A).budget k; let b:=p.threshold;let z:= MintC q d k i; have hb:0<b:=p.threshold_pos
    have hy:R.p=p:=(P.wilson.represents _ _ k (show k ≤ i.1 from hv.le)).vac; have hV:= R.p.order_ge; have hK:d≤ R.p.order:=by omega
    have hz: f.core z=z:=by rw [drop f,show z 0= 0 from Margin.card_zero f (Real_regular hi.puff.regular) hK hh hi.silk]; simp
    have hw: (readsC q d k i)= b^ (2:ℕ) • z:=by unfold readsC; rw [pricedU f (Real_regular hi.puff.regular) hK hh hi.silk h hd, hy]
    rw [hw,show barter (A) k • (b^ (2:ℕ) • z)=z from inv_smul_smul₀ (by positivity) _] at he; rw[norm_sub_rev]; change ‖f.core z-_‖ ≤ _ at he; rw[hz] at he; exact he
end YM.Trace.Slate
