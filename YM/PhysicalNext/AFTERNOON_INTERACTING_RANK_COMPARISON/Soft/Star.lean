import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Notes
import YM.Extra.MULTISOURCE_BOUNDS.Scheme
import YM.Further.ITERATION_RECIPE_PRODUCER.Author
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Ampersand
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Proceed
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Crowns
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Supra
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Spinto
import YM.Progress.CLASSICAL_KIN_RECURSION.Cargo

/-!
# Soft restarted interactions

Use at Ledger on this family & Binding.

Does NOT assert Strong
RankCovariance.Interaction (ancillary P standards differ); gives Choir
et al on actual arguments, consumer through the same Market.Purchases.

The step push and interacting comparisons at restart already earned.

Still requires LanternMarks (e.g. at a Punch) or supplier therefor,
along with procurement of ShowHours/Vents etc.; not constructing the
true cycle history.

Here use independent design, value-only P on restart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis Tree Laurent Bloch Exterior FreeResolvent
     Weaver Worker Radian
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) {O : HaarBudget G} (J : ChartRatio G) {d : ℕ} (F : Cohesion C d) {S : Table C.book} (X : Columns C S d)
local notation "A" => C.path.levels
local notation "U" => F.current k
local notation "p'" => stamp C.path.levels N p
local notation "s"=> clim A k
-- public theorem at launch family per Epoch, before Punch branch
lemma rented (h : Metering F O k w) (Z : ShowHours J B U k w l r) (hv : Vents B U J l r k) (hN : k≤N) (hp : |(C.path.rep N p k).beta-s|≤ s/8) :
    let c:= isohypse M hN p
    ∃ V,Whip B J U Z h.cost c V (Station.width A (U).band k) le_rfl ∧ Nylon c V p' (short B N p) U ∧
       ∀ n : ℕ, ∀ x : Points n,n ≤ 2→ Fit A (U).band k x → Choir U c V (short B N p) x:= by
  intro c; have hb: 0 ≤ (U).band:= ((show (U).band=F.fixed from F.sameB _).symm ▸ F.hr.le)
  obtain ⟨V,hP⟩:= thicket B M J U Z hv h.cost hN hb p _ le_rfl ((Station.wider ..).trans (before ..)) hp
  exact ⟨V,hP, embroidered B J c U M Z hv h.cost V hP hb,fun n x hn he => s_choir B J U M Z V h.cost hP x he hn⟩
lemma backstage (T: Tender F k) (h : Metering F O k w) (Z : ShowHours J B U k w l r) (hv : Vents B U J l r k) (marks : LanternMarks M F X k)
    (hr :∀ N p,k≤N → |(C.path.rep N p k).beta-s|≤ s/8) (ht : ∀ P : BudgetPoint,P.B ≤ walls s →Tickets P (kinetics s))
    (hy : ∀ p N,Seal A k p d 2 (stamp A N p) chartHeat → Wall.Model A d k p (stamp A N p)) : s_supplies F X M h.cost:= by
  intro hk hf
  have hz : d-1≤ C.path.levels.clock.J k-2:= by have hx:= (M.stages d).1; have hl:=C.path.levels.fits.mono hk; omega
  filter_upwards [marks hk hf, eventually_ge_atTop k] with N hF hN
  refine ⟨hN,fun p=> ?_⟩
  let c:= isohypse M hN p; let Q:=stamp A N p; obtain ⟨V,hP,H,hQ⟩:= rented B M J F h Z hv hN (hr N p hN)
  obtain ⟨hs,he⟩:= supply (prepared C.path.levels.clock.kernel) A rfl h.charge.allot.permitted hz T N p
  refine ⟨Q,short B N p,c,V,hP.stops,H,fun i=>?_⟩
  let n:= (X.row i).extra+1; have hn:n≤2:= by unfold n; have hl:=(X.row i).cap; omega
  let γ:=(X.row i).expected; let D:= he _ hn
  obtain ⟨P,hV,h₁,h₂⟩:= D.optics
  refine ⟨premiere γ hn H h.cost.coup (hQ _ γ hn (hf i)) (hf i) ht,
    ⟨hy p N hs,Radian.flown _ _ _ _ _ hV h₂ h₁ D.visor D.hinge D.rotor D.force⟩,fun v hh=> (marking M hk (keeping M p N k hN) c γ _ v _).1 (hF _ p i v hh)⟩
lemma cast_off (h : G.Simple) (Z' : ∃ᶠ k in atTop, Tender F k ∧ Metering F O k w ∧ (∃ l r, ShowHours J B (F.current k) k w l r ∧ Vents B (F.current k) J l r k) ∧ LanternMarks M F X k ) : s_provisions F O X M:= by
  refine (Z'.and_eventually ((follows_prices M h).and ((Radian.commissioned A h d 2 (by decide) chartHeat_pos).and ((Station.hat_rate A h).eventually Flux.timing)))).mono ?_
  rintro k ⟨⟨T,H,⟨l,r,Y,Q⟩,V⟩,hp,hv,hω⟩; exact ⟨w,H,backstage B M J F X T H Y Q V hp hω (fun p N=> hv p _)⟩

lemma wheeled (O : HaarBudget G)(p : Price.Representatives C X)(h : G.Simple)(ht : s_provisions F O X M):∃ Z : X.Trials, Travels_ O p F.fixed Z ∧ Market.Purchases Z:= by
  exact v_obtain_purchases O p _ h M F.hr (v_pay_all O h _ _ F.hr _ (v_culminates O X _ p _ h F.hr M F.gain _ (v_paid_factory F O X M p h ht)))
end YM.PhysicalNext.InteractingRank.Soft
