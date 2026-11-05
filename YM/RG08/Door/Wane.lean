import YM.RG08.Door.Inward
/-!
# Limit step still a heat op. Locality and valuation
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit
open PertExtension.Series.Tested PertExtension.Series.Radial Scores
open scoped BigOperators Topology Real Classical ContDiff
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
variable {I:Type}{u:I→Windows}
section
variable (ν D')
-- Limit strips

def don (X:Chain)(i:ℕ): StripU G (X.S.block i) := ⟨ Summit.slate X G i, Summit.amber X G i, awakening ν (X.patch i) D' X.kernel.penalty (statue X ν D' (i+1)), afternoons (reform (Conductor.compass ν (granite X ν D' i))) ⟩
def didn (X:Chain)(i E:ℕ) : StripU G (X.S.block i):= { don ν D' X i with song := awakening ν (X.patch i) D' X.kernel.penalty (graving E (statue X ν D' (i+1))) }
end
section cutU
variable {α β:Type}[NormedAddCommGroup β][NormedSpace ℝ β][CompleteSpace β][Fintype α]{p:Side}{Q A:Canticle α}{B:Row α α}{U:Screed β α}
lemma darkage (h:∀ i≤E, Q i=A i)(he:e≤E): murmur none B Q U n e r= murmur none B A U n e r:= by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero=> rw [murmur,murmur]
  | ind n ih=>
    rw [murmur_step,murmur_step,ih n le_rfl he]; congr 2
    apply sum_congr rfl; intro b hb; refine sum_congr rfl fun c hc=> ?_; have ht:= mem_antidiagonal.mp hb; have hv:=mem_antidiagonal.mp hc
    rw [show murmur none B Q U b.1 c.1= murmur none B A U b.1 c.1 from funext fun i=>ih b.1 (by omega) (by omega), show Refrain B Q none b.2 c.2=Refrain B A none b.2 c.2 from funext fun i=> leeks _ _ (fun j hj _=> congr_fun (h j hj) _) _ (by omega) _]

variable {V:BoardU D R G}
def dryE (V:BoardU D R G)(E i:ℕ) := if i≤E then V i else 0
private lemma filament_blip {Q':Row (Fink G p) (Fink G p)} {A:Cross p (Loc G 1) (Loc G 1)}{R S:Canticle (Park G p)}(h:∀ i≤E,R i=S i)(V:BoardU D w G): Same (filop Q' A R none τ d V) (filop Q' A S none τ d V) E := by
  intro e he; funext r; unfold filop; apply congr_arg (fun T:Rooted (Voice D w) (Park G p) r=> spring T (scan A)); unfold washed; exact sum_congr rfl fun k _=> darkage h he
lemma push_foot {A B : StripU G p}(he:e≤E)(h:A.cv=B.cv)(hp:A.tree=B.tree)(hg:A.scale=B.scale)(hz:∀ i≤E,A.song i=B.song i): Needle.push A τ d (dryE V E) e=Needle.push B τ d V e := by
   unfold Needle.push; rw [h,hp,hg]
   have ht:= hill_init (filop_init (M:=B.cv) (Q:=B.tree) (H:=A.song) (τ:=τ) (show Same (dryE V E) V E from fun k hk=> if_pos hk) d) B.scale e he
   exact ht.trans (hill_init (filament_blip (h:=hz) V) _ e he)
lemma daylight (he:e≤E) : Needle.push (didn ν D' X i E) τ d (dryE V E) e = Needle.push (don ν D' X i) τ d V e := by
   apply push_foot (A:=didn ν D' X i E) (B:=don ν D' X i) he rfl rfl rfl
   intro j hj; funext r; unfold didn don; dsimp only; unfold awakening graving; rw [if_pos hj]
lemma dayCap (h:SnowFirm E τ V): Fits τ (dryE V E) ∧ ∀ i j,Tidy (dryE V E i j):= by
   constructor
   · intro i j hp
     unfold dryE at hp; split at hp; next ht=> exact (h.sector i ht j).2.2 hp
     exact (hp rfl).elim -- indent
   intro i j; unfold dryE; split; next ht=> exact (h.sector i ht j).1.toTidy
   exact Tidy.zero ..
end cutU
variable (he:Tights T S ν D' u)
include he
local notation "Ⓨ" => menu X
local notation "Δ" => chop X (1/4)
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Γ" => heights (u:=u) X ν D'
local notation "◆" => (zPlay X Ω ν D' H h hD)
local notation "◇" => (wPlay X Ω ν D' H h hD)
local notation "♣" => don ν D' X
lemma lane_here (hk:e≤E): Lease (menu X) (chop X (1/4)) (fun t:Wings u 1=> PowerSeries.coeff e (Γ t).scale) (fun t=> PowerSeries.coeff e (♣ t.i).scale):= by
  simp only [heights, dance,don,onward, afternoons,PowerSeries.coeff_expand,PowerSeries.coeff_mk]
  by_cases hh:2 ∣ e; swap
  · simp only [hh,↓reduceIte]; exact Lease.const ..
  simp only [hh,↓reduceIte]; apply Lease.mat; swap; exact sh X
  intro i hi; refine Lease.reforming (f:=fun i:Wings u 1=> Conductor.compass ν (lunar X ν D' i)) (g:=fun i=> Conductor.compass ν (granite X ν D' i.i)) (sh X) (k:=i) (fun j hj=> ?_) _ le_rfl
  by_cases hm : j=0; · subst j; simp only [compass_zero]; exact Lease.const ..
  simp only [Conductor.compass,hm,↓reduceIte]; exact cost_probe ν (fun _=>S.positive _) (graces he.hc he.hv he.hz he.hs (by omega) _) (he.hc.cup.transfer toLaunch)
-- limits of en tokens
lemma stampE (hk:e ≤ E) (n:ℕ)(hj:n≤windows τ E) r: Both (menu X) (chop X (1/4)) (fun i:Wings u 1=> Refrain (veiled (Γ i).cv) (Γ i).song none n e r) (fun i=>Refrain (veiled (♣ i.i).cv) (didn ν D' X i.i E).song none n e r) (fun i=>T.vi (X.J i.i)) := by
  have hs i:= Gets_awake (X.patch (i: Launch u).i) D' X.kernel ν (successor (i:Launch u) he.hc he.hv he.hz he.hs)
  let U i:= (Γ i).song; let V i:= (didn ν D' X (i:Wings u 1).i E).song
  have hv i : Gets (V i):= hs i.toLaunch
  refine crypt (F:=U) (H:=V) (sh X) he.operator.hs ((fun i=> le_trans (he.operator.ht i).le (bucks_v he.operator i))) (fun i=> ticket_pos Q _) (veil_contract (Summit.smooth he.hc he.hv) he.operator.hs) (fun i=>⟨(he.fair i).lived,(he.fair i).tune⟩) (fun i=>⟨(hv i).1,fun j k=>(hv i).2 j k |>.1⟩) (fun _=>none) (fun i=>le_trans ?_ (T.arcs _)) (fun j k hv=>?_)
  · exact smul_le_smul_of_nonneg_right (show funding e n ≤ funding E (windows τ E) by unfold funding; gcongr <;> omega) ((he.operator.ht _|>.le).trans (bucks_v he.operator _))
  obtain ⟨⟨hl,t',hr⟩,hu⟩:=hv
  have hF:j ≤ E:=by omega
  have hp:=Wings.bothUp he.hc (statues he.hc he.hv he.hz he.hs hF k)
  let v i:= ticketW Q (X.J (i:Wings u 1).i)
  let L i:= luggage ν (X.patch (i:Wings u 1).i) D' X.kernel j k
  have hz i: U i j k=L i-gemL _ (moon X ν D' i.up j k):= nuts _ (X.patch i.i) D' X.kernel j k -- binder
  have Hc i: V i j k=L i-gemL _ (statue X ν D' (i.i+1) j k):= by
    unfold V didn; dsimp only; rw [nuts ν (X.patch i.i) D' X.kernel,graving, if_pos hF]; rfl
  rw [show (fun i=> U i j k)=_ from funext hz,show (fun i=> V i j k)=_ from funext Hc]
  have hL: Voucher (menu X) 1 L v := by
    refine ⟨_,(he.hc.M.post j hF k (by omega)).transfer toLaunch,fun i=>?_⟩
    apply glow_less (tariff_yes ν _ _ _ _ _ (show v i≤1 from min_le_right ..)) le_rfl; simp only [Pi.one_apply,mul_one,le_refl]
  have H:= gem_accrue k (L:=fun t:Wings u 1=>(X.patch t.i).L) (F:=fun v=> moon X ν D' v.up j k) (H:=fun t=>statue X ν D' (t.i+1) j k) (v:=v) (σ:=fun t:Wings u 1=>Tier S (t.i+1)) (y:=menu X) (he.hc.M.crop.transfer toLaunch) (sh X) (fun _=>(ticket_pos Q _).le) (fun _=> min_le_right ..) (fun _=>(S.positive _).le) (fun i=>le_trans (smul_le_smul_of_nonneg_right (show k+1≤E+3 by omega) (ticket_pos Q _).le) (hire he.hc i)) hp
  exact (Both.self hL).sub H (sh X)
end YM.RG08.Door
