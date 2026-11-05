import YM.RemainderComparison.Seasons.Harvest
/-! # Treasury Φ author on short stencil. Period circuits REAL n not taxed here.
 common polynomials and trunc rank selected BEFORE. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seasons
open Function Filter Set Lattice RG Tree Wilson Supply Input Org Shoot
open Push PriceCompiler Push.AbsoluteSums Gauge Pressure Testing SectorMeasure Precision
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Psalm Next.Scheduling AnalyticBridge VerifiedReset
open Extra.Iteration
open Height Roost
open ConnectedActivityE6
open Cadenza
open JointLoad.Heir.Suite
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {S:Sheet G} {K:MapPrices} {D : Rolls S} {R : Targets S K} {X : Expenses R}
variable {L:Side} {s f : ℝ→ℝ} (E:RG.Stage) {A₁ A y a b d e :ℝ}
open Hills Sienna Fare Lapis Lantern Meadow Song Collection Quotes Geo Herbal Uniform
local notation "c"=> E.clip
local notation "X'"=> E.paths
local notation "σ"=> E.width
local notation "Y"=> ConnectedActivityE6.loopBill G L
local notation "p"=> Time.probe E
local notation "M"=> Delay.fineMonitor G L
local notation "I" => (fun x=> betaF G x L)
local notation "P"=> E.supportExponent+3
variable (G L)
-- Compilation.Auth heights Merchant. Y program radius. uses ANY Poster. reserve tolerance L.K.Att actual α path.Level.P.
variable (t : Scrollwork G L)(n j:ℕ)
local notation "U"=> t.volume

def exHeat (G:Gauge)(L:Side)(D Mm A₁:ℝ)(n:ℕ)(s:ℝ):=
   let k:=(n+2)*n; let v:=Delay.fineMonitor G L s
   |Lantern.clump n (Germ.canopy n D 1 A₁+ Germ.canopy n 1 1 (A₁+1)) (Cadence.Glade.exAllowance n)| * ((1+Mm)^k * (1+Mm*(2*v)))
lemma spent (α:ℝ) (R:ℝ→ℝ) (hR:Reserve G L R): Reserve G L (fun x=> exHeat G L (Sienna.wick G L α x) (t.volume x) (R x) n x):=by
   have h₁:= (Reserve.const (G:=G) (L:=L) 1); have hp:= ((Germ.growthC n (Reserve.wig α) h₁ hR).add (Germ.growthC n h₁ h₁ (hR.add h₁))); have hv:= Reserve.covers t.votes; exact ((Reserve.comp n hp (Reserve.const (Cadence.Glade.exAllowance n))).absolute).mul (((h₁.add hv).pow _).mul (h₁.add (hv.mul ((Reserve.const _).mul Reserve.monitoring))))
variable (α V:ℝ) (D' : Quarry)
lemma ration : ∀ᶠ x:ℝ in atTop,0≤U x → Cadence.oxygen n D'.gap (U x) (Sienna.wick G L D'.d x) (D'.charge x) ≤ exHeat G L (Sienna.wick G L D'.d x) (U x) (D'.charge x) n x :=by
   let A:= D'.gap; let k := (n+2)*n; let f :ℝ:=Real.exp ((A/2)⁻¹*(k:ℝ)^2/2)
   obtain ⟨V,hV⟩:= Reserve.covers (Bolt.still (G:=G) (L:=L) f) -- but needed one
   have hv:= (Bolt.still (G:=G) (L:=L) f).listens zero_lt_one
   simp only [Real.rpow_one] at hv; filter_upwards [hv] with x hx ht
   have hh:f≤M x:= (le_abs_self _).trans hx
   unfold Cadence.oxygen Seasons.exHeat Germ.lump; apply mul_le_mul (le_abs_self _) _ _ (abs_nonneg _) <;> first | positivity | gcongr

def footing (X Mm:ℝ) :ℝ:= (X*(Fintype.card PlaqAxes:ℝ))* Quartz.stipend G σ X' c n Mm + Cadence.floral X σ Mm X' G n 3+Cadence.floral X σ Mm X' G n 4
local notation "M₁" Z:max=> outerCost G n Z
-- post variation of α & scalar fees. Does not depend on actual C choice.Press marks cutoff.
def summoner (d Z _:ℝ)(H:ℝ→ℝ)(x:ℝ) := -- remove unused arg ended.R heuristic unrelated
    let Z₁:= outerCost G n Z; let A:= footing G E n (t.siteBill x) Z₁
    |exHeat G L (Sienna.wick G L d x) (t.volume x) (H x) n x|+ (1+|α|)*|A| +|Cadence.floral (t.siteBill x) E.width Z₁ (ConnectedActivityE6.loopBill G L x) G n 2|
lemma accesses (H:ℝ→ℝ)(he:Reserve G L H)(R:ℝ) (d A:ℝ) : Reserve G L (summoner G L E t n α d A R H):=by
    let Z:= (M₁ A); let s:= t.siteBill; have hp:= t.sites_paid
    let v x:= footing G E n (s x) Z
    let hR (k) (F:ℝ→ℝ)(h:Reserve G L F): Reserve G L (fun x=> Cadence.floral (s x) E.width Z (F x) G n k) := hp.mul (h.mul (Reserve.const _))
    have hV:Reserve G L v := (((hp.mul (Reserve.const (Fintype.card PlaqAxes:ℝ))).mul (Reserve.const _)).add (hR 3 _ (Reserve.const X'))).add (hR 4 _ (Reserve.const X'))
    exact (((spent G L t n d H he).absolute).add ((Reserve.const _).mul hV.absolute)).add ((hR _ Y ((Reserve.const _).mul Reserve.monitoring)).absolute)
-- pose weights
local notation "Z!" => D'.Z
local notation "Zx"=> (M₁ (Z!)) -- notate nested
local notation "Zy" => t.siteBill
variable (z:Side) {A' γ:ℝ}
local notation "HK"=> footing G E n (Fintype.card (Site z)) Zx
structure Wellness (ι:ℝ) (x C:ℝ) : Prop where
   oxygen : 0 ≤ t.volume x→ Cadence.oxygen n D'.gap (t.volume x) (Sienna.wick G L D'.d x) (D'.charge x) ≤ C
   earns : ∀ z:Side, (Fintype.card (Site z):ℝ) ≤ t.siteBill x → 0≤ outerCost G n D'.Z →
      Seasons.footing G E n (Fintype.card (Site z)) (outerCost G n D'.Z) ≤ C ∧ ∀ (a W:ℝ), |a| ≤ ι →0 ≤ W→ W ≤ ConnectedActivityE6.loopBill G L x → ‖a‖*(Seasons.footing G E n (Fintype.card (Site z)) (outerCost G n D'.Z))+Cadence.floral (Fintype.card (Site z)) E.width (outerCost G n D'.Z) W G n 2 ≤ C
lemma coupled : ∀ᶠ x:ℝ in atTop, Wellness G L E t n D' α x (Seasons.summoner G L E t n α D'.d D'.Z 0 D'.charge x):=by
    filter_upwards [ration G L t n D'] with x hx; constructor
    · intro ht; unfold summoner; dsimp only; refine (hx ht).trans ((le_abs_self _).trans ((le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (abs_nonneg _))))
    intro z h hZ; have hk: 0 ≤Zy x:= (Nat.cast_nonneg _).trans h; have he:= E.paths_pos; have hu:= Quartz.decent G σ X' c n Zx
    have hp (k :ℕ):= Herbal.prizes_pos (G:=G) (j:=k) (k:=n) hZ E.width_pos
    have hX (k:ℕ)(v w:ℝ)(hv:0≤v)(ht:v ≤ w): 0 ≤Cadence.floral (Fintype.card (Site z)) σ Zx v G n k ∧ Cadence.floral (Fintype.card (Site z)) σ Zx v G n k ≤ Cadence.floral (t.siteBill x) σ Zx w G n k:= by
        unfold Cadence.floral; have H:0≤(1+prize n k G σ (outerCost G n D'.Z)):= by have:= hp k; positivity
        have hK:=hv.trans ht; constructor; positivity; gcongr
    have h0:0 ≤ Seasons.footing G E n (Fintype.card (Site z)) Zx:= add_nonneg (add_nonneg (mul_nonneg (by positivity) hu) (hX 3 _ _ he.le le_rfl).1) (hX 4 _ _ he.le le_rfl).1
    have ht: Seasons.footing G E n (Fintype.card (Site z)) Zx≤ |Seasons.footing G E n (t.siteBill x) Zx|:= by
        refine le_trans ?_ (le_abs_self _); exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) hu) (hX _ _ _ he.le le_rfl).2) (hX _ _ _ he.le le_rfl).2 -- gcongr hp
    have hr:0 ≤ 1+|α|:= by positivity
    unfold summoner; dsimp only []; constructor
    · refine ht.trans ((le_mul_of_one_le_left (abs_nonneg _) (show 1 ≤ 1+|α| from le_add_of_nonneg_right (by positivity))).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))))
    intro a W ha hh hw
    exact add_le_add ((mul_le_mul (ha.trans (le_abs_self α)|>.trans (le_add_of_nonneg_left zero_le_one)) ht h0 hr).trans (le_add_of_nonneg_left (abs_nonneg _))) (((hX _ _ _ hh hw).2).trans (le_abs_self _))
end YM.RemainderComparison.Seasons
