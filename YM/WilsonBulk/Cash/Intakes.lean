import YM.WilsonBulk.Cash.Patience

/-! Balance sheet for strict calls and exact fluct charge-∞. Tariff(f) not contour; positivity on x≥0 even dummy lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Equiv Filter Pert.Bulk Finset Bloch Lattice Laurent
variable {X Y : Type} {D : Rule X} {Q : Rule Y} {T d : Duct X Y} {σ θ A q u v δ x : ℝ} {n : ℕ}
variable {P P' : Page X (n+1)}
lemma Options.lectured_fixed (h : Options D θ δ A P P') (he : Geometry D Q θ σ d)
    (ht : AuditLine T d (n+1) u v) (hs : 0 ≤ σ) : Options Q σ δ (v*u^n*A) (travel T P) (travel T P') := by
  refine ⟨h.nonneg,fare_const he (fun _=>ht) h.plus,fare_const he (fun _=>ht) h.minus,?_⟩
  rw [travel,travel,← tele_sub he (fun _=> ht) h.plus h.minus hs]
  rw [show δ*(v*u^n*A)=v*u^n*(δ*A) by ring]; exact fare_const he (fun _=>ht) h.variation
end Sheet
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {X Y : Type} {n k e E d : ℕ} {σ μ θ η ζ x A M q δ : ℝ}
variable {P : Patch} {K : KernelChoices} {J : ChartRatio G} {T : Model P K} {l : G.ColorIndex}
variable {V U : Bed} {B Q B' Q' : Bed} {I I' : Library G} {D D' : Shaft P.L}

def oilWanted (E : ℕ) (x : ℝ) := x*x^(E+2)*x
def primPrice (E : ℕ) (x : ℝ) := oilWanted E x+x
def podiumPrice (E : ℕ) (x : ℝ) := primPrice E x+oilWanted E x
def condPrice (E e k : ℕ) (x : ℝ) := primPrice E x+recovery e k (podiumPrice E x)
def strictPay (E e n : ℕ) (x : ℝ) := ((n+2:ℕ):ℝ)*(x*x^n*condPrice E e (n+1) x)
lemma oil_tariff (E : ℕ) : Tariff (oilWanted E) := (Tariff.one.prod (Tariff.one.powers _)).prod Tariff.one
lemma tariff_prim (E) : Tariff (primPrice E) := (oil_tariff E).add Tariff.one
lemma tariff_port (E) : Tariff (podiumPrice E):=(tariff_prim E).add (oil_tariff E)
lemma tariff_cond (E e k) : Tariff (condPrice E e k):= (tariff_prim E).add ((tariff_recovery e k).composed (tariff_port E))
lemma tariff_strict (E e n) : Tariff (strictPay E e n):= (Tariff.const _ (by positivity)).prod ((Tariff.one.prod (Tariff.one.powers n)).prod (tariff_cond E e (n+1)))
namespace Warm
variable (h : Warm P K J θ σ μ x E A)
include h
lemma notzero : 0≤A := zero_le_one.trans h.height
lemma oil_post {V : Text (Cloth G) (n+1)} (hp : Within (lawn _) θ A V) (hn : n≤E+1) : Within (lawn (Echelon (Cloth G) (Cloth G) P.L)) μ (oilWanted E A) (Sheet.travel (oil G P) V) := by
  have hx:= h.height
  refine (fare_const (delta_shape h.era.horizonM.le h.era.width_in) (fun _=> climbBill (k:=n+1) (by omega) h.epoch le_rfl) hp).mono le_rfl ?_
  unfold oilWanted; gcongr; linarith -- maybe no goals
lemma primer_cost (he : e≤E) (hk : n≤e+1) : Within (lawn _) μ (primPrice E A) (primer P K J e (n+1)) := by
  exact (oil_post h ((h.hair e he (n+1) (by omega)).mono h.era.input_small le_rfl) (by omega)).sub (h.crown e he (n+1) (by omega))
lemma warning (he : Intake (lawn (Cloth G)) θ δ A I I' e (n+1)) (hE : e ≤ E) (hr : 0≤δ) : Intake (lawn _) μ δ (podiumPrice E A) (dais J P K I) (dais J P K I') e (n+1) := by
  intro i hv k hk hh hf; cases k with
  | zero=> omega
  | succ k=>
    apply (Options.self (primer_cost h (by omega : i≤E) (by omega : k ≤ i+1)) hr).sub
    have hp : Options (lawn _) θ δ A (later I i (k+1)) (later I' i (k+1)):= by unfold later switchBoard; split; exact he i hv _ hk hh hf; exact Options.zero h.notzero hr
    have ht:= h.height
    refine (hp.lectured_fixed (delta_shape h.era.horizonM.le h.era.width_in) (climbBill (by omega) h.epoch le_rfl) h.era.horizonM.le).more le_rfl ?_ le_rfl
    unfold oilWanted; gcongr; omega
end Warm
variable (h : Tarmac l J T B Q D θ σ μ x q E A) (hv : Tarmac l J T B' Q' D' θ σ μ x q E A)
include h hv
lemma onCoat (hf : e ≤ E) (hn : n≤ e+1) (hs : TollDelta G T B Q B' Q' σ μ E A δ) (he : Document I) (hp : Document I')
    (hk : Intake (lawn (Cloth G)) θ δ A I I' e (n+1)) :
    Options (lawn _) σ δ (condPrice E e (n+1) A) (coat T B J I e (n+1)) (coat T B' J I' e (n+1)) := by
  let μ' := podiumPrice E A; have hα : A≤μ':= by
    have ht := (oil_tariff E).1 A h.warm.notzero; unfold μ' podiumPrice primPrice; linarith
  have hy : Options (lawn _) μ δ μ' (comfort (G:=G) T B) (comfort (G:=G) T B') := (show Options _ μ δ A _ _ from ⟨hs.nonneg,h.cargo_in,hv.cargo_in,hs.shift_in⟩).more le_rfl hα le_rfl
  exact (Options.self ((h.warm.primer_cost hf hn).mono h.warm.era.bill le_rfl) hs.nonneg).add ((strict_heat (Warm.warning h.warm hk hf hs.nonneg) hy h.warm.era.horizonM.le (podium_free J _ _ _) (podium_free J _ _ _) (podium_style J P K he).cap (podium_style J P K hp).cap (by omega)).more le_rfl le_rfl (h.warm.era.windows e hf)) -- align μ
lemma strict_cost (hf : e ≤ E) (hn : n≤ e+1) (hs : TollDelta G T B Q B' Q' σ μ E A δ) (he : Document I) (hp : Document I')
    (hk : Intake (lawn (Cloth G)) θ δ A I I' e (n+1)) :
    Options (lawn _) σ δ (strictPay E e n A) (strictMap T B J I e (n+1)) (strictMap T B' J I' e (n+1)) :=
    options_tele (delta_shape h.warm.era.output.le (show σ /(1:Side).val ≤ σ from div_le_self h.warm.era.output.le (by norm_num))) (fun _=> climbBill (k:=n+1) (by omega) h.pot le_rfl) (fun _=> climbBill (k:=n+1) (by omega) hv.pot le_rfl) (fun _=> climbBill (by omega) hs.lake le_rfl) (onCoat h hv hf hn hs he hp hk) h.warm.era.output.le
end Parapet
end YM.WilsonBulk
