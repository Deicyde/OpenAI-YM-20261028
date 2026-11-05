import YM.WilsonBulk.Cash.Intakes

/-! # Atomic pressure recurrence before formal adjacent substitution

Absolute single and pair, distinct η Y height for ALL lower than input. Only same-rank old
masses carried under contraction. No pressure from constant sector. Strong demands include
ALL widths reached (θ flat limit supports launch outline). `tariff` witness of polynomial in contact height
for strict terms not in recurrence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n k e E d : ℕ} {σ μ θ η ζ x A M q δ : ℝ}
variable {P : Patch} {K : KernelChoices} {J : ChartRatio G} {T : Model P K} {l : G.ColorIndex}
variable {V U : Bed} {B Q B' Q' : Bed} {I I' : Library G} {D D' : Shaft P.L}
namespace Tarmac
variable (h : Tarmac l J T B Q D θ σ μ x q E A)
include h
lemma fervid : Lighthouse (beams G T B) := ⟨μ,h.warm.era.horizonM,A,h.warm.notzero,h.arise⟩
lemma claws (hg : Whisper I) (hy : BodyNull I) (hv : Within (lawn _) θ M (I e (n+1))) (hE : n+1 ≤ E+2) (hn : 1≤n)
    (hk : ∀ i:ℕ,0 < i → i≤e → i≤n → Within (lawn _) θ ζ (I (e-i) (n-i+1))) :
    Within (lawn _) σ (turbulent P σ θ q G n * M + strictWall A G e n * ζ) (lecture (install (beams G T B)) I e (n+1)) := by
  let p := h.warm.era
  exact climbing h.greet hg hy ⟨h.deep.1,fun i he=> h.deep.2 i (by unfold fitting at he; omega)⟩ h.fervid ⟨μ, p.horizonM,A,h.warm.notzero,h.corners⟩ (climbBill hE h.harbor_in le_rfl) (climbBill hE h.harbor_post le_rfl) (climbBill hE h.harbor_lamp le_rfl) p.output (p.lamp hE) p.input p.input_small p.hyper (p.high_use (by omega)) hv hk
lemma oil_savor (he : n ≤ E+1) (hv : Within (lawn (Cloth G)) θ M (I e (n+1))) : Within (lawn _) σ (A*A^n*M) (lecture (install (beams G T B)) I e (n+1)):= fare_const (delta_shape h.warm.era.output.le (le_trans h.warm.era.hyper (half_le_self h.warm.era.input.le))) (fun _=>climbBill (k:=n+1) (by omega) h.harbor_post le_rfl) hv
lemma minus_cast (he : Pamphlet I) (hf : Pamphlet I') (e n : ℕ) :
    lecture (install (beams G T B)) (I-I') e (n+1)=lecture (install (beams G T B)) I e (n+1)-lecture (install (beams G T B)) I' e (n+1) := lantern_sub (installMeet (K:=fun _ : Fin (n+1)=> (beams G T B)) (plaza fun _=>h.fervid)) (he e (n+1)) (hf e (n+1))
end Tarmac

def levy (G : Gauge) (E e n : ℕ) (A : ℝ) := A+strictWall A G e n*(A+A) +A*A^n*A +strictPay E e n A
def levyΔ (G : Gauge) (E e n : ℕ) (A : ℝ) := strictWall A G e n*A+ ((n+1:ℕ):ℝ)*(A*A^n*A) +strictPay E e n A
lemma tariffWall (G : Gauge) (e n : ℕ) : Tariff (fun x=>strictWall x G e n) := (Tariff.const _ (by positivity)).prod ((Tariff.one.prod (Tariff.one.powers _)).prod (Tariff.const _ (knee_nn ..))) -- structure * mul shape
lemma levy_formula (G : Gauge) (E e n : ℕ) : Tariff (levy G E e n) := ((Tariff.one.add ((tariffWall G e n).prod (Tariff.one.add Tariff.one))).add ((Tariff.one.prod (Tariff.one.powers _)).prod Tariff.one)).add (tariff_strict ..)
lemma difference_formula (G : Gauge) (E e n : ℕ) : Tariff (levyΔ G E e n) := (((tariffWall G e n).prod Tariff.one).add ((Tariff.const _ (by positivity)).prod ((Tariff.one.prod (Tariff.one.powers _)).prod Tariff.one))).add (tariff_strict ..)
variable (h : Tarmac l J T B Q D θ σ μ x q E A) (h' : Tarmac l J T B' Q' D' θ σ μ x q E A)
include h
lemma fee_levy (hs : G.Simple) (hV : Healthy l (upstream G) V) (he : Healthy l I B) (hn : n ≤ e+1) (hy : 1≤n) (hf : 0<e) (hE : e≤ E)
    (hp : Intake (lawn (Cloth G)) θ δ A I I e (n+1)) (hd : 0≤δ) (ht : turbulent P σ θ q G n ≤ 1) (hx : Within (lawn _) θ M (I e (n+1))) :
    Within (lawn _) σ (turbulent P σ θ q G n * M + levy G E e n A) (pressureI J T B Q I e (n+1)) := by
  obtain hp' := strict_cost h h hE hn (h.delta₀ hd) he.report.style he.report.style hp
  let u:=upstream G; let F:=install (beams G T B); let r:= h.warm.era
  have hu i (hi : i ≤ E) k (hk : k ≤ i+2): Within (lawn _) θ A (upstream G i k) := (h.warm.top i hi k hk).mono r.input_small le_rfl
  have hF : Within (lawn _) θ (M+A) ((I-u) e (n+1)) := hx.sub (hu _ hE _ (by omega))
  have hz (i : ℕ) (hi : 0 < i) (he : i ≤ e) (hj : i ≤ n) : Within (lawn _) θ (A+A) ((I-u) (e-i) (n-i+1)):= by
    refine (hp (e-i) (by omega) (n-i+1) (by omega) (by omega) (by omega)).plus.sub (hu _ (by omega) _ ?_); omega
  have hh := h.claws (he.report.minus hV.report) (Healthy.null l he hV hs) hF (by omega) hy hz
  have hk:= h.warm.notzero
  rw [garnish h he.report.palm hf]; rw [Tarmac.minus_cast h he.report.palm hV.report.palm e n] at hh -- Tarmac
  have hη:= (hh.add (h.oil_savor (by omega : n≤E+1) (hu e hE (n+1) (by omega)))).sub hp'.plus; rw [sub_add_cancel] at hη
  refine hη.mono le_rfl ?_; unfold levy; linarith only [mul_le_mul_of_nonneg_right ht hk]
include h' in
lemma fee_variation (hs : G.Simple) (hv : TollDelta G T B Q B' Q' σ μ E A δ) (he : Healthy l I B) (he' : Healthy l I' B')
    (hn : n≤e+1) (hy : 1≤n) (hf : 0<e) (hE : e≤E)
    (hp : Intake (lawn (Cloth G)) θ δ A I I' e (n+1)) (hI : Within (lawn _) θ A (I' e (n+1))) (hx : Within (lawn _) θ M ((I-I') e (n+1))) :
    Within (lawn _) σ (turbulent P σ θ q G n * M + δ*levyΔ G E e n A) ((pressureI J T B Q I - pressureI J T B' Q' I') e (n+1)) := by
  let r:= h.warm.era; let Y (V : Bed) (U : Library G):=lecture (install (beams G T V)) U e (n+1); let P₀ (B : Bed) (V : Library G):=strictMap T B J V e (n+1)
  obtain hp' := strict_cost h h' hE hn hv he.report.style he'.report.style hp
  have hz (i : ℕ) (hi : 0 < i) (he : i ≤ e) (hj : i≤ n) : Within (lawn _) θ (δ*A) ((I-I') (e-i) (n-i+1)):= (hp (e-i) (by omega) (n-i+1) (by omega) (by omega) (by omega)).variation
  have hh := h.claws (he.report.minus he'.report) (Healthy.null l he he' hs) hx (by omega) hy hz
  rw [Tarmac.minus_cast h he.report.palm he'.report.palm] at hh
  have hY : Within (lawn _) σ (((n+1:ℕ):ℝ)*(A*A^n*A*δ)) (Y B I'-Y B' I'):= tele_delta (delta_shape r.output.le (le_trans r.hyper (half_le_self r.input.le))) (fun _=>climbBill (k:=n+1) (by omega) h.harbor_post le_rfl) (fun _=> climbBill (k:=n+1) (by omega) h'.harbor_post le_rfl) (fun _=>climbBill (k:=n+1) (by omega) hv.stake le_rfl) hI r.output.le
  simp only [Pi.sub_apply,garnish h he.report.palm hf, garnish h' he'.report.palm hf]; unfold levyΔ
  change Within _ _ _ (Y B I - P₀ B I - (Y B' I' - P₀ B' I'))
  rw [show _ - (Y B' I'-_) = (Y B I-Y B I'+(Y B I'-Y B' I'))-(P₀ B I-P₀ B' I') from by abel] -- inference maybe wrong
  refine ((hh.add hY).sub hp'.variation).mono le_rfl ?_; apply Eq.le; ring
end Parapet
end YM.WilsonBulk
