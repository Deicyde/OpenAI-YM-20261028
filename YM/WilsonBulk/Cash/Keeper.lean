import YM.WilsonBulk.Cash.Ferries

/-!
# One-step engine closure for unmarked press and reset representatives. Δ-estimates.
Preconditioned for each positive-order and rank. Exact Tariff independent of step type.
No shrink in Strip pay even with Φ-projection. Must admit widths before block.

Caller supplies Caps on same mesh for previous (e,*) of unreset Pressure (or rather
Rest; at same power not needed). This avoids any demand-expansion over predecessors:
strict heat/coasts INTERNAL; after one step target SAME width for every pressure object.
Use `currency` allowing `cut_i` when its power <2 (non-parity default harmless).
All estimated at actual expansion parameter with REAL canonical basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent Recall PowerSeries
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {P : Patch} {K : KernelChoices} {n k e E d i : ℕ} {σ θ μ η ζ x A M q y p s T δ : ℝ}
variable {J : ChartRatio G} {F : Model P K} {l : G.ColorIndex} {B Q B' Q' : Bed} {I I' : Library G}
variable {D D' : Shaft P.L}

abbrev Rest (σ δ A : ℝ) (e : ℕ) (I I' : Library G) := ∀ i:ℕ,i < e→ ∀ n,Options (lawn _) σ δ A (I i n) (I' i n)
abbrev press (J : ChartRatio G) (F : Model P K) (B Q : Bed) := pressureI J F B Q
def hopPrice (e n : ℕ) (A : ℝ) := (1+A*A)*newOrder e (n+1) A
-- multiplier-variation projector may pay A³? receipt δ? calculate explicit

def hopDiff (e n : ℕ) (A : ℝ) := hopPrice e n A + A*(A+newOrder e (n+1) A)*A
lemma hops_tag (e n : ℕ) : Tariff (hopPrice e n) := ((Tariff.const _ zero_le_one).add (Tariff.one.prod Tariff.one)).prod (price_order e (n+1))
lemma hopsΔ_tag (e n : ℕ) : Tariff (hopDiff e n) := (hops_tag ..).add ((Tariff.one.prod (Tariff.one.add (price_order e (n+1)))).prod Tariff.one)
namespace Tarmac
variable (h : Tarmac l J F B Q D θ σ μ x q E A) (h' : Tarmac l J F B' Q' D' θ σ μ x q E A)
include h
set_option linter.unusedSectionVars false in
lemma awake (hI : Document I) : Crest (press J F B Q I) Q:= funext fun _=>press_lead _ _ _ _ I hI _
lemma aware (hI : Healthy l I B) : Whisper (press J F B Q I):= whispers_post h.h hI.report hI.crests
lemma anchors_here (hI : Document I) : constantCoeff (revenue l (press J F B Q I))=1:= revenue_anchor l (h.awake hI) h.hUnit
lemma reflectPrice : reflector σ x ≤ 1+A*A:= by
  unfold reflector; exact add_le_add_right (mul_le_mul h.warm.coin h.warm.ruby h.summit_home.1 h.warm.notzero) _
lemma reflectPositive : 1 ≤ reflector σ x := reflector_large h.warm.era.output.le h.summit_home.1
include h' in
lemma hopping (hI : Healthy l I B) (hh : Healthy l I' B') (hp : 0≤ δ) (he : Rest σ δ A e (press J F B Q I) (press J F B' Q' I')) :
    Options (lawn _) σ δ (newOrder e n A) (cutReset l (press J F B Q I) e n) (cutReset l (press J F B' Q' I') e n):=
  currency (h.anchors_here hI.report.style) (h'.anchors_here hh.report.style) (moments_book l (fun i hi=> he i hi 2) (h.aware hI).palm (h'.aware hh).palm h.warm.era.output h.warm.notzero hp h.warm.coin) (fun _ _ hi=> he _ hi n)
lemma hop (he : Healthy l I B) (hd : 0≤δ) (hf : 0<e) (hk : Rest σ δ A e (press J F B Q I) (press J F B Q I))
    (hC : Within (lawn _) σ M (press J F B Q I e (n+1))) :
    Within (lawn _) σ (reflector σ x*M+hopPrice e n A) (resetI l (press J F B Q I) e (n+1)) := by
  let R:=press J F B Q I; let x₀ := reflector σ x; have hx:=price_order e (n+1)|>.1 A h.warm.notzero
  have hj: Within (lawn _) σ (M+newOrder e (n+1) A) (patchReset l R e (n+1)):= hC.add (hopping (n:=n+1) h h he he hd hk).plus
  by_cases H:n=1; swap
  · rw [rate_reset (h.awake he.report.style) h.hUnit hf (by omega)]; apply hj.mono le_rfl
    exact add_le_add (le_mul_of_one_le_left hC.1 h.reflectPositive) (le_mul_of_one_le_left hx (le_add_of_nonneg_right (mul_self_nonneg A)))
  subst n; rw [rate_quad (h.aware he) (h.awake he.report.style) h.hUnit hf]; refine (mirror_cost hj h.summit_home h.warm.era.output _).mono le_rfl ?_ -- syntactic
  rw [hopPrice,mul_add]; exact add_le_add_right (mul_le_mul_of_nonneg_right h.reflectPrice hx) _
include h' in
lemma hop_delta (he : Healthy l I B) (hh : Healthy l I' B') (ht : TollDelta G F B Q B' Q' σ μ E A δ) (hf : 0 < e) (hk : Rest σ δ A e (press J F B Q I) (press J F B' Q' I'))
    (h'V : Within (lawn _) σ A (press J F B' Q' I' e (n+1)))
    (hC : Within (lawn _) σ M ((press J F B Q I-press J F B' Q' I') e (n+1))) :
    Within (lawn _) σ (reflector σ x*M+δ*hopDiff e n A) ((resetI l (press J F B Q I)-resetI l (press J F B' Q' I')) e (n+1)) := by
  let U:=press J F B Q I; let V:=press J F B' Q' I'; let d:=newOrder e (n+1) A;
  let x₀ :=patchReset l U e (n+1); let x' :=patchReset l V e (n+1)
  have hp:=hopping (n:=n+1) h h' he hh ht.nonneg hk; have hc : Within (lawn _) σ (A+d) x' := h'V.add hp.minus
  have hr : Within (lawn _) σ (M+δ*d) (x₀-x'):= by unfold x₀ x' patchReset; rw [add_sub_add_comm]; exact hC.add hp.variation
  simp only [Pi.sub_apply]; have hv := h.warm.notzero; have hu := hp.baseline; have hb := ht.nonneg
  by_cases hn : n=1; swap
  · rw [rate_reset (h.awake he.report.style) h.hUnit hf (by omega),rate_reset (h'.awake hh.report.style) h'.hUnit hf (by omega)]; apply hr.mono le_rfl
    refine add_le_add (le_mul_of_one_le_left hC.1 h.reflectPositive) (mul_le_mul_of_nonneg_left ?_ ht.nonneg)
    unfold d hopDiff; refine le_trans (b:=hopPrice e n A) (le_mul_of_one_le_left hu (le_add_of_nonneg_right (mul_self_nonneg A))) (le_add_of_nonneg_right ?_); positivity
  subst n; rw [rate_quad (h.aware he) (h.awake he.report.style) h.hUnit hf, rate_quad (h'.aware hh) (h'.awake hh.report.style) h'.hUnit hf]
  refine (mirror_difference hc hr h.summit_home ht.ahead (smooth_patch (h'.aware hh).palm l _ _) (smooth_patch (h.aware he).palm l _ _) h.warm.era.output l).mono le_rfl ?_
  unfold d; unfold hopDiff hopPrice; -- RHS expanded, δ≥0 etc
  calc _ ≤ (1+0)*reflector σ x*M +(1+A*A)*(δ*newOrder e 2 A)+ A*(A+newOrder e 2 A)*(δ*A) := by
        rw [mul_add (reflector σ x),add_zero,one_mul]; refine add_le_add (add_le_add_right (mul_le_mul_of_nonneg_right h.reflectPrice (mul_nonneg hb hu)) _) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.warm.coin (add_nonneg hv hu)) (mul_nonneg hb hv))
       _ = _ := by ring
end Tarmac
end Parapet
end YM.WilsonBulk
