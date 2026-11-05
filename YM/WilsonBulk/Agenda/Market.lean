import YM.WilsonBulk.Agenda.Winter

/-!
# Spell Tarmac and Finance issuance from quantitative purchases on geometry; no additional kernel hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {F : MapPrices} {i j k n m ℓ N N' E : ℕ} {x a b p σ θ μ w C t δ α : ℝ} {L : Side}
variable {J : ChartRatio G} {T : historyModel A i} {S : Lit G A.clock.kernel F}
variable {X Y : Bed} {l : G.ColorIndex}
namespace Charges
set_option quotPrecheck false
local notation "U" => stage A i
local notation "V" => stage A (i+1)
local notation "PatchX" => historyPatch A i

lemma stout (S : Lit G A.clock.kernel F) (h : H.Suffices F) (hi : i < N) (hf : 5 ≤ V) :
    Heights (preGate G (H.towers N i).A0) 3 (S.gamma V) (F.Ω V) := by
  have he:= permDeep (d:=3) h hi hf; exact ⟨he.1,fun l hl=> strip_mono (he.2 l hl) ((S.awake V).trans (min_le_left ..)) le_rfl⟩
lemma bandwidth {σ x : ℝ} {X Y : Type} {L : Side} {R : Cross L X Y} (h : Heights R n σ x) : R.strip σ |x| := by
  have hz : R.strip σ (x/L.val):= by simpa [advanceC] using h.2 [] (by simp)
  exact strip_mono hz le_rfl ((div_le_self h.1 (by exact_mod_cast L.property)).trans (le_abs_self ..)) -- indent
-- use geometry earlier receipts. independent w cost
lemma charge_kin (he : Charge S T J U E C) (h : LocalRatio J) (hs : H.Suffices F) (hi : i < N) (hk : 5 ≤ V) (l : G.ColorIndex) :
    Tarmac l J T (H.H N (i+1)) (H.H N i) (H.towers N i).A0 (S.width E V) (S.width E U) (S.gamma V) (SeenRank F G U) (F.Ω V) E C := by
  obtain ⟨w,hW⟩:= he; let R:=(H.towers N i).A0; let B:=H.H N (i+1); let X := S.width E V; let Y:= S.width E U; let Z:= S.gamma V
  have hw := hW.poles A H hs _ N hi rfl; have hg :=hW.warm.era; let f:=beam_cap PatchX G A.clock.kernel w; let g:=lanternFull PatchX G w (F.Ω V)
  have h₀ : 0≤w:= zero_le_one.trans hW.lamp; have hz:=stout S hs hi hk; have hC := bandwidth hz
  have hB : (beams G T B).strip Z f:= YM.WilsonBulk.charge T B hg.horizonM.le hw.width hW.spark
  have hA : (lanternPhi G T R).strip Z g:= perch_cost (strip_compose hg.horizonM.le hW.react hC)
  obtain ⟨Ha,HA,Hb,BH,BP,Hm⟩:= hW.tickets; obtain ⟨τ,τ',Hτ,HV,Hw⟩:= hW.costs_turn
  have h' := Passage.actual hs hi T h
  refine ⟨hW.warm,h', price_at_horizon hs hi.le l, hw.lower le_rfl Ha, strip_mono hB le_rfl BH, strip_mono hA le_rfl BP,
    lamp_court (P:=PatchX) R T cascade_up h' hw hg.horizonM.le hC (fun c=> (AnalyticNext.QuarticMatch.Mint.visit hs hi c).2), hz,
    climbBill le_rfl (goByLane (P:=PatchX) hg.output.le hg.bill hg.analytic hC (abs_nonneg (F.Ω V))) τ,
    climbBill le_rfl (goByLane (P:=PatchX) hg.output.le hg.bill hg.analytic hB (beam_nn h₀)) τ', climbBill le_rfl (goByLane (P:=PatchX) hg.output.le hg.bill hg.analytic hA (lantern_nn h₀)) Hτ,
    climbBill le_rfl (hoodRun hg.output.le hg.bill hg.analytic (effer_cost _ hB) (zero_le_one.trans (le_max_right ..))) HV,
    (lawn_pair (corridor_height hw.width h₀) h₀).mono le_rfl Hw, (onTop_cost G (canonical_strip hs hi.le)).mono (((S.lighter E U).2.trans (min_le_right ..)).trans (min_le_left ..)) le_rfl⟩

lemma boost (h : 0 ≤ δ) (hf : 0 ≤ t) (he : a*b≤C) : a*(b*(δ*t)) ≤ C*t*δ := by rw [mul_comm δ,← mul_assoc, mul_assoc C]; exact mul_le_mul_of_nonneg_right he (by positivity)
-- Width charge on BOTH actionKernel slots: Qout with spacecraft σ V, Qin to γ stage. From MUCH smaller thermal covariance width pre stage.
lemma turnstile (h : H.Suffices F) (hs : Charge S T J U E C) (hv : 0≤t) (hx : 0≤δ) (h₁ : i<N) (h₂ : i<N')
    (hb : (minusRows (flat H N (i+1)) (flat H N' (i+1))).strip (S.gamma V) (δ*t))
    (ha : (minusRows (flat H N i) (flat H N' i)).strip (S.width E U) (δ*t)) :
    TollDelta G T (H.H N (i+1)) (H.H N i) (H.H N' (i+1)) (H.H N' i) (S.width E U) (S.gamma V) E (C*t) δ := by
  let B:= H.H N (i+1); let Y:=H.H N' (i+1); let X:=beams G T B; let Z:=beams G T Y
  obtain ⟨w,hw⟩:= hs; have he:= hw.warm.era; have hp : 0 ≤ w:= zero_le_one.trans hw.lamp; have hc:= hw.poles A H h _ _ h₁ rfl; have hz:=hw.poles A H h _ _ h₂ rfl
  let f:=greenFace PatchX G w; let g:=greenTurn PatchX G A.clock.kernel w; let v:=δ*t; let σ:=S.width E U; let η:=S.gamma V
  have hh: 0 ≤ f*v:=mul_nonneg (green_nn hp) (mul_nonneg hx hv); have hE: 0 ≤ g*v:=mul_nonneg (turn_nn hp) (mul_nonneg hx hv)
  have hU : (minusRows (fluct G T B) (fluct G T Y)).strip η (f*v) := by convert! glimpse H h hc hz he.horizonM.le (mul_nonneg hx hv) h₁ h₂ hb using 1; unfold v f greenFace; rw [show harborsN PatchX G=(Fintype.card (Co (A.S.block i) (Loc G 1)):ℝ) from rfl]; ring -- harborsN defeq? P simplifies
  have hV : (minusRows X Z).strip η (g*v) := by apply strip_mono (beam_bill hc hz he.horizonM.le hU hw.spark) le_rfl (Eq.le ?_); unfold g greenTurn f; ring
  obtain ⟨hF,hS,hL,hM,hG,HR⟩:= hw.pricing
  have hu : install X-install Z=install (minusRows X Z):=rfl
  have hC : plain (pilot (G:=G) T B)-plain (pilot (G:=G) T Y)=plain (minusRows (efferos X) (efferos Z)):=rfl
  have ht : comfort (G:=G) T B-comfort (G:=G) T Y=pair (plain (minusRows (cargo (G:=G) T B) (cargo (G:=G) T Y))):=rfl
  refine ⟨hx,strip_mono hU le_rfl ?_,strip_mono hV le_rfl ?_,?_,?_,?_,?_⟩
  · convert! boost (a:=1) (b:=f) hx hv ((one_mul _).trans_le hF) using 1; ring
  · convert! boost (a:=1) (b:=g) hx hv ((one_mul _).trans_le hS) using 1; ring
  · change AuditLine (install X-install Z) _ _ _ _; rw [hu]; exact climbBill le_rfl (goByLane (P:=PatchX) he.output.le he.bill he.analytic hV hE) (boost hx hv hL)
  · change AuditLine (plain _-plain (pilot (G:=G) T Y)) _ _ _ _; rw [hC]; exact climbBill le_rfl (hoodRun he.output.le he.bill he.analytic (effer_delta X Z hV hE) hE) (boost hx hv hM)
  · change Within _ _ _ (comfort (G:=G) T B-comfort (G:=G) T Y); rw [ht]; apply (lawn_pair (corridor_strip hU hh) hh).mono le_rfl; rw [mul_comm δ]; exact boost hx hv hG
  apply (onTop_delta (G:=G) _ _ ha).mono le_rfl; rw [show oxidize G (δ*t)= oxidize G 1*(1*(δ*t)) from by unfold oxidize; ring, mul_comm δ (C*t)]; exact boost hx hv ((mul_one _).trans_le HR)

end Charges
end YM.WilsonBulk.Parapet.Agenda
