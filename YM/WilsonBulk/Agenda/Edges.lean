import YM.WilsonBulk.Agenda.Sky

/-!
# Prices charged after Lighting goals. All numerical purchases at neighbor step; Warm jets real at flat deterministic cells.
No algebraic pressure budgets smuggled in construction. Native Wit roots. policy possibly choosing tree nonoptimally but charge after. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {A : Type} {G : Gauge} {K : KernelChoices} {F : MapPrices} {P : Patch} {i j k n E : ℕ} {x a p σ θ μ : ℝ} {L : Side}
variable {X Y : Type} {J : ChartRatio G}

abbrev kinds (X : Type) [Fintype X] := (Fintype.card X:ℝ)
def lane (P : Patch) (X Y : Type) [Fintype X] [Fintype Y] (σ : ℝ) (n : ℕ) := kinds Y*Real.exp (4*σ) + kinds X * ((P.L.val:ℝ)^4 * Real.exp (4*(n*σ)))
def hood (X Y : Type) [Fintype X] [Fintype Y] := kinds Y + kinds X
lemma lane_nn [Fintype X] [Fintype Y] : 0 ≤ lane P X Y σ n:= by unfold lane; positivity
lemma hood_nn [Fintype X] [Fintype Y] : 0 ≤ hood X Y:= by unfold hood; positivity
lemma goByLane [Fintype X] [Fintype Y] {F : Cross P.L X Y} (h : 0≤ σ) (he : σ ≤ μ) (hp : n*σ≤μ) (hx : F.strip μ x) (hf : 0≤ x) :
    AuditLine (Pert.Bulk.install F) (spotCost P.L σ) n (lane P X Y σ n*x) (lane P X Y σ n*x):= by
  let A:=Real.exp (4*σ); let B:=Real.exp (4*(n*σ)); apply climbCost (install_audited hx hf h he hp); unfold lane kinds; rw [add_mul,mul_assoc]; exact le_add_of_nonneg_right (by positivity)
  unfold lane kinds; rw [add_mul, mul_assoc (Fintype.card X:ℝ) _ _,mul_assoc _ (Real.exp _ : ℝ) x]; -- inspect
  simp_rw [mul_assoc]
  exact le_add_of_nonneg_left (by positivity)
lemma hoodRun [Fintype X] [Fintype Y] {F : Row X Y} (h : 0≤σ) (he : σ≤μ) (hp : n*σ≤μ) (hx : F.strip μ x) (hf : 0≤x) : AuditLine (plain F) (spotCost 1 σ) n (hood X Y*x) (hood X Y*x):= by
  apply climbCost (plain_audited h hx hf he hp)
  · unfold hood; rw [add_mul]; exact le_add_of_nonneg_right (by positivity)
  unfold hood; rw [add_mul]; exact le_add_of_nonneg_left (by positivity)
lemma Forecast_beds (V : Record (Market X)) (e : ℕ) (σ : ℝ) (h : ∀ i n,∃ p,Within (lawn X) σ p (V i n)): ∀ᶠ C:ℝ in atTop,Beds σ e C V:= by
  have hf (i n : ℕ) : ∀ᶠ C:ℝ in atTop,Within (lawn X) σ C (V i n) := by obtain ⟨p,hp⟩:= h i n; exact (eventually_ge_atTop p).mono fun q h=> hp.mono le_rfl h
  have hx : ∀ᶠ C:ℝ in atTop,∀ i:Fin (e+1),∀ n:Fin (e+3),Within (lawn X) σ C (V i n) := eventually_all.mpr (fun i=> eventually_all.mpr fun n=> hf i n)
  exact hx.mono (fun i hi j hj n hn=> hi ⟨j,by omega⟩ ⟨n,by omega⟩)
lemma Forecast_stems [Fintype X] (p : ℕ) (T : X→ Market Y) (F : Tabletop X→ℝ) (e : ℕ) (σ : ℝ) : ∀ᶠ C:ℝ in atTop,Beds σ e C (chapters p T F):= Forecast_beds _ _ _ (fun i n=> ⟨_,chapters_money p T F i n σ⟩)
lemma beds_later (V : Record (Market X)) (hp : Beds μ E x V) (h : 0≤x) : Beds μ E x (later V) := by intro i h n hn; unfold later switchBoard; split; exact hp _ h _ hn; apply Within.zero; assumption
lemma warm_eventually (P : Patch) (K : KernelChoices) (J : ChartRatio G) (r : ℝ) (h : Season P.L θ σ μ E) : ∀ᶠ C:ℝ in atTop,Warm P K J θ σ μ r E C := by
  let φ:ℝ:= max μ (((E+2:ℕ):ℝ)*μ); have hx:= goByLane (X:=Cloth G) (P:=P) (F:=varnish P.L _ (Cloth G)) h.horizonM.le (le_max_left μ (((E+2:ℕ):ℝ)*μ)) (le_max_right ..) (varnish_cost _ _) zero_le_one
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop r,eventually_ge_atTop (momentWeight σ 2),eventually_ge_atTop (lane P (Cloth G) (Echelon (Cloth G) (Cloth G) P.L) μ (E+2)*1), Forecast_stems 0 (swipe G) (tariffJ J) E 1, Forecast_stems 2 (stake P G) (splatter P G K.penalty) E μ, Forecast_stems 2 (hedgerow G) (progressStub G) E 1] with x hp he hm hn hH hN hT
  exact ⟨h,hp,climbBill le_rfl hx hn,hT,beds_later _ hH (by linarith),beds_later _ hN (by linarith),hm,he⟩

-- Card metrics at allotted width (post charges). W always ≥1 when live. Heights
abbrev harborsN (P : Patch) (G : Gauge):= kinds (Co P.L (Loc G 1))
abbrev guidesN (P : Patch) (G : Gauge):= kinds (Echelon (Cloth G) (Cloth G) P.L)
def beam_cap (P : Patch) (G : Gauge) (K : KernelChoices) (w : ℝ) := ‖K.penalty‖*(harborsN P G*(w*w))
def greenFace (P : Patch) (G : Gauge) (w : ℝ) := (harborsN P G*harborsN P G*(kinds PotentialForm))*w*w
-- Lips factors multiply by both Kdelta & heated δ

def greenTurn (P : Patch) (G : Gauge) (K : KernelChoices) (w : ℝ) := ‖K.penalty‖*(harborsN P G*(greenFace P G w * w))
def lanternFull (P : Patch) (G : Gauge) (C x : ℝ) := harborsN P G * (C*|x|)
lemma beam_nn {w:ℝ} (h : 0≤w) : 0 ≤ beam_cap P G K w:= by unfold beam_cap; positivity
lemma green_nn {w:ℝ} (h : 0≤w) : 0 ≤ greenFace P G w:= by unfold greenFace; positivity
lemma turn_nn {w:ℝ} (h : 0≤w): 0 ≤ greenTurn P G K w:= by unfold greenTurn; have he:= green_nn (P:=P) (G:=G) h; positivity
lemma lantern_nn {w x:ℝ} (h : 0 ≤ w) : 0 ≤ lanternFull P G w x := by unfold lanternFull; positivity
end YM.WilsonBulk.Parapet.Agenda
