import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Fresco

/-!
# One pre/post service and two pressures compared

All actual period demands; extrapolation after L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Paintings
open Gauge Filter Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice RG Tree Matrix Finset Precision Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch
    Extra.Iteration Extra.Iteration.Calibration
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} (F T : Forest S.ratio) (t r : S.Choices) {μ B Λ η : ℝ}
    {p : Clip} {R : PathData G} {O : ChartRatio G} {u : In G c → AxisChart G F} {v : In G c→AxisChart G T}
    (ho : LocalRatio O) (hu : Critical F p R u) (hv : Critical T p R v)
    (h : R.Bounds p μ B Λ) (hK : S.patch.Branches S.kernel G)
include t r T F hK h hu hv ho
open Work.F05
lemma leaves (hη : 0<η) (hP : PriceGap T p R η) : determinant F t R p u O=ᶠ[𝓝 0] determinant T r R p v O := by
  have hx := (tag_thermal hK hu O t r).trans (same_thermal hK h hu hv hη hP ho r)
  filter_upwards [hx,graph_switch hK h hu hv hη hP r,(crit_home hu).eventually (loop_switch F T h)] with x ht he hh
  change Precision.loop R (lifting F (represent x) (u x))=Precision.loop R (lifting T (represent x) (switch F T x (u x))) at hh; rw [he] at hh
  simp only [thermal] at ht; unfold determinant; rw [hh] at ht; linarith
lemma leaves' (hη : 0<η) (hP : PriceGap T p R η) (x y : Positions (Primary c G)) :
    iteratedFDeriv ℝ 2 (determinant F t R p u O ∘ tint G _) 0 ![x,y] =
      iteratedFDeriv ℝ 2 (determinant T r R p v O ∘ tint G _) 0 ![x,y] := by
  let P := tint G (Body 1 c)
  rw [(((leaves F T t r ho hu hv h hK hη hP).comp_tendsto (show Tendsto P (𝓝 0) (𝓝 0) from map_zero P ▸ P.continuous.continuousAt.tendsto)).iteratedFDeriv ℝ 2).eq_of_nhds]

end YM.Further.PhysicalPeriodLimitF933.Paintings
namespace YM.Further.PhysicalPeriodLimitF933.Paintings
open Gauge Filter Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice RG Tree Matrix Finset Precision Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch Extra.Iteration Extra.Iteration.Calibration
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {P : Patch} {Q : KernelChoices} {T : Stage} {N : ℕ}

/- Pre path data (includes unscaled incoming caps & width; no `μ : Q.Γ`
chosen on these until paid. Choose once at stage/T.upper p & layout.)
Λ may vary e.g. β-plateau changes field weight on outputs; R held across the two.
-/
structure Supply (G : Gauge) (P : Patch) (Q : KernelChoices) (T : Stage) where -- name ambiguity
  h : Push.Uniform.Before G T.width T.paths P.J Q T.order
  larger : P.Branches Q G
  enough : 4 ≤ T.order

variable (A : Paintings.Supply G P Q T) {R : PathData G} {Λ : ℝ} (hp : R.Bounds T.clip T.width T.paths Λ)
  {O : ChartRatio G} (ho : LocalRatio O)
local notation "Z" => A.h.tables T.clip P
variable {c C f F : Side} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val}

abbrev scale (c : Side) (G : Gauge) := Positions (Primary c G)
abbrev canvas (P : Patch) (c : Side) : Side := c*P.L
namespace Supply
-- addresses renormalized per projection; do NOT need Claim `Larger` anywhere without branches here
def bulletin {P : Patch} {Q : KernelChoices} {G : Gauge} (_z : Paintings.Supply G P Q T) (h : f.val=c.val*P.L.val) := Larger (G:=G) (stepped Q h)


include hp in
lemma stationed (hb : A.bulletin h) (E : Forest (decreed h)) :
    ∃ u : In G c → AxisChart G E, A.h.Service (S:=stepped Q h) E T.clip R u ∧ PriceGap (S:=stepped Q h) E T.clip R (Z).gap ∧ 0<(Z).gap := by
  let t := Lace.plain Q (h:=h)
  obtain ⟨u,hg⟩:= A.h.graph (S:=stepped Q h) E hp hb rfl rfl
  obtain ⟨hU,hV,-⟩ := A.h.full_pack (S:=stepped Q h) E t hp hb rfl rfl
  exact ⟨u,hg,hU,hV⟩

-- arbitrary local read, for period comparisons does NOT have to be selected for future analysis
-- Pay independent of hB/hP witnesses
def declared {h : f.val=c.val*P.L.val} (E : Forest (decreed h)) (r : (stepped Q h).Choices) (u : In G c→AxisChart G E)
    (R : PathData G) (p : Clip) (O : ChartRatio G) (x y : scale c G) :=
    iteratedFDeriv ℝ 2 (determinant (S:=stepped Q h) E r R p u O ∘ tint G (Body 1 c)) 0 ![x,y]

def gallery (h : f.val=c.val*P.L.val) : Forest (decreed h) := Classical.choice (Tree.select _ P.odd_side)

/-- Actually computed intensive kernel answer. Choose the path service exactly once.
Branches elsewhere germ-invariant, useful if constrained on later calls.
-/
def billing (A : Paintings.Supply G P Q T) (h : f.val=c.val*P.L.val) (ha : A.bulletin h) (R : PathData G) (hp : R.Bounds T.clip T.width T.paths Λ) (O : ChartRatio G) (x y : scale c G) :=
  let B := gallery h; let g := Classical.choose (stationed A hp ha B)
  declared B (Lace.plain Q) g R T.clip O x y / (c.val:ℝ)^4

-- compatibility across dependent Period Proof if separate fun operations
include A hp ho
lemma declaration (h : f.val=c.val*P.L.val) (ha : A.bulletin h) (u : Forest (decreed h)) (r : (stepped Q h).Choices) (g) (hs : Critical (S:=stepped Q h) u T.clip R g) (x y : scale c G) :
    declared u r g R T.clip O x y / (c.val:ℝ)^4=A.billing h ha R hp O x y := by
  let B := gallery h; let Y := stationed A hp ha B
  have hh := Classical.choose_spec Y
  exact congr_arg (· / _) (leaves' (S:=stepped Q h) u B r (Lace.plain Q) ho hs (hh.1.critical) hp A.larger hh.2.2 hh.2.1 x y)

variable {M : ℕ} (hC : C.val=c.val*M) (he : 2 ≤ c.val)
local notation "L" => Macrame.Lace.project (h:=h) (H:=H) hC he
local notation "Ψ" => Macrame.Lace.Fitted.narrow L (G:=G)

-- Avoid going through equiv periodizations. BUT keep truly all cells at the price above.
-- Γ ceiling burns P.L but not K(H).
def sights (a : Paintings.Supply G P Q T) := Fresco.stamp (a.h.tables T.clip P)
def allowance (a : Paintings.Supply G P Q T) := ((P.L.val:ℝ)^4 * Fintype.card Axis*G.lieDim)* Fresco.fuel (a.h.tables T.clip P) T.order
-- notation shadow A? capture variable A rather than declaration! fix
include hC he
lemma move (ha : A.bulletin h) (hA : A.bulletin H) (x y : scale c G) (hx : ‖x‖≤1) (hy : ‖y‖≤ 1) :
    let b := onpass Ψ
    0 < A.sights ∧ 0 ≤ A.allowance ∧ |A.billing h ha R hp O x y-A.billing H hA R hp O (b x) (b y)| ≤ A.allowance * Real.exp (-A.sights*c.val) := by
  let b0 := gallery h
  let V := circuit hC he b0 (H:=H)
  let X := stationed A hp hA V
  let Y := stationed A hp ha b0
  obtain ⟨u,hu,hG,hD⟩:=Y
  obtain ⟨v,hv,-,-⟩:=X
  have ht := @Fresco.subscribed G c C f F P Q h H M hC he b0 V (crown hC he b0) R T.clip _ _ _ _ _ A.h O ha hA hp rfl A.enough u hu v hv ho
    (Enrobe.assesses Q hC he b0 (H:=H) T.clip R) (Macrame.Lace.spread hC he b0) x y hx hy
  obtain ⟨hL,hF,hh⟩ := ht
  have hf : P.L.val ≥ 1 := P.L.property
  have hm : 0<M := Nat.pos_of_mul_pos_left (show 0<c.val*M from hC ▸ C.property)
  have hc : 0<(c.val:ℝ) := by exact_mod_cast c.property
  have hy : 0<(C.val:ℝ) := by exact_mod_cast C.property
  let S := (C.val:ℝ)^4; let s := (c.val:ℝ)^4
  have Hs : 0<S := pow_pos hy _
  have hs : 0<s := pow_pos hc _
  have heq : (↑(M^4):ℝ)*s=S := by unfold S s; rw [hC]; push_cast; ring
  intro b
  refine ⟨hL,mul_nonneg (by positivity) hF,?_⟩
  let g := declared (P:=P) (Q:=Q) (h:=h) b0 (Lace.plain Q) u R T.clip O x y
  let k := declared (P:=P) (Q:=Q) (h:=H) V (Lace.plain Q) v R T.clip O (b x) (b y)
  rw [← declaration A hp ho _ ha b0 (Lace.plain Q) u hu.critical, ← declaration A hp ho _ hA V (Lace.plain Q) v hv.critical]
  have hvol : Fintype.card (Key V G) ≤ F.val^4 * Fintype.card Axis * G.lieDim := by
    rw [Fintype.card_prod,Fintype.card_fin]
    have he := Fintype.card_le_of_injective (f:=fun i:V.Free => i.val) Subtype.val_injective
    erw [Fintype.card_prod,site_card] at he
    exact Nat.mul_le_mul_right _ he
  have hx : (Fintype.card (Key V G):ℝ) ≤ S*((P.L.val:ℝ)^4* Fintype.card Axis * G.lieDim) :=
    (show _ ≤ (((F.val^4 * Fintype.card Axis * G.lieDim):ℕ):ℝ) from (by exact_mod_cast hvol)).trans_eq (by rw [H]; unfold S; push_cast; ring)
  have hT : - A.sights * (f.val:ℝ) ≤ - A.sights * (c.val:ℝ) := mul_le_mul_of_nonpos_left (by exact_mod_cast (show c.val ≤ f.val from h ▸ Nat.le_mul_of_pos_right _ hf)) (neg_nonpos.mpr hL.le)
  apply le_of_mul_le_mul_left _ Hs
  change S*|g/s-k/S| ≤ _
  have ht : S*(g/s-k/S)=(↑(M^4):ℝ)*g-k := by rw [mul_sub, ← mul_div_assoc S k,mul_div_cancel_left₀ k Hs.ne',← heq]; field_simp -- cancel form?
  rw [show S*|g/s-k/S|=|S*(g/s-k/S)| by rw [abs_mul,abs_of_pos Hs],ht]
  apply hh.trans
  change _ ≤ S*(A.allowance*Real.exp (_))
  calc
    _ ≤ S*((P.L.val:ℝ)^4* Fintype.card Axis * G.lieDim)*Fresco.fuel Z T.order * Real.exp (-A.sights*c.val) := mul_le_mul (mul_le_mul_of_nonneg_right hx hF) (Real.exp_monotone hT) (Real.exp_pos _).le (mul_nonneg (by have hu : 0 ≤ S := Hs.le; positivity) hF)
    _ = _ := by unfold allowance; ring
end Supply
end YM.Further.PhysicalPeriodLimitF933.Paintings
