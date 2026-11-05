import YM.OPE.Log.PricePlot
import YM.Trace2.Transfer
import YM.SharpGram.Prices.FirstFloor
/-! Fixed-field estimates for unit inputs at every horizon, for all inputs through grade three, and for outputs of weight at most three. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Set Filter Lattice RG Wilson MergeProof Bid Source Extra.Histories Next.UVStress
open Extraction OPE OPE.Log
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (U : Spec.Final C f S)
variable {W r D} (T : TableTickets C W r D) (h : C.Makes) {d k p N : ℕ}

-- shorthand clauses in physical *field space*, quantifiers of the exact ticket
set_option quotPrecheck false
local notation "Φ" => Filter (ℕ × ℕ)

def Supplies (C : Family G) {S : Table C.book} (φ : Filter (ℕ × ℕ)) (d : ℕ) (x : S.Field d) : Prop :=
  ∃ p : ℕ, ∀ᶠ k : ℕ in atTop, ∃ (y : C.label d) (q : ℕ×ℕ → C.label d),
    S.project d y = x ∧ Tendsto q φ (𝓝 y) ∧
    ∀ᶠ i in φ, quota C d k i.1 i.2 (q i) ≤ C.path.levels.clock.hatBeta k^p

def Releases (C : Family G) {S : Table C.book} (φ : Φ) (d w : ℕ) (L : S.Field d →ₗ[ℂ] ℂ) : Prop :=
  ∃ p : ℕ, ∀ᶠ k in atTop, ∀ (u : Φ) [u.NeBot], u ≤ φ →
    ∀ (q : ℕ×ℕ → C.label d) (x : C.label d) (z : ℝ), (∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ z) →
      Tendsto q u (𝓝 x) → ‖L (S.project d x)‖ ≤ C.path.levels.clock.hatBeta k^p / C.S.a k^(d-w) * z

def Kills (B : DiffPlan S) {d w : ℕ} (hw : w ≤ d) (L : S.Field d →ₗ[ℂ] ℂ) : Prop :=
  ∀ e : ℕ, ∀ he : e < w, ∀ x : S.Field e, L (B.rise (he.le.trans hw) x)=0

lemma quota_nonneg (x : C.label d) : 0 ≤ quota C d k N p x := Work.G08.size_nonneg ..
include h
lemma quota_smul (t : ℂ) (x : C.label d) (hk : C.ref d ≤ k) (hx : k ≤ N) :
    quota C d k N p (t • x) = ‖t‖ * quota C d k N p x := by
  obtain ⟨ht,he⟩ := (h.calibrated d N p (hk.trans hx)).linear k hk hx
  unfold quota
  rw [map_smul, show ((C.factory d N p).entries k _).x = _ from ht.map_smul t ((C.factory d N p).terminal.symm x), Size.smul]
lemma quota_unit (hk : C.ref d ≤ k) (hx : k ≤ N) :
    quota C d k N p (C.refUnit d) = C.S.a k ^ d := by
  let F := C.labels.level d
  have hB := h.calibrated d N p (hk.trans hx)
  unfold quota
  have ht : (C.factory d N p).terminal.symm (C.refUnit d) = unitVec F C.path N := by
    apply LinearEquiv.injective (C.factory d N p).terminal
    rw [LinearEquiv.apply_symm_apply, ← hB.reads, hB.unit_coord (C.ref d) le_rfl (hk.trans hx)]
  rw [ht, hB.unit_coord k hk hx]
  change F.coeffSize ((C.S.a k:ℂ)^d • F.e0) = _
  rw [Size.smul, norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos k).le, show F.coeffSize F.e0=1 from Size.size_axis F 0, mul_one]

omit h
variable (hG : G.Simple) {φ : Φ} (hf : φ ≤ f.fuse)
include hG hf
include h
lemma supplyUnit (t : ℂ) : Supplies C φ d (t • S.unit d) := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (C.ref d),(Next.Rank.Station.hat_rate C.path.levels hG).eventually_ge_atTop ‖t‖,
    C.S.shrinks.eventually (ge_mem_nhds zero_lt_one)] with k hk hK hx
  refine ⟨t • C.refUnit d,fun _ => t • C.refUnit d, by rw [map_smul]; rfl,tendsto_const_nhds,?_⟩
  filter_upwards [((Push.RelayDifference.cutoff_grows f).mono_left hf).eventually_ge_atTop k] with i hi
  rw [quota_smul h t (C.refUnit d) hk hi,quota_unit h hk hi,pow_one]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (C.S.a_pos k).le hx)).trans hK

omit h
include T h
omit hf in
/-- Sharper constant test (project AFTER core identity). Uniform at cutoff on
reference-normalized vectors. `L` really descends to the physical field space. -/
theorem coreRead (L : S.Field d →ₗ[ℂ] ℂ) (hL : L (S.unit d) = 0)
    (x : C.label d) (hr : C.ref d ≤ k) (hk : k ≤ N) :
    let M := LinearMap.toContinuousLinearMap (L.comp (S.project d))
    ‖L (S.project d x)‖ ≤ ‖M‖ * ((C.S.a (C.ref d) / C.S.a k)^(d-3) * coreQuota C d k N p x) := by
  intro M
  let F := C.labels.level d
  have hv : M F.e0=0:= by
    have hb : (((C.S.a (C.ref d):ℂ))^d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (C.S.a_pos (C.ref d)).ne')
    refine (mul_eq_zero.mp ?_).resolve_left hb
    change (↑(C.S.a (C.ref d)):ℂ)^d • M F.e0=0
    rw [← map_smul]
    exact hL
  change ‖M x‖ ≤ _
  rw [show M x = M (F.core x) from ?_]
  · refine (M.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (referenceCore T h hG x hr hk) (norm_nonneg _))
  nth_rw 1 [← Size.core_plus F x]
  rw [map_add, map_smul, hv, smul_zero, add_zero]

lemma physicalRelease (w : ℕ) (L : S.Field d →ₗ[ℂ] ℂ) (hw : w ≤ 3)
    (hp : 0 < w → L (S.unit d)=0) : Releases C φ d w L := by
  let M := LinearMap.toContinuousLinearMap (L.comp (S.project d))
  let j := if w=0 then d else d-3
  let a := C.S.a (C.ref d)
  have ha : 0 < a := C.S.a_pos _
  refine ⟨1,?_⟩
  filter_upwards [eventually_ge_atTop (C.ref d), (Next.Rank.Station.hat_rate C.path.levels hG).eventually_ge_atTop (‖M‖ * a^j),
    C.S.shrinks.eventually (ge_mem_nhds zero_lt_one)] with k hk hK hx u hu hf' q x z hq hV
  let l := C.S.a k
  have hl : 0 < l := C.S.a_pos _
  have hc : 0 ≤ z := by obtain ⟨i,hi⟩ := hq.exists; exact (quota_nonneg ..).trans hi
  apply le_trans (b:= ‖M‖ * ((a/l)^j * z)) ?_ ?_
  · change ‖M x‖ ≤ _
    apply le_of_tendsto ((M.continuous.continuousAt.tendsto.comp hV).norm)
    filter_upwards [hq, ((Push.RelayDifference.cutoff_grows f).mono_left (hf'.trans hf)).eventually_ge_atTop k]
      with i hi he
    by_cases hz : w=0
    · have hh := reference (p:=i.2) T h (q i) hk he
      exact (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hh.trans (by unfold j; rw [if_pos hz]; exact mul_le_mul_of_nonneg_left hi (by change 0 ≤ (a/l)^_; positivity))) (norm_nonneg _))
    have he' := coreRead T h hG L (hp (Nat.pos_of_ne_zero hz)) (q i) hk (p:=i.2) he
    rw [show j=d-3 from if_neg hz]
    exact he'.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((coreQuota_le _).trans hi) (pow_pos (div_pos ha hl) _).le) (norm_nonneg _))
  rw [← mul_assoc,div_pow, ← mul_div_assoc,pow_one]
  apply mul_le_mul_of_nonneg_right _ hc
  apply le_trans (div_le_div_of_nonneg_right hK (pow_pos hl j).le)
  refine div_le_div_of_nonneg_left (zero_le_one.trans (C.path.levels.fits.delayed k).le) (pow_pos hl _) ?_
  apply pow_le_pow_of_le_one hl.le hx
  by_cases h0 : w=0
  · simp [j,h0]
  dsimp only [j]; rw [if_neg h0]; omega
omit h
include U -- T available
lemma outletFirst {w : ℕ} (L : S.Field d →ₗ[ℂ] ℂ) (hw : w ≤ d) (he : w ≤ 3)
    (hp : Kills (C:=C) U.sector.derivatives hw L) : Releases C φ d w L := by
  apply physicalRelease T U.room.cutoff hG hf w L he -- order inspect
  intro h'; rw [← U.sector.derivatives.fixs U.phase.transport.injection U.room.kernel.laws (Nat.zero_le d)]
  exact hp 0 h' _
omit T
lemma inletFirst (x : C.label d) (hd : d ≤ 3) : Supplies C φ d (S.project d x) := by
  obtain ⟨t,h'⟩ := Trace.first_grade U hG (by omega : d < 4) (S.project d x)
  rw [h']
  exact supplyUnit U.room.cutoff hG hf _
end YM.SharpGram
