import YM.MultiNext.VACUUM_STABILITY.Tune.Cuts

set_option warningAsError false

/-!
# Charge local singleton moves with a spare exponent *inside* the step

Retained through joins with flag packs. Thus the expansion is at the same Tenders
rates despite moving origins. All tested at every complex parameter, including 0
(parameter-dependent hit budget allowed). No cost per period/cutoff/direction count.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Tune
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {B : Brush V G n} {P : BudgetPoint}

namespace Price

def fareNow (P : BudgetPoint) (m : ℕ) (χ : ℝ) := (6*χ) * Jets.baseFee P * Real.exp ((Rates.inner P+6)*m)
def levy (P : BudgetPoint) (m : ℕ) (χ : ℝ) := toll P.B * fareNow P m χ

def first (P : BudgetPoint) (m : ℕ) (χ : ℝ) := Rates.raw P / (2*(1+levy P m χ))

lemma fare_active {m : ℕ} {χ : ℝ} (he : 1 ≤ χ) : 0 < fareNow P m χ :=
    mul_pos (mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le he)) (Jets.base_pos _)) (Real.exp_pos _)
lemma levy_pos {m : ℕ} {χ : ℝ} (he : 1 ≤ χ) : 0 < levy P m χ := mul_pos (toll_pos _) (fare_active he)
lemma enough {m : ℕ} {χ : ℝ} (he : 1 ≤ χ) : 0 < first P m χ ∧ first P m χ ≤ Rates.raw P ∧
    levy P m χ * (logPrice P * first P m χ) ≤ Rates.window P/2 := by
  have hx := levy_pos (P:=P) (m:=m) he
  have hP := Rates.raw_pos P; have he := logPrice_pos P
  unfold first; refine ⟨by positivity,div_le_self hP.le (by linarith),?_⟩
  have h := Rates.funded P
  rw [← mul_div_assoc,← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left h hx.le, Rates.window_pos P]
end Price

namespace Slicer
variable {L : V → Support n → Prop} {T : Finset V} {S : Slicer B} {m : ℕ} {χ : ℝ}

variable [Fintype V]

/-- Only first-system costs and unmarked base attachment costs. Stronger on
u by six more exponent units. Does NOT ask for computed sticker or wrapped e
responses. -/
structure Endowed (S : Slicer B) (P : BudgetPoint) (m : ℕ) (χ κ : ℝ) (z : V → ℂ) : Prop where
  stage : 1 ≤ χ
  primary : ∃ f : ℕ→ℝ, (∀ i, P.supBounds (B.u i).anchor (B.u i).zone ((B.u i).stamp.tell z) (f i)) ∧
      Ac.Hit (fun i => (B.u i).zone) P.B f (Rates.inner P+13) (Price.first P m χ)
  compulsory : ∃ f : ℕ → ℝ, (∀ i, ∀ U, ‖(B.d i).tell z U‖ ≤ f i) ∧
      Ac.Hit (fun i => (B.pack i).zone) P.B f (Rates.inner P) (κ * Rates.window P)
  background : ∃ f : ℕ→ℝ, (∀ i, ∀ U, ‖(S.base i).stamp.tell z U‖ ≤ f i) ∧
      Ac.Hit (fun i => (S.base i).zone) P.B f (Rates.inner P) (Rates.window P/2)

private lemma plentiful {κ z} (hS : S.Ticket P L T m χ) (h : S.Endowed P m χ κ z) :
    ∃ f : B.Line → ℝ, (∀ i, 0 ≤ f i ∧ ∀ x∈(B.chapter i).zone,
          P.supBounds x (B.chapter i).zone ((B.chapter i).stamp.tell z) (f i)) ∧
        Ac.Hit (fun i => (B.chapter i).zone) P.B f (Rates.inner P+6) (logPrice P * Price.first P m χ) := by
  obtain ⟨p,hp,hP⟩:=h.primary
  let g i := (B.u i).stamp.tell z; let X i := (B.u i).zone
  let a := Rates.inner P + 6; let c := Price.first P m χ
  have hh (i) := (hp i).1
  have ha : 0 ≤ a := add_nonneg (Rates.inner_pos _).le (by norm_num)
  have he := Price.enough (P:=P) (m:=m) h.stage; have hw := Rates.window_pos P
  have hf := he.2.1.trans (Rates.still_thin P); have hn := Rates.cabin P; change c ≤ _ at hf
  have hv : Cluster.Thin X P.B (a+6) p c := by
    refine ⟨by linarith, he.1.le, hh, by linarith, ?_, ?_⟩
    · apply le_trans _ (Rates.launchable P); exact mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans (Rates.gate P))
    rw [show a+6+1=Rates.inner P+13 by unfold a; ring]; exact hP
  let f (i : B.Line) := Jets.charges X P p (B.station.tune.line i)
  have hY i : P.Regular (X i) (g i) := path_scaled _ (hS.lawful i)
  have hs := Chorus.earned B.station X univ B.stat g (fun i => (B.u i).anchor) (fun i => (B.u i).origin) P hY ha hv hp
  have hx i x (he : x∈(B.chapter i).zone) : P.supBounds x (B.chapter i).zone ((B.chapter i).stamp.tell z) (f i) := by
    rw [B.chap_eq]; exact (hs.1 i).2 _ he
  exact ⟨f, fun i => ⟨(hx i _ (B.chapter i).origin).1,hx i⟩, hs.2.1⟩

/-- shrink supports in costing (e.g. keep canonical in its original section stencil).
Complete support of attachments and of remainders is NOT shrunk. -/
private lemma inside {I : Type} (X Y : I → Support n) (h : ∀ i, Y i ⊆ X i) {a c : ℝ} {f : I→ℝ} {M : ℕ}
    (hf : Ac.Hit X M f a c) (hh : ∀ i,0 ≤ f i) (ha : 0 ≤ a) : Ac.Hit Y M f a c := by
  intro x; apply Absolute.compare (hf x)
  · intro i; split; exact mul_nonneg (hh i) (Real.exp_pos _).le; exact le_rfl
  intro i; split
  · rename_i he; rw [if_pos (h i he)]; have hp := hh i; gcongr; exact Corona.cover_mono (h i) _
  exact (hf x).1 _

omit [Fintype V] in
private lemma travel_pay {f : B.Line → ℝ} (hS : S.Ticket P L T m χ) {c : ℝ} (hc : 0 ≤ c) (hh : 1 ≤ χ)
    (hf : ∀ i, 0 ≤ f i) (hs : Ac.Hit (fun i => (B.chapter i).zone) P.B f (Rates.inner P+6) c) :
    let d (i : B.Line) := coverNumber P.B (B.chapter i).zone + m
    Ac.Hit (fun i => (S.cuts i).jointly) P.B (fun i => (6*χ)*f i*(rate P (d i))^P.order) (Rates.inner P) (Price.levy P m χ*c) := by
  intro d
  have hp i : (B.chapter i).anchor ∈ (S.cuts i).jointly := Finset.mem_union_left _ (B.chapter i).origin
  let q i := (6*χ)*f i*(rate P (d i))^P.order
  have he i : 0 ≤ q i := mul_nonneg (mul_nonneg (by linarith) (hf i)) (pow_nonneg (zero_le_one.trans (rate_hi ..)) _)
  unfold Price.levy; rw [mul_assoc]
  apply Hits.everyone (Rates.inner_pos _).le (mul_nonneg (Price.fare_active hh).le hc) he _ hp (fun i => (S.cuts i).span_sum (hS.expenditure i))
  intro x; let a := Rates.inner P
  let w := Price.fareNow P m χ
  have hw : 0 ≤ w := (Price.fare_active hh).le
  apply Absolute.compare (permit_mul (hs x) hw)
  · intro i; split; exact mul_nonneg (he i) (Real.exp_pos _).le; exact le_rfl
  intro i; split
  · rename_i hi
    rw [if_pos (hi ▸ (B.chapter i).origin)]
    let N := coverNumber P.B (B.chapter i).zone
    calc
      _ ≤ ((6*χ)*f i*(Jets.baseFee P*Real.exp (d i)))*Real.exp ((a+5)*d i) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (annual ..) (mul_nonneg (by linarith) (hf i))) (Real.exp_pos _).le
      _ = w * (f i*Real.exp ((a+6)*N)) := by
        unfold w Price.fareNow
        have ht : (d i:ℝ)+(a+5)*d i = (a+6)*m+(a+6)*N := by unfold d N; push_cast; ring
        have hj : Real.exp (d i)*Real.exp ((a+5)*d i)=Real.exp ((a+6)*m)*Real.exp ((a+6)*N) := by rw [←Real.exp_add,ht,Real.exp_add]
        change _ = (6*χ*Jets.baseFee P*Real.exp ((a+6)*m))*_
        rw [mul_assoc _ _ (Real.exp ((a+5)*_)),mul_assoc _ _ (Real.exp ((a+5)*_)),hj]; ring
  exact mul_nonneg hw ((hs x).1 _)

/-- Move prices. Retain also the unmasked-unit price for later linear equality (not on
opportunities). -/
lemma affordability {z κ} (hS : S.Ticket P L T m χ) (hh : S.Endowed P m χ κ z) :
    ∃ f : B.Line→ℝ, Ac.Hit (fun i => (S.cuts i).jointly) P.B f (Rates.inner P) (Rates.window P/2) ∧
    ∀ i, (0 ≤ f i ∧ ∀ x∈(S.partL T i).zone,P.supBounds x (S.partL T i).zone ((S.partL T i).stamp.tell z) (f i)) ∧
      (∀ x∈(S.partR T i).zone,P.supBounds x (S.partR T i).zone ((S.partR T i).stamp.tell z) (f i)) ∧
      (∀ U, ‖(S.flagTerm T P i).stamp.tell z U‖ ≤ f i) ∧ ‖beat (B.chapter i).stamp.name z * (S.cuts i).fiat‖ ≤ f i := by
  obtain ⟨e,he,hP⟩:=plentiful hS hh
  let p i := coverNumber P.B (B.chapter i).zone+m
  let f i := (6*χ)*e i*(rate P (p i))^P.order
  have hv := hh.stage; have hx := Price.enough (P:=P) (m:=m) hv
  have hF : Ac.Hit (fun i => (S.cuts i).jointly) P.B f (Rates.inner P) (Rates.window P/2) := fun x =>
    Absolute.loosen (travel_pay hS (mul_nonneg (logPrice_pos _).le hx.1.le) hv (fun i => (he i).1) hP x) hx.2.2
  have hp := (Absolute.burden (fun i => show (S.cuts i).jointly.Nonempty from ⟨_,(S.cuts i).left.origin⟩) hF).1
  refine ⟨f,hF,?_⟩; intro i
  let t := Stamp.beat (B.chapter i).stamp.name z
  have ht : P.Regular _ _ := Jets.stanza_regular (fun i => (B.u i).zone) (fun i => (B.u i).stamp.ink) P hS.lawful (B.station.tune.line i)
  obtain ⟨ha,hb,hc⟩ := (S.cuts i).issued ht (hS.expenditure i) t ((he i).2 _ (S.cuts i).contained)
  have hf := hp i; have hQ := (he i).1
  have hg : 1 ≤ (rate P (p i))^P.order := one_le_pow₀ (rate_hi ..)
  have hu : ‖Stamp.beat (B.chapter i).stamp.name z*(S.cuts i).fiat‖ ≤ f i := by
    have h := ((S.cuts i).scaled (hS.expenditure i) t ((he i).2 _ (S.cuts i).contained)).2
    unfold f; refine h.trans ?_
    exact le_trans (by nlinarith : χ * e i ≤ 6*χ*e i) (le_mul_of_one_le_right (mul_nonneg (by linarith) hQ) hg)
  refine ⟨⟨hf,?_⟩,?_,?_,hu⟩
  · intro x; unfold partL; split
    · intro hh; obtain ⟨-,h⟩:=ha x hh; refine ⟨hf,fun U hu l hl hh => le_trans (h U hu l hl hh) ?_⟩
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hg); nlinarith
    intro _; dsimp only [quiet,tell]; rw [smul_zero]; exact ⟨hf,fun U hU l hl hv => ((null_path P _).2 x).2 U hU l hl hv |>.trans hf⟩
  · intro x; unfold partR; split
    · intro hh; obtain ⟨-,h⟩:=hb x hh; refine ⟨hf,fun U hu l hl hh => le_trans (h U hu l hl hh) ?_⟩
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hg); nlinarith
    intro _; dsimp only [quiet,tell]; rw [smul_zero]; exact ⟨hf,fun U hU l hl hv => ((null_path P _).2 x).2 U hU l hl hv |>.trans hf⟩
  intro U; unfold flagTerm; split
  · exact hc _
  simp [eraseChime,hf]
lemma paid_all {z κ} (hS : S.Ticket P L T m χ) (hh : S.Endowed P m χ κ z) : Quoted B (S.package P T) P κ z := by
  let a := Rates.window P / 2
  have hP := Rates.cabin P; have hp := Rates.window_pos P; have hm := (Rates.inner_pos P).le
  have he : a+a = Rates.window P := by unfold a; ring
  obtain ⟨f,hf,h⟩:=affordability hS hh
  have ht (i : B.Line) : 0 ≤ f i := (h i).1.1
  have hx i := S.union_zones (P:=P) T i
  constructor
  · obtain ⟨g,hg,hG⟩:=hh.primary
    have hh := Price.enough (P:=P) (m:=m) hh.stage
    exact ⟨g,hg,Absolute.relax hG hh.2.1 (fun i => (hg i).1) (fun _ => le_rfl) (by linarith)⟩
  · let p := S.brine T; let u := Sum.elim f f
    have hu (i) : 0 ≤ u i ∧ ∀ x∈(p i).zone, P.supBounds x (p i).zone ((p i).stamp.tell z) (u i) := by
      obtain i|i:=i
      · exact (h i).1
      exact ⟨ht _, (h i).2.1⟩
    have hl := inside _ (fun i => (S.partL T i).zone) (fun i => ((hx i).1).le) hf ht hm
    have hr := inside _ (fun i => (S.partR T i).zone) (fun i => by rw [(hx i).2.1]; exact Finset.subset_union_right) hf ht hm
    have hw : Ac.Hit (fun i => (p i).zone) P.B u (Rates.inner P) (a+a) := fun x => Absolute.union (hl _) (hr _)
    refine ⟨Pad.wide u 0,fun i => ?_,fun x => ?_⟩
    · unfold package; refine Pad.wider (S.brine T) (tent V G n) u 0 (fun w d => 0 ≤ d ∧ ∀ x∈w.zone,P.supBounds x w.zone
          (w.stamp.tell z) d) i hu ?_; refine ⟨le_rfl, fun x _ => ?_⟩
      simp only [tent,tell,smul_zero]; exact (null_path ..).2 _
    refine Pad.wide_cost p (tent V G n) u (fun w d => if x∈w.zone then d*Real.exp (Rates.radius P * coverNumber P.B w.zone) else 0)
      (by simp) (Absolute.relax hw he.le (fun i => (hu i).1) (fun _ => le_rfl) ?_ x)
    unfold Rates.inner; linarith
  · exact hh.compulsory
  obtain ⟨g,hg,hG⟩:=hh.background; let p := S.jointList T P; let u := Sum.elim f g
  have hu (i) : ∀ U, ‖(p i).stamp.tell z U‖ ≤ u i := by
    obtain i|i:=i
    · exact (h i).2.2.1
    exact hg _
  have hl := inside _ (fun i => (S.flagTerm T P i).zone) (fun i => ((hx i).2.2).le) hf ht hm
  have hw : Ac.Hit (fun i => (p i).zone) P.B u (Rates.inner P) (a+a) := fun x => Absolute.union (hl _) (hG _)
  refine ⟨Pad.wide u 0,fun i => ?_,fun x => Pad.wide_cost p (stub V G n) u
      (fun w d => if x∈w.zone then d*Real.exp (Rates.inner P * coverNumber P.B w.zone) else 0) (by simp) ?_⟩
  · unfold package; exact Pad.wider p (stub V G n) u 0 (fun w d => ∀ U, ‖w.stamp.tell z U‖ ≤ d) i hu (by simp [stub])
  exact Absolute.loosen (hw x) he.le

end Slicer
end YM.Multi.Vacuum.Tune
