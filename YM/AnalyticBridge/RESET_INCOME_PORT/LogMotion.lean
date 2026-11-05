import YM.AnalyticBridge.RESET_INCOME_PORT.Split
import YM.SectorNext.VACUUM_NORMALIZATION.Gas

set_option warningAsError false

/-!
# Quantitative log motion test for the scalar income socket

Signed gas activities, at a FIXED FIELD. To serve the dial price (and
help log calibration). Leash zero-order costs alone, on BOTH sides, then a
small enlarged negative-fugacity bill, imply actual support-weighted hit
bounds on log differences in the SAME cluster calculation. No derivatives
through hard tests. Costs even with d equal or moving to the endpoints.
We use persistent full support prices rather than a topology where point
measure discontinuities would be difficult to pay.

Not a general regularity theorem on the log-jets or component calculus of the output;
no label-level continuity on fitted functions obtained here.

See follow-on
use against the actual post-template readings on all-good points.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome.LogMotion

open Function Filter Set Lattice Wilson RG Pressure MeasureTheory Finset
open SectorNext.Vacuum.ReLog
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {J : Type*} [Fintype J] [DecidableEq J]
local notation "ℰ" => Real.exp
local notation "logr" => Real.log

/-- Companion negative-fugacity comparison for the recursive cash flow:
envelope for both sides, and difference charged against one enlarged table.
ρ (in uses `|a-b|` times a small coefficient) can also be zero. -/
structure Chip (ρ a b u U : ℝ) : Prop where
  paidL : |a| ≤ u
  paidR : |b| ≤ u
  enrich : u ≤ U
  swing : |a-b| ≤ ρ*(U-u)

namespace Chip
variable {s t A B u U v V ρ : ℝ} (h : Chip ρ s A u U) (g : Chip ρ t B v V)

lemma zero (ρ : ℝ) : Chip ρ 0 0 0 0 := by constructor <;> simp
include h
lemma nonneg : 0 ≤ u := (abs_nonneg _).trans h.paidL
include g
lemma add : Chip ρ (s+t) (A+B) (u+v) (U+V) := by
  refine ⟨(abs_add_le ..).trans (add_le_add h.paidL g.paidL), (abs_add_le ..).trans (add_le_add h.paidR g.paidR),
    add_le_add h.enrich g.enrich,?_⟩
  rw [show s+t-(A+B)=(s-A)+(t-B) by ring]
  exact (abs_add_le ..).trans ((add_le_add h.swing g.swing).trans_eq (by ring))
lemma mul (he : 0≤ρ) : Chip ρ (s*t) (A*B) (u*v) (U*V) := by
  let w := U-u; let z := V-v; have hw : 0≤w := sub_nonneg.mpr h.enrich; have hz : 0≤z := sub_nonneg.mpr g.enrich
  constructor
  · rw [abs_mul]; gcongr; exacts [h.nonneg,h.paidL,g.paidL]
  · rw [abs_mul]; gcongr; exacts [h.nonneg,h.paidR,g.paidR]
  · exact mul_le_mul h.enrich g.enrich g.nonneg (h.nonneg.trans h.enrich)
  rw [show s*t-A*B=(s-A)*t+A*(t-B) by ring]
  apply (abs_add_le ..).trans; rw [abs_mul,abs_mul]
  have hL := mul_le_mul h.swing g.paidL (abs_nonneg t) (mul_nonneg he hw)
  have hR := mul_le_mul h.paidR g.swing (abs_nonneg _) h.nonneg
  have hx : 0≤ρ*(w*z) := by positivity
  nlinarith only [hL,hR,hx]
omit g
lemma collect (q : ℝ) (ht : 0≤q) : Chip ρ (s*q) (A*q) (u*q) (U*q) := by
  refine ⟨?_,?_,mul_le_mul_of_nonneg_right h.enrich ht,?_⟩
  · rw [abs_mul,abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_right h.paidL ht
  · rw [abs_mul,abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_right h.paidR ht
  rw [←sub_mul, abs_mul,abs_of_nonneg ht,←sub_mul,←mul_assoc ρ]; exact mul_le_mul_of_nonneg_right h.swing ht

omit h
private lemma exp1 {s u} (h : |s|≤u) : |ℰ s-1| ≤ ℰ u-1 := by
  have ht := Real.exp_monotone (le_of_abs_le h)
  have hk := Real.exp_monotone (neg_le.mp (neg_le_of_abs_le h))
  exact abs_le.mpr ⟨by linarith only [hk,Real.add_one_le_exp s,Real.add_one_le_exp (-s)],by linarith only [ht]⟩
private lemma exp2 (s v : ℝ) : ℰ v*(s-v) ≤ ℰ s - ℰ v := by
  have hi := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s-v)) (Real.exp_pos v).le
  rw [← Real.exp_add,add_sub_cancel] at hi; linarith only [hi]
include h
lemma sell (hc : 0≤ρ) : Chip ρ (ℰ s-1) (ℰ A-1) (ℰ u-1) (ℰ U-1) := by
  refine ⟨exp1 h.paidL,exp1 h.paidR,sub_le_sub_right (Real.exp_monotone h.enrich) _,?_⟩
  have hx : |ℰ s-ℰ A| ≤ ℰ u*|s-A| := by
    rcases le_total s A with hv|hv
    · rw [abs_of_nonpos (sub_nonpos.mpr hv),abs_of_nonpos (sub_nonpos.mpr (Real.exp_monotone hv))]; apply le_trans _
        (mul_le_mul_of_nonneg_right (Real.exp_monotone (le_of_abs_le h.paidR)) (by linarith only [hv]))
      linarith only [exp2 s A]
    rw [abs_of_nonneg (sub_nonneg.mpr hv),abs_of_nonneg (sub_nonneg.mpr (Real.exp_monotone hv))]; apply le_trans _
      (mul_le_mul_of_nonneg_right (Real.exp_monotone (le_of_abs_le h.paidL)) (by linarith only [hv]))
    linarith only [exp2 A s]
  have ht := mul_le_mul_of_nonneg_left h.swing (Real.exp_pos u).le
  simp only [sub_sub_sub_cancel_right]; linarith only [hx,ht,mul_le_mul_of_nonneg_left (exp2 U u) hc]

omit h
lemma sum {I : Type*} (j : Finset I) {a b c d : I → ℝ} (hh : ∀ i∈j,Chip ρ (a i) (b i) (c i) (d i)) :
    Chip ρ (∑ i∈j,a i) (∑ i∈j,b i) (∑ i∈j,c i) (∑ i∈j,d i) := by
  induction j using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero ρ
  | insert a j hj hi => simp only [Finset.sum_insert hj]; exact Chip.add (hh a (Finset.mem_insert_self ..)) (hi fun i hv =>
      hh i (Finset.mem_insert_of_mem hv))
end Chip

variable {s a A u U ρ : ℝ} {z y f F w : Grid J}

/-- Same alphabet. -/
def Chipped (ρ : ℝ) (z y f F : Grid J) := ∀ i, Chip ρ (z i) (y i) (f i) (F i)

namespace Chipped

lemma grows (h : Chip ρ s a u U) (I : List (Leaf J)) (P : Leaf J)
    (hx : ∀ i∈I, Chip ρ (z i) (y i) (f i) (F i)) (hr : 0≤ρ) :
    Chipped ρ (grow I P s z) (grow I P a y) (grow I P u f) (grow I P U F) := by
  have grain_price {s a u U : ℝ} (h : Chip ρ s a u U) (i : Leaf J) :
      Chipped ρ (grain i s) (grain i a) (grain i u) (grain i U) := by
    intro j; unfold grain; split; exact h; exact Chip.zero _
  induction I with
  | nil => exact grain_price h _
  | cons t l ih =>
    let k := grain_price ((hx _ (List.Mem.head _)).sell hr) t
    have hz := ih (fun i hi => hx i (.tail _ hi)); intro i
    refine Chip.add (hz i) (Chip.sum (a:=fun _ => _) Finset.univ (fun j _ => Chip.sum Finset.univ (fun d _ => ?_)))
    by_cases he : j ∪ d = i
    · simpa [he] using (hz j).mul (k d) hr
    simpa [he] using Chip.zero ρ

lemma signals {Z₁ Z₂ L H : Grid J} (h : Chipped ρ z y f F) (hr : 0≤ρ) (i : Leaf J) (x : J)
    (hh : ∀ j⊆i.erase x, Chip ρ (locker Z₁ j) (locker Z₂ j) (locker L j) (locker H j)) :
    Chipped ρ (signal z Z₁ i x) (signal y Z₂ i x) (signal f L i x) (signal F H i x) := by
  intro j; apply Chip.sum; intro t _
  exact Chipped.grows (h t) _ _ (fun u hu => hh u (mem_powerset.mp (mem_filter.mp (Finset.mem_toList.mp hu)).1)) hr j

private lemma ribbons (h : Chipped ρ z y f F) (hr : 0≤ρ) (n : ℕ) :
    Chipped ρ (ribbon z n) (ribbon y n) (ribbon f n) (ribbon F n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro i; unfold ribbon glue; apply Chip.sum; intro j _; apply Chip.sum; intro k _
    split; exact Chip.mul (ih _) (h _) hr; exact Chip.zero _

private lemma lamplight {g : Grid J} (he : Rate w) {i : Leaf J} (hi : i.Nonempty) (h : Pinned i g)
    (ht : crop w g < 1) (j : Leaf J) : HasSum (fun n : ℕ => ribbon g n j*(n+1:ℝ)⁻¹) (lamp g j) := by
  simpa only [lamp,div_eq_mul_inv] using (lamp_dom he hi h ht j).hasSum
lemma shines (h : Chipped ρ z y f F) (hr : 0≤ρ) (he : Rate w) {i : Leaf J} (hi : i.Nonempty)
    (h₁ : Pinned i z) (h₂ : Pinned i y) (h₃ : Pinned i f) (h₄ : Pinned i F) (ht : crop w F < 1) :
    Chipped ρ (lamp z) (lamp y) (lamp f) (lamp F) := by
  have hm {g : Grid J} (hv : ∀ j,|g j|≤F j) : crop w g < 1 := lt_of_le_of_lt (b:=crop w F)
    (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((hv _).trans (le_abs_self _)) (zero_le_one.trans (he.pos _))) ht
  have ha := hm fun i => ((h i).paidL).trans (h i).enrich
  have hb := hm fun i => ((h i).paidR).trans (h i).enrich
  have hc := hm (g:=f) fun i => by rw [abs_of_nonneg (h i).nonneg]; exact (h i).enrich
  intro j
  let σ (a : Grid J) n := ribbon a n j * (n+1:ℝ)⁻¹
  have hp (n : ℕ) : Chip ρ (σ z n) (σ y n) (σ f n) (σ F n) := (h.ribbons hr n j).collect _ (by positivity)
  have hx : HasSum (σ z) (lamp z j) := lamplight he hi h₁ ha j
  have hy : HasSum (σ y) (lamp y j) := lamplight he hi h₂ hb j
  have hz : HasSum (σ f) (lamp f j) := lamplight he hi h₃ hc j
  have hU : HasSum (σ F) (lamp F j) := lamplight he hi h₄ ht j
  have hoof {g g' : ℕ→ℝ} (hg : Summable g) (hg' : Summable g') (hv : ∀ i,|g i|≤g' i) :
      |∑' i,g i| ≤ ∑' i,g' i := (norm_tsum_le_tsum_norm hg.norm).trans (hg.norm.tsum_le_tsum hv hg')
  rw [← hx.tsum_eq, ← hy.tsum_eq,← hz.tsum_eq, ← hU.tsum_eq]
  refine ⟨hoof hx.summable hz.summable (fun i => (hp i).paidL),hoof hy.summable hz.summable (fun i => (hp i).paidR),
    hz.summable.tsum_le_tsum (fun i => (hp i).enrich) hU.summable,?_⟩
  rw [← hx.summable.tsum_sub hy.summable,← hU.summable.tsum_sub hz.summable, ← tsum_mul_left]
  exact hoof (hx.summable.sub hy.summable) ((hU.summable.sub hz.summable).mul_left _) (fun i => (hp i).swing)
end Chipped

variable {H₁ H₂ L H : Grid J}

/- Use the lamp identification only when there is a price *on this
region*, not comparing a purely formal series for the two endpoints.

-/
private lemma sees {g X w : Grid J} {B : Leaf J} (hz : ∀ j,0<X j)
    {x : J} (hx : x∈B) (he : Deletion g X) (hm : Rate w) (ht : crop w (signal g X B x) < 1) :
    locker X B=lamp (signal g X B x) B := by
  let Y := signal g X B x
  have hg (i : Leaf J) : 0<1-shed Y i := sub_pos.mpr ((le_abs_self _).trans_lt ((crop_shed hm Y i).trans_lt ht))
  have hw := changes (fun j => -logr (X j)) x B
  rw [if_pos hx] at hw
  refine hw.symm.trans (Eq.symm (from_shed ?_)); intro C hc
  rw [lamp_shed hm (singleton_nonempty _) (signal_pinned _ _ _ _) ht,matures he hx (fun i _=> hz i) C hc,
    Real.log_mul (hz _).ne' (hg C).ne']; ring

private lemma worth {B : Leaf J} (hF : Deletion F H) (hw : Receipt w F a) {x : J} (_ : x∈B) :
    crop w (signal F H B x)<1 := by
  have hf i : |F i| ≤ F i := le_of_eq (abs_of_nonneg (hw.zero _))
  have h := leash hw hf hF hF
  have hz j : 0 ≤ locker H j := (abs_nonneg _).trans (h j).2.2.1
  let l i := w i * locker H i
  have hW i : 0 ≤ l i := mul_nonneg (zero_le_one.trans (hw.budget.pos _)) (hz i)
  have hN (i : Leaf J) (_ : i ⊆ B) : ∑ u∈neighbors B x i,l u ≤ a * i.card := by
    let t (y : J) u := if y∈u then l u else 0
    have ht (y : J) (u : Leaf J) : 0 ≤ t y u := by unfold t; split; exact hW _; rfl
    have hh y : ∑ u∈neighbors B x i,t y u ≤ a := by
      refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _ => ht y u)).trans ?_
      let P := (Finset.univ : Leaf J)
      have ha : P.powerset = Finset.univ := by ext; simp [P]
      have hb := (h P).2.2.2 y (mem_univ y)
      unfold t; rw [←sum_filter,←ha]; exact hb
    have hv (y) (hy : y∈neighbors B x i) : l y ≤ ∑ z∈i,t z y := by
      obtain ⟨u,ht'⟩ := (mem_filter.mp hy).2
      have he := Finset.single_le_sum (f:=fun z=>t z y) (fun i _=>ht i y) (mem_inter.mp ht').2
      simpa only [t,if_pos (mem_inter.mp ht').1] using he
    refine (sum_le_sum hv).trans ?_; rw [sum_comm]
    exact le_trans (sum_le_sum fun j _=>hh j) (le_of_eq (by simp [mul_comm]))
  unfold signal
  calc
    _ ≤ ∑ i∈owners B x,crop w (sprig (neighbors B x i) i (F i) (locker H)) := crop_fin hw.budget _ _
    _ ≤ ∑ i∈owners B x,w i*F i*ℰ (a*i.card) := by
      refine sum_le_sum fun i hi => ?_
      have he := sprig_cost hw.budget (F i) (locker H) (neighbors B x i) (fun t ht => (mem_filter.mp ht).2)
        (fun u hu => hz u)
      rw [abs_of_nonneg (hw.zero _)] at he
      exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (hN i (mem_powerset.mp (mem_filter.mp hi).1)))
        (mul_nonneg (zero_le_one.trans (hw.budget.pos _)) (hw.zero _)))
    _ ≤ 1-ℰ (-a) := le_trans (sum_le_sum_of_subset_of_nonneg (fun i hi => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩)
      (fun i _ _ => mul_nonneg (mul_nonneg (zero_le_one.trans (hw.budget.pos _)) (hw.zero _)) (Real.exp_pos _).le)) (hw.hits x)
    _ < 1 := by linarith only [Real.exp_pos (-a)]

/-- Apply simultaneously from the two endpoint deletions and the two
comparisons. Concerns SAME orders/log pieces. Not an estimate through a
limit of measurements.
-/
theorem prices (hx : Chipped ρ z y f F) (hr : 0≤ρ) (hw : Receipt w F a)
    (hf : Deletion f L) (hF : Deletion F H) (h₁ : Deletion z H₁) (h₂ : Deletion y H₂) :
    Chipped ρ (locker H₁) (locker H₂) (locker L) (locker H) := by
  have hz i : 0 ≤ f i := (hx i).nonneg
  have hy := leash hw (fun i => ((hx i).paidR).trans (hx i).enrich) hF h₂
  have hZ := leash hw (fun i => ((hx i).paidL).trans (hx i).enrich) hF h₁
  have ht := leash hw (z:=f) (fun i => by rw [abs_of_nonneg (hz _)]; exact (hx _).enrich) hF hf
  intro i
  induction i using Finset.strongInduction with
  | H B ih =>
    by_cases he : Finset.Nonempty B; swap
    · have h0 {f g : Grid J} (hv : Deletion f g) : locker g B=0 := by
        unfold locker; rw [Finset.not_nonempty_iff_eq_empty.mp he,unfold_pieces]; simp [hv.bottom]
      rw [h0 h₁,h0 h₂,h0 hf,h0 hF]; exact Chip.zero ρ
    obtain ⟨x,hb⟩ := he
    have hh := hx.signals (Z₁:=H₁) (Z₂:=H₂) (L:=L) (H:=H) hr B x (fun j hj => ih j
      (Finset.ssubset_iff_subset_ne.mpr ⟨hj.trans (erase_subset ..),fun H => notMem_erase x B (hj (H.symm ▸ hb))⟩))
    have hc := worth hF hw hb
    have h lamp (hz : ∀ i, |lamp i| ≤ signal F H B x i) : crop w lamp < 1 := lt_of_le_of_lt
      (b:=crop w (signal F H B x)) (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((hz i).trans (le_abs_self _))
      (zero_le_one.trans (hw.budget.pos _))) hc
    have ha := sees (fun i=>(hZ i).2.1) hb h₁ hw.budget (h _ (fun i => (hh i).paidL.trans (hh i).enrich))
    have he := sees (fun i=>(hy i).2.1) hb h₂ hw.budget (h _ (fun i => (hh i).paidR.trans (hh i).enrich))
    have hv := sees (fun i=>(ht i).2.1) hb hf hw.budget (h _ (fun i => by rw [abs_of_nonneg (hh i).nonneg]; exact (hh i).enrich))
    rw [ha,he,hv,sees (fun i=>(ht i).1) hb hF hw.budget hc]
    exact hh.shines hr hw.budget (singleton_nonempty _) (signal_pinned _ _ _ x) (signal_pinned _ _ _ x) (signal_pinned _ _ _ x) (signal_pinned _ _ _ x) hc B

variable {ι : Type*} (X : ι → Leaf J)

/-- Chipped on finite *support* tags from the actual, possibly infinite,
address budgets. Summability checked before using `Deletion`. Include the
ordinary hit and legality receipts produced in the very same operation. -/
theorem atomic (hX : ∀ i,(X i).Nonempty) {F f y z : ι → ℝ} {δ : ℝ} (hh : Sufficient X w F a δ)
    (hx : ∀ i,Chip ρ (z i) (y i) (f i) (F i)) (hr : 0≤ρ) :
    let C : Grid J := locker (fumes X (-F))
    let L : Grid J := locker (fumes X (-f))
    let Az : Grid J := fumes X z; let Ay := fumes X y
    Chipped ρ (locker Az) (locker Ay) L C ∧ Applied w Az a C ∧ Applied w Ay a C := by
  intro C L Az Ay
  have H i := hx i
  have hy i : |y i| ≤ F i := ((H i).paidR).trans (H i).enrich
  have hz i : |z i| ≤ F i := ((H i).paidL).trans (H i).enrich
  have hS := supplied_sum hX hh
  have hsf := hS.of_nonneg_of_le (fun i => (H i).nonneg) (fun i => (H i).enrich)
  have hsz : Summable z := Summable.of_norm_bounded hS hz
  have hsy : Summable y := Summable.of_norm_bounded hS hy
  let Z (z : ι → ℝ) (i : Leaf J) := - fresco X z i
  have he (z : ι → ℝ) (i : Leaf J) : Z (-z) i = fresco X z i := by
    unfold Z fresco; rw [← tsum_neg]; apply tsum_congr; intro j; split <;> simp
  refine ⟨prices (w:=w) (a:=a) ?_ hr ?_ (shelf _ hX (-f) hsf.neg) (shelf _ hX (-F) hS.neg) (shelf _ hX z hsz) (shelf _ hX y hsy),
    catalog hX hh z hz,catalog hX hh y hy⟩
  · change Chipped ρ (Z z) (Z y) (Z (-f)) (Z (-F))
    intro i; rw [he,he]; refine ⟨?_,?_,?_,?_⟩
    · unfold Z; rw [abs_neg]; exact attendance hsf (fun i => (H i).paidL) _
    · unfold Z; rw [abs_neg]; exact attendance hsf (fun i => (H i).paidR) _
    all_goals
      let l (g : ι → ℝ) := fun j => if X j=i then g j else 0
      have hl {g : ι → ℝ} (hg : Summable g) : Summable (l g) := Summable.of_norm_bounded hg.norm
        (fun j => by unfold l; split; rfl; rw [norm_zero]; exact norm_nonneg _)
    · unfold fresco; exact (hl hsf).tsum_le_tsum (fun j => by split; exact (H _).enrich; rfl) (hl hS)
    change |- (∑' j,l z j) - -(∑' j,l y j)| ≤ ρ*((∑' j,l F j)-(∑' j,l f j))
    rw [show -(∑' j,l z j) - -(∑' j,l y j) = -((∑' j,l z j)-(∑' j,l y j)) by ring,abs_neg,← (hl hsz).tsum_sub (hl hsy),← (hl hS).tsum_sub (hl hsf),← tsum_mul_left]
    have h := ((hl hsz).sub (hl hsy)).norm
    refine (norm_tsum_le_tsum_norm h).trans (h.tsum_le_tsum ?_ (((hl hS).sub (hl hsf)).mul_left _)); intro j
    change |l z j-l y j| ≤ ρ*(l F j-l f j)
    unfold l; split; exact (H j).swing; simp
  change Receipt w (Z (-F)) a
  rw [funext (he F)]; exact pay_fresco hX hh

end YM.AnalyticBridge.ResetIncome.LogMotion
