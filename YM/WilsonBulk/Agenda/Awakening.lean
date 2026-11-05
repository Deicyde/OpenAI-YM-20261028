import YM.WilsonBulk.Agenda.Market

/-! # Is Year.J. Land granted? yes after lighting:
  require ONLY after-lit & postBlock **numerical** thresholds issued by preflight & post pipeline;
  inputs particular H via Model/spine. Quantifies over reconstruction parameter `c:E`, powers moment request
  `u,d`, offset domain 0, Canonical Levels & sizes, source/color group. No conditional-masked bound assumed!!

  Feasibility of paying these numerical thresholds by strengthened calendars is separate, later attachment.
  (UV family inclusion not automatic). This doesn't assert that any Λ can pay ``Θ stage prices'' on arbitrary
  spans using fixed epoch independent of Λ; read Budgeted precisely (polynomial power on Y_k(W) at actual step using parameters
  reachable in fixed P)).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {F : MapPrices} {i j k n m ℓ N N' E : ℕ} {x a b p σ θ μ w C t δ : ℝ} {L : Side}
variable {T : historyModel A i} {S : Lit G A.clock.kernel F}
variable {M : Motions A}
-- user numerical heights C≥... 
def budgetFit (c : ℝ) (d : ℕ) (x : ℝ) := c*x^d
def Develop (S : Lit G A.clock.kernel F) (M : Motions A) (ℓ k E : ℕ) (x a c : ℝ) (d : ℕ) :=
    Sized S ℓ a E ∧ 1≤x ∧ ∀ i≥ℓ, postTranche S (M.tree i) M.j (stage A i) E a ≤ budgetFit c d (age A.S k x i)
namespace Develop
variable {c : ℝ} {d r : ℕ} (h : Develop S M ℓ k E x a c d)
include h
lemma cost (hi : ℓ ≤ i) : Charge S (M.tree i) M.j (stage A i) E (budgetFit c d (age A.S k x i)):= post_force (h.1 i hi).2 (A.blocks i 0).branches (h.2.2 i hi)
lemma budget_positive (i : ℕ) (hi : ℓ ≤ i) : 1≤budgetFit c d (age A.S k x i):= by obtain ⟨w,h⟩:= h.cost hi; exact h.warm.height
lemma ages (i : ℕ) : 1 ≤ age A.S k x i := h.2.1.trans (age_ge ..)
lemma neighbor (hi : ℓ ≤ i) : age A.S k x (i+1) ≤ age A.S k x i+ budgetFit c d (age A.S k x i) := (age_fade ..).trans (add_le_add_right (RequestLead (h.cost hi)) _)
lemma k_hess (hp : H.Suffices F) (hc : 0≤c) (hb : b<a) (hm : m≤N) (ht : ℓ ≤ m) (hf : N≤N') :
    (minusRows (flat H N m) (flat H N' m)).strip (lureFlat A F m) ((c+c)*momentWeight (a-b) d*age A.S k x m^d*damp A.S b m N) :=
  trim (c+c) a _ (admit_request h.1) hp hp h.2.1 (add_nonneg hc hc) hb hm ht hf (by rw [add_mul]; exact add_le_add (FlatCash (h.cost (ht.trans hm))) (FlatCash (h.cost (ht.trans hm))))
lemma width_ready (hh : ℓ ≤ i) : (S.width E (stage A i))⁻¹ ≤ budgetFit c d (age A.S k x i):= WidthRate (h.cost hh)
end Develop

structure Fund where
 a : ℝ
 b : ℝ
 c : ℝ
 d : ℕ
 positive : a < 1
 mid : b < a
 up : 0 < b
 price : 0≤c
namespace Fund
variable (T : Fund)
abbrev coverage (y : ℝ) := budgetFit T.c T.d y
def tube (y : ℝ) := (T.c+T.c)*momentWeight (T.a-T.b) T.d*y^T.d
def bones (y : ℝ) := T.tube (y+T.coverage y)
def elevation (y : ℝ) := T.coverage y+T.coverage y*T.bones y
lemma coverage_tag : Tariff T.coverage:= (Tariff.const T.c T.price).prod (Tariff.one.powers _)
lemma dew : Tariff T.tube := (Tariff.const _ (mul_nonneg (add_nonneg T.price T.price) (momentWeight_nonneg (sub_nonneg.mpr T.mid.le) _))).prod (Tariff.one.powers _)
lemma price_bones : Tariff T.bones:= T.dew.composed (Tariff.one.add T.coverage_tag)
lemma price_sky : Tariff T.elevation:= T.coverage_tag.add (T.coverage_tag.prod T.price_bones)
lemma sky_ge {x : ℝ} (hx : 0≤x): T.coverage x≤ T.elevation x:= le_add_of_nonneg_right ((T.coverage_tag.prod T.price_bones).1 x hx)
-- specialization: Ωpre, μpre. witness naming σ(E). no assumed norm contracts.

def publicity (V : Horizon A) (P : Lit G A.clock.kernel F) (w : Motions A) (h : V.Suffices F) (hp : LocalRatio w.j) (T : Fund) (E : ℕ) : Shop V :=
  ⟨F,w,h,hp,E,(fun i=>P.width E (stage A i)), (fun i=>P.gamma (stage A (i+1))), T.a,T.b,T.positive,T.up,T.mid,T.elevation,T.price_sky⟩
-- issue
variable (hV : H.Suffices F) (hS : LocalRatio M.j)
lemma developed (hd : Develop S M ℓ k E x T.a T.c T.d) : (publicity H S M hV hS T E).Land ℓ k x := by
  let Q:=publicity H S M hV hS T E; let Y:= age A.S k x; have he (i : ℕ) : T.coverage (Y i) ≤ T.elevation (Y i):= T.sky_ge (zero_le_one.trans (hd.ages _)); let K i:=T.bones (Y i)
  have hH (i N : ℕ) (hi : ℓ ≤ i) (hp : i < N) : Tarmac Q.motion.k Q.motion.j (Q.motion.tree i) (H.H N (i+1)) (H.H N i) (H.towers N i).A0 (Q.σ (i+1)) (Q.σ i) (Q.μ i) (Q.rank₂ i) (Q.xDeep i) E (Q.book (Y i)):= ((Charges.charge_kin (hd.cost hi) hS hV hp (hd.1 i hi).1 M.k).more (he _)) -- import
  have hK (i : ℕ) : 0≤K i:= T.price_bones.1 _ (zero_le_one.trans (hd.ages i))
  have ht (i : ℕ) : T.coverage (Y i)*K i ≤ T.elevation (Y i):= le_add_of_nonneg_left (T.coverage_tag.1 _ (zero_le_one.trans (hd.ages i)))
  have hx (N N' i : ℕ) (hi : ℓ ≤ i) (hh : i≤N) (hN : N ≤ N') :
      (minusRows (flat H N i) (flat H N' i)).strip (Q.σ i) (Q.fall i N*K i) := by
    refine strip_mono (hd.k_hess hV T.price T.mid hh hi hN) ((S.lighter E _).2.trans (min_le_right ..)) ?_; rw [mul_comm (Q.fall ..)]; apply mul_le_mul_of_nonneg_right (T.dew.2.1 _ _ (zero_le_one.trans (hd.ages i)) ?_) (damp_pos ..).le; exact le_add_of_nonneg_right (zero_le_one.trans (hd.budget_positive i hi)) -- maybe parse
  refine ⟨hd.2.1,fun i hi=>(RequestLead (hd.cost hi)).trans (he i),fun i N N' hi he' hf=>?_, hH,fun i N N' hi hN hk=>?_, fun i hi n hn hm=>?_⟩
  · obtain ⟨w,hw⟩:= hd.cost hi; have h' (N : ℕ) (hp : i≤N) : Within (lawn _) (Q.σ i) (Q.book (Y i)) (onTop G (H.H N i)) := (onTop_cost G (canonical_strip hV hp)).mono (((S.lighter E (stage A i)).2.trans (min_le_right ..)).trans (min_le_left ..)) (hw.warm.ruby.trans (he i))
    have hp : 0≤ Q.fall i N:= (damp_pos ..).le
    refine ⟨hp,h' N he', h' _ (he'.trans hf), (onTop_delta _ _ (hx N N' i hi he' hf)).mono le_rfl ?_⟩
    change oxidize G _ ≤ Q.fall i N*T.elevation (Y i)
    rw [show oxidize G (Q.fall i N*K i)=Q.fall i N*(oxidize G 1 * K i) by unfold oxidize; ring]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hw.pricing.2.2.2.2.2 (hK i)).trans (ht _)) hp
  · have hv : (minusRows (flat H N (i+1)) (flat H N' (i+1))).strip (S.gamma (stage A (i+1))) (Q.fall (i+1) N*K i):= by
       apply strip_mono (hd.k_hess hV T.price T.mid (show i+1≤N by omega) (by omega) hk) (S.awake _) ?_; rw [mul_comm (Q.fall ..)]; exact mul_le_mul_of_nonneg_right (T.dew.2.1 _ _ (zero_le_one.trans (hd.ages (i+1))) (hd.neighbor hi)) (damp_pos ..).le
    have hC : Q.fall i N*K i ≤ Q.fall (i+1) N*K i:= mul_le_mul_of_nonneg_right (damp_due A.S T.up.le) (hK i); exact (Charges.turnstile hV (hd.cost hi) (hK i) (show 0≤Q.fall (i+1) N from (damp_pos ..).le) hN (by omega) hv (strip_mono (hx N N' i hi hN.le hk) le_rfl hC)).more (ht i)
  change Q.rDeep i * Q.cDeep i n ≤ damp A.S T.a i (i+1); rw [damp_succ, Shop.cDeep, turbulent,← mul_div_assoc]; exact (hd.1 i hi).2.climb n hn hm
end Fund
end YM.WilsonBulk.Parapet.Agenda
