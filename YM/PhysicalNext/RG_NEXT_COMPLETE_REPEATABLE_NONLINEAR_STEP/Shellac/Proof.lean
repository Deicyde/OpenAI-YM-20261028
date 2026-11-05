import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Pine
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Trebles
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Tune
/-! # Unrearranged auxiliary charge. Still any α. This is post-Kin. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shellac
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare  Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (A : ChartRatio G)
    (B : BudgetPoint) (ρ : Bid.Dir G c→AxisChart G F) (β α : ℝ) (k : S.Choices) {σ C Λ m M v d a H D u Θ γ : ℝ} {j n : ℕ}
local notation "P" => Uniform.Primary c G
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun (x:Xs)=> represent (tint G _ x))
local notation "f₁" => Lapis.table F k T.up T.high
local notation "μ" => Lapis.orbit F ρ
local notation "ψ" => mist F A T.up
local notation "K" => Lapis.gram F T.up T.high ρ k
local notation "Ω" => solar F A β

def shaft (x : Xs):= f₁ (x,μ x)
def cedar (x:Xs):= mainTerm T.low T.down (V x)-shaft F T ρ k x
def hum (x:Xs):= ψ (x,μ x)+ Lantern.shade (K) x
def shed (x:Xs):= draft α T.down T.low (tint G _ x)-hum F T A ρ k x
lemma merit (x:Xs): harmony T B β α x= Real.log Ω + pigment F T A ρ β k D x + lack F T A B ρ β k D x + β * cedar F T ρ k x + shed F T A ρ α k x:= by
  rw [lines]; unfold lack cedar shed hum coverLog shaft; ring -- order pigment unfold

variable (hV : Golf (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (gram F T.up T.high ρ k) n D u u H)
    (hp:T.down.Bounds T.low σ C Λ) (J : BareRates.pre G σ C n) (hs:1 ≤ M) (ht : (Fintype.card (Uniform.Primary c G):ℝ)≤ M)
include hV


def wood (k:ℕ) (d : ℝ) := clump k (1+d+(1+d)) d
lemma vill (x:Xs) (hx : x∈ball 0 u) : Brush n (wood n H) 1 (shaft F T ρ k) x ∧
    Brush n (wood n H+H) 1 (fun x=> hum F T A ρ k x-Lantern.shade (K) 0) x:= by
  replace hx:=mem_ball_zero_iff.mp hx; let f x:=(x,μ x)
  have hh:=hV.curve x hx; have hp : Brush n (1+H) 1 id x:= by
    let e:= ContinuousLinearMap.id ℝ Xs; refine (Brush.linearB e (hx.le.trans hV.small) (by simp [e,ContinuousLinearMap.norm_id_le]) zero_le_one).climb (le_add_of_nonneg_right hh.nonneg) le_rfl
  have hy: Brush n (1+H+(1+H)) 1 f x := hp.pair (((hh.smaller (show n≤n+2 by omega)).climb (le_add_of_nonneg_left zero_le_one) le_rfl))
  obtain ⟨hf,hq⟩:= hV.color 0 0 (0,x) (norm_zero.trans_le hV.off) (by simp) (show ‖(0:ℝ)‖ < u by simp [hV.pos]) hx
  simp only [Lantern.visit,smul_zero, add_zero] at hf hq
  have hb:= hV.gram x hx |>.2
  refine ⟨composite hy (hf.smaller (by omega)), ((composite hy hq).gathering hb).shimmy (Eventually.of_forall (fun i=> by unfold hum; simp [sub_eq_add_neg, f, add_assoc]))⟩

def kinBill (n:ℕ) {σ C : ℝ} (J : BareRates.pre G σ C n) (Z : Clip) (M H : ℝ) := tollS M n (BareRates.bill J Z)+wood n H
include hp J hs ht
lemma sticks (x:Xs) (hx : x∈ball 0 u) : ContDiffAt ℝ n (cedar F T ρ k) x ∧ ∀ i ≤ n, 0 < i → normJ i (cedar F T ρ k) x ≤ kinBill n J T.low M H := by
  obtain ⟨hf,-,hr,hA,hϘ,-⟩:= bareSocket _ J hp (ball_subset_ball hV.small hx) 0
  have hK:= vill F T A ρ k hV x hx|>.1; let f x:=mainTerm T.low T.down (V x)
  refine ⟨(hf.of_le le_top).sub hK.smooth,fun i hi hv =>?_⟩
  change normJ i (f-shaft F T ρ k) _ ≤ _; unfold normJ; rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hK.smaller hi).smooth]; exact (norm_sub_le ..).trans (add_le_add (ratifyS hs ht hr hA.le hϘ hi hv) ((Brush.offer.1 hK).2 i hi))
lemma unshine (X:Xs) (h:X∈ball 0 u) (hk:ClassicalMatch F T.high T.low T.up T.down ρ) (hv:5≤n) :
    Brush n (kinBill n J T.low M H*u^5) u⁻¹ (off (cedar F T ρ k)) X ∧ fderiv ℝ (cedar F T ρ k) 0=0:= by
  have he x (hx:x∈ball (0:Xs) u):= sticks F T A ρ k hV hp J hs ht x hx
  let f x:=mainTerm T.low T.down (represent (x:Bid.Dir G c)); let g x:=tested F k T.high T.up x (ρ x)
  let Y:= cedar F T ρ k
  let L:= (tint G (Exterior.Body 1 c)).toContinuousLinearMap
  have h0 : (0:Xs)∈ball 0 u:=mem_ball_self hV.pos
  have hz i (hi:i<5): iteratedFDeriv ℝ i Y 0=0:= by
    obtain ⟨ha,hb,h⟩:= hk i (show i≤4 from Nat.le_of_lt_succ hi) k
    have ha' : ContDiffAt ℝ (i:ℕ) g (L 0) := map_zero L ▸ ha.of_le le_top
    have hb' : ContDiffAt ℝ (i:ℕ) f (L 0) := map_zero L ▸ hb.of_le le_top
    change iteratedFDeriv ℝ i (f ∘ L-g ∘ L) 0=_
    rw [iteratedFDeriv_sub_apply (hb'.comp (f:=L) 0 L.contDiff.contDiffAt) (ha'.comp (f:=L) 0 L.contDiff.contDiffAt), linear_pull L hb', linear_pull L ha',map_zero]; change iteratedFDeriv ℝ i g 0 = iteratedFDeriv ℝ i f 0 at h; rw [h,sub_self]
  have hf : off Y=Y:=by
    have ht:= norm_iteratedFDeriv_zero (𝕜:=ℝ) (x:=(0:Xs)) (f:=Y); rw [hz 0 (by decide),norm_zero,eq_comm,norm_eq_zero] at ht; funext i; simp [off,ht]
  change Brush n _ _ (off Y) _ ∧ fderiv ℝ Y 0=0
  have hx:= he 0 h0
  constructor
  · rw [hf]; have hg:= pools (b:=0) hV.pos hV.small hv (show 0 ≤ kinBill n J T.low M H from le_trans (norm_nonneg _) (hx.2 5 hv (by decide))) (le_refl 0) (fun i hi=> (he i hi).1) (fun i hi hj x hx=> (he x hx).2 i hj (by omega)) (fun i hi=> by unfold normJ; rw [hz i hi,norm_zero,zero_mul]) _ h
    rwa [mul_zero,add_zero] at hg
  ext1 i; have hh := congr_arg (fun M : Xs [×(1:ℕ)]→L[ℝ] ℝ => M ![i]) (hz 1 (by decide)); rw [iteratedFDeriv_one_apply] at hh; exact hh
end YM.PhysicalNext.Repeat.Shellac
