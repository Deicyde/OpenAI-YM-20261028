import YM.RemainderComparison.Lyric.Forecast
import YM.MergeProof.Appl
import YM.MergeProof.Steps
import YM.MergeProof.Limb

/-! # Actual forced budget with score-return at a finite query horizon

Don't divide the formal long charge by a presumed exponential budget; charge
on the genuine forced labels *after* return to this swing's coarse point.
Includes any attached partner holding evaluations regardless of marker content.
Payload angular derivatives on Aqua budget, but not here on HARD family
(which never undergoes field-angle differentiation here). Marker derivatives
from switching with EXACT assignment counted. The zero includes at masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Daisy
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
open Height AnalyticBridge.VerifiedReset
variable {δ Gp:ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "λ₀" => mulScale ((tax G L x)⁻¹) l
local notation "F'" => Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)

open PhysicalNext.Repeat Mallow Merge.Photo Progress.DirectedRecipe
open Ovens
variable {R':Rep G f} (Y : Cash W x μ L Q o C T R') (D:Match.Alliance Y H 1 0) (V:BudgetPoint)
variable (E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ) (hx: V.threshold=Pressure.temp x)(he:V.B=radiusB x)
local notation "VB"=> Refrain.read Y D χ E t'
local notation "K₀"=> Palette.shoot M H χ λ₀ Y D

def cod (i:ℕ)(U:Config G c)(p:Finset ι):ℝ:= tax G L x^p.card * Switch.jet (fun t v=> Palette.shoot M H χ λ₀ Y D t v i U) p

variable (hp: Premium Q L x a μ L' B j n k s J m Gp) (hl : YM.Merge.Palette.Plot M H (mulScale ((tax G L x)⁻¹) l))
include hp hl N hx he
lemma routine : Motion.Pays VB V K₀ F' a:=by
   constructor
   · intro j; unfold Palette.shoot; rw [show (ways λ₀ 0 j)=(fun _=>0) from (by ext; simp [Palette.ways]),Palette.at0 (t':=t') (E:=E)]
   · intro z w h; exact Palette.earned M H χ Y D V E t' hx (ways λ₀ z w)
   exact Palette.ready M H χ λ₀ hl hp.visit N.balance Y D V E t' he

lemma soundK : ∀ (i:ℕ)(p: Finset ι),
    let f U:=cod M H χ l Y D i U p
    let F:=(VB).forced i
    Lattice.GaugeInvariant f ∧ UsesFinal V.threshold F.support f ∧ Measurable f ∧ ∀ U,f U≠0 → F.eligible V.threshold U ∧
         ∀ j∈p,(M j).crest.image S.ratio.parent ⊆ F.support:=by
   let K:=Palette.shoot M H χ λ₀ Y D
   have h:=routine M H χ l N Y D V E t' hx he hp hl
   intro i p f F
   obtain ⟨hd,hM,hk,hY⟩:=h.rear i p
   refine ⟨fun t U=> congr_arg (tax G L x^p.card*·) (hk t U),fun U V hZ hp=>congr_arg (tax G L x^p.card*·) (hd U V hZ hp), measurable_const.mul hM,fun U hu=>?_⟩
   have ht:= right_ne_zero_of_mul hu
   refine ⟨hY U ht,fun j hj y hy=>?_⟩
   -- If spends on marker j, its support contains the root. Use erasure independence.
   by_contra hm
   obtain ⟨c,hc,-⟩:=h.bought
   apply ht
   refine Switch.jet_erase ((hc i |>.works U).choose_spec) ?_ p hj
   intro t _ s
   by_cases hv:i∈Set.range (Refrain.visa Y D); swap
   · unfold Palette.shoot Palette.shootK; rw [blank _ _ hv]; exact congr_fun (blank _ _ hv).symm U
   obtain ⟨z,rfl⟩:=hv
   unfold Palette.shoot Palette.shootK; simp_rw [stuffed]
   exact Palette.limbs M H χ λ₀ U j y hy _ (fun h=>hm ((Refrain.admitted Y D z).1.symm ▸ h)) t s

lemma funded (hb : inBand (betaF G x L) R.beta) :
    ∃ c:ℕ  → Finset ι→ℝ, (∀ i,∀ p,0 ≤ c i p ∧ ∀ U, ‖cod M H χ l Y D i U p‖ ≤ c i p) ∧
        Ac.Hit (fun i=>((VB).forced i).support) V.B (fun i=>∑ p:Finset ι, if p.card≤ k then c i p else 0) a ((unitK x)^4*(gStep R.beta)^s):=by
   have h := routine M H χ l N Y D V E t' hx he hp hl
   obtain ⟨g,hg,hK⟩:= h.bought
   choose b hb' hB hM using hg
   let C (i:ℕ)(p:Finset ι):=tax G L x^p.card*b i p
   have ht: 1≤ tax G L x:= one_le_pow₀ hp.roll
   have hu: 0 < tax G L x:= zero_lt_one.trans_le ht
   have hz i p:0 ≤ C i p:=mul_nonneg (by positivity) (hb' i p)
   refine ⟨C,fun i p=> ⟨hz i p,fun U=>?_⟩,fun y=>?_⟩
   · obtain ⟨f,HX,h⟩:=hM i U; unfold cod; rw [HX.exact,norm_mul,Real.norm_of_nonneg (le_of_lt (pow_pos hu _))]; exact mul_le_mul_of_nonneg_left (h 0 ⟨le_rfl,zero_le_one⟩ p) (by positivity)
   -- x shadow; avoid
   have h := budget_scale (show 0 ≤ tax G L x^k from by positivity) (hK y)
   refine budget_loosen (budget_mono h ?_ ?_) (hp.forced R.beta hb)
   · intro i; dsimp only; split; next hh=> exact mul_nonneg (sum_nonneg fun i _=> by split; exact hz ..; exact le_rfl) (Real.exp_pos _).le
     next=>rfl
   intro i; dsimp only; split; next h=>
      rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right (le_trans ?_ (mul_le_mul_of_nonneg_left (hB _) (pow_nonneg hu.le _))) (Real.exp_pos _).le
      unfold Switch.high; rw [Finset.mul_sum]; refine sum_le_sum ?_; intro v _; split; next hp=> exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht hp) (hb' ..)
      next=> exact mul_nonneg (by positivity) (hb' ..)
   rw [mul_zero]
end YM.RemainderComparison.Lyric
