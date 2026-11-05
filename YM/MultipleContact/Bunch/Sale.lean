import YM.MultipleContact.Matching.Trade
import YM.MultipleContact.Bunch.Meter
import YM.MergeProof.North.Bonus
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
open Matching
variable {α:Type}[Fintype α][DecidableEq α][Inhabited α]
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D:ℕ)(t:α→ℕ)(h:ℝ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
def loss (h:ℝ)(ρsf:ℝ)(T:∀ b:α,C.label (t b)) (x:α → Cover)(v:C.label D):Config G (C.side N p)→ℂ:= fun q=>
    (↑(ρsf^h):ℂ)*(∏ b:α,C.O N p (T b) (Cells.location C.S j N p (x b)) q)-C.O N p v 0 q
def expenditure (b:α) (ρ:ℝ) : ℝ:=let e:=plumR C (t b) ρ j; if b=default then e/(fuga C.path.levels (m+1))^h else e
lemma exp_pos {ρ:ℝ}(hr:0<ρ) :∀i:α, 0< expenditure C j m t h i ρ :=by
   intro i; unfold expenditure; split
   · exact div_pos (stockpit _ _ _ _ hr) (Real.rpow_pos_of_pos (fugap ..) _)
   exact stockpit _ _ _ _ hr
variable (x:α → Cover)(T:∀ b:α,C.label (t b)) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (hj:j<N)
local notation "sub!"=> loss C N p j D t h rad T x
local notation "τ"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hj.le)))) 0
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (lamp:Side)(b a e X η c:ℝ)
local notation "A"=> fun i=> expenditure C j m t h i b
variable (hT:∀ i,(C.labels.level (t i)).coeffSize (T i) ≤ b)
local notation "ℓ"=> wrap (C.side j p) ∘ x
local notation "L"=> marks C J j p ℓ
local notation "O"=> Cells.location C.S j N p ∘ x
local notation "W'"=> basket C.path.levels (lamp*C.S.block m) j (m+1) δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "B!"=> ((P').B^2+1+2*Matching.patch C.path.levels (lamp*C.S.block m) (m+1))
include hh hp hR hT
lemma vendor' (hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(hT':∀ i:α,C.ref (t i) ≤ j)(hx₀:x default=0)(hW:∀ i i':α,i≠i'→ rad/16≤ ‖C.S.place ((ℓ) i-(ℓ) i')‖)(hw':∀i:α,‖C.S.place ((ℓ) i)‖ ≤4*topZone C.path.levels (lamp*C.S.block m) (m+1))(he:∀i,Interior ((τ).chamber 0) (C.O N p (T i) ((O) i)))(he':∀ z:C.label D, Interior ((τ).chamber 0) (C.O N p z 0))
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ δ H')(hg:BatchRibbons.Thor (slot:=α) C.path δ r μ σ χ i₀)(hα:division C (α:=α) (r:=r) (δ:=χ) i₀ Y')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ: B! ≤ (C.S.toDepth (le_trans hf (le_trans hk (m.le_succ))) p).count.val)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   ∃ z:C.label D,Next.UVStress.quota C D m N p z ≤ 2*e∧ Interior ((τ).chamber 0) (sub! z) ∧ (τ).rootTest (C.beta N p) (sub! z) ≤ 2*(stakes C J k / c):=by
   let R'(i:α):ℂ:=if i=default then (↑(rad^h):ℂ) else 1
   let U i:=R' i • C.O N p (T i) ((O) i)
   have hprod: ∏ i:α,R' i=(↑(rad^h):ℂ):= (prod_eq_single (s:=univ) (f:=R') default (by intro i _ h; change (if i=default then _ else _) = 1; exact if_neg h) (by simp)).trans (if_pos rfl)
   have hA' z: (sub! z)=(∏ i:α,U i)-C.O N p z 0:=by funext v; simp only [loss,Pi.sub_apply,Finset.prod_apply,U,Pi.smul_apply, smul_eq_mul,prod_mul_distrib,hprod,Function.comp_apply]
   have hΔ := hI.trans m.le_succ; let t':Π i:α,C.label (t i):= fun i=>R' i • T i
   have hX (i:α): U i= C.O N p (t' i) (L N (0,i)):= by
      unfold marks
      rw [biteT C J j p N ((ℓ) i) (by omega), vect C j p N ((ℓ) i) hj.le, show (C.S.toDepth hj.le p).embed ((ℓ) i)= (O) i from by dsimp [Function.comp]; rw [Cells.location,dif_pos hj.le]]
      exact ((C.linearO N p (t i) ((O) i)).mk' _ |>.map_smul (R' i) (T i)).symm
   have hμ(i:α): Interior ((τ).chamber 0) (U i):= (he _).scale _
   have hv(i:α): (A) i * Spindle.paid C (t i) j N p (t' i) ≤ fly C.path.levels (t i) j :=by
      have haF:=paid_new C N p j (t i) hh (T i) b hb (hT i) (hT' i) hj
      by_cases hi:i=default
      · change expenditure C j m t h i b * Spindle.paid C (t i) j N p (R' i • T i) ≤ _; simp only [R',if_pos hi]; rw [paid_scale C N p j _ hh hp (hT' i) _ _ hj.le,show ‖(↑(rad^h):ℂ)‖=(rad)^h from by rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos (fugap C m) h|>.le)],expenditure,if_pos hi,←mul_assoc,div_mul_cancel₀ _ (Real.rpow_pos_of_pos (fugap _ _) _|>.ne')]; exact haF
      convert haF using 1; simp [expenditure,t',R',hi]
   subst X η; obtain ⟨z,hz,hU⟩:= mutationWide C N m p D J k lamp c A ℓ hf hk hj hm t t' hh hp hI hR r₀ hx hK hT' hv (exp_pos C j m t h hb) hR' hΩ (by change wrap _ (x _) = _; rw [hx₀]; exact (wrap _).map_zero) hW hw' U (fun i=>by rw [hX i]; exact (itemT C N p _ hh (t' i) (L N (0,i))).symm) (fun i=> by rw [hX i]; exact C.continuousO ..) hμ he' hg (hα _ hΔ|>.1) (hα _ hΔ|>.2.1) (hr.brings m hI N p _|>.2) (hr.dollars m hI) (hr.crisp j (by omega)) (fun i he hi=>hr.brings i (by omega) N p (hi.trans hj)|>.1) (hα _ hΔ|>.2.2.1) (hα _ hΔ|>.2.2.2) hw hL hV hA hC
   have hp₀(ms: Finset α): Interior ((τ).chamber 0) (ms.prod U):=by
       induction ms using Finset.induction with
       | empty=> rw [prod_empty]; exact Interior.constant _ (1:ℂ)
       | insert i ms hi ih=> rw [prod_insert hi]; exact (hμ i).times ih
   refine ⟨z,hz,?_⟩; rw [hA' z]; exact ⟨Next.UVStress.minus (hp₀ _) (he' _),hU⟩
end
end YM.MultipleContact.Bunching
