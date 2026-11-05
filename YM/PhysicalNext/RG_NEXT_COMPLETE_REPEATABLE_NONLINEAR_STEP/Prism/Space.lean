import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Sails
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Sepal

/-! # Cluster E singleton integrand price at paid Gaussian Compact Support

Conditional on at-this-argument occupancy costs (derived post-L).
Do not truncate O.Frame. On the tube where every centered z toll fits small cap
 one may pay BOTH old E factor and its transported density discrepancy separately.
 Else must pay entire near-weight to tails; includes positivity for both normalizers.
 Positions typed at single reference X. Best small-region uses same τ, not a
 separate stencil whose head lies in X-dependent directions. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Prism
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E→ Config G c} {p : E} {n : ℕ} {v N Q K δ τ L : ℝ}
variable (X : Coat T F) {I : Type} {Y : Support c} (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) {bt : BudgetPoint} (D : Record)
  (h : Intake P T X.x R) (hp : Scrim X a) {ζ d A t : ℝ} (ht : Canary G d A) (u : Prices G I)

structure Score (r d ζ δ N Q : ℝ) (A : Anthem n) (Z : E→ Config G c) (p:E) : Prop where
  at_z : Z p=X.V
  geom : (Fintype.card (I×G.ColorIndex):ℝ) ≤ N
  basis : 0 ≤ Q
  delta : 0≤δ
  income : r * Q ≤ 1
  commits : Holds (Malachite.lamp6 X a ∘ Z) p Q n
  adjust : Holds (Malachite.lamp9 X a ∘ Z) p Q n
  earns : ∀ᶠ x in 𝓝 p, (lamp6 X a (Z x)).PosDef ∧ (lamp9 X a (Z x)).PosDef
  invs : EdgePay ((lamp9 X a ∘ Z)-(lamp6 X a ∘ Z)) n δ 1 p
  huy : gear δ Q N n ≤ 1
  huy1 : sail δ Q N n ≤ 1/2
  huy2 : plumage A N Q δ ≤ 1
  rod : Brush n Q 1 (fun x=> pulse X (Z x) a u d R.beta) p
  cods : Moves p n (fun x=> reading6 X (Z x) a u d R.beta) Q
  cols : Moves p n (fun x=> reading9 X (Z x) a u q b d R.beta) Q
  shift : Moves p n (fun x=> reading6 X (Z x) a u d R.beta-reading9 X (Z x) a u q b d R.beta) δ
  cover : Brush n Q 1 (fun x=> coin X i R a d R.beta ζ (Z x) u) p
  veil : Brush n Q 1 (fun x=> Baffle.veil X a q κ b D R.p d R.beta u (Z x)) p

variable (A' : Anthem n) (hs : Score X i R a q κ b D u K d ζ δ N Q A' Z p)

def incomeB (A : Anthem n) (N Q : ℝ) := Q*Bpower A N Q*(1+(1+1))^n
def incomeD (A : Anthem n) (N Q δ : ℝ) := Q*tensor0 A δ N Q*(1+(1+1))^n

include h ht hs
lemma arrows : Brush n (incomeB A' N Q) 1 (fun x=> tax6 X i R a d R.beta (Z x) u) p ∧
    Brush n (incomeD A' N Q δ) 1 (fun x=> tax9 X i R a q b d R.beta (Z x) u - tax6 X i R a d R.beta (Z x) u) p := by
  let I x:= reading6 X (Z x) a u d R.beta; let J x:=reading9 X (Z x) a u q b d R.beta
  have hx (Z : (E→ Config G c)) (p) (hZ:Z p=X.V): reading6 X (Z p) a u d R.beta=u:= by unfold reading6; rw [hZ]; exact fast_zero X a ht h.positive u
  have hL : I p=u:=hx _ _ hs.at_z
  let L:= Malachite.notice X ∘ a.colorSeat G
  let R' x:=lamp6 X a (Z x); let M x:= lamp9 X a (Z x); let g x:= Density.replace (R' x) (R' p) (I x-I p) (I p); let k x:= Density.replace (M x) (R' p) (J x-I p) (I p)
  have hh : Brush n (incomeB A' N Q) 1 (fun x => pulse X (Z x) a u d R.beta*g x) p := (hs.rod.paints (preliminary hs.commits hs.geom hs.basis L (hs.earns.mono fun _ h=> h.1) hs.cods A')).trim
  have hp : Brush n (incomeD A' N Q δ) 1 (fun x=> pulse X (Z x) a u d R.beta*(k x - g x)) p :=
    (hs.rod.paints (proceeds0 hs.commits hs.adjust hs.invs hs.geom hs.delta hs.basis L (hs.earns.mono fun _ h=> h.1) (hs.earns.mono fun _ h=> h.2)
      hs.cods hs.cols hs.shift A' hs.huy hs.huy1 hs.huy2)).trim
  have hq x : tax6 X i R a d R.beta (Z x) u = pulse X (Z x) a u d R.beta*g x:= by
    unfold g tax6 reads_map R'; rw [hL,add_zero,hs.at_z]; rfl
  refine ⟨hh.shimmy (Eventually.of_forall hq),hp.shimmy (Eventually.of_forall fun x=> ?_)⟩
  dsimp only; rw [hq,mul_sub]; unfold k tax9 reads_map R'; rw [hL,hs.at_z]; rfl
variable (hτ : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) τ) (hk : τ ≤ K)
include hτ hk

def altitude (A : Anthem n) (N Q δ : ℝ) := (incomeB A N Q * (A.expE*Q) + (incomeD A N Q δ+incomeB A N Q)*Q)*(1+(1+1))^n
lemma high : Brush n (τ * altitude A' N Q δ) 1 (fun x=> tally X i R a q κ b D Z d ζ x u) p := by
  obtain ⟨hg,hh⟩:= arrows X i R a q κ b D h ht u A' hs
  let B x:= tax6 X i R a d R.beta (Z x) u; let L x:=tax9 X i R a q b d R.beta (Z x) u
  have hl: Brush n (incomeD A' N Q δ + incomeB A' N Q) 1 L p :=
    (hh.gathering hg).shimmy (Eventually.of_forall fun _=> (sub_add_cancel ..).symm)
  let U:= owe X i R a u; let K₀ x:= Baffle.veil X a q κ b D R.p d R.beta u (Z x); let F x:= Real.exp (-(U*coin X i R a d R.beta ζ (Z x) u))-1
  have hU : ‖U‖≤τ:= owing X i R a hτ u
  have hf : Brush n (A'.expE*(τ*Q)) 1 F p := A'.cmd E p _ _ _ (((hs.cover.smul U).opposite).climb
    (mul_le_mul_of_nonneg_right hU hs.basis) le_rfl) ((mul_le_mul_of_nonneg_right hk hs.basis).trans hs.income)
  have hc := (hg.paints hf).gathering (hl.paints ((hs.veil.smul U).climb (mul_le_mul_of_nonneg_right hU hs.basis) le_rfl))
  refine hc.trim |>.climb (le_of_eq (by unfold altitude; ring)) le_rfl|>.shimmy (Eventually.of_forall fun x=>?_)
  change B x*(Real.exp (-U*_)-1)+ L x*(K₀ x*U)=B x*F x+ L x*(U*K₀ x); unfold F; rw [neg_mul,mul_comm U (K₀ _)] -- edit

def ground0 (A : Anthem n) (N Q δ K : ℝ) := K*incomeB A N Q + incomeD A N Q δ
lemma low (hK : K ≤ 1) (he : ∀ᶠ x in 𝓝 p, coin X i R a d R.beta ζ (Z x) u=1 ∧ Baffle.veil X a q κ b D R.p d R.beta u (Z x)=1) :
    Brush n (τ * ground0 A' N Q δ K) 1 (fun x=> tally X i R a q κ b D Z d ζ x u) p := by
  obtain ⟨hb,hh⟩:= arrows X i R a q κ b D h ht u A' hs
  let w:= owe X i R a u; let C:= Real.exp (-w)-1+w
  have hW: ‖w‖≤τ:= owing X i R a hτ u
  have hC: ‖C‖≤τ*K := by
    have ht: ‖-w‖ ≤ (1:ℝ):= by rw [norm_neg]; exact hW.trans (hk.trans hK)
    have hv:=Real.norm_exp_sub_one_sub_id_le ht
    rw [sub_neg_eq_add,norm_neg,sq] at hv
    exact hv.trans (mul_le_mul hW (hW.trans hk) (norm_nonneg _) (hτ.1))
  refine (((hb.smul C).climb (mul_le_mul_of_nonneg_right hC hb.nonneg) le_rfl).gathering
    ((hh.smul w).climb (mul_le_mul_of_nonneg_right hW hh.nonneg) le_rfl)).climb (le_of_eq (by unfold ground0; ring)) le_rfl|>.shimmy (he.mono fun x hx=>?_)
  unfold Baffle.tally; change tax6 X i R a d R.beta (Z x) u *(Real.exp (-w * coin X i R a _ _ _ (Z x) u)-1) + tax9 X i R a q b d R.beta (Z x) u *(Baffle.veil X a q κ b D R.p d R.beta u (Z x)*w)= _
  rw [hx.1,hx.2]; unfold C; simp only [mul_one,one_mul,smul_eq_mul]; ring
end YM.PhysicalNext.Repeat.Prism
