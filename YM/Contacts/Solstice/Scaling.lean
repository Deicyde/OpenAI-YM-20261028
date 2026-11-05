import YM.Contacts.Solstice.Solo
/-!
# Normal scaling on full contact distributions, all labels and weights

Allow tests of `H.scale⁻¹*normal` supported on any fixed compact set in the stage frame. May vary
center continuously, if the stage also records that variable. `Run` makes root `r` the only scale
for this OPE reading; the subtraction length may be fixed or a different scale or `r`, constrained
as on this family of stages. No support annuli requirements for any `Dust` in this file. Allows
also total or partial annuli as in the punctured consequences. Costs here prior to PT alignment.
Scaling degree uses upper powers, not a fixed minimal such exponent. Cover sufficiently small
clearance and regime qualifications by bounding any family of this form, not necessarily admitting
a regular variation through the route.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I J X: Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k}

local notation "GN" => Normal.Group k
local notation "Z'" => Z.sector.derivatives
variable (hg : g.Nonempty)
variable (r : Route P (root g) Unit W)
local notation "K!" => normalOn P g
/-- standard normal rescaling for relative position. -/
abbrev scale (w : W):= r.R g w
def barrel (w : W) := resize (normalOn P g) (scale r w) (r.valid g w).1.ne'
def Run := r.frame = barrel r

-- usual normalization R^(-N) (allows degenerate measures/tests as above) -- complex scalars.
def Jacobian (g : GN) := (System.relative g:ℝ)
def factor (w : W): ℝ:= scale r w ^ (-(Jacobian g))
lemma factor_pos (w : W): 0< factor r w:= Real.rpow_pos_of_pos (r.valid ..).1 _
def normal_test (w : W)(f : SmoothTests E): SmoothTests E := (factor r w : ℂ) • composed (barrel r w).symm f
lemma scaled (w f x) : (normal_test r w f).val x= factor r w • f.val (slide (normalOn P g) (scale r w)⁻¹ x):= by rw [RCLike.real_smul_eq_coe_mul (K:=ℂ)]; rfl
private lemma replace_in (w : W){f : SmoothTests E} : (composed (barrel r w) (normal_test r w f)).val= fun x=> factor r w • f.val x:= by
  funext x; simp_rw [show (composed (barrel r w) (normal_test r w f)).val x= (normal_test r w f).val (barrel r w x) from rfl,scaled,show slide (normalOn P g) (scale r w)⁻¹ _=x from (barrel r w).symm_apply_apply x]
lemma pays (H : Run r) (w:W){p : SmoothTests E}{n : ℕ}{C : ℝ} (h : Jet n univ p.val C): Jet n univ (composed (r.frame w) (normal_test r w p)).val (factor r w * C):= by
   rw [H,replace_in]; exact (h.scalar (infSmooth p) _).mono (by rw [abs_of_pos (factor_pos ..)])
lemma stage_test (w : W)(p : SmoothTests E)(h : tsupport p.val ⊆ (barrel r w) ⁻¹' r.stage w): tsupport (normal_test r w p).val ⊆ r.stage w:= by
   refine closure_minimal (fun x hx=>?_) (r.closedStage w); obtain ⟨y,rfl⟩:= (barrel r w).surjective x; refine h (subset_closure ?_); have he:=congr_fun (replace_in (f:=p) r w) y; change (normal_test r w p).val (barrel r w y)=_ at he; exact fun h=> hx (he.trans (by rw [show p.val y=0 from h,smul_zero]))

include hg
lemma travel (w) (H : Run r) : basic (r.frame w)= (scale r w)^(Jacobian g):= by
   rw [H]
   unfold basic barrel; rw [show (resize (normalOn P g) (scale r w) _).toLinearEquiv.toLinearMap=(slide (normalOn P g) (scale r w)).toLinearMap from rfl,slide_det, dimension_normal hg (r.displaysNormals g (clasp g hg).property)]; rw [abs_of_pos (pow_pos (r.valid ..).1 _), Jacobian, Real.rpow_natCast]; rfl
lemma statement {ε : ℝ} {d : Fin k→ℕ} (w : W)(H : Run r) {B : W→ℝ}{u:ℝ}(hb : B w=scale r w ^ u) : factor r w*r.bag d B w ε = scale r w ^ (u - arityRate d g - ε):=by
    unfold factor bag face surcharges; rw [travel hg r _ H,one_set _ rfl hg,Finset.prod_singleton,hb,Fintype.prod_unique]; let R:=scale r w; have hn:(0:ℝ)<R:= (r.valid ..).1
    have he (v:Unit): r.diameter v w=scale r w:= by rw [scale, Route.R]
    rw [he]; change R^(-(Jacobian g)) * (R^Jacobian g * R^(-(arityRate d g))* R^u * R^(-ε))=R^ (u-arityRate d g-ε); rw [← mul_assoc,← mul_assoc,← mul_assoc, adds hn,neg_add_cancel,Real.rpow_zero,one_mul,adds hn, adds hn]; congr 1; ring
variable (M : Devices Z.sector.derivatives)
variable {q:Fin k→ℕ} (T : W→ Cells S q)
omit hg
variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
-- costs with compactly normalized support. Annulus theorem will use holes with true contractions.
def Claim (D : Reader E W X k Z.sector.derivatives)(ε : ℝ) (u : ℝ) := ∃ C >(0:ℝ),∀ w (f:Menu k)(p:SmoothTests E) (m : ℝ), (∀ i∈(root g).parts,(f i).slice=none) → tsupport p.val ⊆ (barrel r w) ⁻¹' r.stage w → Jet (stairs q (root g)) univ p.val m → Dust (r.windings M D T f w (normal_test r w p)) (C*m* scale r w ^ (u - arityRate q g- ε))

variable {r M T} (H : Run r)(hT : Given T)(hm : r.Authority M q)(A : Services C F S){ε : ℝ}(he : 0< ε)
include hg H hT hm A he
lemma costs_at (B : W→ℝ)(D : Reader E W X k Z.sector.derivatives)(h : Loan Z M r B D) (u : ℝ)(hb : ∀ w,B w=scale r w ^ u) : Claim r M T D ε u:=by
    obtain ⟨c,hc,h⟩:= any_power h hT hm A he; refine ⟨c,hc,fun w f p m hx hv hp=> ?_⟩; apply (h f w _ _ (stage_test r w p hv) (pays r H w hp) hx).mono; apply le_of_eq; rw [← statement hg r w H (hb w)]; ring
variable [Fintype J] {v : J→ℕ} {θ : Backdrop S r v} {α : W→ Viewers Z} {δ : ℝ} {n : ℕ}
lemma full_power (h : θ.Eligible δ): Claim r M T (θ.polls M α) ε 0 := costs_at hg H hT hm A he _ _ (Backdrop.hierarchy_cost h A) 0 (by intro w; rw [Real.rpow_zero]; rfl)
lemma coeff_power (h : sees M (clasp g hg) n r) : Claim r M T (rootCoeff r M n) ε n := costs_at hg H hT hm A he _ _ (coefficient_loan r hg M n h A) _ fun _=>rfl
lemma rem_power (h : sees M (clasp g hg) n r)(hp : θ.Eligible δ): Claim r M T (θ.controlled M (clasp g hg) n false α) ε (n+1:ℝ):= costs_at hg H hT hm A he _ _ (Backdrop.at_front false hp h A) _ fun w=> by unfold jackpot evidence; simp only [Bool.false_eq_true,↓reduceIte,Nat.cast_add,Nat.cast_one]; rfl

end YM.Contacts.Solstice
