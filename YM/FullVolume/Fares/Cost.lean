import YM.FullVolume.Relay.Income
import YM.MergeProof.Tender
import YM.MergeProof.Groom

/-!
 # All after-L queries on physical pressures. Frames fixed by `Sav`;
 requests for any fixed card, all finite indices up to stage's d cap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open Legato.Campaign
open MergeProof  MergeProof.Menu
open Muse Veil Ship Empire Extra.Histories

variable (L:Side)(N:ℕ)(μ x q:ℝ)
open Face
abbrev multis (x:ℝ):ℝ := ((radiusB x+radiusB x+1:ℕ):ℝ)^4
structure Snow (G:Gauge) (L:Side)(N:ℕ)(μ x q:ℝ):Prop where
   capital : multis x*((Doors.stain x+groupBillK G q N L x μ)+creditP x)≤1
   covered : multis x*(Doors.stain x+creditP x)≤1
   height : (Accent.mintK (radiusB x))⁻¹*groupBillE G q N L x ≤ x⁻¹^3
   heights : (Accent.mintK (radiusB x))⁻¹*groupBillK G q N L x μ ≤ x⁻¹^3
   issued : (Accent.mintK (radiusB x))⁻¹*((N:ℝ)*(Real.exp ((Doors.stain x+groupBillK G q N L x μ)+creditP x)-1)) ≤ x⁻¹^3
   crowned : (Accent.mintK (radiusB x))⁻¹*((N:ℝ)*(Real.exp (Doors.stain x+creditP x)-1)) ≤ x⁻¹^3
private lemma credit_bills (G:Gauge)(L:Side) : Rate G L (-2) creditP:=by
   have hc: Rate G L (-2) (fun i=> (4:ℝ) * Mallow.probe (betaF G i L)):=Rate.mul_left Rate.power _
   apply hc.compare
   let w:= G.slopeConstant*Real.log (L.val:ℝ)
   filter_upwards [Delay.shift_pos G L, eventually_ge_atTop w,eventually_gt_atTop (0:ℝ)] with x hx hp hv
   let t:= betaF G x L
   have h_: t≤2*x:=by change x+w≤ _; linarith only [hp];
   rw [abs_of_nonneg (by unfold creditP; positivity), probe, Real.rpow_neg (le_of_lt hx), Real.rpow_ofNat]
   refine le_trans ?_ (le_abs_self _); unfold creditP; rw [inv_pow]; change _≤ 4*(t^2)⁻¹
   rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hx 2),mul_comm, ← div_eq_mul_inv]
   apply (div_le_iff₀ (pow_pos hv 2)).2; exact (pow_le_pow_left₀ hx.le h_ _).trans_eq (by ring)
private lemma stains_bills (G:Gauge)(L:Side) : Rate G L (-2) Doors.stain:=by
   apply (credit_bills G L).compare
   filter_upwards [Doors.stain_beats 2,eventually_gt_atTop (0:ℝ)] with x hx ht
   have h : Doors.stain x ≤ Real.sqrt (Doors.stain x):=by
      have hv:=Doors.stain_le x; have hp:=Doors.stain_pos x; exact Real.le_sqrt_of_sq_le (by nlinarith [hp,hv])
   rw [abs_of_pos (Doors.stain_pos x)]; refine (le_trans (h.trans ?_) (le_abs_self _)); unfold creditP; rw [inv_pow,inv_eq_one_div]; exact (le_div_iff₀ (pow_pos ht 2)).2 hx
private lemma ice {w:ℝ→ℝ}{b:ℝ} (h:∀ᶠ x in atTop, w x≤ b)(hb:0≤ b):∀ᶠ x in atTop,(Accent.mintK (radiusB x))⁻¹*w x≤ x⁻¹^3:=by
     filter_upwards [h,polestar b hb 3 0,eventually_gt_atTop (0:ℝ)] with x hx he hp
     have hv:0<Accent.mintK (radiusB x):=Real.exp_pos _
     apply le_trans (mul_le_mul_of_nonneg_left hx (inv_pos.mpr hv).le)
     rw [← div_eq_inv_mul,div_le_iff₀ hv,inv_pow,mul_comm,← div_eq_mul_inv,le_div_iff₀ (pow_pos hp 3)]; rw [add_zero] at he; exact he
private lemma credit_roll {A:ℝ→ℝ}(h:Rate G L (-2) A): ∀ᶠ x in atTop, multis x*A x≤ 1 ∧ (Accent.mintK (radiusB x))⁻¹*(N*(Real.exp (A x)-1))≤ x⁻¹^3:=by
    have hh:= Rate.radius_price (G:=G) (L:=L)
    have hC:Rate G L 0 multis:= by unfold multis; push_cast; simpa only [zero_mul] using! (((hh.add hh).add (Rate.const 1)).pow 4)
    have hP:= hC.mul h; rw [zero_add] at hP
    have hz:0<Real.log 2:=Real.log_pos (by norm_num)
    have hv : ∀ᶠ x in atTop, (N:ℝ)*(Real.exp (A x)-1) ≤ (N:ℝ):=by
       filter_upwards [h.below (by norm_num) (Real.log 2) hz] with x hx
       have hg : Real.exp (A x) ≤ 2:= (Real.exp_monotone ((le_abs_self _).trans hx)).trans_eq (Real.exp_log (by norm_num)); apply mul_le_of_le_one_right (by positivity); linarith only [hg]
    filter_upwards [hP.below (by norm_num) 1 zero_lt_one, ice hv (Nat.cast_nonneg _)] with x hx he using ⟨(le_abs_self _).trans hx,he⟩
lemma snowfall (h:0<μ):∀ᶠ x in atTop,Snow G L N μ x q:=by
    have hx:Rate G L (-2) (fun x=> groupBillK G q N L x μ):= (((show Rate G L (-2) (straw μ L G) from infuso L 2 (μ/4) (1/4) (by positivity) (by norm_num) _).mul_left _).mul_left _).mul_left _
    have hp:Rate G L (-(3/8)) (fun x=>groupBillE G q N L x):= ((((Rate.power (a:=-(3/8))).mul_left _).mul_left _).mul_left _).mul_left _
    filter_upwards [credit_roll L N (((stains_bills G L).add hx).add (credit_bills G L)),credit_roll L N ((stains_bills G L).add (credit_bills G L)),ice ((hp.below (by norm_num) 1 zero_lt_one).mono fun x he=> (le_abs_self _).trans he) zero_le_one, ice ((hx.below (by norm_num) 1 zero_lt_one).mono fun x he=> (le_abs_self _).trans he) zero_le_one] with x ⟨hb,he⟩ ⟨hi,hφ⟩ hα hψ using ⟨hb,hi,hα,hψ,he,hφ⟩
end YM.PhysicalNext.Repeat.Mallow
#print axioms YM.PhysicalNext.Repeat.Mallow.snowfall
