import YM.FullVolume.Tess.Lease
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
namespace Fan
variable (F:Fan T W p){n:ℕ}(V₀:Fin n→ R.family.book.Token)
local notation "δ"=> intervalClock R
local notation "a"=> R.family.S.a
variable (l:List (MotionIndex n))
-- fixed j,j ≤N layout sample and horizon l restricted operand allow finite splittings. h derivative only sufficiently far to avoid more impulse overlap along shifts.
variable (H:T.Winter)(hx:Jams.Wild R.kit.shape R.alloy.delay)
variable {w:sun} {K:Set (Points n)} (h:IsCompact K) (hp:K⊆ NoHit R.alloy.B.a.S p n)
include H hx h hp
lemma lightsFixed (w:sun):∀ᶠ j in atTop,∀ x:Positions n,tag (R.family.S.a j) x∈K → ∀ s:sun,CauchySeq (fun N:ℕ=> if hu:j≤ N then swellK F V₀ w j N hu l s x else 0):=by
    induction l generalizing K with
    | nil=> filter_upwards with j x hh s
            let y:= tag (a j) x; let t:Face T W:= F.film (scaleSun w s)
            have ht(x:Points n)(hy:Eves.ancestor (S) x)(hv:x∈NoHit (S) p n): CauchySeq (fun i=> (t.V T W).numeric i p V₀ (Rising.robe (P!) p x i)):=Face.peal T W H hx p (fun _=>t) x (ask P! (scaleSun F.spin (scaleSun w s)).val) (by simp only [t,F.presents]; exact tendsto_const_nhds) hy hv V₀
            have hb: Eves.ancestor (S) y:= ⟨j,(by change _=tag (a j) (address (a j) y); unfold y; rw [address_matched (R.family.S.a_pos _)])⟩
            apply Rising.cauchy_copy (ht y hb (hp hh)) -- name
            filter_upwards [eventually_ge_atTop j] with N hn; rw [dif_pos hn]
            let z:= ascending (S) p hn x; have he: tag (a N) z=y:= arrivesP (S) p hn x
            have hu:Rising.robe P! p y N=wrap _ ∘ z:=by rw [← he]; unfold Rising.robe; erw [address_matched (R.alloy.B.a.S.a_pos _)]
            rw [hu]; rfl
    | cons i l ih=>
       obtain ⟨t,ht,hT⟩:=h.exists_cthickening_subset_open (nohitOpen (S) p n) hp
       filter_upwards [ih h.cthickening hT,R.family.S.shrinks.eventually (ge_mem_nhds ht)] with j hj hz x hp s
       let z:= x+drive i
       have hδ: dist (tag (a j) z) (tag (a j) x)= a j:=by simpa only [one_smul,Nat.cast_one,one_mul] using! paidDist x (a j) (R.family.S.a_pos j) i 1
       have hx:= hj z (mem_cthickening_of_dist_le _ _ _ _ hp (hδ.trans_le hz)) s
       have h:=hj x (mem_cthickening_of_dist_le _ _ _ _ hp ((dist_self _).trans_le ht.le)) s
       obtain ⟨p,hv⟩:=cauchySeq_tendsto_of_complete hx; obtain ⟨q,hh⟩:=cauchySeq_tendsto_of_complete h
       apply (Tendsto.congr' ?_ ((hv.sub hh).const_mul ((a j:ℂ)⁻¹))).cauchySeq
       filter_upwards [eventually_ge_atTop j] with N hn; simp only [dif_pos hn]; rfl -- fix
omit H hx h hp in
lemma economySteps (C:ℝ) : Summable fun j:ℕ=> C/Real.sqrt (δ j):=by
    simp_rw [div_eq_mul_inv]; apply Summable.mul_left; let u j:=(Real.sqrt (δ j))⁻¹; let q:ℝ:=(Real.sqrt 3)⁻¹; have hp: 0<q:=by unfold q; positivity
    have hq:q<1:= by unfold q; rw [inv_lt_one₀ (by positivity)]; have h:= Real.sq_sqrt (by norm_num : (0:ℝ)≤3); nlinarith [Real.sqrt_nonneg 3]
    apply Summable.of_nonneg_of_le (f:=fun i:ℕ=>q^i) (fun i=> inv_nonneg.mpr (Real.sqrt_nonneg _)) _ (summable_geometric_of_lt_one hp.le hq)
    intro i; induction i with
    | zero=> unfold intervalClock; simp
    | succ i ih=>
       change _≤ q^(i+1); have hP:0<δ i:=zero_lt_one.trans_le (one_clock _); have hg:(3:ℝ) ≤ minutes R i:=by unfold minutes; exact_mod_cast (S).block_large i
       rw [show δ (i+1) = δ i * minutes R i from (by unfold intervalClock minutes; rw [Schedule.denominator,PNat.mul_coe,Nat.cast_mul]),Real.sqrt_mul hP.le,mul_inv, pow_succ]
       exact mul_le_mul ih (inv_anti₀ (by positivity) (Real.sqrt_le_sqrt hg)) (inv_nonneg.mpr (Real.sqrt_nonneg _)) (pow_nonneg hp.le _)
omit H hx h hp in
lemma tideP (b:ℕ)(C:ℝ)(hC:0≤C) : ∃ D:ℝ, 0≤ D ∧ ∀ j:ℕ,C*(δ (j+1))^b+C*(δ j)^b ≤ D*δ j ^(2*b):=by
    obtain ⟨c,hc,h⟩:=R.family.S.mesh_inequality (P!|>.fits.mesh)
    refine ⟨2*C*c⁻¹^b,(by positivity),fun j=>?_⟩
    have hx:0<δ (j+1):=zero_lt_one.trans_le (one_clock _); have hp:0<δ j:=zero_lt_one.trans_le (one_clock _)
    have hv:δ (j+1)≤ c⁻¹*(δ j)^2:=by have hh:c*(δ j)⁻¹^2 ≤ (δ (j+1))⁻¹:= h j; field_simp at hh ⊢; linarith
    have hi:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hv b) hC; exact (add_le_add hi (le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le (Sky.lazy (R:=R) j) b) hC) hi)).trans_eq (by rw [mul_pow,pow_mul]; ring)
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.lightsFixed
