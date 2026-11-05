import YM.UVExtension.Mast.Lark
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "V!"=> Voice F H n
local notation "μ!"=> Music F H N n
local notation "sT"=> Legato.Bandage.waybill (A.B.a)

open Eyelet

open Cellar Pans Extraction Accent Motion Cells Push
variable {t:ℕ→ℕ} {R S} {v}(U: Cellar S t R) (B:Orchard.Rose S) (he: Tendsto (fun i=>(v i n).val) atTop (𝓝 B.val)) -- v inference
local notation "C'"=>Cellar.yard v U
local notation "f'"=> (U.gate v d N n)
local notation "g'"=> U.cantors v d n
local notation "bt"=> (fun i=> (g').feeds S v d n)
local notation "D'"=> D!
local notation "k0"=> t d
-- Exact terminal reads.Id moves.
section orchestra
-- Primer matches any fixed vector. Actual r-value unique? use Quired.
-- Param K and ζ on exact Φ history.F
variable (K:ℕ→ℕ) (h: Scrim (Cellar.yard v U) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a)
    (J k:ℕ)(hw:Stock.Tabs.opens A.B.a 1 J m)(x: ((frames G).level d).Index)(w:ℝ)(hy:0<w)
    (hp:t d ≤ m)(hk:m≤ k)(hx:t d ≤ N)
    (hA:w*‖alto (Orchard.Path S v) m d‖*(4*(1+(A.B.a.params k).columns)/Bid.gainChart (Orchard.Path S v) k m) ≤ Legato.Bandage.fly A.B.a d m/2)
include hy hw hp hk hA h
variable (hc:GridApprox.room A.B.a J k (lensScope (yard v U) d))
local notation "Ve"=> Size.axis F x
local notation "iT"=> GridApprox.window (0:Site ((yard v U).side k n)) (lensScope (yard v U) d)
include hK hc
open Relay
local notation "O0"=> (0:Site ((yard v U).side N n))
local notation "X"=> (cantors v U d n)
local notation "C0"=> yard v U
local notation "Φ"=> (C'|>.labels.level d)

open Remnant Lacing
-- inverse-lens coefficient matrix. actual.E expanded values bought, chord persistence
omit hy hw hp hk hA h hK hc
lemma winds {d:ℕ} (Z:Labels.Frame G d) (t:ℕ → Z.Index→ Z.Coeff) (v:ℕ→ Z.Coeff) (x:ℕ→Z.Coeff)
    (hV: ∀ᶠ N:ℕ in atTop, ∀ i:Z.Index,Z.coeffSize (Size.axis Z i -t N i)≤1/4)
    (h:∀ᶠ N:ℕ in atTop,x N=∑ i:Z.Index,(v N i) • t N i) (hx:∀ i,UVExtension.Arrives (fun n=> t n i))(hq: UVExtension.Arrives x) : UVExtension.Arrives v:=by
    let g (i) : Z.Coeff→ₗ[ℂ] Z.Coeff:= {
      toFun:= fun v=> ∑ j,v j • t i j
      map_add':=fun x y=>by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
      map_smul':=fun x y=>by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,smul_smul, Finset.smul_sum] }
    let M n:= (g n).toContinuousLinearMap; have hp : ∀ᶠ n:ℕ in atTop,∀ x:Z.Coeff,Z.coeffSize x ≤ 2*Z.coeffSize (M n x):=by
       filter_upwards [hV] with n hn x
       let p:= M n x; have hh : Z.coeffSize (x-p) ≤ Z.coeffSize x /4:=by
          have he : x-p=∑ i,x i • (Size.axis Z i-t n i):=by simp_rw [smul_sub,Finset.sum_sub_distrib]; exact congr_arg₂ (·-·) ((Size.sum_axes Z x)|>.symm) rfl -- orientation
          rw [he]; refine (Size.finite ..).trans (le_trans (Finset.sum_le_sum (fun i _=> show Z.coeffSize _≤ ‖x i‖*(1/4) from ?_)) ?_)
          · rw [Size.smul]; exact mul_le_mul_of_nonneg_left (hn i) (norm_nonneg _)
          rw [←Finset.sum_mul]; unfold Labels.Frame.coeffSize; linarith only
       linarith only [Work.G08.size_triangle Z x p, hh, Work.G08.size_nonneg Z p]
    have hZ(y): UVExtension.Arrives fun n=> (steers (M n)).symm y:=by
       apply Lacing.Remnant.solved (h:=fun v=> UVExtension.Arrives.sum (s:=Finset.univ) (fun i _=> (hx i).post (continuous_const_smul (v i)))) (2*((Z.extra+1:ℕ):ℝ)) _
       filter_upwards [hp] with n hn y; exact (Push.Local.norm_le_size ..).trans ((hn y).trans ((mul_le_mul_of_nonneg_left (Push.Local.size_le_norm ..) zero_le_two).trans_eq (mul_assoc ..).symm))
    apply (Lacing.Remnant.loops (f:=fun n=> (steers (M n)).symm.toLinearMap) (x:=x) hZ hq).copy; filter_upwards [hp,h] with n hn he
    have hi: Injective (g n):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x e=>by apply Work.G08.size_separates; simpa only [show M n x=0 from e,Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero] using hn x)
    have hM:Bijective (M n):=⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
    have hp:x n=steers (M n) (v n):= he.trans ((Lacing.steers_eq (M n) hM (v n))|>.symm)
    rw [hp]; exact (steers (M n)).symm_apply_apply _
include hy hw hp hk hA h hK hc he
lemma lensM (z:(F).Coeff): ∃ (f:ℕ→ (F).Coeff)(S': ((F).Index)→ ℕ → (F).Coeff), UVExtension.Arrives f ∧ (∀ i, UVExtension.Arrives (S' i))∧
    ∀ N:ℕ,∀ hN:k < N,(∀ i, LatchUp C' k J N n d (hw.1.trans (hk.trans hN.le)) hN.le (stakes C' J m/w) i (S' i N)) ∧ z=∑ i, (f N i) • S' i N ∧ (F).coeffSize (f N) ≤ stockK C' k d z:= by
    let Z j:= (g').song j; let m0 (i j :ℕ):= ((X).song i|>.tone j).index
    choose P' hP hf using fun i=> pref (v:=v) d m n U B he K h hK J k hw w hy hp hk hA hc i
    let f(j:ℕ)(i:(F).Index):= (Cellar.gate v U d j n).terminal.symm (P' i j)
    let g (j :ℕ) (i:(F).Index):= m0 j k (f j i)
    have hz(i):UVExtension.Arrives (fun j=>g j i):=by
       have h:= Remnant.loops (f:=fun j=> (Pans.feeds S v d n X k j).toLinearMap) (fun z=> (X).spikes S v R d n (U.pay v d n) (U.flow d n v B he) k (hp.trans hk) z) (hP i)
       apply h.copy;filter_upwards [eventually_gt_atTop k] with j hj; unfold g f; rw [peak d j n U (hp.trans (hk.trans hj.le))]; rfl
    let y j:= (Pans.feeds S v d n X k j) z
    have ht(N)(hN:k<N):∃ t:(F).Coeff,z=(∑ i,t i • P' i N)∧ (F).coeffSize t ≤ stockK C' k d z:=by
       let Q:= (C'); let T:= (Z N); let r:= U.gate v d N n
       have hl:=(X).lyr N (hp.trans (hk.trans hN.le)); have heq:= (launch v U d N n).choose_spec (hp.trans (hk.trans hN.le))
       obtain ⟨t,hb,hx⟩:= Vintage.YM.MergeProof.Accent.dials Q N k n d (intakeV v U) z T (f N) (hp.trans hk) hN.le heq.2 hl.earned (fun i=> hf i N hN|>.2)
       refine ⟨t,hb.trans ?_,hx⟩; refine Finset.sum_congr rfl fun i _=> congr_arg (t i • ·) ?_; exact r.terminal.apply_symm_apply _
    let Gt i:= if hx:k < i then (ht i hx).choose else 0
    have hM i (hi:k < i):= (dif_pos hi : Gt i=(ht i hi).choose)
    refine ⟨Gt,P',?_ ,hP, fun i hi=> ?_⟩
    · apply winds F g Gt y _ _ hz ((X).spikes S v R d n (U.pay v d n) (U.flow d n v B he) k (hp.trans hk) z)
      · filter_upwards [eventually_gt_atTop k] with i hi j; exact (hf j i hi).2
      filter_upwards [eventually_gt_atTop k] with i hi
      have hv :∀ j, g i j= (Pans.feeds S v d n X k i) (P' j i):=by intro j; unfold g f; rw [peak d i n U (hp.trans (hk.trans hi.le))];rfl
      unfold y; rw [show Gt i=(ht i hi).choose from hM i hi]; refine (congr_arg ((Pans.feeds S v d n X k i) ·) ((ht i hi).choose_spec.1)).trans ?_; rw [map_sum]; simp_rw [hv,map_smul]; try rfl
    rw [show Gt i=(ht i hi).choose from hM i hi]; exact ⟨fun j=>(hf j i hi).1,(ht i hi).choose_spec⟩
end orchestra
end YM.UVExtension.Mast
