import YM.OPE.Log.Silken
import YM.UVExtension.Gale.Havens
import YM.OPE.Rough.Factory
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.RG12Joint
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
open Mallow Pressure ConnectedActivityE6 Blaze.March
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
variable {s:Sheet G} {D:Rolls s} {θ: Protection D}
variable (Z:Stage) (L:Side) (d:ℕ)
include G
lemma silken_for_all : ∀ᶠ x:ℝ in atTop, ∀ P:Teller G, ∀ T:ConnectedActivityE6.Target G P,
    modest T L Z d x:=by
   -- adapting rate arithmetic from YM/OPE/Log/Silken
   let f x:=2*(L.val:ℝ)^d*(Mercury.volt x Z.order Z.power*(Pressure.betaF G x L)^(1/2:ℝ))
   have hz : Rate G L 0 shiftG:= (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4 -- should 1
   have hp:Rate G L (1/2:ℝ) (fun x=> Pressure.betaF G x L^(1/2:ℝ)):= Rate.power
   have hh:Rate G L (1/2:ℝ) f:= ((((hz.pow (Z.power*Z.order)).weaken (b:=0) (by simp)).mul_right _|>.mul hp).mul_left _|>.weaken (by linarith))
   have hf: Rate G L (1/2:ℝ) (fun x=>|f x|):= hh.compare (by filter_upwards with x; rw [abs_abs])
   have he:= (((Rate.const (coinFee G Z d L)).weaken (show (0:ℝ) ≤ 1/2 by norm_num) |>.add hf).mul_right (host G Z d)) 1 (by norm_num)
   filter_upwards [he, (Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx hb P A
   refine le_trans ?_ ((le_abs_self _).trans (hx.trans_eq (Real.rpow_one _)))
   unfold f ConnectedActivityE6.Target.goal; simp only [abs_mul]; have hp:= (simpleH G Z d).le; gcongr
   rw [← Real.rpow_neg (zero_le_one.trans hb)]
   exact Real.rpow_le_rpow_of_exponent_le hb (by linarith only [A.start])

lemma silk_extra (T:Delays θ) : ∃ U: Delays θ, DelayLe T U ∧ ∀ V:Delays θ,DelayLe U V →
    ∀ (M:MapPrices)(X:Targets s M), FrameAccord X D V:=by
   obtain ⟨u,-,hv,H⟩:= collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i h=> ((Finset.range (i+1)).eventually_all.mpr (fun d hd=> silken_for_all (G:=G) (s.profile i) (D.L j) d))))
   exact ⟨{T with betaEntry:=u},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun _ hz M X j x hx i hi d hd=> H j x ((hz.beta j).trans hx) i hi d (Finset.mem_range.mpr (by omega)) _ _⟩

open YM.Merge Push.AbsoluteSums MergeProof.Ribbons
variable {Q Q' : ℕ → ℕ}
variable {p : Teller G} {X: ConnectedActivityE6.Target G p}{μ x:ℝ}{n k:ℕ}
lemma narrow_tariff (h: Mallow.Tariff X L n μ x)(hc:k≤n): Mallow.Tariff X L k μ x:=by
  let r:= radiusB x; let b:= probe (betaF G x L); let c:= station (betaF G x L)
  have hb:0 ≤ b:= h.probeT.le; have he:0 ≤ c:=h.nonneg
  let y:=straw μ L G x; let T:= radiusB (betaF G x L)
  have hx(i):0 ≤ Extra.Multi.siteFactor i:=by unfold Extra.Multi.siteFactor; positivity
  have hv:(k:ℝ)≤n:=by exact_mod_cast hc
  have hN : radiusTab T k b≤ radiusTab T n b:=by unfold radiusTab; gcongr; try exact hx _
  have hf: y+k*Extra.Multi.siteFactor r*b≤ y+n*Extra.Multi.siteFactor r*b:=by gcongr; try exact hx _
  refine ⟨h.nonneg,h.probeT,h.small,?_ ,?_ ,?_ ,?_⟩
  · apply le_trans _ h.shipping; change (k:ℝ)*Extra.Multi.siteFactor _*(Real.exp _*c)≤ (n:ℝ)*Extra.Multi.siteFactor _*(Real.exp _*c); gcongr; try exact hx _
  · apply le_trans _ h.buy; apply add_le_add hN; apply mul_le_mul (Real.exp_monotone hN) hN _ (Real.exp_pos _).le; unfold radiusTab; change 0 ≤ ↑k*_*b+4*b; positivity [hx T]
  · exact (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ (((r+r+1:ℕ):ℝ)^4))).trans h.lodging
  exact (sub_le_sub_right (Real.exp_monotone hf) 1).trans h.credits -- sub_le_sub right?

lemma narrow_hymen (h: Hymen X μ L Z n d x)(hc:k ≤ n) (hp:0 ≤ probe (betaF G x L)): Hymen X μ L Z k d x:=by
  let t:=radiusB x; let f:=Salt.scent t; let a:= Z.supportExponent+1/2; let c:=probe (betaF G x L); let b:= straw μ L G x
  have hv:(k:ℝ)≤n:=by exact_mod_cast hc
  have he : f k a 1 c 1 b ≤ f n a 1 c 1 b:=by
    have hp : 0 ≤ c:=hp; have hs : 0≤ b:=by unfold b straw lauge; positivity
    unfold f Salt.scent; gcongr
  exact ⟨(mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (((t+t+1:ℕ):ℝ)^4))).trans h.1,(sub_le_sub_right (Real.exp_monotone he) 1).trans h.2.1,h.2.2⟩

variable {LQ:Metals G}{LR:Rolls LQ.p}{A:Alloy LQ LR}{B:Factor A} -- Metals? easier general use of X:Factor parameters
lemma shrink (h: Mallow.Minty B.shape Q A.delay) (hV: AccordV B.shape Q A.delay)(hle:Q'≤Q):
    Mallow.Minty B.shape Q' A.delay ∧ AccordV B.shape Q' A.delay:= by
      refine ⟨⟨h.hold,fun j x hx i hi=> narrow_tariff _ (h.word j x hx i hi) (hle j)⟩,fun j x hx i hi k hk=>?_⟩
      exact narrow_hymen _ _ _ (hV _ _ hx _ hi k hk) (hle j) (h.word _ _ hx _ hi).probeT.le
end YM.PhysicalNext.Repeat.Legato.RG12Joint
