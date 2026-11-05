import YM.UVExtension.Pier.Power
import YM.UVExtension.Gale.Tambour
import YM.UVExtension.Pier.Haven
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} (S: Uses R hG)
    (N n m k:ℕ) {a z:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a) (hm:m≤N)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "Y"=> Row a
local notation "V0"=> fun (b:Row a) => S.realBeat b.val N n m
local notation "P"=> A.B.a.budget m
local notation "T₀"=> A.B.a.S
local notation "Z"=> ball (0:ℂ) a
open Concert Tabernacle
include ha hp
local notation "n₀"=> A.B.a.S.side m n
local notation "V"=> S.cart N n
local notation "H"=> S.fits N n
local notation "Γ"=> drawer G n₀
local notation "ρ"=> A.B.a.clock.allowance m
include hm
lemma treasury : Stalk (ChimeE G (A.B.a.budget m) (A.B.a.S.side m n)) T (fun (b:Row a) i t=> ↑((t:Tap (A.B.a.budget m) G ((drawer G _).reg i).site ((drawer G _).reg i).support).read ((S.realBeat b.val N n m).activities.E i))) (A.B.a.clock.allowance m) := by
    let P' := A.B.a.budget m; let U:= (S.fits N n).W m; let K:= ChimeE G P' (A.B.a.S.side m n); let V':= S.grove.coins; let k:= A.B.a.clock.allowance m; have hx:= fundedP m A.B.a|>.1; let w z:= H|>.gates V V' z m hm; let g z:=(k:ℂ) • (w z).1
    have h:= H|>.lamps V V' m hm
    have hg: Bumps (desk a ha).span g:= by
       let Hx:DifferentiableOn ℂ w Z:= h.1.mono hp; exact bumps _ g (DifferentiableOn.const_smul (Hx.fst) (k:ℂ))
    let r(b:Y): K.Slot:= trill P' G (Γ).reg P'.supportExponent ((V0 b).activities.E); have hh b:g ((desk a ha).call b)=vibe K (r b):=by
       have hv:= hp (desk a ha|>.within b); have hs := (H).realX V (S.token N n) V' (b:=b.val) hv m hm; unfold g w; rw [show (desk a ha).call b=(b.val:ℂ) from rfl,hs]; change (k:ℂ) • (k⁻¹ • tuningE P' _)= vibe K _; rw [← Oriel.rsmul (Chime K),smul_smul,← Complex.ofReal_mul,mul_inv_cancel₀ hx.ne',Complex.ofReal_one,one_smul]; rfl
    have he(b):∃ u,K.MeasureP (r b) u:=⟨k,(Above.floorE P' _).2 (liveR S N n m (roseK S ha hp b) hm|>.labels.boundE)⟩
    have hu z(hz:z∈Z): ‖g z‖≤k/2:=by
        unfold g; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hx.le]
        exact (mul_le_mul_of_nonneg_left (((le_max_left ‖(w z).1‖ ‖(w z).2‖).trans (h.2 z (hp hz))).trans (by norm_num [Camp.soft,Oriel.rim] : Camp.soft≤1/2)) hx.le).trans_eq (by ring)
    obtain ⟨P'⟩:=charmP K r g hg hh he hu; exact (Stalk.ascend P').eases (by change k/2+k/2≤ k; linarith)
omit ha hp hm
-- extensive OK in this section ONLY. no fake absolute prices
lemma net {E B:Type} [Fintype B]{M: Meter E B} (hw:∀ i,∃ y:B,1 ≤ M.cost y i){u:E→ ℝ} (h:∀ i,0≤u i){v:ℝ}(hs:∀ y:B, SumBudget (fun i=> M.cost y i*u i) v): SumBudget u ((Fintype.card B:ℝ)*v):=by
    let g(y:B)(i):= M.cost y i*u i
    have ht : SumBudget (fun i=> ∑ j,g j i) ((Fintype.card B:ℝ)*v):=by
       have hx s : SumBudget (fun i=> ∑ j∈s,g j i) (∑ _∈s,v):=by
          induction s using Finset.induction with
          | empty=> simp only [Finset.sum_empty]; exact Local.sumBudget_zero le_rfl
          | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact Local.sumBudget_add (hs i) ih
       simpa using hx Finset.univ
    refine Local.sumBudget_mono ht h (fun i=>?_) le_rfl; obtain ⟨y,hy⟩:= hw i; apply le_trans (le_mul_of_one_le_left (h i) hy); exact Finset.single_le_sum (fun j _=> (hs j).1 i) (Finset.mem_univ y)
include ha hp hm
lemma fundsG (U : Config G (A.B.a.S.side m n)): Sail T (fun b:Y=> ( (V0 b).activities.additive P U:ℂ)) ((Fintype.card (Site (A.B.a.S.side m n)):ℝ)*ρ) := by
    let P':=P; let Q:= ChimeE G P' n₀; obtain ⟨f,hf,hP,h⟩:= (treasury S N n m ha hp hm).rises; let X i:= (Γ).reg i
    let r:= (Fintype.card (Site n₀):ℝ)*ρ; let g(z:ℂ) (i:ℕ):= if hz:Healthy P'.threshold (X i).support U then f z i (⟨U,hz,[],Nat.zero_le _,by simp⟩:Tap P' G (X i).site (X i).support) else 0; have hg i:Bumps (T).span (fun z=> g z i):=by unfold g; split; exact hf _ _; exact bumps _ _ (differentiableOn_const _)
    have hh z(hz:z∈Z): SumBudget (fun i=> ‖g z i‖) r:=by
       obtain ⟨b,hb,hV⟩:= (h z hz).afloat; have he:∀ i,∃ x:Site n₀,1≤ Q.cost x i:=by
          intro i; refine ⟨(X i).site,?_⟩; unfold Q ChimeE Concert.fork; dsimp only; rw [if_pos rfl]; exact Real.one_le_exp (mul_nonneg P'.exponent_pos.le (Nat.cast_nonneg _))
       refine Local.sumBudget_mono (net he (fun i=>hb i|>.1) hV) (fun _=> norm_nonneg _) (fun i=> ?_) le_rfl
       unfold g; split; exact (hb i).2 _; rw [norm_zero]; exact (hb i).1
    have he:= fundedP m A.B.a|>.1; refine ⟨fun z=> ∑' i,g z i, washed (u:=r) _ hg hh (mul_nonneg (Nat.cast_nonneg _) he.le), fun d=> ?_,fun z hz=>(norm_tsum_le_tsum_norm (hh z hz).2.1).trans (hh z hz|>.2.2)⟩
    unfold Activities.additive; simp only; rw [Complex.ofReal_tsum]; refine tsum_congr fun i=>?_; unfold g; rw [hP d]; unfold Activities.regularOccurrence; split
    next hz=> rw [masked_eq _ _ _ _ (show Healthy (P).threshold ((S.realBeat d.val N n m).activities.reg i).support U from hz)]; rfl
    next hy=> rw [masked_ne _ _ _ _ (show ¬Healthy (P).threshold ((S.realBeat d.val N n m).activities.reg i).support U from hy),Complex.ofReal_zero]
end YM.UVExtension.Pier
