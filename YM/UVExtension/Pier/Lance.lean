import YM.UVExtension.Pier.Strokes
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
include ha hp hm
local notation "n₀"=> A.B.a.S.side m n
local notation "W"=> A.B.a.clock.forcedAllowance m
local notation "p"=> Real.exp ((Fintype.card (Site (A.B.a.S.side m n)):ℝ)*W)
omit ha hp hm
private lemma collection {b:ℕ→ℝ}(h:SumBudget b z):SumBudget (fun i:Finset ℕ=> ∏ j∈i,b j) (Real.exp z):=by
    let F(i:Finset ℕ):ℝ:= if i=∅ then 1 else 0; have he : SumBudget F 1:=⟨fun i=> by unfold F; split<;> positivity,summable_of_ne_finset_zero (s:={∅}) (fun i hi=>by simp_all [F]), (tsum_eq_single ∅ (fun i hi=> if_neg hi)).trans_le (by simp [F])⟩
    have hf:= Local.sumBudget_add (Local.sumBudget_exponential h) he; convert! hf using 1; congr 1
    · funext i; by_cases hp:i=∅ <;> simp_all [Finset.nonempty_iff_ne_empty,F]
    simp -- Credit.H
private lemma cut {b:ℕ→ℝ}(h:SumBudget b z)(k:ℕ): SumBudget (fun i:Finset ℕ=> if k∈i then ∏ j∈i.erase k,b j else 0) (Real.exp z):=by
    let q:= (fun i:Finset ℕ=> if k∈i then ∏ j∈i.erase k,b j else 0); let g(i):= ∏ j∈i,b j; have hp:= collection h; have hv i:0≤q i:=by unfold q; split; exact hp.1 _; exact le_refl _
    have he (f:Finset (Finset ℕ)) : ∑ i∈f,q i ≤ Real.exp z:=by
       let R:= f.filter (fun i=> k∈i); have ht i(hi:i∈R): k∈i := (Finset.mem_filter.mp hi).2
       calc
        ∑ i∈f,q i = ∑ i∈R,g (i.erase k):=by rw [show R=_ from rfl, Finset.sum_filter]
        _= ∑ i∈ R.image (fun i=>i.erase k),g i:=by rw [Finset.sum_image]; intro i hi j hj hh; simpa only [Finset.insert_erase (ht i hi), Finset.insert_erase (ht j hj)] using congr_arg (insert k) hh
        _≤_:= budget_sum hp _
    exact ⟨hv,summable_of_sum_le hv he,Real.tsum_le_of_sum_le hv he⟩
include ha hp hm
lemma flashes (U:Config G (A.B.a.S.side m n)): let b:= Real.exp ((Fintype.card (Site (A.B.a.S.side m n)):ℝ)*W); Sail T (fun d:Y=> ((V0 d).activities.gas P U:ℂ)) b ∧ ∀ i:ℕ,Sail T (fun d:Y=> dressed (V0 d) i U) b:=by
   intro b; let K:= S.realBeat 0 N n m; obtain ⟨g,hg,hT,hP⟩:= (Gale.strongK S N n ha hp m hm).rises
   have ht z(hz:z∈Z): SumBudget (fun i=> ‖g z i U‖) ((Fintype.card (Site n₀):ℝ)*W):=by
      obtain ⟨c,hc,hV⟩:= (hP z hz).afloat; have hu i: ∃ x:Site n₀, 1 ≤ (ChimeK G P n₀).cost x i:=by
         let V:= K.activities.forced i; obtain ⟨x,hx⟩:= V.inventory_ne.mono V.inventory_sup; refine ⟨x,?_⟩; unfold ChimeK Concert.bell; dsimp only; rw [if_pos (show x∈(Ovens.Pipes.addr _ _ _).support from hx)]; exact Real.one_le_exp (mul_nonneg (P).exponent_pos.le (Nat.cast_nonneg _))
      exact Local.sumBudget_mono (net hu (fun i=> hc i|>.1) hV) (fun _=>norm_nonneg _) (fun i=> (hc i).2 _) le_rfl
   have hh(d:Y)(i): (V0 d).activities.admissible P U i↔ K.activities.admissible P U i:= Iff.rfl
   have hu(i:Finset ℕ): Bumps Z (fun z=> ∏ j∈i,g z j U):= fun s r hs h he=> DifferentiableOn.fun_finsetProd (fun i _=> hg i U s r hs h he)
   constructor
   · let f(i:Finset ℕ) z:= if K.activities.admissible P U i then ∏ j∈i,g z j U else 0; have h₁ z(hz:z∈Z): SumBudget (fun i=> ‖f i z‖) b:=by
        refine Local.sumBudget_mono (collection (ht z hz)) (fun _=>norm_nonneg _) (fun i=> ?_) le_rfl; change ‖f _ _‖≤_; unfold f; split
        · rw [norm_prod]
        rw [norm_zero]; positivity
     have he i:Bumps Z (f i):=by unfold f; split; exact hu i; exact bumps _ _ (differentiableOn_const _)
     refine ⟨_, washed _ he h₁ (Real.exp_pos _).le,fun d=>?_,fun z hz=> (norm_tsum_le_tsum_norm (h₁ z hz).2.1).trans (h₁ _ hz).2.2⟩
     simp only [Activities.gas,Complex.ofReal_tsum]; refine tsum_congr fun i=>?_; unfold f Activities.gasOccurrence; rw [show (S.realBeat d.val N n m).activities.admissible _ _ _ ↔ _ from hh d i,hT]; split
     · rw [Complex.ofReal_prod]
     rw [Complex.ofReal_zero]
   intro k; let f(i:Finset ℕ)(z:ℂ):= if k∈i∧ K.activities.admissible P U i then ∏ j∈i.erase k,g z j U else 0; have h₁ z(hz:z∈Z): SumBudget (fun i=> ‖f i z‖) b:=by
      refine Local.sumBudget_mono (cut (ht z hz) k) (fun _=>norm_nonneg _) (fun i=>?_) le_rfl; change ‖f i z‖≤ _; unfold f; split; next h=> rw [if_pos h.1,norm_prod]
      next h=> rw [norm_zero]; exact (cut (ht z hz) k).1 _
   have he i:Bumps Z (f i):=by unfold f; split; exact hu _; exact bumps _ _ (differentiableOn_const _)
   refine ⟨_, washed _ he h₁ (Real.exp_pos _).le,fun d=>?_,fun z hz=> (norm_tsum_le_tsum_norm (h₁ z hz).2.1).trans (h₁ _ hz).2.2⟩
   refine tsum_congr fun i=>?_ ; unfold f coat; rw [show (V0 d).p=P from rfl,hh,hT]
end YM.UVExtension.Pier
