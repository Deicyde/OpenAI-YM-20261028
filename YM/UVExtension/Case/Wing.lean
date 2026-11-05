import YM.UVExtension.Case.Postal
import YM.MergeProof.Seaside
/-! Adapt sailsV with the corresponding bought retarget price. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Case
open PhysicalNext PhysicalNext.ThroughLaunch Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open WilsonStartup Further.StrongStartup Extra.Histories Next.Foundations Pressure Testing Org
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

/-- T : MapPrices here = the pre-quote used by free `H.Suffices`. Actual
*chosen* M gets the Builder quote from that T, regardless of later recalculated
minimum L. -/
def provider (s : Sheet G) (T : MapPrices) (n : ℕ→ℕ) : Metals G :=
    ⟨raise s n,actualPay s T,chart G,chart_ok G⟩

variable {s : Sheet G} {T : MapPrices} {n : ℕ → ℕ} {L : Rolls (raise s n)} {Θ : Protection L} {D : Delays Θ}
    {Q : PostCost L} {Y : Bar D} {W : Wait Y}

/-- Freeze the data on this output-calibration, witnesses for ALL history lengths and periods,
M is the post-facing kinetic choice (supplies actual unmasked station/path Hessian & alpha receipts,
higher-order shape etc. as in Kin.Planned). No awaiting a choice of cheap L in which
only kinetic penalties isolated are paid. `layer` recovers the earlier free and
thermal purchases for M (not for another orientation). -/
structure Conveyor {s : Sheet G} {n : ℕ → ℕ} {L : Rolls (raise s n)}
    (O T : MapPrices) (l : ℕ → ℝ) (Q : PostCost L)
    (a : Levels G) (M : Horizon a) (k : Kin M (chart G)) : Prop where
  finalMap : M.Suffices (actualPay s T)
  paths : k.Planned Q
  top i : k.path i i = Design.top G (a.params i).clip
  forms : Free.Report M (actualPay s T)
  ages : Reward.Ends a k.path k.alpha
  layer : ∃ (X W : Horizon a) (u : Kin W (chart G)), Craft.Rack a O X ∧ Next.Free.Present a X l ∧
    Bid.Retained W X ∧ W.Suffices T ∧ Next.Free.Present a W l ∧ (∀ N m t, m ≤ N → Bid.Sworn (W.H N m) t G) ∧
      Stationary.FullPaths u Q ∧ k.path=Change.revised u ∧ k.alpha=u.alpha ∧
      (∀ N m p F, m+1 < N → k.stationary N m p F = u.stationary N m p F) ∧ Change.Overlay M W ∧ (∀ N m,m<N→ (M.towers N m).T=(W.towers N m).T)

open Next.Scheduling Next.SectorChange

-- PAY even if scheduling grows after this. These requirements available
-- on the j-height, not taken from a finally-chosen realization.
private lemma carG {E : Delays Θ} (h : Boost D E) (B : Extra.Multi.Scope) (t : Extra.Multi.Tariff)
    (Y : Extra.Multi.Gated D B t (localSection G)) : Extra.Multi.Gated E B t (localSection G) :=
  ⟨h.priced Y.priced,fun i j x hp hv hx => Y.gates i j x hp hv ((h.beta j).trans hx)⟩
private lemma carC {E : Delays Θ} (h : Boost D E) {Q : MapPrices} {g a X : ℕ → ℕ → ℝ}
    (Y : Cosmos (chart G) Q D g a X) : Cosmos (chart G) Q E g a X := by
  intro i j hj hv; obtain ⟨ha,hx,H⟩ := Y i j hj hv
  exact ⟨ha,hx,fun x he=> H x ((h.beta i).trans he)⟩

/-- Pre knobs P chosen such that any higher AFTER floors/numbers called
below work. Pay on the actual input of a given StepData in the Typed
context. `O` here is the initial rack price, `T` the next from Free; no
renaming P to query in nonlinear inputs after applying Builder's quote
(this would be dependent on a later number). Epoch floor statuses are
synchronizable by choosing larger floors **before** Hull analysis.
-/
structure Purchased (s : Sheet G) (O T : MapPrices) (l γ C : ℕ → ℝ) (p : Bid.Worth)
    (t : Tariffs) (B : Extra.Multi.Scope) (v : ℕ → ℕ) : Prop where
  slopePrice i : 0<γ i
  suitable i : s.first ≤ i → Design.Suitable G (s.profile i)
  liftL : s.floorL ≤ v
  plan : Doors.Plans s C p
  -- θ thresholds imposed later; shell growth can still be enlarged there
  ship (n : ℕ→ℕ) (hn : v ≤ n) (L : Rolls (raise s n)) :
    ∃ η : ℕ→ℝ, Stationary.BudgetGap (raise s n) L O η ∧
    ∀ Q : PostCost L, Q.η=η → 1 ≤ Q.Γ → Q.c ≤ γ →
    ∀ (Θ : Protection L) (K : Extra.Multi.Tariff) (z : ℝ), 0 ≤ z → ∀ A : Delays Θ,
      ∃ D : Delays Θ, Boost A D ∧
        ∃ F κ ℓ : ℕ → ℕ → ℝ,(∀ i j, z ≤ F i j) ∧ ∀ E : Delays Θ, Boost D E →
          Prices (raise s n) t (localSection G) E.betaEntry ∧ Stock.Priced E ∧
          Ringing (actualPay s T) F E ∧ Cosmos (chart G) (actualPay s T) E F κ ℓ ∧
            ∀ (Y : Bar E) (W : Wait Y) (a : Levels G), Paid W a → Doors.Budget a C p ∧
              Extra.Multi.Prepared B K (localSection G) a ∧ ∃ (M : Horizon a) (k : Kin M (chart G)), Conveyor O T l Q a M k


theorem brines (C : Supply.Sheet G) (K : MapPrices) (hc : ∀ i ≥ C.first,Design.Suitable G (C.profile i)) {n : ℕ → ℕ} {D : Supply.Rolls {C with floorL:=n}}
    {Θ : Supply.Protection D} {W : Supply.Delays Θ} {Y : Supply.Bar W} {I : Supply.Wait Y} {a : Levels G} (hI : Supply.Paid I a)
    {M : Horizon a} (hM : M.Suffices K) {O : ChartRatio G} (hO : LocalRatio O) {Q : PostCost D}
    (kin : Kin M O) (hg : kin.Planned Q) (hr:Free.Report M K)(hB:Reward.Ends a kin.path kin.alpha) : ∃ H : Horizon a, ∃ v : Kin H O, H.Suffices (actualPay C K) ∧ v.Planned Q ∧ v.path=Change.revised kin ∧
    v.alpha=kin.alpha ∧ (∀ N m p F, m+1<N → v.stationary N m p F=kin.stationary N m p F) ∧ Change.Overlay H M ∧
    (∀ N m,m<N → (H.towers N m).T=(M.towers N m).T) ∧ Free.Report H (actualPay C K) ∧ Reward.Ends a v.path v.alpha:= by
  have hx (m) : Design.Suitable G (a.params m) := by
    have hs := hI.firstZero ▸ a.fits.mono (Nat.zero_le m)
    unfold Levels.params Calendar.params; rw [hI.stage]; exact hc _ hs
  obtain ⟨H,h,hv,hK,hT⟩ := (Case.retarget_arc C K).choose_spec a hI.stage (fun i => (hx i).direct) M hM
  obtain ⟨v,h1,h2,h3,h4⟩ := Change.engine hv hO hg hx
  refine ⟨H,v,h,h1,h2,h3,h4,hv,hK, storeReport hr h (fun m=> (eventually_gt_atTop m).mono fun n h=> hv.other n m h) (fun i=> (eventually_gt_atTop (i+1)).mono fun n h=> hT n i h),?_⟩
  rw [h3,h2]; refine ⟨hB.prices,fun i=>?_⟩
  obtain ⟨R,w,hw,hL⟩:=hB.fields i
  exact ⟨R,w,hw,fun s hs=> Reward.translate_data (hL _ hs) ((eventually_gt_atTop i).mono fun n hi=> (if_neg hi.ne))⟩

/-- No invoice for the analytic suppliers in later arcs: e.g. C chosen here
as input, not shown to work in any persistence or opportunity estimates later. -/
theorem sailsV {K : KernelChoices} (hG : G.Simple) (hK : ∀ P : Patch, P.Branches K G) {o : Orders} (hp : Draft o)
    (C : ℕ → ℝ) (hC : ∀ i, 1≤C i) : ∃ (s : Sheet G) (O T : MapPrices) (l γ : ℕ → ℝ) (p : Bid.Worth),
    s.kernel = K ∧ WithStage s o ∧ ∀ (t : Tariffs) (B : Extra.Multi.Scope), ∃ v : ℕ → ℕ, Purchased s O T l γ C p t B v := by
  obtain ⟨O,l,g,b,h,hT⟩ := Free.profiles (G:=G) K
  obtain ⟨ε,hε⟩:= Projection.pick Projection.wavePulse
  obtain ⟨σ,A,he,hA,hP⟩ := Reward.office G hG O K g (fun i => (h.fit i).le) (Stationary.pouring G hG) ε hε.pos (by linarith [hε.small])
  obtain ⟨X,hX,hX',hx,hx'⟩ := housing hK hp b g σ h.fit he
  obtain ⟨a,c,hY⟩ := Further.StrongStartup.shelves X (fun i _ => (hx' i).2.1)
  let G' i := max (a i) (A i)
  obtain ⟨Y,hj,hY',hu,h1,h2⟩ := buy_shelves X G' c
  obtain ⟨hc,-⟩ := hY Y hj (fun i => let ⟨h1,h2,h3,h4,h5⟩ := h1 i; ⟨h1,h2,h3,(le_max_left ..).trans h4,h5⟩)
  have ho : WithStage Y o := ⟨hj.trans hx.first,fun i=>(h1 i).2.2.1.trans (hx.jets _), fun i=>(h2 i).1.trans (hx.powers _),
    fun i=>(h2 i).2.1.trans (hx.prices _)⟩
  let P i := (Y.profile i).width; let A' i := (Y.profile i).paths
  have hσ : P ≤ σ := fun i => ((h1 i).2.1.trans (hx' i).2.2).le
  have hs0 : A ≤ A' := fun i => (le_max_right ..).trans (h1 i).2.2.2.1
  obtain ⟨d,γ,u,-,hg,H⟩ := hP P A' hσ (fun i => (Y.profile i).width_pos) hs0
  have hY (i : ℕ) : (Y.profile i).clip.direct ≤ g i := by rw [(h1 i).1]; exact (hx' i).1
  obtain ⟨s,p,hs,hS,hc',hw,hB,hN,hQ⟩ := developer Y (hY'.trans hX) hc hY ho hp u d C hC
  obtain ⟨T,h⟩ := hT s hs
  obtain ⟨u,e,ht⟩ := Doors.afford s C p hc'
  refine ⟨s,O,T,l,γ,p,hs,hS,fun t B => ?_⟩
  obtain ⟨v,r,hv,hr⟩ := Further.StrongStartup.prices s (actualPay s T) B t (localSection G) hG
    (fun i hi => (hQ i hi).direct) hN
  let v' j := max (max (v j) (u j)) (B.ask j (s.profile j))
  have hv' : v ≤ v' := fun _ => le_trans (le_max_left ..) (le_max_left ..)
  have hu' : u ≤ v' := fun _ => le_trans (le_max_right ..) (le_max_left ..)

  refine ⟨v',⟨hg,hQ,hv.trans hv',hc',fun n hn L => ?_⟩⟩
  have hV := hv'.trans hn
  obtain ⟨x,y,hy,hZ⟩ := H (raise s n) hs ⟨hB.axis,hB.fields,hB.gradient,
      fun i => (hB.days i).trans ((hv.trans hV) i)⟩ L
  obtain ⟨hb,hr⟩ := hr n hV
  refine ⟨y,hy,fun Q h1 h2 h3 Θ K z hz W => ?_⟩
  obtain ⟨Δ,hH⟩ := hZ Θ
  let W' : Delays Θ := {W with shells:=fun i=> max (x i) (W.shells i),
                                 betaEntry:=fun i=> max (W.betaEntry i) (max (e i) (Δ i))}
  obtain ⟨D,hv₀,hv₁,hp₀,hp₁,hp₂,F,hF,hF',hG'⟩ := hr L K z hz Θ W'
  obtain ⟨Q',hq',hq,h',hd,hU⟩ := Extra.Multi.raise_gates hG D B K (localSection G)
  have hdB : Boost D Q' := ⟨h',hd,hq'.symm.le,hq.symm.le⟩
  obtain ⟨E,hDE,hF,hΓ,hΩ,hE⟩ := issue_cosmos (chart G) (actualPay s T) (chart_ok G) Q' F (Bid.recheck hdB.beta hF)
  have hDE' := hdB.chain hDE
  have HW : Boost W' D := ⟨hp₁,hp₀,hv₀.symm.le,hv₁.symm.le⟩
  have hW : Boost W E := (Boost.chain (V:=W) (W:=W') ⟨fun _ => le_max_left ..,le_rfl,fun _ => le_max_right ..,le_rfl⟩ HW).chain hDE'
  refine ⟨E,hW,F,hΓ,hΩ,hF',fun S hx => ?_⟩
  have hz := hDE'.chain hx; have hT := HW.chain hz
  refine ⟨hb _ (le_trans hp₂ hz.beta), Boost.priced (hDE.chain hx) hU.priced,
    Bid.recheck hx.beta hF, carC (s:=s) (n:=n) hx hE, fun X W A hA => ?_⟩
  obtain ⟨M,H,h₃,h₄,h₅,h₆,h₇,h₈,hT'⟩:= h A hA.stage (hA.kernel.trans hs) (Next.Free.credit_from_sheet hA _ _ (fun i _=> hB.axis i)
    (fun i _=> le_trans (show b i ≤ s.floorL i from (congr_fun ((hu).trans hX') i) ▸ hw i) ((hv.trans hV) i)))
  have hK : Δ ≤ S.betaEntry := fun i => le_trans (le_max_right ..) ((le_max_right ..).trans (hT.beta i))
  obtain ⟨Kn,Hk⟩:= hH S X W hK ((show x ≤ W'.shells from fun _=>le_max_left ..).trans hT.shells) Q h1 h2 h3 A hA
  let q := Classical.choice (Stationary.colorAvail G hG)
  obtain ⟨U,hU,hBout⟩ := Reward.ticket hA q (chart_ok G) hε (Hk M H h₃ h₅ (chart G) (chart_ok G)) (Reward.reportBuried hT')
  obtain ⟨J,j,H',Hj,hp,hp',ha,ha',haX,hForms,hEOut⟩ := Case.brines s T hQ hA h₆ (chart_ok G) U hU.linked hT' hBout
  have hΓ (i) : j.path i i=Design.top G (A.params i).clip := hp ▸ if_pos rfl
  refine ⟨ht n (hu'.trans hn) L A hA.lengths hA.stage (fun m => ?_), Extra.Multi.Gated.prepares S _ _ _ hN
    (fun j=> le_trans (le_trans (le_max_right ..) (hn j)) (L.large j).need) (carG (s:=s) (n:=n) (hDE.chain hx) B K ‹Extra.Multi.Gated Q' B K (localSection G)›) hA,
    J,j,H',Hj,hΓ,hForms,hEOut, M,H,U, h₃,h₄,h₅,h₆,h₇,h₈,hU,hp,hp',ha,ha',haX⟩
  exact (le_trans (le_max_left ..) ((le_max_right ..).trans (hT.beta _))).trans (hA.pays _)
end YM.UVExtension.Case
