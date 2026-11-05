import YM.TraceExtension.Loft.Awake
set_option autoImplicit false
/-!
# Extraction at actual Ward roots ties Path Data currents. Extract uniform finite period
statement not assuming triangular path p across levels. Budget α,C fixed by m. -/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Audience Metric Lamp Det Planned.PrimaryIntegral295 Next.Free Org Input Extra.Histories
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→Side}{F:Filter W}{G:Gauge}{f:Side}{M: Metals G}{D:Rolls M.p}{A:Alloy M D}(B:Bolt A){α σ a L ε:ℝ}
lemma deep_n (S:Schedule)(k:ℕ): Tendsto (fun p=> (S.side k p).val) atTop atTop:=by
   apply StrictMono.tendsto_atTop
   intro x y h; exact mul_lt_mul_of_pos_right (S.period_strict h) (S.denominator k).property
variable (N p:W→ℕ)(k:ℕ)(h:∀ w,k < N w) (hG:G.Simple)
def Baton (A: Alloy M D)(N:W→ℕ)(k:ℕ): W→PathData G:=fun w=> A.B.kin.path (N w) k
include h hG
lemma colorWire (A:Alloy M D): let s:=A.B.a.params k; let n:= A.B.a.S.side k; let f' w:=n (p w); let R:=Baton A N k;
    Flare f' R s.clip s.width s.paths ∧ ∃ A C D ε σ:ℝ,∃ V:Jar G,∃ F:Skuta W G, Cred f' s.clip R F V σ ε A C D:=by
   intro s n f' R; let η:= M.K.η (A.B.a.clock.J k); let Ω:=M.K.Ω (A.B.a.clock.J k); let α:=M.K.α (A.B.a.clock.J k)
   have hx:0<α:=M.K.alpha_pos _; have hp:0<η:=M.K.eta_pos _; let H(w):=A.B.M.H (N w) k
   let i:=plaquette (⟨(0,1),by decide⟩:PlaqAxes); have hQ: 0 ≤ Ω:=(price_step_metric hx ((A.B.plan.rows k k le_rfl).2.1) i i).budget_nonneg
   -- re-use pack
   obtain ⟨x,E,hx',hE,V,hV,hB⟩:= vintageWilson G
   obtain ⟨v,P,hv,hP,H'⟩:=saunter G hG α η Ω s.clip.direct s.width s.paths hx hQ (s.clip.quadratic_pos.le) s.width_pos s.paths_pos.le
   let w':=min x v; have hT:0 < w':=lt_min hx' hv
   have hY : V.fees w' E:=hV.less hT (min_le_left ..) le_rfl
   have hl(w):= A.B.support.cap (N w) k (h w).le
   have hs(w):= A.B.support.links (N w) k (h w).le
   have hh(w):∀ n, Floor (H w) s.clip n η Ω:=A.B.plan.all (N w) k (h w).le
   have HT(w): (H w).metric.strip α Ω:= (A.B.plan.rows (N w) k (h w).le).2.1
   have hm(w i) : Bid.Sworn (H w) (n i) G:= (Edens.laureates A.B.a A.B.M A.B.plan _ k i (h w)).2.2
   have hy: Tendsto (fun i=> (n i).val) atTop atTop:= deep_n _ _
   choose X h1 h2 h3 using fun w=>H' n hy (H w) s.clip (R w) _ (hl w) (hs w) (HT w) le_rfl (hh w) (hm w)
   have he(w): (X w).fees w' P:= (h1 w).less hT (min_le_right ..) le_rfl
   let W'(w):= (X w).combine V
   have ht(w): (W' w).fees w' (P+E):= (he w).pay hY
   have hd(w i): Ticket (W' w).cast (fineFlare s.clip (R w) (m:=n i)):=by
       have hu : AnalyticAt ℝ (intended s.clip (R w) (m:=n i)) 0:= (strain _ _ (hl w)).analytic
       have hw:= (Wilson_stream G 2).1 (n i)
       have hi:= Jar.sequelQ (hu.sub hw) hw (h3 w i) (hB _); rw[sub_add_cancel] at hi; exact Jar.cast_book (ht w) _ hi (hl w)
   let Y:ℝ:= 1; let u:=min α (min w' (Y*(1/128)))
   have hZ:0 < u:= lt_min hx (lt_min hT (by unfold Y; norm_num)); let V':Skuta W G:=⟨X,H,fun _=>s.clip,fun _=>u,fun _=>Y⟩
   refine ⟨⟨fun w=> ⟨_,_,_,_,hl w,hh w _,hs w,hm w (p w)⟩⟩, E,P,Ω,η,w',V,V', ⟨fun w=>⟨?_,he w,h2 w⟩,hB,hY,hT,hp,hE,hP,fun w=>hd w (p w)⟩⟩
   have hw: u ≤ min w' (Y*(1/128)):=min_le_right ..; have hL:=hw.trans (min_le_right ..)
   have hr:0 < Y:=zero_lt_one; have hk:= (ht w).live.mono (hw.trans (min_le_left ..)); have HB: (H w).metric.strip u Ω:=fun i j=> (HT w i j).mono (min_le_left ..) le_rfl
   exact ⟨hk,HB,⟨hr,le_rfl⟩,hL,hZ,massifTabs hk hy (hd w) (hl w) (hh w _) (fun i=> hh w (n i)) (hs w) (hm w) HB hr le_rfl hL hZ, hh w,hp⟩
omit h hG in
lemma actual_path (N i p:ℕ)(h:i≤N) : A.B.kin.path N i=((Issue.trail B).rep N p i).path:=by
   have hx:=((B.sticks N p).prices i (Nat.zero_le _) h).1.path; rw[A.B.bases] at hx; exact hx.symm
end YM.Trace.Loft
