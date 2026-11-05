import YM.UVExtension.Tabernacle.Grit
import YM.UVExtension.Guild.Hull
import YM.UVExtension.Guild.Contract
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Dales
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (N m n:ℕ) (hm:m<N) (T:Levels G)
lemma fundedP : 0< T.clock.allowance m∧0<T.clock.forcedAllowance m:=by
     have he:= zero_lt_one.trans (T.fits.delayed m)
     unfold Calendar.allowance Calendar.forcedAllowance Calendar.hatCoupling; exact ⟨Real.rpow_pos_of_pos (inv_pos.mpr (Real.sqrt_pos_of_pos he)) _,Real.exp_pos _⟩

abbrev Cham (T:Levels G) (m n:ℕ):= Tabernacle.Charm G (T.budget m) (T.S.side m n)
abbrev Sheath (T:Levels G) (m n:ℕ) := Tabernacle.Field G (T.S.side m n)
def mount (_R:Factor A) (N m n:ℕ)(v:Sheath A.B.a m n)(β b:ℝ):RG.Rep G (A.B.a.S.side m n):=⟨A.B.kin.path N m,(A.B.a.params m).clip,Tabernacle.floor (A.B.a.budget m) v,A.B.a.budget m,β,b⟩
abbrev Valve (z:Cham T m n) := ↥(z.Shed (T.budget m))
abbrev Health (z:Cham T m n)(v:z.Shed (T.budget m)):= Tabernacle.copied (T.budget m) z v.val
abbrev Hold (T:Levels G)(m n:ℕ) (u:Cham T m n) := u.Hall (T.clock.allowance m) (T.clock.forcedAllowance m)
abbrev place (T:Levels G)(m n:ℕ)(u:Cham T m n): Valve m n T u→ₗ[ℝ] Hold T m n u:=u.embed (T.clock.allowance m) (T.clock.forcedAllowance m)
lemma tapT (d : Cham T m n) (v:Valve m n T d): ‖place T m n d v‖≤1 ↔ (Tabernacle.floor (T.budget m) v.val).Valid (T.budget m) (T.clock.allowance m) (T.clock.forcedAllowance m):=by
   have h:= fundedP m T
   have he:= Tabernacle.tickP (T.budget m) _ _ h.1 h.2 (d.income _ v).1 (a:=1)
   simp only [one_mul] at he; exact he
-- caps before CPU. works with *same* restricted data+scalar and only Φ(d). reuse proof Application.intake_at. 
variable {N m n}
lemma outset (v:Sheath A.B.a (m+1) n) (β b:ℝ) (h: (Tabernacle.floor (A.B.a.budget (m+1)) v).Valid (A.B.a.budget (m+1)) (A.B.a.clock.allowance (m+1)) (A.B.a.clock.forcedAllowance (m+1))) (hp: β ∈ band A.B.a (m+1)) (hm:m<N):∃ H:Guide A.B R.shape N m n (Dales.mount R N (m+1) n v β b),Opera.Price A.B R.shape N m n (Dales.mount R N (m+1) n v β b) H:= by
    let a:= A.B.a; let t:= a.clock; let x:= t.hatBeta m; let S:=t.op m n; let d:=(Dales.mount R N (m+1) n v β b); have he': t.hatBeta (m+1)=Pressure.betaF G x S.patch.L:= ConnectedActivityE6.Application.clock_next a m n
    have hy := Planning.testing A.B R.shape R.pledging.conducts.income.grow.1 N m n hm
    apply (hy.2.2.2.2 _ _ _ _ hy.2.2.1).2 (Opera.protocol A.B hm R.pledging.conducts.full)
    have hS: Pressure.betaF G x S.patch.L / 2≤ d.beta ∧ d.beta≤ 2*Pressure.betaF G x S.patch.L:=he' ▸ hp
    have hU : incomingK G S.patch.L x=t.forcedAllowance (m+1):=by unfold incomingK Delay.fineMonitor; rw [← he']; rfl
    have hF : incomingE G S.patch.L x=t.allowance (m+1):=by unfold incomingE; rw [← he']; rfl
    have hg : t.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G S.patch.L x:=by
      unfold Calendar.loopCap ConnectedActivityE6.loopBill Delay.fineMonitor; rw [← he']
      have he' := t.adm (m+1)
      have ht := A.B.a.fits.thetaRange (m+1)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [show Vac.Numbers.P (t.hatBeta (m+1)) = (t.monitor (m+1)) ^ (1:ℝ) by rw [Real.rpow_one]; rfl]
      apply Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)); refine ht.2.trans (inv_le_one_of_one_le₀ ?_); exact_mod_cast show 1 ≤ t.J (m+1) by omega
    have hh (m:ℕ): a.params m= X.p.profile (t.J m):= params_eq A.B.valid m
    refine ⟨Pressure.Testing.proceeds A.B N m n hm,⟨rfl,rfl,?_⟩, ⟨?_,hF.symm ▸ hU.symm ▸ h⟩,?_,he' ▸ (a.fits.delayed (m+1)),?_,hS⟩
    · change _=Pressure.temp (Pressure.betaF G x S.patch.L); rw [← he']; rfl
    · change (A.B.kin.path N _).Bounds _ (X.p.profile (t.J (m+1))).width (X.p.profile (t.J (m+1))).paths (ConnectedActivityE6.loopBill G _ _); rw [← hh]; have he':=A.B.support.cap N (m+1) hm
      exact {he' with two:= budget_loosen he'.two hg}
    · exact (congr_arg RG.Stage.supportExponent (hh (m+1))).symm
    exact congr_arg Pressure.radiusB he'
structure Tour (N m n:ℕ)(ε:ℝ) where
    atTopH : Guide A.B R.shape N m n (Dales.mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0)
    W: Zeal R.target R.shape A N m
    k: ℕ
    hr: Wheeled R atTopH W (ε:=ε) k
    enough : N≤k
    hm:m<N
variable {ε:ℝ}(t:Crest R ε) (z : Cham A.B.a (m+1) n)
include t z hm
lemma touring : Nonempty (Tour R N m n ε):= by
    let P:= A.B.a; let σ:= P.clock.allowance (m+1); let b:=P.clock.hatBeta (m+1); let v:Valve (m+1) n P z:=0
    obtain ⟨H,hV⟩:= outset R _ b 0 ((tapT _ n _ z v).1 (by simp [v])) (by have ht : 0<b:= zero_lt_one.trans (P.fits.delayed _); change b/2≤ b∧b≤ 2*b; constructor <;> linarith) hm
    have hY := hp_width R hm (mount R N (m+1) n v.val b 0)
    obtain ⟨W⟩:= Rain.learns hm R.pledging.conducts.income.grow.1 R.pledging.conducts.full
    obtain ⟨k,hk,h⟩:= ((wheels R hm t H W hY.1 rfl).and (eventually_ge_atTop N)).exists
    exact ⟨⟨H,W,k,hk,h,hm⟩⟩
end YM.UVExtension.Dales
