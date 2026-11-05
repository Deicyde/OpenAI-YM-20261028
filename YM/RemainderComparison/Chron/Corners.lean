import YM.RemainderComparison.Chron.Age
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Chron
open Function Filter Set Lattice RG Tree Wilson Supply Input Org Shoot
open Push PriceCompiler Push.AbsoluteSums Gauge Pressure Testing SectorMeasure Precision
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Psalm Next.Scheduling AnalyticBridge VerifiedReset
open Extra.Iteration
open Height Roost
open ConnectedActivityE6
open Cadenza
open JointLoad.Heir.Suite
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {s:Sheet G} {K:MapPrices} {D : Rolls s} {R : Targets s K} {X : Expenses R}
variable {P: Protection D} {p : ℕ →ℝ}{w: Return.Wages}

open PhysicalNext.Repeat Push.Uniform
variable (G' : Firmament D) {T:Contemple G}
abbrev Book := ∀ i j, Fin (G'.count i j) → Cadenza.Quarry
variable (C:Programs s)(r:ℕ→ℕ→ℕ)(u:ℕ→ℕ→JointLoad.Heir.Record) (Y':PostCost D)(F: PhysicalNext.Repeat.Register D X w p)
-- argument order for P.µ.. etc
structure Pillar (T: Contemple G) (Q: Delays P) (k:Book G') : Prop where
    expenses : ∃ (f:ℕ→ℕ)(C':ℕ→ℕ→ℝ),Chron.Pledge R T C r f C' ∧ ∀ j,f j ≤ (D.L j).val
    buys (j i:ℕ)(g:Fin (G'.count j i)) : StepStages j i→ s.first ≤ i → ∀ (h : 4 ≤ j), (Mural.sheet s D h).Branches (Testing.query s K j i|>.bind) G →
       let K:= G'.slots j i g; let W:= K.award (s.profile i) (Glint.partition (s.profile i) (R j i).exp); let V:= k j i g
       W.Heart (s.profile i) (R j i).exp ∧ 0<V.d∧ PaintSupply G W.wind V.Z ∧ Allot (R j i) (F.o j i) (Mural.sheet s D h) W K.propAim K.scope (s.profile i) V (μ:= F.μ j i) s.kernel (s.profile j) (C j i) (u j i) Chi.canonical (r j i) K.η_goal K.limit K.ξ (Q.betaEntry j) ∧ ∀ x,Q.betaEntry j ≤ x → K.books.extra V x
    brings (j i:ℕ) (g:Fin (G'.count j i)) : StepStages j i→ s.first ≤ i → ∀ x:ℝ, Q.betaEntry j ≤ x → ∀ (c:Side), Q.shells j * (1+radiusB x)^(Q.growth j) ≤ c.val→ (G'.slots j i g).scope.Tiled x c
-- pillar.brings expression only output B.Ok.
open Push.Uniform
variable {C' : ℕ→ℕ→ℝ}{k:ℕ→ℕ}
-- no Branch affordability assertion.P.B. Query canonical at all scales.
lemma grows (T0:Delays P) (hf:Pledge (s:=s) R T C r k C')(hk:∀ i,k i ≤ (D.L i).val) (he:∀ j i,StepStages j i→s.first ≤ i → (u j i).ε≤1/4) (ht:∀ j i,(s.profile i).supportExponent+3 < (R j i).exp):∃ (W:Delays P) (B:Book G'), DelayLe T0 W ∧ ∀ U:Delays P,DelayLe W U→ Pillar G' C r u F T U B:=by
    have hv j i (g:Fin (G'.count j i)):∃ V:Cadenza.Quarry, ∀ h:4≤j, StepStages j i→ s.first ≤ i → (Mural.sheet s D h).Branches (Testing.query s K j i|>.bind) G →
       let Y:= G'.slots j i g; let A:=Y.award (s.profile i) (Glint.partition (s.profile i) (R j i).exp)
       0<V.d ∧ PaintSupply G A.wind V.Z ∧ ∀ᶠ x:ℝ in atTop, Allot (R j i) (F.o j i) (Mural.sheet s D h) A Y.propAim Y.scope (s.profile i) V (μ:= F.μ j i) s.kernel (s.profile j) (C j i) (u j i) Chi.canonical (r j i) Y.η_goal Y.limit Y.ξ x ∧ (∀ y, x≤ y→ (G'.slots j i g).books.extra V y):=by
       let v:Cadenza.Quarry:=⟨⟨0,0,0,0,0,0,0,0,0⟩,0,0,0,0,0,0⟩
       by_cases ha:4≤j
       · let h:= Mural.sheet s D ha
         by_cases hc:StepStages j i ∧ s.first ≤ i ∧ h.Branches (Testing.query s K j i|>.bind) G
         · obtain ⟨hp,hp',hz⟩:=hc
           have hT:= (hf j i).2 hp (D.L j) (hk j)|>.1; let s':=G'.slots j i g
           obtain ⟨V,x,hN,hZ,hX⟩:=hT h rfl hz (w j i) (F.μ j i) (F.o j i) (F.consumes _ _ hp).1 (F.consumes _ _ hp).2.1 s'.propAim s'.scope Chi.canonical (s.profile j) (s.profile i) (s'.award (s.profile i) (Glint.partition (s.profile i) (R j i).exp)) (s'.song _ (ht j i)) (C j i) (u j i) (he j i hp hp') (r j i) s'.η_goal s'.limit s'.ξ s'.positive s'.border s'.grant
           obtain ⟨z,hz'⟩:=eventually_atTop.mp (s'.books.actually V _ hX.length)
           exact ⟨V,fun _ _ _ _=>⟨hN,hZ,(eventually_ge_atTop (max x z)).mono (fun y hy=>⟨⟨hX.length,fun x hx=>hX.expenses x ((le_max_left ..).trans (hy.trans hx))⟩,fun t ht=>hz' t ((le_max_right ..).trans (hy.trans ht))⟩)⟩⟩
         exact ⟨v,fun _ hx hp hz=>(hc ⟨hx,hp,hz⟩).elim⟩
       exact ⟨v,fun h=>(ha h).elim⟩
    choose B hB using hv
    let Pℓ (j i:ℕ)(x:ℝ)(u':Fin (G'.count j i))(h:4≤j) :=
       let Y:= G'.slots j i u'; let A:= Y.award (s.profile i) (Glint.partition (s.profile i) (R j i).exp); Allot (R j i) (F.o j i) (Mural.sheet s D h) A Y.propAim Y.scope (s.profile i) (B j i u') (μ:= F.μ j i) s.kernel (s.profile j) (C j i) (u j i) Chi.canonical (r j i) Y.η_goal Y.limit Y.ξ x ∧ (∀ y, x≤ y→ Y.books.extra (B j i u') y)
    let q j i:= Finset.univ.sup (fun (g:Fin (G'.count j i))=> 4*(G'.slots j i g).scope.ℓ+50)
    let V j:= max (T0.shells j) (fromMax q j)
    have hy j i (h: StepStages j i) : ∀ᶠ x: ℝ in atTop,∀ g:Fin (G'.count j i), s.first ≤ i → (∀ h':4 ≤ j,(Mural.sheet s D h').Branches (query s K j i|>.bind) G → Pℓ j i x g h')∧∀ c:Side,V j * (1+radiusB x) ≤ c.val→ (G'.slots j i g).scope.Tiled x c := by
       apply eventually_all.mpr; intro g; by_cases hp:s.first ≤ i; swap; · exact Eventually.of_forall fun _ hx=>(hp hx).elim
       have hh1 :∀ᶠ x:ℝ in atTop,∀ h':4 ≤j, (Mural.sheet s D h').Branches (query s K j i|>.bind) G→ Pℓ j i x g h':= by
          by_cases he:4≤j; swap; · exact Eventually.of_forall fun _ hx=>(he hx).elim
          by_cases ht:(Mural.sheet s D he).Branches (query s K j i|>.bind) G
          · exact ((hB j i g he h hp ht).2.2).mono fun _ hh _ _=> hh
          exact Eventually.of_forall fun _ _ hx=>(ht hx).elim
       let s':= (G'.slots j i g).scope; have hV: 4*s'.ℓ+50 ≤ V j := (show (4*s'.ℓ+50)≤ q j i from Finset.le_sup (f:=fun g=> (4*(G'.slots j i g).scope.ℓ+50)) (b:=g) (Finset.mem_univ _)).trans ((le_fromMax q h).trans (le_max_right ..)) -- b?
       filter_upwards [hh1,s'.growth] with x hx ht hi; refine ⟨hx,fun c hc=>?_⟩
       obtain ⟨h1,h2,h3,h4,h5⟩:= ht; let d:=radiusB x; have he: (4*s'.ℓ+50)*(1+d) ≤ c.val:= (Nat.mul_le_mul_right _ hV).trans hc
       change s'.Tiled x c; rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at he
       unfold d at he; constructor; all_goals omega
    obtain ⟨X,-,hx,hX⟩:= collect_upper T0.betaEntry _ (fun j=>eventually_transitions j _ _ (hy j)); refine ⟨{T0 with betaEntry:=X,shells:=V,growth:=fun j=> max (T0.growth j) 1},B,⟨hx,le_rfl,fun i=>le_max_left ..,fun i=>le_max_left ..⟩,fun U hU=>?_⟩
    have hQ j: X j ≤ U.betaEntry j:= hU.beta j; refine ⟨⟨_,_,hf,hk⟩,fun j i g h hv hj hs=> ?_,fun j i g h hi x hx c hc=>?_⟩
    · exact ⟨(G'.slots j i g).song _ (ht _ _),(hB j i g hj h hv hs).1,(hB j i g hj h hv hs).2.1,(hX j _ (hQ j) i h g hv).1 hj hs⟩
    have h : 1 ≤ U.growth j:= (le_max_right ..).trans (hU.growth j)
    apply (hX j x ((hQ j).trans hx) i ‹StepStages _ _› g hi).2 c
    exact (Nat.mul_le_mul (hU.shells j) (le_self_pow₀ (by omega) (by omega))).trans hc
end YM.RemainderComparison.Chron
