import YM.TraceExtension.Shepherd.Shipyard
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side}{R:Rep G n}{x:V→Site n} {d:V→Step}{ν:G.El→ G.El}{o:V↪Site n} {P:V→ Support n}{J:V→ Config G n→ G.El →ℂ}
    {σ A v δ u:ℝ}(h:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent) (m:ℕ) {D:ℝ} (HX: Palace R x d ν o P J m D)
local notation "M!"=>R.p.B
local notation "d!"=>R.p.supportExponent
local notation "C!"=> hull R m HX.terse HX.seats (d:=d) (ν:=ν) (J:=J)
-- input extensive. sum-dependent
structure ExpenseH (A v b δ u σ p D w:ℝ)(R:Rep G n)(l m k:ℕ):Prop where
   weight : 1 ≤ w
   sum : tariff R (wingC R D σ A v) (2*δ) ≤ 1
   omega : 4*(Real.exp (-(m:ℝ))*tariff R (leaseC R σ A v) δ) ≤ 1
   pay : ∃ c r:ℝ, 1 ≤ c ∧ 4*c*Real.exp ((R.p.supportExponent-4+1)*(l:ℝ)) ≤ Real.exp k ∧ 0 ≤ r ∧
               (p*Real.exp ((R.p.supportExponent-4+1)*(l:ℝ))*Real.exp 2)*(w^2/c)≤r ∧
               (let t:= r+(2*4*Real.exp k*(Real.exp (-(m:ℝ))*tariff R (leaseC R σ A v) δ)+2*Real.exp k*b); (((R.p.B + R.p.B +1)^4:ℕ):ℝ)*t ≤ 1 ∧ Real.exp t-1 ≤ u)
include h H hv he HX
lemma scoops (w c p r:ℝ)(hw:1 ≤ w)(hc:1 ≤ c)(hr: 0 ≤ r)(l:ℕ)(hp:0≤ p)(hf:∀ i U k,‖J i U k‖ ≤ p)(hP:∀ i,coverNumber M! (P i)≤ l)(hq: tariff R (wingC R D σ A v) (2*δ) ≤ 1)(hD:(p*Real.exp ((R.p.supportExponent-4+1)*(l:ℝ))*Real.exp 2)*(w^2/c)≤r)
    : ∃ f:(Yarns R x m)→ℝ,(∀ i,0≤ f i∧∀ U v,‖(C!|>.paint i U v)‖*(w^2/c) ≤ f i)∧ Hit (C!|>.size) M! f (d!-4+1) r:=by
   let a:= d!-4; let M:= C!;let e:=w^2/c; have hp':0≤e:=by positivity
   have he':0≤ a:= sub_nonneg.mpr he
   have hs(i:V):∃ f: Finset (docks R x m i) →ℝ, (∀ p,0≤ f p∧∀ U v,‖M.paint ⟨i,p⟩ U v‖ ≤ f p)∧∑ j, f j*Real.exp ((a+1)*coverNumber M! (M.size ⟨i,j⟩)) ≤ p*Real.exp ((a+1)*l)*Real.exp 2:=by
       have hy:= HX.uses i; have ht:= (G.chord_nonneg _).trans (hy.price 1)
       obtain ⟨b,hb,hv'⟩:= wings R h H (by linarith) D ht
       obtain ⟨f,hf,hg⟩:= earns R (x i) (d i) h H hv he m _ _ (HX.uses i) (HX.terse i) (a+1) p (by linarith only[he']) (show d!-4+1≤d!-1 by linarith) (hf i) hp b hb _ hv' hq
       exact ⟨f,hf,hg.trans (by gcongr; exact_mod_cast hP i)⟩
   choose f hf hy using hs; let Y(i:Yarns R x m):=f i.1 i.2*e
   have hz(i:Yarns R x m):0 ≤ Y i:= mul_nonneg ((hf _ _).1) hp'
   refine ⟨Y,fun ⟨i,j⟩=>⟨hz _,fun U v=>mul_le_mul_of_nonneg_right ((hf _ _).2 U v) hp'⟩,painter M _ _ hr Y hz ?_ ?_⟩
   · intro i; let F(y:Yarns R x m):= Y y*Real.exp ((a+1)*coverNumber M! (M.size y)); let Q:= univ.filter fun p:Yarns R x m=> p.1=i
     let u: Finset (docks R x m i)↪ Yarns R x m:= { toFun y:= ⟨i,y⟩, inj':=fun u v h=> eq_of_heq (Sigma.mk.inj h).2 }
     have ht: Q=univ.map u:=by
        ext ⟨j,k⟩; simp only [Q,mem_filter,mem_univ,true_and,mem_map]; constructor
        · intro ht; subst i; exact ⟨k,rfl⟩
        rintro ⟨c,hc⟩; exact (congr_arg Sigma.fst hc).symm
     change ∑ y∈ Q,F y ≤ r; rw [ht, Finset.sum_map]; apply le_trans _ ((mul_le_mul_of_nonneg_right (hy i) hp').trans hD); rw[Finset.sum_mul]; apply le_of_eq; refine Finset.sum_congr rfl (fun j _=>?_); change f i j*e*_= f i j*_*e; rw[mul_right_comm]; rfl
   intro i j hij; refine Finset.disjoint_left.mpr (fun k hk hm=> ?_)
   change i.1≠j.1 at hij
   have hs(x':Yarns R x m): M.size x'⊆ inspected (bluff R x P m x'.1):=by
       intro k hk; apply mem_union_left; refine mem_union.mpr ((mem_union.mp hk).imp id ?_); intro hz; obtain ⟨w,_,hh⟩:=mem_biUnion.mp hz; exact mem_biUnion.mpr ⟨w,mem_univ _,hh⟩
   exact disjoint_left.mp (HX.festival (Set.mem_univ _) (Set.mem_univ _) hij) (hs _ hk) (hs _ hm)
lemma welfare (w p:ℝ)(hp: 0≤p) (l k:ℕ) (hk:1 ≤ k)(hg:∀ i,coverNumber M! (P i) ≤ l)(hm: ∀ i j,i≠j→64*M!*k+2*M! ≤ separation (x i) (x j))(hf:∀ i U v,‖J i U v‖ ≤ p)(hZ:ExpenseH A v u δ 1 σ p D w R l m k) : Decked (agency C!) R (lance C!) (fun _=>w) (d!-4) 1:=by
   obtain ⟨c,r,h₁,hc,hr,hW,Hq⟩:= hZ.pay
   obtain ⟨f,hf,hx⟩:= scoops h H hv he m HX w c p r hZ.weight h₁ hr l hp hf hg hZ.sum hW
   obtain ⟨b,hb,Hb⟩:= tallL R h H (by linarith) m
   rw[show d!-2=d!-4+2 by ring] at Hb
   exact lay C! w _ _ _ (polo R h H hv he m HX) h.labels (sub_nonneg.mpr he) (by linarith only) k l c h₁ hk hm (fun i hi j hj hz=> (Finset.disjoint_of_subset_left (fun _ hx=> Finset.mem_union_left _ (Finset.mem_union_left _ hx)) (Finset.disjoint_of_subset_right (fun _ hx=> Finset.mem_union_left _ (Finset.mem_union_left _ hx)) (HX.festival hi hj hz)))) hg hc hZ.weight _ _ hZ.omega b hb Hb f hf hx Hq
end YM.Trace.Shepherd
