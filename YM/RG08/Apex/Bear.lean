import YM.RG08.Apex.Marble
/-! # Carry normalization through all admitted grades. r=1 read
 at e from R^(q) might touch inadmissible precision; rank1 identically
 zero at these grades, no appeal to readout outside them. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Summit
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free
open scoped BigOperators Topology Real Classical
open Chain Wings
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {I : Type} {u : I→Windows} {r e j s : ℕ}

lemma statues_here (t : Launch u) (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E)(r): Mending (fun i=>moon X ν D (low (escalates t i)) e r) (statue X ν D t.i e r) := Both.mended (δ:=fun i=> chop X (1/4) (escalates t i)) (y:= t.farY X) (B:= Tier S t.i) ((statues h hp hv hs he _).mold (fun i=>low (escalates t i))) (fun _=> (gain_pos ..).le) (bye X t) (S.positive _)
lemma leasePass {y : ℝ} {v:ℕ→ℝ}{δ:ℕ→ℝ} {x : ℝ} (hδ: 0 ≤ δ)(he:Tendsto δ atTop (𝓝 0))(h : Lease (fun _=> y) δ v (fun _=>x)) : Tendsto v atTop (𝓝 x) := by
  obtain ⟨A,⟨C,p,hc,H⟩,hv⟩:=h.asset; apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i=> norm_nonneg _) (fun i=> (hv i).trans (mul_le_mul_of_nonneg_right (H i).2 (hδ i))) (by simpa using he.const_mul (C*y^p))
lemma leaseKinetic (h:Circuit S ν D u) : Lease (menu X) (chop X (u:=u) (r:=0) (1/4)) (fun i=>probeK ν (orbit X i)) (fun i=>probeK ν (quartz X G i.i)) := cost_probe ν (fun _=> S.positive _) (patched h) (h.cup.transfer toLaunch)
lemma Lease.whirls {y δ f g:I→ℝ}{J:Type}(h : Lease y δ f g)(u : J→I) : Lease (fun i=>y (u i)) (fun i=>δ (u i)) (fun i=> f (u i)) (fun i=>g (u i)) := ⟨h.has.transfer _,h.also.transfer _,_,h.asset.choose_spec.1.transfer u,fun i=> h.asset.choose_spec.2 _⟩
lemma probe_kept (t:Launch u)(h:Circuit S ν D u) : probeK ν (quartz X G t.i)=1:=
    tendsto_nhds_unique_of_eventuallyEq (leasePass (y:= t.farY X) (x:=probeK ν (quartz X G t.i)) (fun _=> (gain_pos ..).le) (bye X t) (Lease.whirls (leaseKinetic h) (fun i=> low (escalates t i)))) tendsto_const_nhds (.of_forall (fun i=> (X.high_stocks ..).2.2))
lemma square_glow (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E) : probeK ν (statue X ν D t.i e 2)=0 := by
  have ht:= cost_probe ν (fun _=>S.positive _) (statues h hp hv hs he 2) (h.cup.transfer toLaunch)
  refine tendsto_nhds_unique_of_eventuallyEq (leasePass (y:=t.farY X) (x:=probeK ν (statue X ν D t.i e 2)) (fun _=> (gain_pos ..).le) (bye X t) (Lease.whirls ht (fun i=> low (escalates t i)))) tendsto_const_nhds (.of_forall (fun i=> (rallies hp hv _).totes.balance e))
lemma monument (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E)(hh:r<2) : statue X ν D t.i e r=0 := tendsto_nhds_unique_of_eventuallyEq (statues_here t h hp hv hs he r|>.played) tendsto_const_nhds (.of_forall (fun i=> barren hs hp hv _ _ hh))
lemma graces_get (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple) : Gets (graving E (granite X ν D t.i)):= graving_stop _ (A:=fun i=> lunar X ν D (escalates t i)) (fun i=> (X.rawStep ν D hp hv (escalates t i).cut).1) (fun e he=>grantPass t h hp hv hs he)
lemma haltLocal (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple) : Gets (graving E (statue X ν D t.i)):= graving_stop _ (A:=fun i=> moon X ν D (low (escalates t i))) (fun i=> (X.packing ν D hp hv (escalates t i|>.low.cut)).1) (fun e he=> statues_here t h hp hv hs he)

lemma granite_port (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E) : granite X ν D t.i e 1=0:= by
   refine tendsto_nhds_unique_of_eventuallyEq (grantPass t h hp hv hs he _|>.played) tendsto_const_nhds (.of_forall fun i=> ?_)
   let k:= escalates t i
   let A := lunar X ν D k
   have hu := X.rawStep ν D hp hv k.cut
   by_cases he : A e 1≠0
   · obtain ⟨hp,q,hq⟩:= hu.1.1 e 1 he
     apply first_stencil (F:=A e 1) hs (hu.1.2 e 1).1
     intro m; obtain ⟨f,H,hF⟩:=hu.2 m q 1; refine ⟨f,H, (hF _ le_rfl).trans ?_⟩
     rw [sector_unique _ _ hp (by decide) hq.symm]
   exact not_ne_iff.mp he

private lemma rentSeal (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e ≤ E) (ha:Played e (r+2)) : Both (menu X) (chop X (1/4)) (fun t:Wings u 1=> moon X ν D t.low e (r+2)) (fun t=> correct ν (granite X ν D t.i) (quartz X G t.i) e (r+2)) (fun t=>Tier S t.i) := by
  have hz:= (patched h).mold low; obtain ⟨hx,k,hk⟩:=ha
  have ht : e=r+2*k:=by omega
  subst e
  have hh (t:Wings u 1) : probeK ν (quartz X G t.i)=1:= probe_kept t.toLaunch h
  simp_rw [action_step hp hv _ hx]
  let Y : Wings u 1→Air G := fun t=> granite X ν D t.i
  match r with
  | 0=>
    cases k with
    | zero=> omega
    | succ k=>
      have hT : 2*(k+1) ≤ E:=by omega
      have hF:= duetCharge (U:=Y) (T:=lunar X ν D) (P:=fun t:Wings u 1=> orbit X t) (M:=fun t=>quartz X G t.i) ν (sh X) (fun _=> S.positive _) (h.cup.transfer toLaunch) k (fun j H Hp=> graces h hp hv hs (e:=2*j) (by omega) 2) hz
      have hH:= penny_both ν (r:=0) (sh X) (fun _=> S.positive _) (h.cup.transfer toLaunch) hz (graces h hp hv hs hT 2)
      have hm (t:Wings u 1): correct ν (granite X ν D t.i) (quartz X G t.i) (0+2*(k+1)) (0+2) = penny ν (quartz X G t.i) 0 (Y t (2*(k+1)) 2)+duetT ν (Y t) (quartz X G t.i) k:= by simp only [Nat.zero_add]; exact deuce ν _ _ k (hh t)
      simp_rw [hm,Nat.zero_add,morph,Nat.add_sub_cancel]; exact hH.add hF (sh X)
  | j+1=>
    have hT := titanCharge (T:=fun t=> lunar X ν D t) (U:=Y) (P:=fun t:Wings u 1=> orbit (G:=G) X t) (M:=fun t=>quartz X G t.i) ν (sh X) (fun _=>S.positive _) (h.cup.transfer toLaunch) k j (fun i H hx=> graces h hp hv hs (e:=2*i) (by omega) _) (fun i H=> graces h hp hv hs (e:=j+1+2*i) (by omega) _)
    simp_rw [show ∀ (t:Wings u 1), correct ν (granite X ν D t.i) (quartz X G t.i) (j+1+2*k) (j+1+2)=Y t (j+1+2*k) (j+3)+ eclat ν (Y t) (quartz X G t.i) k j from fun t=>tinder ν _ _ k j] -- meta tactic choose?
    exact (graces h hp hv hs he (j+3)).add hT (sh X)

theorem resets (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E)(r) : statue X ν D t.i e r=correct ν (granite X ν D t.i) (quartz X G t.i) e r:= by
    by_cases ha:Played e r; swap
    · have hh := not_ne_iff.mp (mt ((haltLocal t h hp hv hs).1 e r) ha); rw [graving,if_pos he] at hh; rw [correct,if_neg (by tauto),hh]
    match r with
    | 0=> rw [monument t h hp hv hs he (by decide),correct, if_neg (by simp)]
    | 1=>
      obtain ⟨h₁,q,hq⟩:=ha
      rw [monument t h hp hv hs he (by decide),correct_p _ _ _ (by decide) h₁ hq]; symm; refine Finset.sum_eq_zero fun j hj=> ?_
      have ht:=mem_range.mp hj; unfold sector; rw [granite_port t h hp hv hs (by omega),smul_zero]
    | j+2=>
      let V:=correct ν (granite X ν D t.i) (quartz X G t.i) e (j+2)
      apply tendsto_nhds_unique (statues_here t h hp hv hs he _).played
      exact Mending.played (V:=V) (Both.mended (y:= t.farY X) (δ:=fun i=>chop X (1/4) (escalates t i)) (B:=Tier S t.i) ((rentSeal h hp hv hs he ha).mold (escalates t)) (fun _=>(gain_pos ..).le) (bye X t) (S.positive _))
end YM.RG08.Summit
