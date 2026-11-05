import YM.TraceExtension.Wicket.Basks
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open Planned.AtomRegular.Foliage Next.Fluctuations Next.SectorChange
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Edge (Site n)}{A K C:ℝ}{B:BudgetPoint}{P Q:Support n}{U:Config G n}{F H:Mellow G n}
def zest (R:Rep G n)(o:Edge (Site n))(s:ℝ): Badge n → Mellow G n:= Sum.elim (saw R s o) (fun i=> frog o s R.p (R.activities.E i))
lemma zested (G:Gauge)(k p:ℕ)(T:Collar G k)(hk:1≤k) : ∃ V A:ℝ,∃ P':ℕ,0≤V∧0≤A∧ ∀ (r r' m:ℕ)(s D σ δ w u C:ℝ)(Λ:ℝ)(n:Side)(R:Rep G n)(H:Finset (Badge n))(o:Edge (Site n))(Q:Support n), let B:=R.p;∀ h:B.order=k, Cube.Wire B 8 (h.symm ▸ T) →B.power=p→R.Lawful σ C Λ δ u→Geo.Width B R.clip σ→2≤ B.B→64*D≤ B.threshold→(∀ v:G.Color,‖v‖≤1→G.chord (G.lieExp (s • v))≤D)→ 20<n.val→halo 9 {o.1}⊆ Q→separation o.1 0 ≤r'→Below R o r m H→ ringsZ R o m r'→B.threshold*(1+(r':ℝ))^p ≤1→
    ∃ f:Badge n→ℝ,(∀ i∈H, let P:=Q∪boothC R i;0 ≤ f i ∧ Cohort B P o (zest R o s i)∧Career B P (zest R o s i) (f i))∧
       ∑ i∈H,B.mass (boothC R i) (f i) ≤ beamAmt R C σ Λ V r P' + vat B r' A * (((r'+r'+1)^4:ℕ)*δ):=by
    obtain ⟨V,⟨hv,D,k',hD,H⟩,he⟩:= saws G k; obtain ⟨C,hC,H'⟩:= dppaid G k p hk T; refine ⟨D,C,k',by positivity,hC,?_⟩; intro r r' m s E σ δ w u A Λ n R B o Q P h ht hp hR hG hB he' hS hQ hU hr hπ hNt hz; subst k; obtain ⟨f,hf,hf'⟩:= hR.labels.boundE
    let p':= fun i=> vat R.p r' C* f i; let g:Badge n→ℝ:= Sum.elim (fun i=> ladder R i V) p'; have hx: 0 ≤ vat R.p r' C:=by unfold vat; positivity[hikeFee_nonneg R.p r']
    have hh(i:Acre n): True:=trivial
    refine ⟨g,?_,?_⟩
    · intro i hi; obtain ⟨hw,hj,hM⟩:= hπ i hi; cases i with
      | inl i=> exact ⟨mul_nonneg (by positivity) (mul_nonneg (ports_n ..) (hv _)), saw_cohort s o _ _ hR.paths hB subset_union_right, he _ _ R i s o r' (hNt _ hw hj) rfl hB (by rw[show R.p.power=p from hp]; exact hz)⟩
      | inr j=>
        let x:= (R.activities.reg j).site; let V:=Q∪boothC R (.inr j); have h1:=hU.trans (subset_union_left (s₂:=boothC R (Sum.inr j))); have ht':= hR.labels.regular.smooth j
        exact ⟨mul_nonneg hx ((hf _).1), frogger ht' h1 subset_union_right E hS he',frog_price ht' (hf _) h1 subset_union_right r' (by have h:=hNt _ hw hj (R.activities.reg j).anchor; obtain ⟨q,hq,h⟩:=halo_spec.mp h; rw[mem_singleton.mp hq] at h; rw[separation_comm]; exact h) hr (H' P rfl hp ht n _ _ hQ h1) E hS he'⟩
    rw [sum_sum_eq_sum_toLeft_add_sum_toRight]; refine add_le_add (amount_beam o m hR hG V hv D (by positivity) k' r H B hπ) ?_; let y(i:ℕ):=R.p.mass (boothC R (.inr i)) (f i)
    have he := amount_E o m hR f hf hf' r r' B hNt hπ; apply le_trans ?_ (mul_le_mul_of_nonneg_left he hx); rw[Finset.mul_sum]; apply le_of_eq; exact sum_congr rfl fun i _=>mul_left_comm ..
lemma zenV(k:ℕ):0 ≤ budC k:=by induction k <;> unfold budC<;> positivity
-- Cost for products gathered: exact exponent, non-empty powerset buys slack
variable {L:Type}[DecidableEq L]
def velvet (B:BudgetPoint)(f:L→Mellow G n)(H:Mellow G n)(S:Finset L): Mellow G n:= fun U v=> H U v *∏ i∈S,(Real.exp (f i U v)-1)
lemma velvet_step {i:L}{f:L→Mellow G n}{S:Finset L}(h:i∉S): velvet B f H (insert i S)= (fun U v=> Real.exp (f i U v)-1)*velvet B f H S:=by ext1 U; ext1 v; unfold velvet; rw [prod_insert h,mul_left_comm]; rfl
abbrev brick {n:Side}(Q:Support n)(X:L→ Support n)(p:Finset L):= Q∪p.biUnion X
abbrev tidy (B:BudgetPoint)(f:L→ℝ)(i:L):= (2:ℝ)^B.order*(budC B.order*f i)
lemma velvet_grows (f:L→Mellow G n)(hx:L→Support n)(H:Mellow G n)(U:Finset L)(p:L→ℝ) (hp:∀ i∈U, Cohort B (Q∪hx i) o (f i)∧Career B (Q∪hx i) (f i) (p i)∧p i ≤ 1)(hh:Cohort B Q o H)(hZ:Career B Q H A): Cohort B (brick Q hx U) o (velvet B f H U)∧ Career B (brick Q hx U) (velvet B f H U) ((∏ i∈U,tidy B p i)*A):=by
    induction U using Finset.induction with
    | empty =>
       simp only [brick,biUnion_empty,union_empty,prod_empty,one_mul]; rw[show velvet B f H ∅=H from funext fun i=>funext fun j=>by simp[velvet]]; exact ⟨hh,hZ⟩
    | insert i V h ih=>
      obtain ⟨hx',hi,hT⟩:= hp i (mem_insert_self ..); let W:= brick Q hx (insert i V); let z:=velvet B f H V; obtain ⟨hk,hV⟩:=ih (fun j hj=> hp j (mem_insert_of_mem hj))
      have he : brick Q hx V⊆ W:=by unfold W brick; rw[biUnion_insert]; exact union_subset (subset_union_left) (subset_trans subset_union_right subset_union_right)
      have hX: Q∪hx i⊆ W:= union_subset subset_union_left ((subset_biUnion_of_mem hx (mem_insert_self i V)).trans subset_union_right); rw [velvet_step h,prod_insert h]; let g:= fun U v=> Real.exp (f i U v)-1; have ht: Career B W g (budC B.order*p i):=fun U hU v hv=>(Career.up hi hX U hU v hv).bud hT
      refine ⟨(hx'.sprout.up hX).blend (hk.up he),?_⟩
      convert! (Career.blend ht (Career.up hV he)) using 1; unfold tidy; ring
lemma block_brick (S:Finset L)(X:L→Support n)(v:Site n)(h:v∈Q)(hp:∀ i∈ S,v∈X i):coverNumber B.B (brick Q X S) ≤ coverNumber B.B Q+∑ i∈S,coverNumber B.B (X i):=by
    induction S using Finset.induction with
    | empty=>simp[brick]
    | insert i S hi ih=>
      rw [show brick Q X (insert i S)=X i∪brick Q X S from (by simp[brick,union_left_comm]),sum_insert hi,add_left_comm]; exact (Corona.meets_sum (hp _ (mem_insert_self ..)) (show v∈brick Q X S from mem_union_left _ h) _).trans (add_le_add_right (ih fun j hx=> hp j (mem_insert_of_mem hx)) _)
abbrev polar(B:BudgetPoint)(t:ℝ):=2^B.order*(budC B.order*t)
lemma light_wings (f:L→Mellow G n)(S:Finset L)(X:L→Support n)(o:Edge (Site n))(p:L→ℝ)(hf:o.1∈Q)(hp:∀ i∈S,0≤p i∧o.1∈X i)(he:∑ i∈S,B.mass (X i) (p i)≤C)(hA:0 ≤ A)(hx:polar B C ≤1):
   ∑ i∈S.powerset.erase ∅, B.mass (brick Q X i) ((∏ j∈i,tidy B p j)*A) ≤ 2*polar B C*B.mass Q A:=by
    let c(i:L):= B.mass (X i) (p i); let u:=polar B C; let P:=S.powerset.erase ∅; let f(i:L):=tidy B p i; let g(i:L):=polar B (c i)
    have hp'(i:L)(h:i∈S):0≤g i:= by unfold g c polar BudgetPoint.mass; positivity[zenV B.order,(hp _ h).1];
    have hy:∑ i∈S,g i ≤ u:=by simp_rw[g,u,polar, ← mul_sum]; unfold c; gcongr; exact zenV _
    have hh : (∑ i∈P,∏ j∈i,g j)+1 ≤ Real.exp u:=by
        rw [show (1:ℝ)= ∏ j∈ (∅:Finset L),g j from prod_empty.symm, show (∑ i∈P,∏ j∈i,g j)+_= _ from Finset.sum_erase_add S.powerset (fun i=>∏ j∈i,g j) (show ∅∈ S.powerset from mem_powerset.mpr (empty_subset _)), ← prod_one_add]; apply le_trans _ (Real.exp_monotone hy); rw [Real.exp_sum]; exact prod_le_prod (fun i hi=> add_nonneg zero_le_one (hp' i hi)) fun i hi=> (add_comm ..).trans_le (Real.add_one_le_exp _)
    have hu : 0 ≤ u:= (sum_nonneg fun i hi=>hp' i hi).trans hy
    have hZ: (∑ i∈P,∏ j∈i,g j) ≤ 2*u:=by
       have h := Real.abs_exp_sub_one_le (show |u| ≤1 from (abs_of_nonneg hu).trans_le hx); rw [abs_of_nonneg hu] at h; linarith only [le_abs_self (Real.exp u-1),h,hh]
    apply le_trans (b:=(∑ i∈P,∏ j∈i,g j)*B.mass Q A) _ (mul_le_mul_of_nonneg_right hZ (mul_nonneg (Real.exp_pos _).le hA)); rw [Finset.sum_mul]; refine sum_le_sum fun j hj=> ?_
    have h' := mem_powerset.mp (mem_of_mem_erase hj); let Y:= brick Q X j; have hx : (coverNumber B.B Y:ℝ) ≤ coverNumber B.B Q+ ∑ i∈j,(coverNumber B.B (X i):ℝ):= by exact_mod_cast block_brick (B:=B) j X o.1 hf (fun i hi=> hp i (h' hi)|>.2)
    have hG(i:L): g i=f i*Real.exp (B.supportExponent*coverNumber B.B (X i)):=by unfold g f c polar BudgetPoint.mass tidy;ring
    conv_rhs => simp only [hG,prod_mul_distrib,← Real.exp_sum,← mul_sum]
    change Real.exp (B.supportExponent* coverNumber B.B Y) * ((∏ i∈j,f i)*A)≤ _; refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left hx B.exponent_pos.le)) ?_) (le_of_eq ?_)
    · exact mul_nonneg (prod_nonneg (fun i hi=>by unfold f tidy; positivity [(hp _ (h' hi)).1,zenV B.order])) hA
    rw [mul_add,Real.exp_add]; unfold BudgetPoint.mass;ring
-- Returns for ANY P.Envelope off domain not required.
lemma returns (C Z:ℝ)(f:L→Mellow G n)(e:Lines G n 1)(X:L→Support n)(S:Finset L)(A:ℝ)(hC: C ≤1)(hp:polar B C ≤1)(hA:0 ≤ A) (p:L→ℝ)(ho:(beaconR e).1 ∈ Q)(h : ∀ i∈S,0≤ p i ∧ (beaconR e).1 ∈X i ∧ Cohort B (Q∪X i) (beaconR e) (f i) ∧Career B (Q∪X i) (f i) (p i)) (hg:Cohort B Q (beaconR e) H) (hy:Career B Q H A) (ht:∑ i∈S,B.mass (X i) (p i)≤ C) :
    (∀ i∈S.powerset,let F:=warp (velvet B f H i) e; let P:=brick Q X i; Cohort B P (beaconR e) (velvet B f H i) ∧ B.Regular P F ∧ B.supBounds (0:Site n) P F ((∏ j∈i,tidy B p j)*A))∧
   ∑ i∈S.powerset.erase ∅, B.mass (brick Q X i) ((∏ j∈i,tidy B p j)*A) ≤2*polar B C*B.mass Q A:=by
   refine ⟨fun i hi=>?_,light_wings f S X (beaconR e) p ho (fun i hi=> ⟨(h _ hi).1,(h _ hi).2.1⟩) ht hA hp⟩
   have hQ : i⊆ S:= mem_powerset.mp hi; have hx(j)(hj:j∈S): p j ≤ 1:=by
      apply (B.loMass (X j) _ (h j hj|>.1)).trans (le_trans ?_ (ht.trans hC)); exact single_le_sum (f:=fun i=>B.mass (X i) (p i)) (fun i hi=> mul_nonneg (Real.exp_pos _).le ((h i hi).1)) hj
   obtain ⟨hz,hV⟩:= velvet_grows f X H i p (fun j hj=> ⟨(h j (hQ hj)).2.2.1,(h j (hQ hj)).2.2.2,hx j (hQ hj)⟩) hg hy
   exact ⟨hz,hz.garment,hz.limitH hV (mul_nonneg (prod_nonneg fun i hi=>by unfold tidy; positivity [zenV B.order, (h i (hQ hi)).1]) hA) ⟩
end YM.Trace.Wicket
