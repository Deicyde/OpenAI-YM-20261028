import YM.FullVolume.Train.Destination
/-! Backbone T/A assembled from actual alias weights, at puncture—analytic extension later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.OnTrack
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Flight Finset
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} (A:Levels G) (i:ℕ) {k:ℝ}
lemma _root_.Filter.Tendsto.matrix_mul {α β γ : Type*}[Fintype β]{R:ℕ→Matrix α β ℂ}{S:ℕ→Matrix β γ ℂ} {r s}(h:Tendsto R atTop (𝓝 r))(hx:Tendsto S atTop (𝓝 s)): Tendsto (fun i=> R i*S i) atTop (𝓝 (r*s)):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_finsetSum _ fun x _=> ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) x).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hx x) j))
private lemma bright (k:ℝ)(hk:0<k){j}(v:ℕ→Train j){p:Momentum}(hp:physical p){Y x}(h:Tendsto (fun n=>levelD k (v n) x p) atTop (𝓝 Y)): Silver Y:=by
   refine ⟨Y.re,ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp h) (fun n=>(D_cost k hk _ _ hp).re_nonneg), tendsto_nhds_unique h ?_⟩
   exact ((Complex.continuous_re.continuousAt.tendsto.comp h).ofReal).congr fun n => (D_cost k hk _ _ hp).of_real
private lemma golden (j) : Continuous (mask j):=by unfold mask inventory; fun_prop
private lemma coins (k:ℝ)(hk:0<k){j}(v:ℕ→Train j){p:Momentum}(hp:p∈realCube zone)(he:p≠0)(h:∀ x,∃ y:ℂ,0<y.re ∧ Tendsto (fun n=>levelD k (v n) x p) atTop (𝓝 y)) (S:Side):
      (∀ x, ∃ y:ℂ, 0<y.re ∧ Tendsto (fun n=>scaleD S k (v n) p x) atTop (𝓝 y)) ∧ ∃ a:ℂ,a≠0 ∧ Tendsto (fun n=>scaleR S k (v n) p) atTop (𝓝 a) ∧ ∃ F M, Tendsto (fun n=> pulse k (v n) p) atTop (𝓝 F) ∧ Tendsto (fun n=> vault k (v n) p) atTop (𝓝 M) ∧ ∃ D I, Tendsto (fun n=>fieldD S k (v n) p) atTop (𝓝 D) ∧ Tendsto (fun n=>fieldI S k (v n) p) atTop (𝓝 I):=by
   choose y hy hv using h
   have heS := Silver.side S; let Y :ℂ:= ((S.val:ℂ)^2)⁻¹; have ha : Silver Y:= (heS.pow _).inv; have hx : Y≠0:=inv_ne_zero (pow_ne_zero _ (side_ne S))
   have HS x:Silver (y x):=bright k hk v hp.1 (hv x)
   have Hy x:y x≠0:=by intro hz; have hp:=hy x; rw [hz] at hp; exact lt_irrefl _ hp
   refine ⟨fun x=>⟨Y*y x,?_, (hv x).const_mul _⟩,?_⟩
   · rw [ha.real_mul]; exact mul_pos (ha.re_ne hx) (hy x)
   let R:=∑ i,jewel 1 p i/y i; have H : Tendsto (fun n=>rho k (v n) p) atTop (𝓝 R):=tendsto_finsetSum _ fun i _=> tendsto_const_nhds.div (hv i) (Hy i)
   have hR:R≠0:=by
        have hj (x:Axis): Silver (jewel 1 p x) :=by
             have hg:= seedQ_flip 1 p x; rw [show star p=p from hp.1] at hg; unfold jewel; rw [hg]
             exact Silver.gram _
        have hz(i):Silver (jewel 1 p i/y i):=(hj i).div (HS i)
        by_contra hu
        have hh x:jewel 1 p x/y x=0:=by
                 by_contra hk; apply not_lt_of_ge (show R.re≤0 by rw [hu]; exact le_rfl); unfold R; rw [Complex.re_sum]; exact lt_of_lt_of_le ((hz x).re_ne hk) (Finset.single_le_sum (f:=fun i=> (jewel 1 p i/y i).re) (fun i _=> (hz i).re_nonneg) (Finset.mem_univ _))
        have hh'(x): jewel 1 p x=0:=by have hX:= hh x; field_simp at hX; simp_all
        exact divisor_ne 1 hp he (by unfold divisor; change ∑ x,jewel 1 p x=0; simp [hh'])
   have hJ : Tendsto (fun n=> fun i=>levelD k (v n) i p) atTop (𝓝 y):= tendsto_pi_nhds.mpr hv
   refine ⟨(S.val:ℂ)^4*R,mul_ne_zero (pow_ne_zero _ (side_ne _)) hR,H.const_mul _,_,_,((H.inv₀ hR).smul ((golden 2).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun i=> (hv i).inv₀ (Hy i)))).congr (fun n=> (pulse_sources k hk _ hp he).symm), (H.smul ((golden 2).continuousAt.tendsto.comp hJ)).congr (fun n=>(vault_sources k hk _ hp he).symm),_,_,(golden 1).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun i=> (hv i).const_mul Y),(golden 1).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun i=> ((hv i).const_mul Y).inv₀ (mul_ne_zero hx (Hy i)))⟩
lemma blade {p:Momentum}(hp:p∈baseCube)(hk:0<k): ∃ M F, Tendsto (fun n=> (pink k (location A n i)).read p) atTop (𝓝 F) ∧ Tendsto (fun n=> (blue k (location A n i)).read p) atTop (𝓝 M):=by
   have hX n:= heart_true k hk (A.clock.adm i) (location A n i)
   by_cases ht:p=0
   · subst p; exact ⟨1,1,tendsto_const_nhds.congr (fun n=> ((hX n).1.echo _ hp|>.trans (pulse_zero ..)).symm), tendsto_const_nhds.congr fun n=> ((hX n).2.echo _ hp|>.trans (vault_zero ..)).symm⟩
   obtain ⟨-,a,-,-,F,M,hF,hM,-⟩:= coins k hk _ (base_subset_realCube zone_pos hp) ht (fun x=> arrival A x i hp ht hk) 1
   exact ⟨M,F,hF.congr fun n=> ((hX n).1.echo _ hp).symm,hM.congr fun n=> ((hX n).2.echo _ hp).symm⟩
local notation "L"=> A.S.block i
set_option maxHeartbeats 600000 in
private lemma lorries (p:Momentum)(hp:p∈baseCube)(he:p≠0)(hk:0<k) : ∀ l:Site (A.S.block i), ∃ T R,Tendsto (fun n=>pilot k (destination A n i) p l) atTop (𝓝 T) ∧ Tendsto (fun n=>wire k (destination A n i) p l) atTop (𝓝 R):=by
   let v (N):= destination A N i; let Q(l:Site (A.S.block i)):= aliasAt p l
   have hp':= base_subset_realCube zone_pos hp; have hkP (l:Site (A.S.block i)):= alias_regular (P:=v 0) hp' l (Or.inr he)
   have hV (x): ∃ y:ℂ,0<y.re ∧ Tendsto (fun n=>levelD k (v n|>.land) x p) atTop (𝓝 y):=by
       obtain ⟨Y,h,H⟩:= arrival A x i hp he hk; refine ⟨Y,h,H.congr' ?_⟩
       filter_upwards [eventually_gt_atTop i] with n hn; simp only [loc_land A n i hn,v]
   obtain ⟨b,a,ha,hF,S,Y,hS,hY,D,I,hD,hI⟩:= coins k hk _ hp' he hV 1
   choose z c hc hF' S' Y' hS' hY' D' I' hD' hI' using fun l:Site L=>coins k hk (fun n=>v n|>.wing) (p:=Q l) (hkP l).1 (hkP l).2 (fun x=> arrival A x (i+1) (alias_base hp l (v 0|>.odd)) (hkP l).2 hk) L
   choose r hr ht using z; let J:= (v 0).patch
   let Z(l:Site L):=yen (massFilter J) (Q l); let T(l:Site L):=∑ i, r l i; let V:=∑ l,Z l*T l
   have hT l: Tendsto (fun n=> total k (v n) (Q l)) atTop (𝓝 (T l)):= by
        -- P.L from dest fixed
        let B : ℕ→Axis→ℂ:= fun n x=> scaleD L k (location A n (i+1)) (Q l) x
        exact tendsto_finsetSum (f:=fun i n=> B n i) _ fun i _ => ht l i
   have hV': Tendsto (fun n=>tabE k (v n) p) atTop (𝓝 V):= tendsto_finsetSum (ι:=Site L) (f:=fun l n=> Z l * total k (v n) (Q l)) (Finset.univ : Finset (Site L)) fun l _=> (hT l).const_mul (Z l)
   have hz (l): Silver (Z l):=by
       have h : star (massFilter J (Q l))=massFilter J (-Q l) :=by unfold massFilter; rw [star_pow,Train.area_conj,show star (Q l)=Q l from (hkP l).1.1]
       unfold Z yen; rw [← h]; exact Silver.gram _
   have hm:V ≠ 0:=by
       have hZ: Z 0≠0:=by
           have hh:= mass_filter_live (v 0) hp'; have hy:= mass_filter_live (v 0) (realCube_neg hp'); rw [show aliasAt (-p) (0:Site (v 0|>.L))=-aliasAt p (0:Site (v 0|>.L)) from by simpa only [neg_zero] using alias_reverse p (v 0|>.odd) (0: Site (v 0|>.L))] at hy; exact mul_ne_zero hh hy
       have hw l : 0<(T l).re := by unfold T; rw [Complex.re_sum]; exact lt_of_lt_of_le (hr l 0) (Finset.single_le_sum (f:=fun i=> (r l i).re) (fun i _=> (hr l i).le) (Finset.mem_univ _))
       intro h; have hV:0<V.re:=by
           unfold V; rw [Complex.re_sum]; simp_rw [(hz _).real_mul]; exact lt_of_lt_of_le (mul_pos ((hz 0).re_ne hZ) (hw 0)) (Finset.single_le_sum (f:=fun i: Site L=>_) (fun i _=> mul_nonneg ((hz i).re_nonneg) (hw i).le) (Finset.mem_univ _))
       rw [h] at hV; exact lt_irrefl _ hV
   intro l; have he' := ((hT l).const_mul (massFilter J (-Q l))).div hV' hm
   have hf' := ((tendsto_const_nhds (x:=Z l)).mul hF).div (hF' l) (hc l)
   let F:= flux (v 0) 1 (Q l); let H:= flux (v 0) 2 (Q l)
   have hM := ((tendsto_const_nhds (x:=mirage 1 1 p)).matrix_mul hS).matrix_mul (tendsto_const_nhds (x:=signal 1 1 p))
   have ht':= (hF.inv₀ ha).smul ((tendsto_const_nhds (x:=mirage 1 0 p)).matrix_mul hI)
   have hA:= ((((hD' l).matrix_mul (tendsto_const_nhds (x:=F))).matrix_mul hM).add (he'.smul ((tendsto_const_nhds (x:=signal L 0 (Q l))).matrix_mul ht')))
   have hQ:= (tendsto_const_nhds (x:=(1:Frequency 2 2))).sub (((hS.matrix_mul (tendsto_const_nhds (x:=signal 1 1 p))).matrix_mul hD).matrix_mul (tendsto_const_nhds (x:=mirage 1 1 p)))
   have hB := ((((((hS' l).matrix_mul (tendsto_const_nhds (x:=signal L 1 (Q l)))).matrix_mul (hD' l)).matrix_mul (tendsto_const_nhds (x:=F))).matrix_mul (tendsto_const_nhds (x:= mirage 1 1 p))).add (hf'.smul ((tendsto_const_nhds (x:=H)).matrix_mul hQ)))
   exact ⟨_,_, hA.congr fun n=>(pilot_match k hk (v n) hp' he l).symm, hB.congr fun n=> (wire_match k hk (v n) hp' he l).symm⟩
lemma presentT (p:Momentum)(hp:p∈baseCube)(he:p≠0)(hk:0<k):
    (∀ x y,∃ T:ℂ,Tendsto (fun n=> (duo k (destination A n i)|>.A0).read p (x:Co L (TypeFace 1)) y) atTop (𝓝 T)) ∧
    ∀ x y,∃ R:ℂ,Tendsto (fun n=> (duo k (destination A n i)|>.T).read p (x:Co L (TypeFace 2)) y) atTop (𝓝 R):=by
    choose T R h g using lorries A i p hp he hk; let P n:= destination A n i
    obtain ⟨hx,ho⟩:= secure_both k hk (A.clock.adm (i+1)) (A.clock.adm i)
    constructor <;> intro ⟨x,y⟩ z
    · have H l:= (h l).const_smul (toll L 1 * listChip (aliasAt p l) [])|>.const_smul (mode (aliasAt p l) (lift x))
      have hm := tendsto_finsetSum (Finset.univ : Finset (Site L)) fun i _=> H i
      exact ⟨_, (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hm y) z).congr fun n=> (hx.bankRead (A.clock.adm _) 1 (u:=[]) (by simp) (P n) x hp y z).symm⟩
    have H l:= (g l).const_smul (toll L 2 * listChip (aliasAt p l) [])|>.const_smul (mode (aliasAt p l) (lift x))
    have hm := tendsto_finsetSum (Finset.univ : Finset (Site L)) fun i _=> H i
    exact ⟨_, (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hm y) z).congr fun n=> (ho.bankRead (A.clock.adm _) 2 (u:=[]) (by simp) (P n) x hp y z).symm⟩
end YM.Next.Free.OnTrack
