import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Line
import YM.Push.LOCAL_SPLITTING.Projection
import YM.Push.LOCAL_SPLITTING.Budget
import YM.Corona.Fit

/-!
True periodic density-germ normalization for a one-location source in the
Wilson history, for local comparison estimates (towards sec:qphys).

It does
NOT drop the wrapping regular terms or change the vacuum.

Efficiencies here
use bounds on jets of the *unmasked* regulars; identities only test on the
common germ with globally empty flag set.

Supports and test paths are the same
ones as in `Coefficient.Format` at the specified origin.

The price multiplier
in `germ_close` is fixed before period, threshold and stage.

No multi-source
estimate is implicit.
-/
noncomputable section
namespace YM.Trace.Physical.Germ
open Function Set Filter MeasureTheory Labels Lattice Wilson RG Source Analysis Next.Foundations
open ProjectorNext.Equivariance
open Push.Local
open Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 180000
variable {G : Gauge} {d : ℕ} {n : Side}
variable (F : Labels.Frame G d) (A : Hol G)

def label (A:Hol G)(o : Site n) (f:Config G n→ℂ)(d:ℕ) : Label G d :=
    if H : ∃ p : Label G d, JetTest A o p f then H.choose else 0

def jet (i : Probe G d) (θ : ℝ) (o:Site n)(f : Config G n→ℂ) := iteratedDeriv i.2.val (f ∘ A.testLinks d o (θ • i.1)) 0

def vector (θ: ℝ) (o:Site n) (f:Config G n→ℂ):F.Coeff := F.scaled θ (F.coords (label A o f d))

def projection (θ : ℝ) (o:Site n) (q:Coefficient F n):F.Coeff := q.x + ∑' i, vector F A θ o (q.regular i)

/-- The spatial wrapping suppression, not a small-coupling assertion. -/
def wraps (B:BudgetPoint)(n:Side) : ℝ := Real.exp (2*B.supportExponent - B.supportExponent * n.val / (10*(4*↑B.B+2)))

section
lemma wrap_lower_nat (K : ℕ) (X : Support n) (o:Site n)(hz:o∈X) (hx:¬Nonwrapping X o): n.val ≤ 10*(4*K+2)*(2+coverNumber K X) := by
    unfold Nonwrapping at hx; push Not at hx; obtain ⟨t,ht,hT⟩:=hx
    exact le_trans hT (le_trans (by gcongr; exact Corona.extent X K ht hz)
       (Nat.mul_le_mul_left _ (show coverNumber K X*(4*K+2)+2*K≤(4*K+2)*(2+coverNumber K X) by nlinarith)) |>.trans_eq (.symm (Nat.mul_assoc ..)))
lemma unweigh {c : ℝ}(hc :0≤c) (B:BudgetPoint)(X:Support n)(o:Site n)(hz:o∈X)(h:¬Nonwrapping X o): c ≤ wraps B n * B.mass X c := by
    have hb : (n.val:ℝ) ≤ 10*(4*(B.B:ℝ)+2)*(2+coverNumber B.B X):= by exact_mod_cast wrap_lower_nat B.B X o hz h
    have h0:0<10*(4*(B.B:ℝ)+2):=by positivity
    replace hb : (n.val:ℝ)/(10*(4*↑B.B+2)) ≤ 2+↑(coverNumber B.B X) := (div_le_iff₀ h0).mpr (by rw [mul_comm]; exact hb)
    unfold wraps BudgetPoint.mass; rw [mul_div_assoc,← mul_assoc, ←Real.exp_add]
    apply le_mul_of_one_le_left hc (Real.one_le_exp ?_)
    have he:= mul_le_mul_of_nonneg_left hb B.exponent_pos.le
    linarith
lemma computed {U:Support n}{f:Config G n→ℂ}{B:BudgetPoint}(hf:B.Regular U f)(o:Site n)(h:d≤B.order) : JetTest A o (label A o f d) f := by
    have he:=read_projection A o d f hf.symmetry ((hf.smooth _ (one_healthy U _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr h))
    unfold label; rw [dif_pos he.exists]; exact Classical.choose_spec he.exists
lemma charged (θ:ℝ){f : Config G n → ℂ}{o:Site n}{p:Label G d}(h:JetTest A o p f)(j : Probe G d): runProbe F j (F.scaled θ (F.coords p)) = jet A j θ o f := by
    let hz:= h (θ • j.1)
    unfold jet; rw [runProbe_eq, comp_def,(hz).2.2 _ (Nat.le_of_lt_succ j.2.isLt)]
    simp_rw [read_frame_scaled,F.coords.symm_apply_apply]
    congr 1
    funext t
    rw [show θ • scaleJet j.1 t=scaleJet (θ • j.1) t from (funext fun i => smul_comm θ (t^(i+2)) _)]
lemma short_vector {q:Coefficient F n}{R:Rep G n}{o:Site n}{i} (hf:q.Format o A R)(hd:d≤R.p.order)(hx : Nonwrapping (q.support i) o) : vector F A R.p.threshold o (q.regular i)=0 := by
    unfold vector; have hz : label A o (q.regular i) d=0:= JetTest.unique (computed A (hf.smooth i) o hd) ((jetTest_zero_iff A o (q.regular i) d).mpr (hf.projects i hx)) -- wrong
    rw [hz,map_zero,map_zero]

private theorem vector_price : ∃ C>0,∀ {n:Side}{B:BudgetPoint}{X:Support n}(o:Site n){f:Config G n→ℂ}{e:ℝ}, d≤B.order → d≤B.power → B.Regular X f → B.supBounds o X f e → F.coeffSize (vector F A B.threshold o f) ≤ C*e := by
    choose Q hQ hqt using fun (i:Probe G d)=> test_bound A i.1 d i.2 (Nat.le_of_lt_succ i.2.isLt)
    obtain ⟨U,K,hK,h⟩:=probe_budget F
    let D:=1+∑ i∈U,Q i
    have hz:0≤ ∑ i∈U,Q i:=Finset.sum_nonneg fun i _=>hQ i
    refine ⟨K*D,mul_pos (zero_lt_one.trans_le hK) (by unfold D; positivity), fun {n B X} o {f e} hd hp hreg he=>?_⟩
    have he0:=he.1
    have ht:0≤D*e:=mul_nonneg (add_nonneg zero_le_one hz) he0
    rw [mul_assoc]; refine h _ _ ht fun i hi=>?_ 
    rw [vector,charged _ _ _ (computed A hreg o hd)]; exact (hqt i n o X B f e hd hp hreg he).trans (mul_le_mul_of_nonneg_right (le_trans (Finset.single_le_sum (fun i _=>hQ i) hi) (le_add_of_nonneg_left zero_le_one)) he0)
-- explicit binder variable names above? implicit intro bind names n,B etc automatically not in scope
private theorem correction_budget {n : Side} {q:Coefficient F n}{R:Rep G n}{o:Site n}{κ r:ℝ}(hf:q.Format o A R)(hd:d≤R.p.order)(hp:d≤R.p.power)(hr:q.remBound o R κ r) (C:ℝ)(hC: C>0 ∧ ∀ {n:Side}{B:BudgetPoint}{X:Support n}(o:Site n){f:Config G n→ℂ}{e:ℝ}, d≤B.order → d≤B.power → B.Regular X f → B.supBounds o X f e → F.coeffSize (vector F A B.threshold o f) ≤ C*e) : SumBudget (fun i=>‖vector F A R.p.threshold o (q.regular i)‖) (C * wraps R.p n * r) := by
    obtain ⟨a,b,ha,hb,hab,hκ,⟨e,he,hs⟩,hf'⟩:=hr
    let u :=wraps R.p n
    have hc :0≤C:=hC.1.le
    have hu : 0≤u:=(Real.exp_pos _).le
    have hCU := mul_nonneg hc hu
    have hf0 :0≤r:= by linarith only [ha,hb,hab]
    let m(i):=R.p.mass (q.support i) (e i)
    refine sumBudget_mono (sumBudget_mul_left he hCU) (fun _=>norm_nonneg _) (fun i=>le_trans ?_ (by rw [mul_assoc])) (mul_le_mul_of_nonneg_left (by linarith) hCU)
    by_cases hwrap : Nonwrapping (q.support i) o
    · rw [short_vector F A hf hd hwrap,norm_zero]; exact mul_nonneg hc (mul_nonneg hu (he.1 i))
    exact (norm_le_size F _).trans ((hC.2 o hd hp (hf.smooth i) (hs i)).trans (mul_le_mul_of_nonneg_left (unweigh (hs i).1 R.p _ o (hf.origin i) hwrap) hc))
lemma vector_summable {n : Side}{R:Rep G n}{q:Coefficient F n}{o:Site n}{κ r:ℝ}(hf:q.Format o A R)(hr:q.remBound o R κ r)(hd:d≤R.p.order)(hp:d≤R.p.power) : Summable (fun i=>vector F A R.p.threshold o (q.regular i)):= by
    let h:= correction_budget F A hf hd hp hr (vector_price F A).choose (vector_price F A).choose_spec -- type pair vs Exists
    exact h.2.1.of_norm
theorem germ_close : ∃ C>0,∀ {n:Side}(R:Rep G n){o:Site n} (q:Coefficient F n){κ r:ℝ}, q.Format o A R → q.remBound o R κ r → d≤R.p.order → d≤R.p.power → ‖projection F A R.p.threshold o q-q.x‖ ≤ C*wraps R.p n*r := by
    obtain ⟨C,hC,h⟩:=vector_price F A
    refine ⟨_,hC,fun {_} R {_} q {_ _} hf hr hd hp=> ?_⟩
    simp only [projection,add_sub_cancel_left]; obtain H := correction_budget F A hf hd hp hr C ⟨hC,h⟩
    exact (norm_tsum_le_tsum_norm H.2.1).trans H.2.2
private theorem jet_vector {n:Side}{B:BudgetPoint}{X:Support n}(o:Site n){f:Config G n→ℂ}(hf:B.Regular X f)(hd:d≤B.order)(p:Probe G d): runProbe F p (vector F A B.threshold o f)=jet A p B.threshold o f := charged _ _ _ (computed A hf o hd) p
private lemma extract_cost {n:Side}{q:Coefficient F n}{R:Rep G n}{o:Site n} (h : ∃ v c, q.remBound o R v c) : ∃ E : ℕ → ℝ, (∀ i, R.p.supBounds o (q.support i) (q.regular i) (E i)) ∧ Summable E := by
  obtain ⟨v,c,a,b,ha,hb,hc,hv,⟨E,hE,he⟩,hf⟩ := h
  exact ⟨E,he,hE.2.1.of_nonneg_of_le (fun i=>(he i).1) (fun i=>R.p.loMass _ _ (he i).1)⟩
lemma probes_injective {x y:F.Coeff}(h:∀ p,runProbe F p x=runProbe F p y):x=y:= sub_eq_zero.mp (norm_le_zero_iff.mp ((norm_le_size ..).trans (((probe_budget F).choose_spec.choose_spec.2 _ 0 le_rfl (fun p _=>by rw [_root_.map_sub,h p,sub_self,norm_zero])).trans_eq (mul_zero _))))
lemma linear_projection {U:Type*}[AddCommGroup U][Module ℂ U]{n:Side}{R:Rep G n}{o:Site n}(x:U→Coefficient F n)(hd:d≤R.p.order)(hp:d≤R.p.power)(h:∀ u,(x u).Format o A R)(he:∀u,∃ κ r,(x u).remBound o R κ r)(hl:IsLinearMap ℂ (fun u=>(x u).x) ∧ IsLinearMap ℂ (fun u=>(x u).regular)) : IsLinearMap ℂ (fun u=>projection F A R.p.threshold o (x u)):= by
    have ht u:= let ⟨_,_,hb⟩:=he u; vector_summable F A (h u) hb hd hp
    constructor
    · intro u v
      have h1(i): vector F A R.p.threshold o ((x (u+v)).regular i) = vector F A R.p.threshold o ((x u).regular i)+vector F A R.p.threshold o ((x v).regular i):= by
        refine probes_injective F (fun p=>?_)
        rw [map_add,jet_vector _ _ _ ((h u).smooth i) hd,jet_vector _ _ _ ((h v).smooth i) hd,jet_vector _ _ _ ((h (u+v)).smooth i) hd]
        rw [show (x (u+v)).regular i = (x u).regular i+(x v).regular i from congr_fun (hl.2.map_add ..) i]
        have hw(u) := (computed A ((h u).smooth i) o hd (R.p.threshold • p.1)).1
        unfold jet
        exact iteratedDeriv_fun_add ((hw u).of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt))) ((hw v).of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt)))
      unfold projection; simp_rw [h1,(ht u).tsum_add (ht v),show (x (u+v)).x=(x u).x+(x v).x from hl.1.map_add ..]; abel
    intro k u
    have h1(i): vector F A R.p.threshold o ((x (k • u)).regular i) = k • vector F A R.p.threshold o ((x u).regular i):= by
        refine probes_injective F (fun p=>?_)
        rw [map_smul,jet_vector _ _ _ ((h u).smooth i) hd,jet_vector _ _ _ ((h (k • u)).smooth i) hd]
        rw [show (x (k • u)).regular i = k • (x u).regular i from congr_fun (hl.2.map_smul ..) i]
        unfold jet; exact iteratedDeriv_fun_const_smul_field (x:=0) (n:=p.2.val) k (fun t=>(x u).regular i (A.testLinks d o (R.p.threshold • p.1) t))
    unfold projection; simp only [h1,(ht u).tsum_const_smul,show (x (k • u)).x=k • (x u).x from hl.1.map_smul ..,smul_add]
lemma intrinsic_at {n:Side}{R:Rep G n} (B: SectionData F) (hb:B.Sound A) (o:Site n) (hsize:∀ x∈B.stencil,∀ i:Axis,20*((x i).natAbs+1)≤n.val)(hd:d≤R.p.order)(hp:d≤R.p.power)(hw: ∀ v,HasOrderAt (B.places v o) 1 d) (q v:Coefficient F n) (hq:q.Format o A R)(hv:v.Format o A R)(eq : ∃ κ r,q.remBound o R κ r)(ev : ∃ κ r,v.remBound o R κ r)
    (hden : q.density o B R =ᶠ[𝓝 1] v.density o B R): projection F A R.p.threshold o q=projection F A R.p.threshold o v := by
    let θ:=R.p.threshold
    have Q:=let ⟨_,_,H⟩:=eq; vector_summable F A hq H hd hp
    have V:=let ⟨_,_,H⟩:=ev; vector_summable F A hv H hd hp
    obtain ⟨a,h1a,ha⟩ := extract_cost F eq
    obtain ⟨b,h1b,hh⟩ := extract_cost F ev
    let G₀ (q : Coefficient F n):=B.places (F.scaled θ⁻¹ q.x) o
    have ht0 : G₀ v - G₀ q =ᶠ[𝓝 1] fun U=> ∑' i,(q.regular i-v.regular i) U := by
        filter_upwards [offFlags θ R.p.threshold_pos,hden] with U hu hE
        have hx i : Healthy R.p.threshold (q.support i) U := by unfold Healthy; rw [hu]; simp
        have hW i : Healthy R.p.threshold (v.support i) U := by unfold Healthy; rw [hu]; simp
        have hI : Summable fun i => q.regular i U := Summable.of_norm_bounded ha (fun i=>(h1a i).2 U (hx i) [] (by simp) (by simp))
        have hJ : Summable fun i => v.regular i U := Summable.of_norm_bounded hh (fun i=>(h1b i).2 U (hW i) [] (by simp) (by simp))
        rw [noFlagCharge _ _ _ hb hu,noFlagCharge _ _ _ hb hu] at hE
        simp only [Pi.sub_apply]; rw [hI.tsum_sub hJ]; apply sub_eq_sub_iff_add_eq_add.mpr
        exact (mul_left_cancel₀ (noFlagEval hu) hE |>.symm.trans (add_comm ..))
    let X(i):=q.support i ∪ v.support i
    have hs(i):R.p.Regular (X i) (q.regular i-v.regular i) ∧ R.p.supBounds o (X i) (q.regular i-v.regular i) (a i+b i):= by
        have hu:=regular_larger (u:=X i) (hq.smooth i) Finset.subset_union_left
        have hx:=regular_larger (u:=X i) (hv.smooth i) Finset.subset_union_right
        exact ⟨regular_sub hu hx, bound_sub hu hx (bound_larger (h1a i) Finset.subset_union_left) (bound_larger (h1b i) Finset.subset_union_right)⟩
    have h0(i)(q : Coefficient F n)(h : q.Format o A R)(t : Probe G d) : ContDiffAt ℝ (t.2.val:WithTop ℕ∞) (q.regular i ∘ A.testLinks d o (θ • t.1)) 0:= ((computed A (h.smooth i) o hd _).1.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ t.2.isLt))) -- computed JetTest type
    have hG(q : Coefficient F n): JetTest A o (F.coords.symm (F.scaled θ⁻¹ q.x)) (G₀ q) := by
        simpa only [Reads,if_pos (nonwrapping_placement B o hsize)] using placed_reads B o hsize hb (F.scaled θ⁻¹ q.x)
    have hcost(q : Coefficient F n)(p : Probe G d): runProbe F p q.x=jet A p θ o (G₀ q):= by simpa only [F.coords.apply_symm_apply, LinearMap.map_zero,F.scaled_inv (show θ ≠ 0 from R.p.threshold_pos.ne')] using charged F A θ (hG q) p
    have hS: ∀ w≥0, ‖projection F A θ o q - projection F A θ o v‖ ≤ (probe_budget F).choose_spec.choose * w:= by
        intro w hw'; apply le_trans (norm_le_size ..)
        apply (probe_budget F).choose_spec.choose_spec.2 _ w hw'
        rintro ⟨J,k⟩ hk
        let p : Probe G d:=⟨J,k⟩
        have hg:=jet_sum (P:=R.p) (fun i=>(hs i).1) (fun i=>(hs i).2) (ha.add hh) ht0 d ((hw _).sub (hw _)) hd A (θ • J) k (Nat.le_of_lt_succ k.isLt)
        have j0 (f g:Config G n→ℂ) (hf:ContDiffAt ℝ (k.val:WithTop ℕ∞) (f ∘ A.testLinks d o (θ • J)) 0)(hg:ContDiffAt ℝ (k.val:WithTop ℕ∞) (g ∘ A.testLinks d o (θ • J)) 0): jet A p θ o (f-g) = jet A p θ o f-jet A p θ o g:= by
            exact iteratedDeriv_fun_sub hf hg
        have H := (Q.hasSum.sub V.hasSum).mapL (runProbe F p)
        have hin (i): runProbe F p (vector F A θ o (q.regular i) - vector F A θ o (v.regular i)) = jet A p θ o (q.regular i-v.regular i):= by
           rw [map_sub,jet_vector _ _ _ (hq.smooth i) hd,jet_vector _ _ _ (hv.smooth i) hd]
           exact (j0 _ _ (h0 i q hq p) (h0 i v hv p)).symm
        have hg': HasSum (fun i=>runProbe F p (vector F A θ o (q.regular i) - vector F A θ o (v.regular i))) (jet A p θ o (G₀ v-G₀ q)):= by simpa only [hin,jet,p,comp_def] using hg
        rw [j0 (G₀ v) (G₀ q) ((hG v _).1.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt))) ((hG q _).1.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt)))] at hg'
        have HT:=HasSum.unique H hg'
        rw [←hcost,←hcost,_root_.map_sub,sub_eq_sub_iff_add_eq_add] at HT
        have HE: runProbe F p (projection F A θ o q) = runProbe F p (projection F A θ o v):=by
            simpa only [projection,map_add,add_comm (runProbe F p q.x)] using HT
        change ‖runProbe F p (projection F A θ o q - projection F A θ o v)‖ ≤ _
        simpa only [map_sub,HE,sub_self,norm_zero]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [mul_zero] using hS 0 le_rfl))
end
end YM.Trace.Physical.Germ
